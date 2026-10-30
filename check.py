#!/usr/bin/env python3
"""Offline local launcher. Never invokes Elan, updates packages, or fetches caches.
Use --lake /absolute/path/to/installed/bin/lake, then preflight/build/replay/heads/help.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unicodedata
import uuid

P = Path(__file__).resolve().parent


def canonical(path):
    """Resolved path in Unicode NFC, so that NFC and NFD spellings of one directory compare equal."""
    return Path(unicodedata.normalize('NFC', str(Path(path).resolve())))


def within(path, root):
    return canonical(path).is_relative_to(canonical(root))


def date():
    return subprocess.check_output(['date', '+%Y-%m-%d %H:%M:%S %Z'], text=True).strip()


def state(root):
    result = {}
    for parent, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d != '.git')
        for name in sorted(files):
            path = Path(parent) / name
            if path.is_symlink():
                if not path.resolve().is_relative_to(root.resolve()):
                    raise RuntimeError('Dependency symlink escapes clone: ' + str(path))
                result[str(path.relative_to(root))] = ['symlink', str(path.readlink())]
                continue
            st = path.stat()
            result[str(path.relative_to(root))] = [st.st_size, st.st_mtime_ns]
        for name in dirs:
            if (Path(parent) / name).is_symlink():
                raise RuntimeError('Dependency directory symlink: ' + str(Path(parent) / name))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', type=Path, required=True)
    parser.add_argument('action', choices=['preflight', 'build', 'replay', 'heads', 'help'])
    parser.add_argument('--internal-artifacts', type=Path,
                        help='Read existing artifacts of the four internal projects for heads only')
    args = parser.parse_args()
    lake = args.lake.absolute()
    if not lake.is_file() or not (lake.parent / 'lean').is_file():
        parser.error('An installed toolchain with lake and lean is required; no Elan proxy')
    if args.internal_artifacts and args.action != 'heads':
        parser.error('--internal-artifacts is available only for read-only head comparison')
    stamp = subprocess.check_output(['date', '+%Y%m%d_%H%M%S'], text=True).strip()
    log = P / '.lake/m10-check' / (stamp + '_' + args.action + '_' + uuid.uuid4().hex[:8])
    log.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LAKE_CACHE_DIR='', MATHLIB_NO_CACHE_ON_UPDATE='1',
               GIT_ALLOW_PROTOCOL='', GIT_TERMINAL_PROMPT='0', LEAN_NUM_THREADS='2')
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env['PATH'] = str(lake.parent) + os.pathsep + env.get('PATH', '')
    records = []
    def run(label, command, run_env=env):
        start, tic = date(), time.monotonic()
        with (log / (label + '.log')).open('w') as output:
            code = subprocess.run(command, cwd=P, env=run_env, stdout=output,
                                  stderr=subprocess.STDOUT).returncode
        row = dict(label=label, command=[str(c) for c in command], cwd=str(P),
                   start=start, end=date(), duration_seconds=round(time.monotonic()-tic, 3), code=code)
        records.append(row)
        print(json.dumps(row), flush=True)
        (log / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        return code
    prefix = [str(lake), '--no-cache']
    if args.action == 'help':
        return run('help', prefix + ['build', '--help'])
    manifest = json.loads((P / 'lake-manifest.json').read_text())
    packages = P / '.lake/packages'
    if any(folder.is_symlink() for folder in [P / '.lake', P / '.lake/build', packages]):
        raise RuntimeError('Export build/cache directories must be independent, not symlinks')
    for package in manifest['packages']:
        root = packages / package['name']
        if package['type'] != 'git' or root.is_symlink():
            raise RuntimeError('Non-independent dependency: ' + package['name'])
        rev = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'],
                                      env=env, text=True).strip()
        if rev != package['rev']:
            raise RuntimeError('Dependency revision mismatch: ' + package['name'])
    before = state(packages)
    (log / 'dependencies-before.json').write_text(json.dumps(before, sort_keys=True) + '\n')
    code = 1
    try:
        # Lake checks all transitive fingerprints without running build jobs.
        code = run('dependencies-no-build', prefix + ['--no-build', 'build', 'Mathlib'])
        if code:
            print('STOP: dependencies require rebuilding; no build or replay attempted', flush=True)
            return code
        code = run('lean-path', prefix + ['env', 'printenv', 'LEAN_PATH'])
        if code:
            return code
        # Lake may print a manifest warning before printenv's single output line.
        path_lines = (log / 'lean-path.log').read_text().strip().splitlines()
        if not path_lines:
            raise RuntimeError('Missing LEAN_PATH output')
        paths = path_lines[-1].split(os.pathsep)
        paths = [str((P / p).resolve()) if not Path(p).is_absolute() else str(Path(p).resolve()) for p in paths]
        for path in paths:
            if not (within(path, P) or within(path, lake.parent.parent)):
                raise RuntimeError('Lean search path escapes the export/toolchain: ' + path)
        if args.action == 'preflight':
            return 0
        if args.action == 'build':
            code = run('build', prefix + ['build'])
        elif args.internal_artifacts:
            # Lean reads .olean files from internal projects, never writes there.
            # Lake is used only in this export to obtain the external search path.
            internal = args.internal_artifacts.absolute()
            local = [str(internal / p / '.lake/build/lib/lean') for p in
                     ['D_fondations', 'C_lean', 'H_eid', 'K_pont_dpr']]
            paths = [p for p in paths if canonical(p) != canonical(P / '.lake/build/lib/lean')]
            read_env = dict(env, LEAN_PATH=os.pathsep.join(local + paths))
            code = run('heads-internal', [str(lake.parent / 'lean'), 'Heads.lean'], read_env)
        else:
            file = 'Replay.lean' if args.action == 'replay' else 'Heads.lean'
            code = run(args.action, prefix + ['env', 'lean', file])
        return code
    finally:
        after = state(packages)
        # A refusal raised after a successful step must not be reported as code 0.
        if sys.exc_info()[0] is not None:
            code = 2
        result = dict(dependency_artifacts_unchanged=before == after,
                      dependency_files=len(before), code=code,
                      before_sha256=hashlib.sha256(json.dumps(before, sort_keys=True).encode()).hexdigest(),
                      after_sha256=hashlib.sha256(json.dumps(after, sort_keys=True).encode()).hexdigest())
        (log / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result), flush=True)
        print('LOG_DIR=' + str(log), flush=True)
        if before != after:
            raise RuntimeError('Dependency artifacts changed; stop and investigate before any further build')


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
        print('CHECK_REFUSED: ' + str(exc), file=sys.stderr)
        raise SystemExit(2)
