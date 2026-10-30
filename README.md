# Energy image density in Lean 4

A Lean 4 / Mathlib formalisation of the energy image density (EID) property for
Dirichlet structures, following the short proof of Eriksson-Bique and Murugan,
together with the part of the De Philippis–Rindler structure theorem that this
proof uses.

All mathematical results formalised here are due to their authors (see
[Sources](#sources)); no new mathematical result is claimed. To our knowledge
(searches of 29 October 2026), this is the first formal verification of the EID
property, both in the formulation of Eriksson-Bique–Murugan and in the printed
sigma-finite formulation of Bouleau–Hirsch.

## Main statements

Each statement below is checked by the Lean kernel and depends only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Energy image density:

- `DprBridge.TextStatements.ebm_theorem_1_7`: every carré du champ of a Dirichlet
  structure in the sense of Eriksson-Bique–Murugan, Definition 1.1 (a local
  Dirichlet form on a probability space), has the EID property
  (Eriksson-Bique–Murugan, Theorem 1.7).
- `DprBridge.eid_unconditional`: the same property for Bouleau's error
  structures on a probability space, for finite tuples in the domain.
- `DprBridge.BH1991.bh1991_printed_eid_conjecture`: the EID statement as printed
  by Bouleau and Hirsch (1991; definitions in Chapter I, EID in Chapter V, p. 185,
  and Notes, p. 302), on a sigma-finite measure space, without the probability and
  constants hypotheses. The proof follows the normal-current method of
  Eriksson-Bique–Murugan (Section 4.2, Remark 4.12) and uses the De Philippis–Rindler
  structure theorem.
- `DprBridge.TextStatements.missingNormalContractions`: normal contractions act on
  the domain of a Dirichlet structure of Definition 1.1 and do not increase the
  energy (Bouleau–Hirsch 1991, Proposition I.3.3.1, in this local probability
  setting).

First-order De Philippis–Rindler statements (constant coefficients):

- `GeometricMeasure.ae_rank_matrixPolar_le`: for a finite square-matrix-valued
  measure whose row-wise divergence is a finite measure, the polar has rank at most
  d − 1 almost everywhere for the singular part (De Philippis–Rindler,
  Corollary 1.13).
- `GeometricMeasure.HasRectMeasureDivergence.ae_rank_polar_le` and
  `GeometricMeasure.HasRectMeasureDivergenceOn.ae_rank_polar_le`: the same rank bound
  for rectangular r × d matrices, with a global or a local equation.
- `GeometricMeasure.FirstOrderOperator.HasEquation.ae_polar_mem_waveCone`: for a
  general first-order operator with constant coefficients, a zeroth-order term and a
  measure right-hand side, the polar lies in the wave cone almost everywhere for the
  singular part (De Philippis–Rindler, Theorem 1.1 with k = 1 and Remark 1.3).
- `GeometricMeasure.VectorMeasure.ae_apply_polar_mem_of_polar_linearImage_mem` and
  `GeometricMeasure.VectorMeasure.ae_apply_polar_mem_of_polar_linearImage_mem_on`:
  transfer of such a cone condition through a linear map, globally and on a set.
- `GeometricMeasure.coordinateDePhilippisRindler`,
  `GeometricMeasure.absolutelyContinuous_volume_of_span_polar` and
  `GeometricMeasure.absolutelyContinuous_volume_of_finite_span_polar`: absolute
  continuity of a measure dominated by the masses of normal one-currents whose
  directions span the space (De Philippis–Rindler, Corollary 1.12), in the
  coordinate interface used by EID, for an arbitrary positive measure, and for a
  finite family of currents.
- `GeometricMeasure.LocalStructureContracts.targetA3`, `targetA4Local`,
  `targetA5Local`, `targetA4`, `targetA5Finite`: the rank bound, the first-order
  structure statement and Corollary 1.12 for locally finite masses and local
  equations, and their finite-mass forms.

The full list of selected declarations, modules and SHA-256 hashes is in
`MANIFEST.json`.

## Scope and limitations

- Only first-order operators with constant coefficients are covered. A Lean 4
  formalisation of the De Philippis–Rindler theorem for operators of every order,
  with variable coefficients, was made public by S. Armstrong on 23 October 2026:
  [`A-free-measures`](https://github.com/scottnarmstrong/A-free-measures).
- The functional calculus is proved for C¹ Lipschitz functions; the Lipschitz chain
  rule of Eriksson-Bique–Murugan is neither formalised nor needed.
- Non-vacuity: the hypotheses of Theorem 1.7 are instantiated by the
  one-dimensional Ornstein–Uhlenbeck structure (`DprBridge.TextStatements.ebmOU`).
  For the sigma-finite Bouleau–Hirsch statement, the only formal instance is the
  zero form on an infinite measure space (`DprBridge.BH1991.infinite_model`); a
  non-degenerate instance such as the Sobolev form on H¹(ℝ) is not formalised.
- Faithfulness of the formal definitions to the printed ones is checked by human
  and independent reading, not by the kernel.

## Building and replaying

The Lean toolchain is pinned in `lean-toolchain`; Mathlib and all transitive
dependencies are pinned in `lake-manifest.json`. From this directory:

```sh
lake exe cache get
lake build
lake env lean Replay.lean
```

`Replay.lean` checks each selected declaration, prints its axioms, then audits
every constant defined by the four libraries (`Foundations`, `ErrorCalculus`,
`GeometricMeasure`, `DprBridge`), including private and generated auxiliaries; any
axiom other than the three above makes it fail. `Heads.lean` prints the fully
explicit types of the selected declarations. `check.py` wraps these steps for an
offline machine (`python3 check.py --help`); it requires Python 3, Git, an installed
Lean toolchain of the pinned version (its `lake`, passed with `--lake`, not an Elan
proxy) and the dependencies already present in `.lake/packages` at the pinned
revisions. It never downloads anything.

## Layout

- `Foundations/`: Wiener space and Gaussian series, Hermite and chaos expansions,
  the Ornstein–Uhlenbeck semigroup, logarithmic Sobolev inequalities,
  one-dimensional Sobolev spaces and absolutely continuous functions.
- `ErrorCalculus/`: Dirichlet forms, carré du champ, error structures, EID from a
  named De Philippis–Rindler hypothesis.
- `GeometricMeasure/`: finite vector measures, polar and Lebesgue decompositions,
  normal one-currents, blow-ups, Calderón–Zygmund estimates, and the
  De Philippis–Rindler statements above. This library depends only on Mathlib and
  can be used on its own (`lake build GeometricMeasure`).
- `DprBridge/`: discharge of the De Philippis–Rindler hypothesis, the
  Eriksson-Bique–Murugan interface, and the Bouleau–Hirsch 1991 statement.

The library trees are copied byte for byte from a private development repository;
`MANIFEST.json` records the hash of each file.

## Sources

- S. Eriksson-Bique and M. Murugan, *On the energy image density conjecture of
  Bouleau and Hirsch*, arXiv:2510.13659 (2025).
- G. De Philippis and F. Rindler, *On the structure of A-free measures and
  applications*, Ann. of Math. 184 (2016), 1017–1039.
- N. Bouleau and F. Hirsch, *Dirichlet Forms and Analysis on Wiener Space*,
  de Gruyter, 1991.
- N. Bouleau, *Error Calculus for Finance and Physics: The Language of Dirichlet
  Forms*, de Gruyter, 2003.

## Licence and citation

Copyright 2026 Victor Rabiet. Released under the Apache License, Version 2.0; see
`LICENSE`.

Developed with the assistance of AI tools (OpenAI Codex and ChatGPT; Anthropic
Claude Opus 5.5 and Claude Fable 5.1). All statements and proofs are checked by the
Lean kernel (see `Replay.lean`).

To cite this repository, use the metadata in `CITATION.cff` (GitHub's “Cite this
repository” button), or:

```bibtex
@software{Rabiet_EID_Lean_2026,
  author  = {Rabiet, Victor},
  title   = {Energy image density in {Lean} 4},
  year    = {2026},
  version = {1.0},
  url     = {https://github.com/HubHubHubHubHub/energy-image-density-lean}
}
```
