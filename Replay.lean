import EidFormal
import Lean

#check DprBridge.eid_unconditional
#print axioms DprBridge.eid_unconditional
#check DprBridge.TextStatements.ebm_theorem_1_7
#print axioms DprBridge.TextStatements.ebm_theorem_1_7
#check DprBridge.BH1991.bh1991_printed_eid_conjecture
#print axioms DprBridge.BH1991.bh1991_printed_eid_conjecture
#check GeometricMeasure.ae_rank_matrixPolar_le
#print axioms GeometricMeasure.ae_rank_matrixPolar_le
#check GeometricMeasure.coordinateDePhilippisRindler
#print axioms GeometricMeasure.coordinateDePhilippisRindler
#check GeometricMeasure.VectorMeasure.ae_apply_polar_mem_of_polar_linearImage_mem
#print axioms GeometricMeasure.VectorMeasure.ae_apply_polar_mem_of_polar_linearImage_mem
#check GeometricMeasure.VectorMeasure.ae_apply_polar_mem_of_polar_linearImage_mem_on
#print axioms GeometricMeasure.VectorMeasure.ae_apply_polar_mem_of_polar_linearImage_mem_on
#check GeometricMeasure.HasRectMeasureDivergence.ae_rank_polar_le
#print axioms GeometricMeasure.HasRectMeasureDivergence.ae_rank_polar_le
#check GeometricMeasure.HasRectMeasureDivergenceOn.ae_rank_polar_le
#print axioms GeometricMeasure.HasRectMeasureDivergenceOn.ae_rank_polar_le
#check GeometricMeasure.FirstOrderOperator.HasEquation.ae_polar_mem_waveCone
#print axioms GeometricMeasure.FirstOrderOperator.HasEquation.ae_polar_mem_waveCone
#check GeometricMeasure.absolutelyContinuous_volume_of_finite_span_polar
#print axioms GeometricMeasure.absolutelyContinuous_volume_of_finite_span_polar
#check GeometricMeasure.LocalStructureContracts.targetA3
#print axioms GeometricMeasure.LocalStructureContracts.targetA3
#check GeometricMeasure.LocalStructureContracts.targetA4Local
#print axioms GeometricMeasure.LocalStructureContracts.targetA4Local
#check GeometricMeasure.LocalStructureContracts.targetA5Local
#print axioms GeometricMeasure.LocalStructureContracts.targetA5Local
#check GeometricMeasure.LocalStructureContracts.targetA4
#print axioms GeometricMeasure.LocalStructureContracts.targetA4
#check GeometricMeasure.LocalStructureContracts.targetA5Finite
#print axioms GeometricMeasure.LocalStructureContracts.targetA5Finite
#check GeometricMeasure.absolutelyContinuous_volume_of_span_polar
#print axioms GeometricMeasure.absolutelyContinuous_volume_of_span_polar
#check DprBridge.TextStatements.missingNormalContractions
#print axioms DprBridge.TextStatements.missingNormalContractions

-- Audit traversal only; no change to the imported mathematical proofs.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut total := 0
  let mut totalModules := 0
  for ns in [`Foundations, `ErrorCalculus, `GeometricMeasure, `DprBridge] do
    -- Select by defining module, including declarations in external namespaces.
    let names := env.constants.toList.map Prod.fst |>.filter (fun name =>
      match env.getModuleIdxFor? name with
      | none => false
      | some idx => ns.isPrefixOf env.header.moduleNames[idx]!)
    let names := names.mergeSort (fun a b => a.toString ≤ b.toString)
    let modules := env.header.moduleNames.filter (fun name => ns.isPrefixOf name)
    totalModules := totalModules + modules.size
    logInfo m!"AUDIT_LIBRARY={ns} MODULES={modules.size} DECLARATIONS={names.length}"
    total := total + names.length
    for name in names do
      elabCommand (← `(command| #print axioms $(mkIdent name)))
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unexpected foundational constant {axiomName} in {name}"
  unless totalModules == 407 do
    throwError "Imported module count differs from the export manifest: {totalModules}"
  logInfo m!"AUDIT_MODULES={totalModules}"
  logInfo m!"AUDIT_DECLARATIONS={total}"
  logInfo "AUDIT_OK: only propext, Classical.choice, Quot.sound"
