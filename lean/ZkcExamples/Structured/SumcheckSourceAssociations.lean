module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.SumcheckSourceLaws
public import ZkcExamples.Structured.SumcheckHelperBodies
public import ZkcExamples.Structured.MapPrefixContracts
public import ZkcExamples.Structured.SumcheckSourceNormalForms

@[expose] public section
namespace ZkcExamples.Structured.SumcheckSourceAssociations
open Zkc.Source Zkc.Source.Structured SumcheckSourceViews

/-! Every non-formula helper of the complete original unit has its own
membership, full signature and raw-tree witness; `SumcheckContractBindings`
associates the formula helpers. The imported admission phases remain in Views;
none of these facts equates this unit's meanings with another source table. -/

structured_associations SumcheckSourceViews
  [less := MapFirstBodies.less, rows := MapFirstBodies.rows, shape := MapFirstBodies.shape,
    table := MapFirstBodies.table, width := MapFirstBodies.width,
    «variables» := MapFirstBodies.variables, empty := SumcheckHelperBodies.empty,
    halves := MapFirstBodies.halves, sums := SumcheckHelperBodies.sums,
    interpolate := MapFirstBodies.interpolate, map := MapFirstBodies.map,
    first := MapFirstBodies.first, append := SumcheckHelperBodies.append,
    step := MapPrefixBodies.step, foldStep := MapPrefixBodies.foldStep,
    fold := MapPrefixBodies.fold, foldWrapper := MapPrefixBodies.foldWrapper,
    «prefix» := MapPrefixBodies.prefix, values := MapFirstBodies.values,
    valuesRealization := MapFirstBodies.valuesRealization,
    checkTable := SumcheckHelperBodies.checkTable, check := SumcheckHelperBodies.check]

theorem first_bodies : MapFirstContracts.Bodies unit.definitions :=
  ⟨less_association, rows_association, shape_association, table_association,
    halves_association, interpolate_association, map_association, first_association⟩

theorem prefix_bodies : MapPrefixContracts.Bodies unit.definitions :=
  ⟨step_association, foldStep_association, fold_association, foldWrapper_association,
    prefix_association, values_association, valuesRealization_association⟩

/-- Both actual protocol trees retain their own complete signatures and membership. -/
theorem protocols_exact :
    (runDefinition ∈ unit.protocols ∧
      runDefinition.signature = SumcheckSourceBodies.runSignature ∧
      runDefinition.raw = SumcheckSourceBodies.runBody.erase) ∧
    (reduceDefinition ∈ unit.protocols ∧
      reduceDefinition.signature = SumcheckSourceBodies.reduceSignature ∧
      reduceDefinition.raw = SumcheckSourceBodies.reduceBody.erase) :=
  ⟨⟨run_member, run_signature, run_raw⟩, ⟨reduce_member, reduce_signature, reduce_raw⟩⟩

theorem helper_inventory_length : unit.definitions.length = 27 := rfl

/-- This is literal source identity; it is not a verifier or security bound. -/
theorem repeat_metadata :
    ProtocolOp.repeat (SumcheckVerifierBodies.repeatSpec SumcheckSourceNormalForms.reduceMaximum) "s15" ∈
      reduceDefinition.raw.operations :=
  by structured_mem

/-- Preserve this original caller's application context. -/
theorem application_context :
    ProtocolOp.protocolApply SumcheckSourceBodies.reduceSignature [0, 1]
      "label_726564756365" ∈ runDefinition.raw.operations :=
  by structured_mem

end ZkcExamples.Structured.SumcheckSourceAssociations
