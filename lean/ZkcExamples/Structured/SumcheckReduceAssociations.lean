module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.SumcheckReduceLaws
public import ZkcExamples.Structured.SumcheckHelperBodies
public import ZkcExamples.Structured.MapPrefixContracts
public import ZkcExamples.Structured.SumcheckReductionNormalForms

@[expose] public section
namespace ZkcExamples.Structured.SumcheckReduceAssociations
open Zkc.Source Zkc.Source.Structured SumcheckReduceViews

/-! Every non-formula helper of the complete original unit has its own
membership, full signature and raw-tree witness; `SumcheckContractBindings`
associates the formula helpers. The imported admission phases remain in Views;
none of these facts equates this unit's meanings with another source table. -/

structured_associations SumcheckReduceViews
  [less := MapFirstBodies.less, rows := MapFirstBodies.rows, shape := MapFirstBodies.shape,
    table := MapFirstBodies.table, width := MapFirstBodies.width,
    «variables» := MapFirstBodies.variables, empty := SumcheckHelperBodies.empty,
    halves := MapFirstBodies.halves, sums := SumcheckHelperBodies.sums,
    interpolate := MapFirstBodies.interpolate, map := MapFirstBodies.map,
    first := MapFirstBodies.first, append := SumcheckHelperBodies.append,
    values := MapFirstBodies.values]

theorem first_bodies : MapFirstContracts.Bodies unit.definitions :=
  ⟨less_association, rows_association, shape_association, table_association,
    halves_association, interpolate_association, map_association, first_association⟩

/-- Both actual protocol trees retain their own complete signatures and membership. -/
theorem protocols_exact :
    (runDefinition ∈ unit.protocols ∧
      runDefinition.signature = SumcheckReduceBodies.runSignature ∧
      runDefinition.raw = SumcheckReduceBodies.runBody.erase) ∧
    (reduceDefinition ∈ unit.protocols ∧
      reduceDefinition.signature = SumcheckReduceBodies.reduceSignature ∧
      reduceDefinition.raw = SumcheckReduceBodies.reduceBody.erase) :=
  ⟨⟨run_member, run_signature, run_raw⟩, ⟨reduce_member, reduce_signature, reduce_raw⟩⟩

theorem helper_inventory_length : unit.definitions.length = 18 := rfl

/-- This is literal source identity; it is not a verifier or security bound. -/
theorem repeat_metadata :
    ProtocolOp.repeat (SumcheckVerifierBodies.repeatSpec SumcheckReductionNormalForms.reduceMaximum) "s15" ∈
      reduceDefinition.raw.operations :=
  by structured_mem

/-- Preserve this original caller's application context. -/
theorem application_context :
    ProtocolOp.protocolApply SumcheckReduceBodies.reduceSignature [0, 1]
      "s3" ∈ runDefinition.raw.operations :=
  by structured_mem

/-- Reduction's actual helper inventory has no terminal checker or prefix chain. -/
theorem terminal_helpers_absent :
    SumcheckHelperBodies.checkHelper ∉ unit.definitions.map CheckedDefinition.helper ∧
    SumcheckHelperBodies.checkTableHelper ∉ unit.definitions.map CheckedDefinition.helper ∧
    MapPrefixBodies.prefixHelper ∉ unit.definitions.map CheckedDefinition.helper := by decide +kernel

end ZkcExamples.Structured.SumcheckReduceAssociations
