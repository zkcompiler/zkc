module

public import ZkcExamples.Structured.SumcheckReduceLaws
public import ZkcExamples.Structured.SumcheckHelperBodies
public import ZkcExamples.Structured.MapPrefixContracts

@[expose] public section
namespace ZkcExamples.Structured.SumcheckReduceAssociations
open Zkc.Source Zkc.Source.Structured SumcheckReduceViews

/-! Every helper of the complete original unit has its own membership, full
signature and raw-tree witness. The imported admission phases remain in Views;
none of these facts equates this unit's meanings with another source table. -/

theorem less_member : lessDefinition ∈ unit.definitions :=
  List.mem_cons_self

theorem less_signature : lessDefinition.helper = MapFirstBodies.lessHelper := rfl

theorem less_shared_raw : lessDefinition.raw = MapFirstBodies.lessBody.erase := rfl

theorem less_association : BodyIn unit.definitions MapFirstBodies.lessHelper MapFirstBodies.lessBody :=
  ⟨lessDefinition, less_member, less_signature, less_shared_raw⟩

theorem rows_member : rowsDefinition ∈ unit.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_self)

theorem rows_signature : rowsDefinition.helper = MapFirstBodies.rowsHelper := rfl

theorem rows_shared_raw : rowsDefinition.raw = MapFirstBodies.rowsBody.erase := rfl

theorem rows_association : BodyIn unit.definitions MapFirstBodies.rowsHelper MapFirstBodies.rowsBody :=
  ⟨rowsDefinition, rows_member, rows_signature, rows_shared_raw⟩

theorem shape_member : shapeDefinition ∈ unit.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem shape_signature : shapeDefinition.helper = MapFirstBodies.shapeHelper := rfl

theorem shape_shared_raw : shapeDefinition.raw = MapFirstBodies.shapeBody.erase := rfl

theorem shape_association : BodyIn unit.definitions MapFirstBodies.shapeHelper MapFirstBodies.shapeBody :=
  ⟨shapeDefinition, shape_member, shape_signature, shape_shared_raw⟩

theorem table_member : tableDefinition ∈ unit.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem table_signature : tableDefinition.helper = MapFirstBodies.tableHelper := rfl

theorem table_shared_raw : tableDefinition.raw = MapFirstBodies.tableBody.erase := rfl

theorem table_association : BodyIn unit.definitions MapFirstBodies.tableHelper MapFirstBodies.tableBody :=
  ⟨tableDefinition, table_member, table_signature, table_shared_raw⟩

theorem width_member : widthDefinition ∈ unit.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))

theorem width_signature : widthDefinition.helper = MapFirstBodies.widthHelper := rfl

theorem width_shared_raw : widthDefinition.raw = MapFirstBodies.widthBody.erase := rfl

theorem width_association : BodyIn unit.definitions MapFirstBodies.widthHelper MapFirstBodies.widthBody :=
  ⟨widthDefinition, width_member, width_signature, width_shared_raw⟩

theorem variables_member : variablesDefinition ∈ unit.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))

theorem variables_signature : variablesDefinition.helper = MapFirstBodies.variablesHelper := rfl

theorem variables_shared_raw : variablesDefinition.raw = MapFirstBodies.variablesBody.erase := rfl

theorem variables_association : BodyIn unit.definitions MapFirstBodies.variablesHelper MapFirstBodies.variablesBody :=
  ⟨variablesDefinition, variables_member, variables_signature, variables_shared_raw⟩

theorem empty_member : emptyDefinition ∈ unit.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))

theorem empty_signature : emptyDefinition.helper = SumcheckHelperBodies.emptyHelper := rfl

theorem empty_shared_raw : emptyDefinition.raw = SumcheckHelperBodies.emptyBody.erase := rfl

theorem empty_association : BodyIn unit.definitions SumcheckHelperBodies.emptyHelper SumcheckHelperBodies.emptyBody :=
  ⟨emptyDefinition, empty_member, empty_signature, empty_shared_raw⟩

theorem halves_member : halvesDefinition ∈ unit.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))

theorem halves_signature : halvesDefinition.helper = MapFirstBodies.halvesHelper := rfl

theorem halves_shared_raw : halvesDefinition.raw = MapFirstBodies.halvesBody.erase := rfl

theorem halves_association : BodyIn unit.definitions MapFirstBodies.halvesHelper MapFirstBodies.halvesBody :=
  ⟨halvesDefinition, halves_member, halves_signature, halves_shared_raw⟩

theorem sums_member : sumsDefinition ∈ unit.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))

theorem sums_signature : sumsDefinition.helper = SumcheckHelperBodies.sumsHelper := rfl

theorem sums_shared_raw : sumsDefinition.raw = SumcheckHelperBodies.sumsBody.erase := rfl

theorem sums_association : BodyIn unit.definitions SumcheckHelperBodies.sumsHelper SumcheckHelperBodies.sumsBody :=
  ⟨sumsDefinition, sums_member, sums_signature, sums_shared_raw⟩

theorem interpolate_member : interpolateDefinition ∈ unit.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))

theorem interpolate_signature : interpolateDefinition.helper = MapFirstBodies.interpolateHelper := rfl

theorem interpolate_shared_raw : interpolateDefinition.raw = MapFirstBodies.interpolateBody.erase := rfl

theorem interpolate_association : BodyIn unit.definitions MapFirstBodies.interpolateHelper MapFirstBodies.interpolateBody :=
  ⟨interpolateDefinition, interpolate_member, interpolate_signature, interpolate_shared_raw⟩

theorem map_member : mapDefinition ∈ unit.definitions :=
  SumcheckReduceLaws.map_member

theorem map_signature : mapDefinition.helper = MapFirstBodies.mapHelper := rfl

theorem map_shared_raw : mapDefinition.raw = MapFirstBodies.mapBody.erase := rfl

theorem map_association : BodyIn unit.definitions MapFirstBodies.mapHelper MapFirstBodies.mapBody :=
  ⟨mapDefinition, map_member, map_signature, map_shared_raw⟩

theorem first_member : firstDefinition ∈ unit.definitions :=
  SumcheckReduceLaws.first_member

theorem first_signature : firstDefinition.helper = MapFirstBodies.firstHelper := rfl

theorem first_shared_raw : firstDefinition.raw = MapFirstBodies.firstBody.erase := rfl

theorem first_association : BodyIn unit.definitions MapFirstBodies.firstHelper MapFirstBodies.firstBody :=
  ⟨firstDefinition, first_member, first_signature, first_shared_raw⟩

theorem append_member : appendDefinition ∈ unit.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))

theorem append_signature : appendDefinition.helper = SumcheckHelperBodies.appendHelper := rfl

theorem append_shared_raw : appendDefinition.raw = SumcheckHelperBodies.appendBody.erase := rfl

theorem append_association : BodyIn unit.definitions SumcheckHelperBodies.appendHelper SumcheckHelperBodies.appendBody :=
  ⟨appendDefinition, append_member, append_signature, append_shared_raw⟩

theorem values_member : valuesDefinition ∈ unit.definitions :=
  SumcheckReduceLaws.values_member

theorem values_signature : valuesDefinition.helper = MapFirstBodies.valuesHelper := rfl

theorem values_shared_raw : valuesDefinition.raw = MapFirstBodies.valuesBody.erase := rfl

theorem values_association : BodyIn unit.definitions MapFirstBodies.valuesHelper MapFirstBodies.valuesBody :=
  ⟨valuesDefinition, values_member, values_signature, values_shared_raw⟩

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

theorem helper_inventory_length : unit.definitions.length = 14 := rfl

/-- This is literal source identity; it is not a verifier or security bound. -/
theorem repeat_metadata :
    ProtocolOp.repeat
      ⟨SumcheckReduceBodies.repeatState, [.service "random.bls12-381.fr/0"],
        [0, 1], [[0], [0], [0], [0], [1], [1]], 4⟩ "s15" ∈
      reduceDefinition.raw.operations :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))))))

/-- Preserve this original caller's application context. -/
theorem application_context :
    ProtocolOp.protocolApply SumcheckReduceBodies.reduceSignature [0, 1]
      "s3" ∈ runDefinition.raw.operations :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))

/-- Reduction's actual helper inventory has no terminal checker or prefix chain. -/
theorem terminal_helpers_absent :
    SumcheckHelperBodies.checkHelper ∉ unit.definitions.map CheckedDefinition.helper ∧
    SumcheckHelperBodies.checkTableHelper ∉ unit.definitions.map CheckedDefinition.helper ∧
    MapPrefixBodies.prefixHelper ∉ unit.definitions.map CheckedDefinition.helper := by decide +kernel

end ZkcExamples.Structured.SumcheckReduceAssociations
