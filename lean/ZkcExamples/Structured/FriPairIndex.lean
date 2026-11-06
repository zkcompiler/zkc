module

public import ZkcExamples.Structured.FriApplications
public import Zkc.Source.Structured.ProtocolEmbeddingCheck
public import Zkc.Source.Structured.OracleReferenceLaws
public import Zkc.Source.Structured.WordDerivation

@[expose] public section

/-! The virtual Fold and the protocol verifier call the same pair-index
helper in different installed tables. Both use its ordinary body law. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriPairIndex
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews
attribute [local implicit_reducible] Op.arguments Op.results ProtocolOp.arguments ProtocolOp.results

theorem pairResult (model : DomainModel)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface) (position rows : Nat) :
    helper14Body.denote (Evaluation.meaningOn model SiteObservations.closed table)
      (Values.cons (Value := model.Value) (ty := .index) position (.cons rows .nil)).get =
      .done (.cons (bitAnd position (wrappingSubtract (logicalShiftRight rows 1) 1)) .nil) := by
  derive_word_process

def law (model : DomainModel) : ReferenceLaw model helper14Helper.inputs helper14Helper.outputs where
  body := helper14Body
  Requires _ _ := True
  reference
    | .cons position (.cons rows .nil) => .returned (.cons
        (bitAnd position (wrappingSubtract (logicalShiftRight rows 1) 1)) .nil)
  valid table
    | .cons position (.cons rows .nil), _ => pairResult model table position rows

theorem mathFragment : ProtocolEmbedding.MathFragment unit.definitions :=
  ProtocolEmbedding.checkMathFragment_sound _ (by kernel_rfl)

theorem verifier (model : DomainModel) (position rows : Nat) :
    invoke (unit.oracleCalculations model 1) helper14Helper
      (.cons (some (ProtocolValue.ofConcrete .index position)) (.cons (some (ProtocolValue.ofConcrete .index rows)) .nil)) =
      .done (.cons (some (ProtocolValue.ofConcrete .index
        (bitAnd position (wrappingSubtract (logicalShiftRight rows 1) 1)))) .nil) := by
  exact (law model).invokeOracleConcrete unit 1 rfl mathFragment unit.linked
    (by exact_body helper14Definition) (.cons position (.cons rows .nil)) trivial

end ZkcExamples.Structured.FriPairIndex
