module

public import Zkc.Realization.QueryContinuation
public import Zkc.Realization.AnswerReads

@[expose] public section

/-! Connect saved, kind-indexed answers to the actual controller operands.
Different oracle kinds may share one value type while owning different arenas.
The association keeps the kind until the physical reads have been justified;
only the resulting ordered value tuple forgets it. -/
set_option autoImplicit false
namespace Zkc.Realization.QueryAnswerReads
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {Kind : Type} {model : DomainModel} {answerType : Kind → Ty}

/-- Change only the tuple's type index after its kind-specific reads are proved. -/
def values : {kinds : List Kind} →
    Values (fun kind ↦ model.Value (answerType kind)) kinds →
      Values model.Value (kinds.map answerType)
  | _, .nil => .nil
  | _, .cons value rest => .cons value (values rest)

/-- The controller must establish these reached operands from its saved frame
and current arenas. Equal answer types alone cannot supply this association. -/
inductive ArenaOperands (model : DomainModel) (answerType : Kind → Ty)
    (arenas : (kind : Kind) → List (model.Value (answerType kind)))
    (environment : Domain.Environment model.toCarriers) :
    {kinds : List Kind} → AnswerReads.Placement (kinds.map answerType) → List Nat → Prop where
  | nil : ArenaOperands model answerType arenas environment (kinds := []) .nil []
  | cons {kind : Kind} {kinds : List Kind} {arena index slot : Nat}
      {rest : AnswerReads.Placement (kinds.map answerType)} {indices : List Nat}
      (inputData : (Primitive.sequenceAt (answerType kind)).arguments.all Domain.localType = true)
      (outputData : (Primitive.sequenceAt (answerType kind)).results.all Domain.localType = true)
      (read : Domain.read environment [arena, index] = Domain.encodeValues
        (tys := [.sequence (answerType kind), .index]) (.cons (arenas kind) (.cons slot .nil)))
      (tail : ArenaOperands model answerType arenas environment rest indices) :
      ArenaOperands model answerType arenas environment
        (kinds := kind :: kinds) (.cons arena index rest) (slot :: indices)

theorem ArenaOperands.readback
    {arenas : (kind : Kind) → List (model.Value (answerType kind))}
    {environment : Domain.Environment model.toCarriers} {kinds : List Kind}
    {placement : AnswerReads.Placement (kinds.map answerType)} {indices : List Nat}
    {answers : Values (fun kind ↦ model.Value (answerType kind)) kinds}
    (operands : ArenaOperands model answerType arenas environment placement indices)
    (read : QueryContinuation.AnswersRead arenas indices answers) :
    AnswerReads.Readback model environment placement (values answers) := by
  induction operands with
  | nil => cases read; exact .nil
  | cons inputData outputData actual tail ih =>
    cases read with
    | cons found rest => exact .cons _ _ inputData outputData actual found (ih rest)

set_option backward.isDefEq.respectTransparency false in
theorem ArenaOperands.extended
    {arenas : (kind : Kind) → List (model.Value (answerType kind))}
    {environment : Domain.Environment model.toCarriers} {kinds : List Kind}
    {placement : AnswerReads.Placement (kinds.map answerType)} {indices : List Nat}
    (operands : ArenaOperands model answerType arenas environment placement indices)
    (suffix : Domain.Environment model.toCarriers) :
    ArenaOperands model answerType arenas (environment ++ suffix) placement indices := by
  induction operands with
  | nil => exact .nil
  | @cons kind kinds arena index slot rest indices inputData outputData read tail ih =>
    apply ArenaOperands.cons inputData outputData _ ih
    have encoding := Original.encodeHelperResult_eq (carriers := model.toCarriers)
      inputData (.cons (arenas kind) (.cons slot .nil))
    rw [encoding] at read ⊢
    exact RecordAllocator.read_extended _ _ _ _ read

/-- Saved answer lookup and reached operand association jointly discharge the
physical read block. Its checkpoints and complete ordered result are retained. -/
theorem ArenaOperands.actual
    {arenas : (kind : Kind) → List (model.Value (answerType kind))}
    {environment : Domain.Environment model.toCarriers} {kinds : List Kind}
    {placement : AnswerReads.Placement (kinds.map answerType)} {indices : List Nat}
    {answers : Values (fun kind ↦ model.Value (answerType kind)) kinds}
    (operands : ArenaOperands model answerType arenas environment placement indices)
    (read : QueryContinuation.AnswersRead arenas indices answers)
    (program : Program) (context : Context) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (environment ++ AnswerReads.encoded (values answers)))
      (Domain.evaluate model program context placement.instructions environment)) :=
  (operands.readback read).actual program context

end Zkc.Realization.QueryAnswerReads
