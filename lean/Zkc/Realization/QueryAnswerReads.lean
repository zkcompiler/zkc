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

/-- Installation fixes the arena of each occurrence before saved indices are
loaded. Kinds with the same answer type remain distinct here. -/
inductive Arenas (model : DomainModel) (answerType : Kind → Ty)
    (arenas : (kind : Kind) → List (model.Value (answerType kind)))
    (environment : Domain.Environment model.toCarriers) :
    {kinds : List Kind} → AnswerReads.Placement (kinds.map answerType) → Prop where
  | nil : Arenas model answerType arenas environment (kinds := []) .nil
  | cons {kind : Kind} {kinds : List Kind} {arena index : Nat}
      {rest : AnswerReads.Placement (kinds.map answerType)}
      (answerData : (answerType kind).isHandle = false)
      (read : Domain.Value.encode (ty := .sequence (answerType kind)) (arenas kind) =
        environment[arena]?)
      (tail : Arenas model answerType arenas environment rest) :
      Arenas model answerType arenas environment (kinds := kind :: kinds) (.cons arena index rest)

theorem Arenas.extended
    {arenas : (kind : Kind) → List (model.Value (answerType kind))}
    {environment : Domain.Environment model.toCarriers} {kinds : List Kind}
    {placement : AnswerReads.Placement (kinds.map answerType)}
    (installed : Arenas model answerType arenas environment placement)
    (suffix : Domain.Environment model.toCarriers) :
    Arenas model answerType arenas (environment ++ suffix) placement := by
  induction installed with
  | nil => exact .nil
  | @cons kind kinds arena index rest answerData read tail ih =>
      refine .cons answerData ?_ ih
      obtain ⟨value, encoded⟩ := Domain.Value.encode_local_exists (carriers := model.toCarriers)
        (ty := .sequence (answerType kind))
        (by simp [Domain.localType, Domain.dataType, Ty.isHandle, answerData]) (arenas kind)
      rw [encoded] at read ⊢
      exact (Original.read_append read.symm suffix).symm

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

/-- The saved index tuple and installed arenas construct every physical read
operand. No companion reconstructs the generated read traversal. -/
theorem Arenas.operands
    {arenas : (kind : Kind) → List (model.Value (answerType kind))}
    {environment : Domain.Environment model.toCarriers} {kinds : List Kind}
    {placement : AnswerReads.Placement (kinds.map answerType)}
    (installed : Arenas model answerType arenas environment placement)
    (indices : List Nat)
    (read : Domain.read environment placement.indices =
      some (indices.map (fun index ↦ Domain.Value.data (.index index)))) :
    ArenaOperands model answerType arenas environment placement indices := by
  induction installed generalizing indices with
  | nil =>
      have empty : indices = [] := by simpa [Domain.read, AnswerReads.Placement.indices] using read.symm
      subst indices
      exact .nil
  | @cons kind kinds arena index rest answerData arenaRead tail ih =>
      cases current : environment[index]? with
      | none => simp [Domain.read, AnswerReads.Placement.indices, current] at read
      | some value =>
          cases remaining : Domain.read environment rest.indices with
          | none =>
              simp only [Domain.read] at remaining
              simp [Domain.read, AnswerReads.Placement.indices, current, remaining] at read
          | some values =>
              have remainingMap := remaining
              simp only [Domain.read] at remainingMap
              have joined : value :: values = indices.map (fun index ↦ Domain.Value.data (.index index)) := by
                apply Option.some.inj
                simpa [Domain.read, AnswerReads.Placement.indices, current, remainingMap] using read
              cases indices with
              | nil => cases joined
              | cons slot indices =>
                  obtain ⟨head, restValues⟩ := List.cons.inj joined
                  subst value
                  subst values
                  apply ArenaOperands.cons
                    (by simp [Primitive.arguments, Domain.localType, Domain.dataType, Ty.isHandle, answerData])
                    (by simp [Primitive.results, Domain.localType, Domain.dataType, answerData]) _ (ih indices remaining)
                  simp [Domain.read, ← arenaRead, current, Domain.encodeValues_cons,
                    Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle]

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
