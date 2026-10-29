module

public import ZkcExamples.Executable.SumcheckCompleteness
public import Tests.SumcheckFamilyControls

@[expose] public section

/-! Stopping branches and the exact extra admission required by canonical typed
requests. Local controls quantify arbitrary nominal descriptions and histories. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace Tests.SumcheckFamilyStops
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Construction.Uniform Zkc.Construction.Uniform.DomainAdapter
open ZkcExamples.Executable

variable {F G : Type} [Field F] [DecidableEq F]
variable (shape : SumcheckFamily.Source.Shape) (oracle : History F G → F) (initial : History F G)
  (index : Nat) (point : List F) (claim : F) (history : Domain.History (Structured.uniformCarriers F G))

theorem missing_first : run (m := Id) Origin.withoutCoordinates initial oracle
    (SumcheckFamily.Source.roundState shape index point claim history) [] = (.stopped .refused, []) := rfl

theorem wrong_first (proof : Proof F G) : run (m := Id) Origin.withoutCoordinates initial oracle
    (SumcheckFamily.Source.roundState shape index point claim history) (.boolean false :: proof) =
      (.stopped .refused, .boolean false :: proof) := rfl

theorem missing_second (low : F) : run (m := Id) Origin.withoutCoordinates initial oracle
    (SumcheckFamily.Source.roundState shape index point claim history) [.field shape.names.scalar low] =
      (.stopped .refused, []) := by
  simp only [DomainAdapter.run, DomainAdapter.runK, SumcheckFamily.Source.roundState, Value.decode, ite_true]
  rfl

theorem wrong_second (low : F) (proof : Proof F G) : run (m := Id) Origin.withoutCoordinates initial oracle
    (SumcheckFamily.Source.roundState shape index point claim history)
      (.field shape.names.scalar low :: .boolean true :: proof) =
      (.stopped .refused, .boolean true :: proof) := by
  simp only [DomainAdapter.run, DomainAdapter.runK, SumcheckFamily.Source.roundState, Value.decode, ite_true]
  rfl

theorem false_round (low high : F) (proof : Proof F G) (wrong : claim ≠ low + high) :
    run (m := Id) Origin.withoutCoordinates initial oracle
      (SumcheckFamily.Source.roundState shape index point claim history)
      (.field shape.names.scalar low :: .field shape.names.scalar high :: proof) =
        (.stopped .reject, proof) := by
  simp only [DomainAdapter.run, DomainAdapter.runK, SumcheckFamily.Source.roundState, Value.decode, ite_true, wrong, ite_false]
  rfl

omit claim history in
/-- An unrepresentable nominal suffix refuses before invoking the scalar
oracle; both messages have been consumed and the exact tail remains unread. -/
theorem unreadable_suffix (low high : F) (proof : Proof F G) :
    run (m := Id) Origin.withoutCoordinates initial oracle
      (SumcheckFamily.Source.roundState shape index point (low + high) [.publicBinding ⟨"test", []⟩])
      (.field shape.names.scalar low :: .field shape.names.scalar high :: proof) =
        (.stopped .refused, proof) := by
  simp [DomainAdapter.run, DomainAdapter.runK, SumcheckFamily.Source.roundState, Value.decode, SumcheckFamily.Source.drawOrigin,
    query, readbackHistory, readbackEvent, Domain.drawRequest, Request.draw]
  rfl

/-- Mere origin presence from the old interface admits a non-draw request. -/
def malformedContext : Context :=
  Tests.SumcheckFamilyControls.actual.description.context.mapReplacement fun replacement =>
    { replacement with request := some ⟨"unsupported", [], .field "bls12-381.fr"⟩ }

def malformedDescription : SumcheckFamily.ProgramShape.Description :=
  { Tests.SumcheckFamilyControls.actual.description with context := malformedContext, suite := rfl }

theorem old_origin_presence :
    (malformedDescription.names.firstMessage.origin malformedContext).isSome ∧
    (malformedDescription.names.secondMessage.origin malformedContext).isSome ∧
    (malformedDescription.names.draw.origin malformedContext).isSome ∧
    (malformedDescription.names.delivery.origin malformedContext).isSome := by decide +kernel

theorem malformed_query_none (index : Nat) :
    Domain.queryOrigin malformedContext malformedDescription.names.suite malformedDescription.names.scalar
      malformedDescription.names.draw [index] = none := by rfl

theorem malformed_occurrences_impossible : ¬ SumcheckFamily.Source.Occurrences malformedDescription := by
  intro admitted
  have result := admitted.draw 0
  change none = some _ at result
  cases result

/-- The raw native lowering check is unchanged, but nominal request admission
rejects this context with its exact finite-check diagnostic. -/
theorem malformed_native_refused : DomainVM.checkNativeLowering malformedDescription.program malformedContext
    installed Tests.SumcheckFamilyControls.actual.participant Tests.SumcheckFamilyControls.actual.validator =
      .error (.different "nominal operation scope") := by
  unfold DomainVM.checkNativeLowering
  have checked : checkLowering installed Tests.SumcheckFamilyControls.actual.participant
      Tests.SumcheckFamilyControls.actual.validator = .ok SumcheckProof.lowered := SumcheckProof.accepted
  rw [checked]
  kernel_rfl

/-- A short binding cannot satisfy the fixed framing header, even at zero
rounds where there are no message bytes to mask its actual length. -/
theorem short_binding_header (binding : List UInt8) (short : binding.length < 32) :
    ((magic ++ binding).take 40).length < 40 := by
  have length : magic.length = 8 := rfl
  simp only [List.length_take, List.length_append, length]
  omega

end Tests.SumcheckFamilyStops
