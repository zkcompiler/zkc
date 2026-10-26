module

public import ZkcExamples.Construction.SumcheckDomainConnection
public import Zkc.Construction.Uniform.DomainHandler

@[expose] public section
/-! Kernel-checked boundaries of the retained model transition. -/
set_option autoImplicit false
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter

/-- Actual-coordinate occurrences cannot be identified by spelling alone. -/
theorem nominal_queries_distinct :
    Domain.atCoordinates (staticOrigin drawTemplate) [0] ≠
      Domain.atCoordinates (staticOrigin drawTemplate) [1] := by
  intro same
  have events := congrArg Origin.event same
  simp only [Domain.atCoordinates, List.map_cons, List.map_nil] at events
  have suffix := List.append_cancel_left events
  have zeroChar : Nat.digitChar 0 = '0' := Nat.digitChar_eq_zero.mpr rfl
  have oneChar : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  simp [Nat.repr_of_lt (n := 0) (by decide), Nat.repr_of_lt (n := 1) (by decide),
    zeroChar, oneChar] at suffix

/-- The legacy boundary deliberately collapses these occurrence coordinates.
Consequently a fresh nominal random oracle is not the mapped legacy oracle. -/
theorem legacy_query_collision :
    legacyOrigin (Domain.atCoordinates (staticOrigin drawTemplate) [0]) =
      legacyOrigin (Domain.atCoordinates (staticOrigin drawTemplate) [1]) :=
  (legacy_origins 0).2.2.1.trans (legacy_origins 1).2.2.1.symm

def malformedGuard : Construction.Instruction := ⟨.guard "diagnostic", [0], [.data .boolean], []⟩

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The broad raw legacy theorem concerns a different model: it ignores this
guard's declared result metadata and continues successfully. -/
theorem legacy_malformed_guard (context : Context) (proof : Proof F G) :
    idealStep (m := Id) context (fun _ => (0 : F)) [] malformedGuard [.data (.boolean true)] proof
      (fun _ unread => pure (.returned (), unread)) = (.returned (), proof) := rfl

/-- The authoritative instruction meaning checks that a guard has no results.
Unconditional legacy/new equality is therefore false. -/
theorem nominal_malformed_guard (context : Context) (program : Structured.Program) :
    Domain.step (ringModel F G) program context malformedGuard [.data (.boolean true)] =
      .halt .refused := rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem opaque_initial_history (suite : String) (key : Origin → Origin) (initial : History F G) :
    readbackValue suite key initial (.transcript suite []) = some (.transcript initial) := by
  simp [readbackValue, readbackHistory]

theorem message_identities :
    staticOrigin lowTemplate = SumcheckProof.context.message
      "apply_18_label_726564756365_label_726f756e64_0" 0 1 ∧
    staticOrigin highTemplate = SumcheckProof.context.message
      "apply_18_label_726564756365_label_726f756e64_1" 0 1 ∧
    staticOrigin deliveryTemplate = SumcheckProof.context.message
      "apply_18_label_726564756365_label_64656c6976657279_0" 1 0 := by
  constructor
  · kernel_rfl
  constructor <;> kernel_rfl

theorem query_identity : staticOrigin drawTemplate = SumcheckProof.context.query
    "apply_18_label_726564756365_label_6368616c6c656e6765" (.draw "bls12-381.fr") := by kernel_rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem query_not_delivery (value : F) :
    (Event.challenge (staticOrigin drawTemplate) : Event F G) ≠
      .message (staticOrigin deliveryTemplate) (.field "bls12-381.fr" value) := by
  intro same
  cases same

end ZkcExamples.Construction.SumcheckDomainConnection
