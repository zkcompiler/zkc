import Tests.CompositeReuseContracts
import Mathlib.Algebra.Ring.Int.Defs

/-! Positive and refusal clients for the actual three source protocols. -/
set_option autoImplicit false
set_option smartUnfolding false
noncomputable section
namespace Tests.CompositeReuse
open Zkc.Source Zkc.Source.Structured Zkc.Obligations Zkc.Transcript
open Tests.CompositeReuseSource Tests.CompositeReuseBodies Tests.CompositeReuseContracts

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem outer_result (first second : F) (runtime : Runtime F) :
    outer (G := G) first second runtime =
      if runtime.enabled then .done (runtime.value.map (fun value => value + first + second))
      else .halt .reject := by
  rw [outer_binding, shift_binding]
  split
  · rename_i enabled
    change shift (G := G) second (route runtime (runtime.value.map (· + first))) = _
    rw [shift_binding]
    simp only [route, enabled, ↓reduceIte, Option.map_map, Function.comp_def]
  · rfl

theorem third_result (first second last : F) (runtime : Runtime F) :
    third (G := G) first second last runtime =
      if runtime.enabled then .done (runtime.value.map (fun value => value + first + second + last))
      else .halt .reject := by
  rw [third_binding, outer_result]
  split
  · rename_i enabled
    change shift (G := G) last (route runtime (runtime.value.map (fun value => value + first + second))) = _
    rw [shift_binding]
    simp only [route, enabled, ↓reduceIte, Option.map_map, Function.comp_def]
  · rfl

/-- Absence is allowed by scope but cannot establish either claim side. -/
theorem missing_input_refused (E : Type) (yes gap first second last marker : F) :
    scope marker (⟨marker, none, true⟩ : Runtime F) ∧
      ¬ (thirdComponent (G := G) E yes gap first second last).InputNo marker ⟨marker, none, true⟩ [] ∧
      ¬ (thirdComponent (G := G) E yes gap first second last).InputYes marker ⟨marker, none, true⟩ [] :=
  ⟨⟨rfl, rfl⟩, ReadbackHolds.none _, ReadbackHolds.none _⟩

theorem missing_output_refused (E : Type) (yes gap delta marker : F) (runtime : Runtime F)
    (history : List E) :
    ¬ (shiftComponent (G := G) E yes gap delta).OutputNo marker runtime history none :=
  ReadbackHolds.none _

/-- The root participant without the declared V inputs obtains no value. -/
theorem excluded_role (first second last : F) (runtime : Runtime F) :
    ((thirdDefinition.denoteWith (.silent _) (participantActions F G) tables protocols
      {} 0 (thirdInputs first second last runtime)).bind fun values => .done (values.get .here)) =
      (PIR.Process.done none : PIR.Process (I (F := F) (G := G)) (Option F)) := by
  rcases runtime with ⟨ignored, value, enabled⟩
  cases enabled <;> cases value <;> kernel_rfl

/-- Callee lookup requires the entire retained signature, including scopes. -/
theorem changed_signature_refused (first second : F) (runtime : Runtime F) :
    invokeProtocol (protocols (F := F) (G := G))
      { Tests.Generated.CompositeReuseBodies.outerSignature with
        inputScopes := [[0], [1], [1], [1], [1]] }
      {} 1 (outerInputs first second runtime) = .halt .refused := by
  kernel_rfl

/-- Exact source operands distinguish the marker from the carried value. -/
theorem wrong_operand_refused :
    third (G := Int) (3 : Int) 4 5 ⟨99, some 2, true⟩ ≠ .done (some (99 + 3 + 4 + 5)) := by
  rw [third_result]
  change (PIR.Process.done (some (14 : Int)) : PIR.Process (I (F := Int) (G := Int)) (Option Int)) ≠
    .done (some 111)
  intro same
  cases same

theorem wrong_route_refused :
    ¬ ∀ value output : Int, (some value).map (· - 3) = some output →
      (some (value + 1) : Option Int) = some ((firstConnection (G := Int) Unit 0 1 3 4).map output) := by
  intro square
  have impossible := square 3 0 (by decide)
  change (some (4 : Int) : Option Int) = some 3 at impossible
  cases impossible

theorem changed_frame_refused :
    ¬ scope (99 : Int) ⟨100, some 0, true⟩ := by
  intro invariant
  cases invariant.1

theorem changed_capture_refused (marker value : Int) :
    ¬ scope marker ⟨marker, some value, false⟩ := by
  intro invariant
  cases invariant.2

/-- A guard failure really stops; it cannot be accepted as honest completion. -/
theorem disabled_stops (first second last marker value : F) :
    third (G := G) first second last ⟨marker, some value, false⟩ = .halt .reject := by
  rw [third_result]
  rfl

theorem rejecting_is_not_complete {S O : Type} (handler : PIR.Handler (I (F := F) (G := G)) S O)
    (state : S) (first second last marker value : F) :
    ¬ ∃ result, (third first second last ⟨marker, some value, false⟩).run handler state =
      ⟨.returned result, state, []⟩ := by
  rw [disabled_stops]
  rintro ⟨result, impossible⟩
  cases impossible

/-- Yes equivalence alone cannot transport the No side across a changed gap. -/
theorem same_yes_different_no :
    (∀ value : Int, (gapped 0 1).token.Yes value ↔ (gapped 0 2).token.Yes value) ∧
      ¬ (gapped (0 : Int) 1).SoundLink (gapped 0 2) id := by
  refine ⟨fun _ => Iff.rfl, ?_⟩
  intro law
  exact (law 2 (show (2 : Int) ≠ 0 ∧ 2 ≠ 1 from by decide)).2 rfl

/-- Concrete prefixes instantiate the independent frame law for Yes (0), gap
(1), and No (2), including a nonidentity first mathematical map. -/
def prefixes {E P : Type} {Raw : E → Type}
    (absorb : Interface (I (F := Int) (G := Int)) E P Raw) (escape : EscapeJudgment E Raw)
    (history : List E) :
    ∀ value ∈ ([0, 1, 2] : List Int),
      Derivation absorb escape (fun _ result => scope 99 (route ⟨99, some value, true⟩ result))
        history (third 3 4 5 ⟨99, some value, true⟩) :=
  fun value _ => third_frame absorb escape 3 4 5 99 ⟨99, some value, true⟩ history ⟨rfl, rfl⟩

example : (gapped (0 : Int) 1).token.Yes 0 ∧
    (¬ (gapped (0 : Int) 1).token.Yes 1 ∧ ¬ (gapped (0 : Int) 1).No 1) ∧
    (gapped (0 : Int) 1).No 2 := by
  refine ⟨⟨(), rfl⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨_, impossible⟩
    change (1 : Int) = 0 at impossible
    cases impossible
  · intro wrong
    exact wrong.2 rfl
  · change (2 : Int) ≠ 0 ∧ 2 ≠ 1
    decide

open Lean in
run_cmd do
  let environment ← getEnv
  for (consumer, contract) in [
      (``third_sound, ``outer_sound), (``third_honest, ``outer_honest)] do
    unless (environment.find? contract).any (fun info => match info with
        | .opaqueInfo _ => true | _ => false) do
      throwError "the exported composite contract must be opaque: {contract}"
    let some declaration := environment.find? consumer
      | throwError "missing source consumer: {consumer}"
    unless ((declaration.value? true).map Lean.Expr.getUsedConstants).getD #[] |>.contains contract do
      throwError "the source consumer must use the exported contract: {consumer}"
  logInfo "COMPOSITE-OPAQUE-REUSE-PASS"

#print axioms Tests.CompositeReuseSource.kernel_admission
#print axioms outer_invocation
#print axioms third_selected_root
#print axioms outer_binding
#print axioms third_binding
#print axioms outer_sound
#print axioms third_sound
#print axioms outer_honest
#print axioms third_honest
#print axioms outer_frame
#print axioms third_frame
#print axioms prefixes
#print axioms missing_input_refused
#print axioms excluded_role
#print axioms changed_signature_refused
#print axioms wrong_operand_refused
#print axioms wrong_route_refused
#print axioms changed_frame_refused
#print axioms changed_capture_refused
#print axioms rejecting_is_not_complete
#print axioms same_yes_different_no

end Tests.CompositeReuse
