import ZkcSecurity.Tools.ComponentDerivation
import ZkcSecurity.Obligations.RepeatedComponent
import Tests.Obligations
import TestsSecurity.Obligations
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option trace.zkc.componentAssembly true
noncomputable section
namespace TestsSecurity.PropertyAssembly
open Zkc.Obligations Zkc.Transcript ZkcSecurity.Obligations
open Tests.Obligations

/-- An installed ComponentInterface/SoundnessContract supplies the shared loop
body law. Scope, No entry and mathematical exit are explicit responsibilities;
no whole-source, artifact-reading or SSA equation is an extra premise. -/
def installed_family_loop {I : PIR.Signature} {E P R : Type} {Raw : E → Type}
    (component : ComponentInterface I E R R) (absorb : Interface I E P Raw)
    (escape : EscapeJudgment E Raw) (soundness : SoundnessContract component absorb escape)
    (parameters : Nat → component.Parameters) (invariant : List E → Nat → R → Prop)
    (enter : ∀ remaining history runtime, invariant history (remaining + 1) runtime →
      component.Scope (parameters remaining) runtime history ∧
        component.InputNo (parameters remaining) runtime history)
    (exit : ∀ remaining runtime history returned,
      component.OutputNo (parameters remaining) runtime history returned → invariant history remaining returned)
    (count : Nat) (history : List E) (runtime : R) (holds : invariant history count runtime) :
    Derivation absorb escape (fun final => invariant final 0) history
      (PIR.repeatN count component.body runtime) := by
  let bodyLaw := Zkc.Obligations.RepeatedComponent.NoContract.ofSoundness component
    soundness parameters invariant enter exit
  assemble_component_property [bodyLaw] unfolding [] repeating [invariant]
    reporting "installed family symbolic loop" from component

/-- A non-Sumcheck component retains a private residual while changing both
the counter and the reached history. The symbolic count is never unfolded. -/
def counter (count : Nat) (history : List Nat) (state : Nat × Nat)
    (charge : List Nat → Nat → ENNReal) :
    Derivation sendInterface (boundedEscape charge)
      (fun reached value => value.1 + 0 = state.1 + count ∧ value.2 = state.2 ∧
        reached.length + 0 = history.length + count)
      history (PIR.repeatN count increment state) := by
  let invariant := fun (reached : List Nat) (remaining : Nat) (value : Nat × Nat) =>
    value.1 + remaining = state.1 + count ∧ value.2 = state.2 ∧
      reached.length + remaining = history.length + count
  have stepLaw : ∀ reached remaining value, invariant reached (remaining + 1) value →
      Derivation sendInterface (boundedEscape charge) (fun final => invariant final remaining)
        reached (increment value) := by
    intro reached remaining value valid
    refine .send rfl (.done ?_)
    dsimp [invariant] at valid ⊢
    simp only [List.length_append, List.length_singleton]
    exact ⟨by omega, valid.2.1, by omega⟩
  assemble_component_property [stepLaw] unfolding [] repeating [invariant] finishing simp_all
    reporting "counter residual and frame" from (count, state)

def two_calls {I : PIR.Signature} {E P : Type} {Raw : E → Type}
    [∀ event, SampleableType (Raw event)]
    (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (left right : PIR.Process I Bool) (history : List E)
    (leftLaw : ∀ history, Derivation absorb (boundedEscape charge)
      (fun _ value => value = false) history left)
    (rightLaw : ∀ history, Derivation absorb (boundedEscape charge)
      (fun _ value => value = false) history right) :
    Derivation absorb (boundedEscape charge) (fun _ value => value = false) history
      (left.bind fun a => right.bind fun b => .done (a || b)) := by
  fail_if_success
    solve | assemble_component_property [leftLaw, rightLaw history] unfolding [] repeating [] finishing simp_all
      reporting "fixed initial history cannot serve the second call" from (left, right)
  assemble_component_property [leftLaw, rightLaw] unfolding [] repeating [] finishing simp_all
    reporting "two component calls" from (left, right)

/-- Nested symbolic components use the inner contract once per shared body.
Neither symbolic count is expanded into a list of calls. -/
def nested_counter (outer inner : Nat) (history : List Nat) (state : Nat × Nat)
    (charge : List Nat → Nat → ENNReal) :
    Derivation sendInterface (boundedEscape charge)
      (fun reached value => value.1 + 0 * inner = state.1 + outer * inner ∧ value.2 = state.2 ∧
        reached.length + 0 * inner = history.length + outer * inner)
      history (PIR.repeatN outer (fun value => PIR.repeatN inner increment value) state) := by
  let invariant := fun (reached : List Nat) (remaining : Nat) (value : Nat × Nat) =>
    value.1 + remaining * inner = state.1 + outer * inner ∧ value.2 = state.2 ∧
      reached.length + remaining * inner = history.length + outer * inner
  have innerLaw : ∀ reached remaining value, invariant reached (remaining + 1) value →
      Derivation sendInterface (boundedEscape charge) (fun final => invariant final remaining)
        reached (PIR.repeatN inner increment value) := by
    intro reached remaining value valid
    exact (counter inner reached value charge).consequence (fun final returned observed => by
      dsimp [invariant] at valid ⊢
      simp only [Nat.add_zero] at observed
      simp only [Nat.add_mul, Nat.one_mul] at valid
      exact ⟨by omega, observed.2.1.trans valid.2.1, by omega⟩)
  assemble_component_property [innerLaw] unfolding [] repeating [invariant] finishing simp_all
    reporting "nested shared repeat" from (outer, inner, state)

/-- Missing mathematics remains an ordinary caller goal. The builder must not
invent the law's precondition, nor absorb the independent Unit goal. -/
def explicit_premise {I : PIR.Signature} {E P : Type} {Raw : E → Type}
    [∀ event, SampleableType (Raw event)]
    (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (body : PIR.Process I Bool) (history : List E) (x y : Nat)
    (law : x + y = y + x → Derivation absorb (boundedEscape charge)
      (fun _ value => value = false) history body) :
    Derivation absorb (boundedEscape charge) (fun _ value => value = false) history body × Unit := by
  constructor
  assemble_component_property [law] unfolding [] repeating []
    reporting "explicit component premise" from body
  exact Nat.add_comm x y
  exact ()

/-- Unknown components stay open for nontrivial properties. -/
def unknown_stays_open {I : PIR.Signature} {E P : Type} {Raw : E → Type}
    [∀ event, SampleableType (Raw event)]
    (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (body : PIR.Process I Bool) (history : List E)
    (law : Derivation absorb (boundedEscape charge) (fun _ value => value = false) history body) :
    Derivation absorb (boundedEscape charge) (fun _ value => value = false) history body := by
  fail_if_success
    solve | assemble_component_property [] unfolding [] repeating [] finishing simp_all
      reporting "unknown must remain unresolved" from body
  assemble_component_property [] unfolding [] repeating [] finishing simp_all
    reporting "unknown component" from body
  exact law

/-- A prefix can be unrestricted only when every possible return admits a
suffix proof of the same final property. Here the final result is constant. -/
def universal_suffix {I : PIR.Signature} {E P : Type} {Raw : E → Type}
    [∀ event, SampleableType (Raw event)]
    (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (body : PIR.Process I Bool) (history : List E) :
    Derivation absorb (boundedEscape charge) (fun _ value => value = false) history
      (body.bind fun _ => .done false) := by
  assemble_component_property [] unfolding [] repeating [] finishing rfl
    reporting "universal suffix" from body

/-- Returning the prefix's unconstrained value cannot establish rejection.
Unrestricted success is unavailable for this nontrivial requested property. -/
def nonuniversal_suffix_refused {I : PIR.Signature} {E P : Type} {Raw : E → Type}
    [∀ event, SampleableType (Raw event)]
    (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (body : PIR.Process I Bool) (history : List E)
    (law : Derivation absorb (boundedEscape charge) (fun _ value => value = false) history body) :
    Derivation absorb (boundedEscape charge) (fun _ value => value = false) history
      (body.bind .done) := by
  fail_if_success
    solve | assemble_component_property [] unfolding [] repeating [] finishing simp_all
      reporting "unrestricted prefix with nonuniversal suffix refused" from body
  simpa only [PIR.Process.bind_done] using law

/-- Replacing a query's complete exceptional set by a smaller maximum bound
is not an assembly rule. The same challenge can satisfy either local bad event. -/
theorem shared_challenge_max_refused (history : List Unit) :
    ¬ boundedEscape (Raw := fun _ : Unit => Bool) (fun _ _ => (2 : ENNReal)⁻¹)
      history () (fun bit => bit = true ∨ bit = false) := by
  change ¬ Pr{let bit ← $ᵗ Bool}[bit = true ∨ bit = false] ≤ (2 : ENNReal)⁻¹
  have total : Pr{let bit ← $ᵗ Bool}[bit = true ∨ bit = false] = 1 :=
    (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr (fun bit => by cases bit <;> simp)
  rw [total]
  norm_num

/-- Both uses are of one returned challenge. One installed escape cut suffices
for this property; the builder neither resamples nor assumes independence. -/
def shared_challenge (history : List Unit) :
    Derivation queryBit (boundedEscape (fun _ _ => (2 : ENNReal)⁻¹))
      (fun _ value => value = false) history
      (echo.bind fun bit => .done (bit || bit)) := by
  assemble_component_property [TestsSecurity.Obligations.query_derived]
    unfolding [] repeating [] finishing simp_all
    reporting "one shared challenge; one installed cut" from echo

/-- The return tuple retains the arbitrary received value. Its private frame
holds for every reply, without substituting an honest message. -/
def receive_private_frame (history : List Bool) (privateValue : Nat)
    (charge : List Bool → Bool → ENNReal) :
    Derivation attackerReceive (boundedEscape charge) (fun _ value => value.2 = privateValue)
      history (echo.bind fun bit => .done (bit, privateValue)) := by
  assemble_component_property [] unfolding [echo] repeating [] finishing rfl
    reporting "arbitrary receive retains private frame" from (echo, privateValue)

def actual_branch (choice : Bool) (history : List Nat) (charge : List Nat → Nat → ENNReal) :
    Derivation sendInterface (boundedEscape charge) (fun _ value => value = false) history
      (if choice then .done false else .halt .reject) := by
  assemble_component_property [] unfolding [] repeating [] finishing rfl
    reporting "actual branch returns or stops" from choice

example (_history : List Unit) : True := by
  fail_if_success
    have unsupported : Derivation queryBit (boundedEscape (fun _ _ => (2 : ENNReal)⁻¹))
        (fun _ (_ : Bool) => False) _history echo := by
      solve | assemble_component_property [] unfolding [echo] repeating [] finishing simp_all
        reporting "shared challenge union needs a genuine bound" from echo
  trivial

def attribution_first (history : List Nat) (charge : List Nat → Nat → ENNReal) :
    Derivation sendInterface (boundedEscape charge) (fun _ value => value = false)
      history (.done false) := by
  assemble_component_property [] unfolding [] repeating [] finishing rfl
    reporting "first attribution" from (0 : Nat)

def attribution_second (history : List Nat) (charge : List Nat → Nat → ENNReal) :
    Derivation sendInterface (boundedEscape charge) (fun _ value => value = false)
      history (.done false) := by
  assemble_component_property [] unfolding [] repeating [] finishing rfl
    reporting "different attribution" from (1 : Nat)

/-- Reporting metadata does not enter the checked derivation term. Receipt
classification/meaning stays with the existing request-owned path. -/
theorem attribution_irrelevant (history : List Nat) (charge : List Nat → Nat → ENNReal) :
    attribution_first history charge = attribution_second history charge := rfl

#print axioms counter
#print axioms installed_family_loop
#print axioms two_calls
#print axioms nested_counter
#print axioms explicit_premise
#print axioms unknown_stays_open
#print axioms universal_suffix
#print axioms nonuniversal_suffix_refused
#print axioms shared_challenge_max_refused
#print axioms shared_challenge
#print axioms receive_private_frame
#print axioms actual_branch
#print axioms attribution_irrelevant
end TestsSecurity.PropertyAssembly
