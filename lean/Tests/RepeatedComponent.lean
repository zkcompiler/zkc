import Zkc.Obligations.RepeatedComponent
import Tests.Obligations

set_option autoImplicit false
namespace Tests.RepeatedComponent
open Zkc.Obligations Zkc.Obligations.RepeatedComponent
open Tests.Obligations

def counter : ComponentInterface sendSignature Nat (Nat × Nat) (Nat × Nat) where
  Parameters := Unit
  Input := Unit
  InputWitness := Unit
  Output := Unit
  OutputWitness := Unit
  input := ClaimRelation.exact (fun _ _ => True)
  output := ClaimRelation.exact (fun _ _ => True)
  body := increment
  Scope _ _ _ := True
  inputView _ _ _ := some ()
  outputView _ _ _ _ := some ()

/-- The reference contains the full private frame and is available for any
runtime counter, independently of any claim predicate. -/
def reference : Representation counter (fun _ => Nat × Nat) where
  readback _ runtime := some runtime
  transition _ before after := after.1 = before.1 + 1 ∧ after.2 = before.2
  preserves _ runtime reference same := by
    cases Option.some.inj same
    exact fun _ => ⟨(runtime.1 + 1, runtime.2), rfl, rfl, rfl⟩

theorem private_frame (privateValue : Nat) :
    FrameContract counter (fun _ runtime => runtime.2 = privateValue) :=
  fun _ _ holds _ => holds

example (count : Nat) (runtime : Nat × Nat) :
    PIR.Yields (fun result => result.2 = runtime.2) (PIR.repeatN count counter.body runtime) :=
  frame_repeatN counter (private_frame runtime.2) count runtime rfl

example (count : Nat) (runtime : Nat × Nat) :
    PIR.Yields (fun result => ∃ decoded, reference.readback 0 result = some decoded)
      (PIR.repeatN count counter.body runtime) :=
  representation_repeatN counter reference count runtime ⟨runtime, rfl⟩

/-- False mathematical claims do not prevent representation or private frames.
Only the installed runtime body matters to these independent obligations. -/
def falseClaims : ComponentInterface sendSignature Nat (Nat × Nat) (Nat × Nat) :=
  { counter with
    input := ClaimRelation.exact (fun _ _ => False)
    output := ClaimRelation.exact (fun _ _ => False) }

def falseClaimsReference : Representation falseClaims (fun _ => Nat × Nat) where
  readback := reference.readback
  transition := reference.transition
  preserves := reference.preserves

theorem false_claim_frame (privateValue : Nat) :
    FrameContract falseClaims (fun _ runtime => runtime.2 = privateValue) :=
  private_frame privateValue

def handler : PIR.Handler sendSignature Nat Nat :=
  fun event state => ⟨.returned (), state + 1, [event]⟩

def honestInvariant (total privateValue : Nat) (history : List Nat) (remaining : Nat)
    (runtime : Nat × Nat) (machine : Nat) : Prop :=
  runtime.1 + remaining = total ∧ runtime.2 = privateValue ∧
    machine = runtime.1 ∧ history.length = runtime.1

theorem honest_step (total privateValue : Nat) :
    HonestContract counter handler (honestInvariant total privateValue) := by
  intro history remaining runtime machine holds
  change honestInvariant total privateValue (history ++ [runtime.1]) remaining
    (runtime.1 + 1, runtime.2) (machine + 1)
  simp only [honestInvariant, List.length_append, List.length_singleton] at holds ⊢
  exact ⟨by omega, holds.2.1, by omega, by omega⟩

example (count privateValue : Nat) :
    PIR.WeakestPrecondition.satisfies
      ((PIR.repeatN count counter.body (0, privateValue)).run handler 0)
      (fun returned final reached => honestInvariant count privateValue reached 0 returned final)
      (fun _ _ _ => False) [] :=
  honest_repeatN counter handler (honestInvariant count privateValue)
    (honest_step count privateValue) count [] (0, privateValue) 0
      ⟨Nat.zero_add count, rfl, rfl, rfl⟩

/-- Stops satisfy partial frames and No derivations, but never honest return. -/
def stops : ComponentInterface sendSignature Nat (Nat × Nat) (Nat × Nat) :=
  { counter with body := fun _ => .halt .reject }

example : FrameContract stops (fun _ _ => True) := fun _ _ _ => trivial

theorem stopping_honesty_refused : ¬ HonestContract stops handler (fun _ _ _ _ => True) := by
  intro alleged
  exact alleged [] 0 (0, 0) 0 trivial

def overwrites : ComponentInterface sendSignature Nat (Nat × Nat) (Nat × Nat) :=
  { counter with body := fun value => .done (value.1 + 1, 0) }

/-- An installed name or a vacuous No premise cannot supply a private frame. -/
theorem overwritten_frame_refused :
    ¬ FrameContract overwrites (fun _ runtime => runtime.2 = 9) := by
  intro alleged
  have impossible : (0 : Nat) = 9 := alleged 0 (0, 9) rfl
  omega

#print axioms representation_repeatN
#print axioms frame_repeatN
#print axioms no_repeatN
#print axioms NoContract.ofSoundness
#print axioms no_fold
#print axioms honest_repeatN
#print axioms falseClaimsReference
#print axioms false_claim_frame
#print axioms stopping_honesty_refused
#print axioms overwritten_frame_refused
end Tests.RepeatedComponent
