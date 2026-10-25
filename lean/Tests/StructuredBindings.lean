import Zkc.Source.Structured.Bindings.Assembly
import Zkc.Protocols.AlgebraicRounds.Gate
import Zkc.Polynomial.Multilinear.Restriction
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace Tests.StructuredBindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open Zkc.Protocols.AlgebraicRounds

abbrev interface : PIR.Signature := ⟨Nat, fun _ => Bool⟩
def receive : PIR.Process interface Bool := .call 0 .done

theorem arbitrary_receive : receive ≠ .call 0 (fun _ => .done true) := by
  intro same
  have reply := PIR.Process.call.inj same
  have eq := congrFun (eq_of_heq reply.2) false
  cases eq

def guarded (reply : Bool) : PIR.Process interface Bool :=
  if reply then .done true else .halt .reject

theorem dropped_guard : (.call 0 guarded : PIR.Process interface Bool) ≠ .call 0 (fun _ => .done true) := by
  intro same
  have reply := PIR.Process.call.inj same
  have eq := congrFun (eq_of_heq reply.2) false
  cases eq

theorem stopped_prefix : (.call 1 (fun _ => .halt .reject) : PIR.Process interface Unit) ≠ .halt .reject := by
  intro same
  cases same

theorem private_residual :
    (.done (some 7, true) : PIR.Process interface (Option Nat × Bool)) ≠ .done (none, true) := by
  intro same
  cases same

def step (state : Nat × Option Nat) : PIR.Process interface (Nat × Option Nat) :=
  .call state.1 fun _ => .done (state.1 + 1, state.2)

theorem repeat_zero (state : Nat × Option Nat) : PIR.repeatN 0 step state = .done state := rfl

theorem partial_repeat : PIR.repeatN 1 step (0, some 9) =
    .call 0 (fun _ => .done (1, some 9)) := rfl

def helper : Helper := ⟨"same-name", .math, [], [.boolean]⟩
def helperTable (answer : Bool) : HelperTable (assignment Nat Unit) interface :=
  [⟨helper, fun _ => .done (.cons answer .nil)⟩]

theorem same_named_changed_helper :
    invoke (helperTable true) helper .nil ≠ invoke (helperTable false) helper .nil := by
  simp only [helperTable]
  intro same
  cases same

def operands (left right : Nat) : PIR.Process interface Nat := .done (left - right)

theorem operand_permutation : operands 2 1 ≠ operands 1 2 := by
  intro same
  cases same

/-- Both consumers receive exactly the same whole-process binding. -/
theorem shared_binding (actual view : Meaning interface Unit (Nat × Option Nat))
    (equation : Contract (fun _ _ => True) view actual)
    (first second : PIR.Process interface (Nat × Option Nat) → Prop)
    (firstProof : first (view {} ())) (secondProof : second (view {} ())) :
    first (actual {} ()) ∧ second (actual {} ()) :=
  both equation first second {} () trivial firstProof secondProof

open Zkc.Polynomial.Multilinear

def oneBit : Table ℚ 1 := fun bits => if bits 0 then 1 else 0

/-- Equal Boolean values do not justify collapsing separately retained factors. -/
theorem product_table_off_cube :
    extension 1 oneBit (fun _ => 2) * extension 1 oneBit (fun _ => 2) ≠
      extension 1 (fun bits => oneBit bits * oneBit bits) (fun _ => 2) := by
  norm_num [oneBit, extension, half]

/-- The actual gate coefficient recipe interpolates a cubic impostor's
endpoints, but cannot represent its off-cube value. -/
theorem cubic_impostor :
    (Gate.message (0 : ℚ) 0 0 1 0 1 0 1).evaluate 2 ≠
      Gate.value (Gate.interpolate 0 0 2) (Gate.interpolate 0 1 2)
        (Gate.interpolate 0 1 2) (Gate.interpolate 0 1 2) := by
  norm_num [Gate.message, Gate.value, Gate.interpolate, Gate.quadratic,
    Zkc.Protocols.AlgebraicRounds.Message.evaluate]

#print axioms Zkc.Source.Structured.Bindings.invocation
#print axioms Zkc.Source.Structured.Bindings.actualCallees_hold
#print axioms Zkc.Source.Structured.Bindings.certificate
#print axioms Zkc.Protocols.AlgebraicRounds.Gate.evaluation_remainder
end Tests.StructuredBindings
