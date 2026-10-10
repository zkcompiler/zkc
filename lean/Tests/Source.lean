import Zkc
import Zkc.Source.Elaboration
import Mathlib.Algebra.Ring.Int.Defs

set_option autoImplicit false

namespace PIR.Tests.Source
open Zkc.Source.Expressions

def identityClosure : Closure Nat := ⟨1, .var ⟨0, by decide⟩, fun _ => .var 0⟩
def slot (v : Int) : Zkc.Source.Availability.Env Int := fun j => if j = 0 then some v else none
def missing : Zkc.Source.Availability.Env Int := fun _ => none
def result (scope : List Nat) (s : Zkc.Source.Availability.Env Int) (c : Closure Nat) : Option Int :=
  (PIR.Source.issue scope s c).map PIR.Source.Bound.value

theorem scope_check_is_not_availability :
    Zkc.Source.Expressions.check [0] (identityClosure.captures ⟨0, by decide⟩) = true ∧
    result [0] missing identityClosure = none := ⟨rfl, rfl⟩

theorem available_zero_is_not_missing : result [0] (slot 0) identityClosure = some 0 := rfl

def world (hidden : Nat) : SourceView.World Bool Int Nat :=
  ⟨fun j => if j = 0 then some 5 else if j = 1 then some 9 else none,
    fun owner j => if j = 0 then some (if owner then 17 else 11) else none,
    hidden⟩

theorem own_input_is_admitted :
    (PIR.Source.admit false [.owned false 0] (world 0) identityClosure).map
      PIR.Source.Bound.value = some 11 := rfl

theorem another_owners_present_input_is_refused :
    (PIR.Source.admit false [.owned true 0] (world 0) identityClosure).map
      PIR.Source.Bound.value = none := rfl

theorem hidden_provider_change_preserves_issuance :
    PIR.Source.admit false [.owned false 0] (world 0) identityClosure =
      PIR.Source.admit false [.owned false 0] (world 99) identityClosure :=
  PIR.Source.admission_same_view _ _ _ _ _ ⟨rfl, rfl⟩

def guarded : Closure Nat :=
  ⟨1, .var ⟨0, by decide⟩, fun _ => .ifz (.var 1) (.var 0) (.lit 3)⟩

theorem unavailable_guard_is_refused : result [0,1] (slot 5) guarded = none := rfl

def dormant : Closure Nat :=
  ⟨1, .var ⟨0, by decide⟩, fun _ => .ifz (.lit 0) (.var 0) (.var 1)⟩

theorem dormant_missing_branch_is_refused : result [0,1] (slot 5) dormant = none := rfl

def unusedCapture : Closure Nat := ⟨1, .lit 7, fun _ => .var 1⟩

/-- Expression substitution preserves value meaning but can hide a declared
    capture obligation if admission is incorrectly run only after expansion. -/
theorem expanding_before_capture_admission_loses_an_obligation :
    Zkc.Source.Expressions.check [] unusedCapture.expand = true ∧
    result [1] missing unusedCapture = none := ⟨rfl, rfl⟩

theorem unused_but_available_capture_is_admitted :
    result [1] (fun j => if j = 1 then some 12 else none) unusedCapture = some 7 := rfl

theorem captured_values_do_not_follow_later_environment_changes :
    result [0] (slot 5) identityClosure = some 5 ∧
    (PIR.Source.capture identityClosure (slot 5)).value = 5 ∧
    result [0] (slot 9) identityClosure = some 9 := ⟨rfl, rfl, rfl⟩

def subtractInputs : Closure Nat :=
  ⟨2, .sub (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩), fun i => .var i.val⟩

theorem same_typed_input_permutation_changes_meaning :
    (PIR.Source.admit false [.shared 0, .shared 1] (world 0) subtractInputs).map
      PIR.Source.Bound.value = some (-4) ∧
    (PIR.Source.admit false [.shared 1, .shared 0] (world 0) subtractInputs).map
      PIR.Source.Bound.value = some 4 := ⟨rfl, rfl⟩

/-- Dependency checks compare a fixed source, not a secret host generator
    choosing between dependency-free literals. -/
def generated (secret : Bool) : Closure Nat :=
  ⟨0, .lit (if secret then 1 else 0), fun i => nomatch i⟩

theorem different_generated_literals_are_not_same_view_security :
    result [] missing (generated false) = some 0 ∧
    result [] missing (generated true) = some 1 := ⟨rfl, rfl⟩

def emitSig : Signature := ⟨Int, fun _ => Unit⟩
def emit : Handler emitSig Nat Int := fun value n => ⟨.returned (), n+1, [value]⟩
def abortAfterEmission (value : Int) : Proc emitSig Unit :=
  .call value (fun _ => .halt .abort)

theorem issued_source_retains_stopping_context_effects :
    (PIR.Source.issue [0] (slot 5) identityClosure).map
      (fun b => ((PIR.Source.elaborate b).bind abortAfterEmission).run emit 0) =
    some ⟨.stopped .abort, 1, [5]⟩ := rfl

theorem failed_admission_does_not_execute_a_context :
    (PIR.Source.issue [0] missing identityClosure).map
      (fun b => ((PIR.Source.elaborate b).bind abortAfterEmission).run emit 0) = none := rfl

end PIR.Tests.Source
