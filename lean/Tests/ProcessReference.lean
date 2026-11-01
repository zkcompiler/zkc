module

public import Zkc.Semantics.Continuation
public meta import ZkcTools.StructuredSource.ProcessReference

/-! A generated reference retains the complete function type, ordered outputs,
arbitrary effects and stops. The equation is generated with the reference. -/
namespace Tests.ProcessReference
open PIR

def source {I : Signature} (first : Process I Nat)
    (next : Nat → Process I Bool) : Process I (Nat × Bool) :=
  (first.bind fun value => (next value).bind fun accepted =>
    .done (value, accepted)).bind Process.done

source_reference reference from @source using [source, Process.bind_done]

example {I : Signature} (first : Process I Nat) (next : Nat → Process I Bool) :
    reference first next = first.bind (fun value =>
      (next value).bind fun accepted => .done (value, accepted)) := rfl

example {I : Signature} (first : Process I Nat) (next : Nat → Process I Bool) :
    source first next = reference first next :=
  congrFun (congrFun (congrFun reference_equation I) first) next

def swapped {I : Signature} (left right : Nat) : Process I (Nat × Nat) :=
  .done (right, left)

source_reference ordered from @swapped using [swapped]

example {I : Signature} : ordered (I := I) 3 5 = .done (5, 3) := by
  fail_if_success
    have : ordered (I := I) 3 5 = .done (3, 5) := rfl
  rfl

def stopping {I : Signature} (stop : Bool) (value : Nat) : Process I Nat :=
  (if stop then Process.halt .incomplete else .done value).bind Process.done

source_reference stopped from @stopping using [stopping, Process.bind_done]

example {I : Signature} : stopped (I := I) true 7 = .halt .incomplete := rfl
example {I : Signature} : stopped (I := I) false 7 = .done 7 := rfl

/-- Rewriting preserves a false returned decision; it does not turn it into a stop. -/
example {I : Signature} : reference (I := I) (.done 7) (fun _ => .done false) =
    .done (7, false) := rfl

def guarded {I : Signature} (value : Nat) : Process I Nat :=
  if value = 0 then .halt .refused else .done value

theorem guarded_returns {I : Signature} (value : Nat) (nonzero : value ≠ 0) :
    guarded (I := I) value = .done value := by
  simp only [guarded, nonzero, ↓reduceIte]

-- A conditional library law does not add its premise to the source function.
source_reference guardedReference from @guarded using [guarded_returns]

example {I : Signature} : guardedReference (I := I) 0 = .halt .refused := rfl

/- The reference is generated without an applicability-proof runtime argument,
while the correspondence theorem keeps the source theorem's premise. -/
source_reference positiveReference from_equation @guarded_returns using []

example {I : Signature} (value : Nat) : positiveReference (I := I) value = .done value := rfl
example {I : Signature} (value : Nat) (nonzero : value ≠ 0) :
    guarded (I := I) value = positiveReference value :=
  positiveReference_equation value nonzero

example {I : Signature} : guarded (I := I) 0 ≠ positiveReference 0 := by
  intro impossible
  cases impossible

/-- An already checked structural equation can retain arbitrary reply effects
and all returned coordinates, without restating the process in the client. -/
theorem complete_equation {I : Signature} (first : Process I Nat)
    (next : Nat → Process I Bool) :
    source first next = (first.bind fun value =>
      (next value).bind fun accepted => .done (value, accepted)) := by
  simp only [source, Process.bind_done]

source_reference completeReference from_equation @complete_equation using []
example {I : Signature} (first : Process I Nat) (next : Nat → Process I Bool) :
    source first next = completeReference first next := completeReference_equation first next
example {I : Signature} : completeReference (I := I) (.halt .abort) (fun _ => .done true) =
    .halt .abort := rfl

open Lean Elab Command Term in
run_elab do
  let refused ← try
    let _ ← withoutErrToSorry <| elabTerm
      (← `(term| checked_process_reference% (fun n : Nat => n + 1) using [])) none
    pure false
  catch error =>
    if error.isRuntime || error.isInterrupt then throw error
    pure ((← error.toMessageData.toString).contains "requires a process")
  unless refused do throwError "a non-process was admitted as a process reference"

#print axioms positiveReference_equation
#print axioms completeReference_equation
#print axioms reference_equation
#print axioms ordered_equation
#print axioms stopped_equation
end Tests.ProcessReference
