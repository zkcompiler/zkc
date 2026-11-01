import Zkc.Algorithms.ListReadback
import Zkc.Source.Structured.DeterministicFold

/-! The deterministic fold transport is independent of a field, tuple ABI,
source helper name, or protocol. Stops and nontrivial return encodings are kept. -/
set_option autoImplicit false
namespace Tests.DeterministicReadback
open Zkc.Source Zkc.Algorithms

example : ListReadback.scan 8 2 ["red", "green", "blue"] "missing" 0 =
    .returned ("blue", 3) := rfl

example : ListReadback.scan 8 6 ["red", "green", "blue"] "missing" 0 =
    .returned ("missing", 3) := rfl

example : ListReadback.scan 8 8 ["red"] "missing" 0 = .stopped .refused := rfl

example : ListReadback.scan 8 8 ([] : List String) "missing" 8 =
    .returned ("missing", 8) := rfl

-- Overflow is checked even after a value has already been selected.
example : ListReadback.scan 4 2 ["selected", "later"] "missing" 2 =
    .stopped .refused := rfl

example (xs : List String) (current : String) (position offset : Nat) :
    xs.foldl (ListReadback.transition position) (current, offset) =
      (if offset ≤ position then xs[position - offset]?.getD current else current,
        offset + xs.length) := ListReadback.fold xs position offset current

private def encode (state : String × Nat) : Bool × Nat × String := (true, state.2, state.1)

private def encodedStep (state : Bool × Nat × String) (value : String) :
    PIR.Process Zkc.Source.Structured.closedInterface (Bool × Nat × String) :=
  (Finite.toProcess (ListReadback.step 4 2 (state.2.2, state.2.1) value)).bind
    (fun result => .done (encode result))

example (xs : List String) (initial : String × Nat) :
    Finite.fold encodedStep xs (encode initial) =
      (Finite.toProcess (ListReadback.scan 4 2 xs initial.1 initial.2)).bind
        (fun result => .done (encode result)) := by
  exact Finite.fold_checked_encode encodedStep (ListReadback.step 4 2) encode
    (fun _ _ => rfl) xs initial

example : Finite.fold encodedStep ["selected", "later"] (encode ("missing", 2)) =
    .halt .refused := rfl

#print axioms ListReadback.fold
#print axioms ListReadback.scan_bounded
#print axioms Finite.fold_checked_encode
#print axioms Zkc.Source.Structured.Evaluation.denoteFoldOn_checked
end Tests.DeterministicReadback
