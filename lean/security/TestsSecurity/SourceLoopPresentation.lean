module

public import Zkc.Source.Structured.LoopPresentation

@[expose] public section

/-! Indexed loop representations retain all adversarial replies and a refused
branch. The source carries an extra counter that is not in the mathematical
state, so neither ordinary fold congruence nor successful runs alone suffice. -/
set_option autoImplicit false
namespace TestsSecurity.SourceLoopPresentation
open Zkc.Source
open Zkc.Source.Structured.LoopPresentation

abbrev interface : PIR.Signature where
  Op := Unit
  Reply _ := Nat

def reference (value index : Nat) : PIR.Process interface Nat :=
  .call () fun reply =>
    if reply ≤ index then .done (value + reply) else .halt .refused

def actual (state : Nat × Nat) (index : Nat) : PIR.Process interface (Nat × Nat) :=
  if state.2 = index then
    .call () fun reply =>
      if reply ≤ index then .done (state.1 + reply, index + 1) else .halt .refused
  else .halt .reject

/-- Full process equality, including the extra final counter, for arbitrary
trip counts. A dishonest reply can stop either side at the same reached query. -/
theorem indexed_full_process (start count value : Nat) :
    Finite.fold actual (List.range' start count) (value, start) =
      (Finite.fold reference (List.range' start count) value).bind
        (fun result => .done (result, start + count)) := by
  apply foldInvariant actual reference (fun index value => (value, index))
    (fun _ _ => True) (start + count)
  · intro index value _ _
    simp only [actual, reference, ↓reduceIte, PIR.Process.bind]
    congr 1
    funext reply
    split <;> rfl
  · intro index value _ _ reply
    change PIR.Yields (fun _ => True)
      (if reply ≤ index then .done (value + reply) else .halt .refused)
    split <;> trivial
  · omega
  · trivial

/-- The presentation rule does not turn a refused path into completeness. -/
theorem stale_counter_refused (value : Nat) : actual (value, 1) 0 = .halt .reject := by
  simp [actual]

#print axioms indexed_full_process
end TestsSecurity.SourceLoopPresentation
