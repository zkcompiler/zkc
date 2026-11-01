import Zkc.Source.Structured.ObservedLoop

/-! Generic observed-loop controls: complete values and traces, including
arbitrary replies, stops at either boundary, nested loops and shrinking state. -/
set_option autoImplicit false
namespace Tests.ObservedLoop
open Zkc.Source Zkc.Source.Structured

inductive Operation where
  | enter (site : String) (index : Nat)
  | leave (site : String) (index : Nat)
  | query (index : Nat)
  deriving DecidableEq, Repr

abbrev signature : PIR.Signature where
  Op := Operation
  Reply
    | .enter .. | .leave .. => Unit
    | .query _ => Nat

def observations : IterationObservations signature := .observed
  (fun site index => .call (.enter site index) .done)
  (fun site index => .call (.leave site index) .done)

def handler (reply : Nat) : PIR.Handler signature Nat Operation
  | .enter site index, state => ⟨.returned (), state + 1, [.enter site index]⟩
  | .leave site index, state => ⟨.returned (), state + 1, [.leave site index]⟩
  | .query index, state => ⟨.returned reply, state + 1, [.query index]⟩

def step (values : List Nat) (index : Nat) : PIR.Process signature (List Nat) :=
  .call (.query index) fun reply =>
    if reply ≤ index then .done (values ++ [reply]) else .halt .reject

/-- An empty loop returns the complete initial value and never enters a body. -/
example : (ObservedLoop.counted observations "empty"
    (fun (_ : List Nat) _ => .halt .abort) 7 0 [9, 8]).run (handler 100) 4 =
    ⟨.returned [9, 8], 4, []⟩ := rfl

example : (ObservedLoop.counted observations "round" step 2 2 [9]).run (handler 1) 0 =
    ⟨.returned [9, 1, 1], 6,
      [.enter "round" 2, .query 2, .leave "round" 2,
       .enter "round" 3, .query 3, .leave "round" 3]⟩ := by rfl

/-- A dishonest reply retains its reached prefix and has no leave or next enter. -/
example : (ObservedLoop.counted observations "round" step 2 3 [9]).run (handler 3) 0 =
    ⟨.stopped .reject, 2, [.enter "round" 2, .query 2]⟩ := by rfl

/-- Enter observations may themselves stop before any callback executes. -/
example : (ObservedLoop.counted (I := signature)
    (.observed (fun _ _ => .halt .incomplete) (fun site index => .call (.leave site index) .done))
    "round" step 2 2 [9]).run (handler 1) 0 = ⟨.stopped .incomplete, 0, []⟩ := by rfl

def refusingLeave : PIR.Handler signature Nat Operation
  | .leave site index, state => ⟨.stopped .refused, state + 1, [.leave site index]⟩
  | operation, state => handler 1 operation state

/-- A refused leave discards the pending return and prevents later iterations. -/
example : (ObservedLoop.counted observations "round" step 2 2 [9]).run refusingLeave 0 =
    ⟨.stopped .refused, 3, [.enter "round" 2, .query 2, .leave "round" 2]⟩ := by rfl

def nested : PIR.Process signature (List Nat) :=
  ObservedLoop.counted observations "outer" (fun values index =>
    (ObservedLoop.counted observations "inner" step 4 1 values).bind fun next =>
      .done (next ++ [index])) 2 2 [9]

example : nested.run (handler 1) 0 =
    ⟨.returned [9, 1, 2, 1, 3], 10,
      [.enter "outer" 2, .enter "inner" 4, .query 4, .leave "inner" 4, .leave "outer" 2,
       .enter "outer" 3, .enter "inner" 4, .query 4, .leave "inner" 4, .leave "outer" 3]⟩ := by
  rfl

example : nested.run (handler 5) 0 =
    ⟨.stopped .reject, 3, [.enter "outer" 2, .enter "inner" 4, .query 4]⟩ := by rfl

/-- List values, the accumulated prefix and source indices retain their order. -/
example : (ObservedLoop.forEach observations "values"
    (fun values value index => (.call (.query index) fun reply => .done (values ++ [value, reply])))
    4 [7, 2, 5] [9]).run (handler 3) 0 =
    ⟨.returned [9, 7, 3, 2, 3, 5, 3], 9,
      [.enter "values" 4, .query 4, .leave "values" 4,
       .enter "values" 5, .query 5, .leave "values" 5,
       .enter "values" 6, .query 6, .leave "values" 6]⟩ := by rfl

example : (ObservedLoop.forEach observations "values"
    (fun (_ : List Nat) (_ : Nat) _ => .halt .abort) 4 [] [9]).run (handler 3) 7 =
    ⟨.returned [9], 7, []⟩ := rfl

abbrev plain : PIR.Signature where
  Op := Nat
  Reply _ := Nat

def erase : PIR.OperationInterpretation signature plain
  | .enter .. | .leave .. => .done ()
  | .query index => .call index .done

theorem observations_erase : IterationObservations.Interprets erase observations .silent :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Process equality holds for every reply tree, including rejected replies. -/
theorem all_replies (start count : Nat) (values : List Nat) :
    (ObservedLoop.counted observations "round" step start count values).interpret erase =
      Finite.fold (fun values index => PIR.Process.call (I := plain) index fun reply =>
        if reply ≤ index then .done (values ++ [reply]) else .halt .reject)
        (List.range' start count) values := by
  rw [ObservedLoop.counted, ObservedLoop.interpret erase observations_erase]
  apply Finite.fold_congr
  intro values index
  change (PIR.Process.call (I := plain) index fun reply =>
    (if reply ≤ index then PIR.Process.done (values ++ [reply]) else .halt .reject).interpret erase) = _
  congr 1
  funext reply
  split <;> rfl

/-- The state really changes type at every iteration. Its list is still the
complete pending value, and the final finite coordinate must be zero. -/
def shrinkingStep (remaining : Nat) (state : Fin (remaining + 2) × List Nat) (index : Nat) :
    PIR.Process signature (Fin (remaining + 1) × List Nat) :=
  (step state.2 index).bind fun values =>
    .done (⟨min state.1.val remaining, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩, values)

example : (ObservedLoop.descending (State := fun remaining => Fin (remaining + 1) × List Nat)
    observations "shrinking" shrinkingStep 7 0 (⟨0, by decide⟩, [9])).run (handler 3) 4 =
    ⟨.returned (⟨0, by decide⟩, [9]), 4, []⟩ := rfl

example : (ObservedLoop.descending (State := fun remaining => Fin (remaining + 1) × List Nat)
    observations "shrinking" shrinkingStep 2 2 (⟨2, by decide⟩, [9])).run (handler 1) 0 =
    ⟨.returned (⟨0, by decide⟩, [9, 1, 1]), 6,
      [.enter "shrinking" 2, .query 2, .leave "shrinking" 2,
       .enter "shrinking" 3, .query 3, .leave "shrinking" 3]⟩ := by rfl

example : (ObservedLoop.descending (State := fun remaining => Fin (remaining + 1) × List Nat)
    observations "shrinking" shrinkingStep 2 2 (⟨2, by decide⟩, [9])).run (handler 3) 0 =
    ⟨.stopped .reject, 2, [.enter "shrinking" 2, .query 2]⟩ := by rfl

example (start count : Nat) (initial : Fin (count + 1) × List Nat) :
    (ObservedLoop.descending (State := fun remaining => Fin (remaining + 1) × List Nat)
      observations "shrinking" shrinkingStep start count initial).interpret erase =
    ObservedLoop.descending .silent "shrinking"
      (fun remaining state index => (shrinkingStep remaining state index).interpret erase)
      start count initial :=
  ObservedLoop.descending_interpret erase observations_erase _ _ _ _ _

#print axioms all_replies
#print axioms ObservedLoop.interpret
#print axioms ObservedLoop.descending_interpret
end Tests.ObservedLoop
