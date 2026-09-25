import Zkc.Semantics.Iteration
import Zkc.Source.Family

set_option autoImplicit false
namespace Tests.Iteration
open PIR

abbrev signature : Signature := ⟨Unit, fun _ => Nat⟩
def handler : Handler signature Nat Nat := fun _ state =>
  ⟨.returned state, state + 1, [state]⟩

/-- Retry consumes the next tape coordinate. Only the selected successful
attempt's payload is returned; failed attempts' audit events persist. -/
def attempt (target : Nat) (_ : Unit) : Proc signature (Unit ⊕ Nat) :=
  .call () fun draw => if draw < target then .done (.inl ()) else .done (.inr draw)

def result (fuel target : Nat) := PIR.Iteration.evaluate (attempt target) handler fuel () 0
example : (result 0 2).outcome = .returned (.inl ()) := rfl
example : (result 2 2).outcome = .returned (.inl ()) := by decide
example : (result 3 2).outcome = .returned (.inr 2) := by decide
example : (result 30 2).state = 3 := by decide
example : (result 30 2).events = [0, 1, 2] := by decide
example : (PIR.Iteration.close (result 2 2)).outcome = .stopped .exhausted := by decide
example : (PIR.Iteration.close (result 2 2)).state = 2 := by decide

example (fuel target : Nat) :
    PIR.Iteration.evaluateM (m := Option) (attempt target)
      (fun op s => pure (handler op s)) fuel () 0 = some (result fuel target) :=
  PIR.Iteration.evaluateM_pure _ _ _ _ _

/-- An outer failure after one successful call does not produce a stopped
record. Complete probabilistic records need a law of the chosen outer effect. -/
def outerFailure : MonadHandler Option signature Nat Nat := fun op state =>
  if state = 0 then some (handler op state) else none
example : PIR.Iteration.evaluateM (attempt 2) outerFailure 1 () 0 =
    some ⟨.returned (.inl ()), 1, [0]⟩ := rfl
example : PIR.Iteration.evaluateM (attempt 2) outerFailure 2 () 0 = none := rfl

/-- Grouping two steps changes the meaning of an unchanged fuel value. The
positive block law translates that value rather than erasing pending work. -/
example : (PIR.Iteration.evaluate
    (fun c => PIR.Iteration.approximate (attempt 2) 2 c) handler 2 () 0).outcome ≠
    (result 2 2).outcome := by decide
example (width blocks : Nat) :
    PIR.Iteration.evaluate (fun c => PIR.Iteration.approximate (attempt 2) width c)
      handler blocks () 0 = result (blocks * width) 2 := by
  simp only [result, PIR.Iteration.evaluate, PIR.Iteration.approximate_blocks]

def fatal (_ : Unit) : Proc signature (Unit ⊕ Nat) := .call () fun _ => .halt .reject
example : (PIR.Iteration.evaluate fatal handler 10 () 4).outcome = .stopped .reject := by decide
example : (PIR.Iteration.evaluate fatal handler 10 () 4).state = 5 := by decide
example : (PIR.Iteration.evaluate fatal handler 10 () 4).events = [4] := by decide

def never (_ : Unit) : Proc signature (Unit ⊕ Nat) := .call () fun _ => .done (.inl ())
theorem never_pending (fuel state : Nat) :
    (PIR.Iteration.evaluate never handler fuel () state).outcome = .returned (.inl ()) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => simpa [PIR.Iteration.evaluate, PIR.Iteration.approximate, never,
      Proc.bind, Proc.run, handler, Execution.follow] using ih (state + 1)
example : PIR.Iteration.Diverges never handler () 0 := by
  intro fuel
  simp [PIR.Iteration.Finished, never_pending]

/-- Identical local views cannot select different schedules, even if both
worlds are admitted. A future challenge is not entry knowledge. -/
example : ¬ Nonempty (Zkc.Source.Family.Known (fun (_ : Bool) => True)
    (fun _ => ()) id) := by
  rintro ⟨known⟩
  have bad := known.agree false true trivial trivial rfl
  contradiction

def ingress (raw : Nat) (state : Nat) : Execution Nat Nat (Sigma (fun _ : Nat => Unit)) :=
  if raw < 4 then ⟨.returned ⟨raw, ()⟩, state + 1, [10]⟩
  else ⟨.stopped .refused, state + 1, [11]⟩
def selected (raw : Nat) := Zkc.Source.Family.run ingress attempt handler raw 0
example : Zkc.Source.Family.Selects ingress (fun _ _ => True) (fun count _ => count < 4) := by
  intro raw state bound _ chosen
  unfold ingress at chosen
  split at chosen
  next small =>
    cases Outcome.returned.inj chosen
    exact small
  next large => cases chosen
example : ¬ Zkc.Source.Family.Selects
    (fun (_ : Nat) (state : Nat) => (⟨.returned ⟨4, ()⟩, state, []⟩ :
      Execution Nat Nat (Sigma (fun _ : Nat => Unit))))
    (fun _ _ => True) (fun count _ => count < 4) := by
  intro invalid
  have impossible := invalid 0 0 ⟨4, ()⟩ trivial rfl
  exact Nat.lt_irrefl 4 impossible
example : (selected 4).outcome = .stopped .refused := by decide
example : (selected 4).state = 1 := by decide
example : (selected 4).events = [11] := by decide
example : (selected 0).outcome = .returned (.inr 1) := by decide
example : (selected 0).events = [10, 1] := by decide

/-- Publication is a separate actual action. Audit events are retained, while
only a produced payload reaches the publication suffix. The sink may fail. -/
def publish (fuel target : Nat) (fail : Bool) : Execution Nat (Nat ⊕ Nat) Unit :=
  let completed := PIR.Iteration.close (result fuel target)
  let staged : Execution Nat (Nat ⊕ Nat) Nat :=
    ⟨completed.outcome, completed.state, completed.events.map Sum.inl⟩
  staged.follow fun payload state =>
    if fail then ⟨.stopped .abort, state, []⟩
    else ⟨.returned (), state, [.inr payload]⟩

example : (publish 2 2 false).events = [.inl 0, .inl 1] := by decide
example : (publish 30 2 false).events = [.inl 0, .inl 1, .inl 2, .inr 2] := by decide
example : (publish 30 2 true).outcome = .stopped .abort := by decide
example : (publish 30 2 true).state = 3 := by decide
example : (publish 30 2 true).events = [.inl 0, .inl 1, .inl 2] := by decide

end Tests.Iteration
