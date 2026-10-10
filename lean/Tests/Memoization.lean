import Zkc.Transformations.Memoization
import Zkc.Semantics.Execution
import Zkc.Semantics.Preparation.Emission

set_option autoImplicit false

namespace Tests.Memoization

open Zkc.Modules.ImmutableCache Zkc.Transformations.Memoization

def provider (key : Nat) : Nat := key * key + 1
def always : Cache Nat Nat → Nat → Bool := fun _ _ => true
def never : Cache Nat Nat → Nat → Bool := fun _ _ => false

def adaptive : Client Nat Nat Nat (Nat × Nat) :=
  .call 1 fun first => .emit first (.call 1 fun again =>
    .call (if first = 2 then 2 else 3) fun last => .emit last (.done (again, last)))

example : (runMemo provider always empty adaptive).1 = ([2, 5], (2, 5)) := rfl
example : (runMemo provider never empty adaptive).1 = ([2, 5], (2, 5)) := rfl

example (first second : Cache Nat Nat → Nat → Bool) :
    (runMemo provider first empty adaptive).1 = (runMemo provider second empty adaptive).1 :=
  arbitrary_policy_same_observer provider first second adaptive

def stale : Cache Nat Nat := insert empty 1 9

example : ¬Valid provider stale := by
  intro valid
  have wrong : (9 : Nat) = 2 := valid 1 9 rfl
  contradiction

example : (runMemo provider always stale adaptive).1 = ([9, 10], (9, 10)) := rfl

def before (key : Nat) : Nat := key + 1
def after (key : Nat) : Nat := if key = 1 then 10 else before key
def prepared : Cache Nat Nat := insert empty 1 (before 1)

example : Valid before prepared := insert_valid before empty (empty_valid before) 1
example : ¬Valid after prepared := by
  intro valid
  have wrong : (2 : Nat) = 10 := valid 1 2 rfl
  contradiction

def ordered (key : Nat × Nat) : Nat := 2 * key.1 + key.2
example : ordered (1,2) ≠ ordered (2,1) := by decide

abbrev counter : PIR.Signature := ⟨Unit, fun _ => Nat⟩
def stateful : PIR.Handler counter Nat Nat := fun _ state =>
  ⟨.returned state, state + 1, [state]⟩
def twice : PIR.Proc counter (Nat × Nat) :=
  .call () fun first => .call () fun second => .done (first, second)

/-- The concrete mutable service cannot be replaced by a pure zero-valued call. -/
example : (twice.run stateful 0).outcome = .returned (0,1) := rfl
example : (twice.run stateful 0).outcome ≠ .returned (0,0) := by decide

def prepare (key : Nat) : Nat × Nat := (key + 1, 4)
def prices : Zkc.Modules.Preparation.Prices Nat Nat := ⟨fun _ _ => 1, fun _ _ => 2⟩

def abortAfterReuse :
    PIR.Proc (PIR.Preparation.signature Nat Nat (PIR.Preparation.Emission.signature Nat)) Unit :=
  .call (.prepare 3) fun value => .call (.external value) fun _ =>
    .call (.prepare 3) fun _ => .halt .abort

def direct := abortAfterReuse.run
  (PIR.Preparation.handler prepare prices .direct PIR.Preparation.Emission.handler) (empty, ())
def memoized := abortAfterReuse.run
  (PIR.Preparation.handler prepare prices .memo PIR.Preparation.Emission.handler) (empty, ())

example : PIR.Related (PIR.Preparation.StateRel prepare) PIR.Preparation.view PIR.Preparation.view
    direct memoized :=
  PIR.Preparation.contextual_memo prepare prices PIR.Preparation.Emission.handler
    abortAfterReuse (empty, ()) (empty, ()) ⟨empty_valid prepare, empty_valid prepare, rfl⟩

example : memoized.outcome = .stopped .abort ∧ memoized.state.1 3 = some (4,4) := ⟨rfl, rfl⟩
example : PIR.observeEvents PIR.Preparation.view memoized.events = [4] := rfl
example : PIR.Preparation.work memoized.events = 4 ∧
    PIR.Preparation.saved memoized.events = 4 ∧
    PIR.Preparation.overhead memoized.events = 4 := ⟨rfl, rfl, rfl⟩

/-- The protocol projection excludes accounting; raw accounting remains available
and cannot be included in an equality claim without another observation law. -/
example : direct.events ≠ memoized.events := by decide

def repeated : Zkc.Modules.Preparation.Program Nat Nat Nat Unit :=
  .request 3 fun _ => .request 3 fun _ => .done ()
def expensive : Zkc.Modules.Preparation.Prices Nat Nat := ⟨fun _ _ => 5, fun _ _ => 0⟩

example :
    let result := Zkc.Modules.Preparation.run prepare expensive .memo repeated empty
    result.work + result.overhead >
      (Zkc.Modules.Preparation.run prepare expensive .direct repeated empty).work := by decide

end Tests.Memoization
