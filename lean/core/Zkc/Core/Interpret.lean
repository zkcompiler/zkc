module

public import Zkc.Core.Process

public section

/-! Interpretations of effect trees.

`interpret` and its laws are the part of the maintained `Zkc.Program.Interpretation`
that a structural theorem about a step needs: an operation of one signature becomes a
process of another with the same reply type, and interpretation commutes with
sequencing.

A step that threads a value is an interpretation with a state: the handler of an
operation takes the state and returns the reply with the next state. `interpretWith`
is that interpretation, `interpretWith_bind` its sequencing law and
`interpretWith_repeatN` and `interpretWith_iterateN` its laws for bounded iteration: the
iteration of the interpreted step over the carried value paired with the state. A handler without a state is a
special case (`interpretWith_stateless`).

Two steps that thread are two interpretations, one after the other. `composeHandlers` is
the one handler over the pair of the two states: an operation is handled by the first
handler, and what the first handler performs is interpreted by the second.
`interpretWith_interpretWith` says that interpreting by the first handler and then by the
second is interpreting by the composed handler.
-/

set_option autoImplicit false

namespace PIR

variable {I J : Signature} {A B S : Type}

/-- An interpretation preserves the reply type of each source operation. -/
abbrev OperationInterpretation (I J : Signature) :=
  (op : I.Op) → Process J (I.Reply op)

/-- An interpretation with a state: the reply and the next state. -/
abbrev StatefulInterpretation (I J : Signature) (S : Type) :=
  (op : I.Op) → S → Process J (I.Reply op × S)

namespace Process

def interpret (operations : OperationInterpretation I J) : Process I A → Process J A
  | .done value => .done value
  | .halt why => .halt why
  | .call op next => (operations op).bind fun reply => (next reply).interpret operations

theorem interpret_bind (operations : OperationInterpretation I J) (source : Process I A)
    (next : A → Process I B) :
    (source.bind next).interpret operations =
      (source.interpret operations).bind fun value => (next value).interpret operations := by
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op tail ih =>
    simp only [bind, interpret, bind_assoc]
    congr 1
    funext reply
    exact ih reply

theorem interpret_identity (source : Process I A) :
    source.interpret (fun op => .call op .done) = source := by
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op next ih =>
    simp only [interpret, bind]
    congr 1
    funext reply
    exact ih reply

/-- The interpretation of a process from a state: its value and the final state. -/
@[expose] def interpretWith (handler : StatefulInterpretation I J S) : Process I A → S → Process J (A × S)
  | .done value, state => .done (value, state)
  | .halt why, _ => .halt why
  | .call op next, state =>
      (handler op state).bind fun reply => (next reply.1).interpretWith handler reply.2

/-- A prefix and a suffix are interpreted one after the other, and the suffix starts
from the state the prefix left. -/
theorem interpretWith_bind (handler : StatefulInterpretation I J S) (source : Process I A)
    (next : A → Process I B) (state : S) :
    (source.bind next).interpretWith handler state =
      (source.interpretWith handler state).bind fun result =>
        (next result.1).interpretWith handler result.2 := by
  induction source generalizing state with
  | done value => rfl
  | halt why => rfl
  | call op tail ih =>
    simp only [bind, interpretWith, bind_assoc]
    congr 1
    funext reply
    exact ih reply.1 reply.2

/-- An interpretation without a state leaves the state as it is. -/
theorem interpretWith_stateless (operations : OperationInterpretation I J) (source : Process I A)
    (state : S) :
    source.interpretWith (fun op state => (operations op).bind fun reply => .done (reply, state))
        state =
      (source.interpret operations).bind fun value => .done (value, state) := by
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op tail ih =>
    simp only [bind, interpretWith, interpret, bind_assoc]
    congr 1
    funext reply
    exact ih reply

end Process

/-- Bounded iteration under an interpretation with a state is the iteration of the
interpreted step over the carried value and the state. -/
theorem interpretWith_repeatN (handler : StatefulInterpretation I J S) (step : A → Process I A) :
    ∀ (count : Nat) (value : A) (state : S),
      (repeatN count step value).interpretWith handler state =
        repeatN count (fun pair : A × S => (step pair.1).interpretWith handler pair.2)
          (value, state)
  | 0, _, _ => rfl
  | count + 1, value, state => by
      simp only [repeatN, Process.interpretWith_bind]
      congr 1
      funext result
      exact interpretWith_repeatN handler step count result.1 result.2

/-- The same for a step that takes its iteration number. -/
theorem interpretWith_iterateN (handler : StatefulInterpretation I J S)
    (step : Nat → A → Process I A) :
    ∀ (count start : Nat) (value : A) (state : S),
      (iterateN count step start value).interpretWith handler state =
        iterateN count
          (fun iteration (pair : A × S) => (step iteration pair.1).interpretWith handler pair.2)
          start (value, state)
  | 0, _, _, _ => rfl
  | count + 1, start, value, state => by
      simp only [iterateN, Process.interpretWith_bind]
      congr 1
      funext result
      exact interpretWith_iterateN handler step count (start + 1) result.1 result.2

/-! ## Two handlers, one after the other -/

section Compose

variable {K : Signature} {T : Type}

/-- Two handlers as one handler over the pair of their states: an operation is handled by
the first, and what the first performs is interpreted by the second. -/
@[expose] def composeHandlers (first : StatefulInterpretation I J S)
    (second : StatefulInterpretation J K T) : StatefulInterpretation I K (S × T) :=
  fun op states =>
    ((first op states.1).interpretWith second states.2).bind fun result =>
      .done (result.1.1, (result.1.2, result.2))

/-- Interpreting by one handler and then by another is interpreting by the composed
handler from the pair of the two states: the value, the final state of the first and the
final state of the second are the same. -/
theorem Process.interpretWith_interpretWith (first : StatefulInterpretation I J S)
    (second : StatefulInterpretation J K T) (source : Process I A) (state : S) (other : T) :
    (source.interpretWith first state).interpretWith second other =
      (source.interpretWith (composeHandlers first second) (state, other)).bind fun result =>
        .done ((result.1, result.2.1), result.2.2) := by
  induction source generalizing state other with
  | done value => rfl
  | halt why => rfl
  | call op tail ih =>
    simp only [Process.interpretWith, composeHandlers, Process.interpretWith_bind,
      Process.bind_assoc, Process.done_bind]
    congr 1
    funext result
    exact ih result.1.1 result.1.2 result.2

end Compose

end PIR
