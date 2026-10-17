import Zkc.Source.Participant

/-! Shared participant rules need no mathematical language or Common scalar sorts.
Open-process equations cover role ownership, missing inputs and actual replies.
A deterministic service is a valid policy. -/

set_option autoImplicit false

namespace Tests.ParticipantInterface

open Zkc.Source Zkc.Source.Participant PIR

section ReplyTypes

variable {Role Ty : Type} {services : Services Ty} {Value : Ty → Type}

example (ty : Ty) (site : String) (sender : Role) :
    (interface Role Ty services Value).Reply (.receive ty site sender) = Value ty := rfl

example (site : String) (op : services.Op) (args : Values Value (services.arguments op)) :
    (interface Role Ty services Value).Reply (.query site op args) =
      Value (services.result op) := rfl

theorem receive_independent [DecidableEq Role] (self sender : Role) (different : sender ≠ self)
    (site : String) (ty : Ty) (localValue : Option (Value ty)) :
    Participant.exchange (services := services) (Value := Value) self sender self site localValue =
      .call (.receive ty site sender) (fun received => .done (some received)) := by
  simp only [Participant.exchange, different, ↓reduceIte]

end ReplyTypes

inductive ValueSort where
  | count | flag

abbrev Value : ValueSort → Type
  | .count => Nat
  | .flag => Bool

abbrev services : Services ValueSort where
  Op := Unit
  arguments _ := [.count, .flag]
  result _ := .count

abbrev actions := interface Nat ValueSort services Value

def handler (received : Bool) : Handler actions Unit Unit
  | .send .., state => ⟨.returned (), state, []⟩
  | .receive .count .., state => ⟨.returned 0, state, []⟩
  | .receive .flag .., state => ⟨.returned received, state, []⟩
  | .query _ () (.cons count (.cons flag .nil)), state =>
      ⟨.returned (if flag then count + 1 else count), state, []⟩

def delivery (self : Nat) (localValue : Option Bool) : Proc actions (Option Bool) :=
  Participant.exchange self 0 1 "delivery" (ty := ValueSort.flag) localValue

-- Sending aliases the sender's operand; it never substitutes a received value.
example (sent : Bool) : delivery 0 (some sent) =
    .call (.send (ty := .flag) "delivery" 1 sent) (fun _ => .done (some sent)) := rfl

example : delivery 0 none = .halt .incomplete := rfl

-- A receiver uses the actual reply even when its operand is absent or disagrees.
example (localValue : Option Bool) (received : Bool) :
    ((delivery 1 localValue).run (handler received) ()).outcome = .returned (some received) := rfl

example : ((delivery 1 (some true)).run (handler false) ()).outcome = .returned (some false) := rfl

example (localValue : Option Bool) : delivery 2 localValue = .done none := rfl

-- Sender precedence is preserved even for an exchange rejected by admission.
example (value : Bool) :
    (Participant.exchange 0 0 0 "self" (ty := ValueSort.flag) (some value) : Proc actions (Option Bool)) =
      .call (.send (ty := .flag) "self" 0 value) (fun _ => .done (some value)) := rfl

def increment (self : Nat) (count : Option Nat) (flag : Option Bool) : Proc actions (Option Nat) :=
  Participant.query self 0 "increment" () (.cons count (.cons flag .nil))

-- Query arguments retain their heterogeneous order and the reply is a Nat.
example (count : Nat) (flag : Bool) : increment 0 (some count) (some flag) =
    .call (.query "increment" () (.cons count (.cons flag .nil)))
      (fun reply => .done (some reply)) := rfl

example (count : Nat) (flag received : Bool) :
    ((increment 0 (some count) (some flag)).run (handler received) ()).outcome =
      .returned (some (if flag then count + 1 else count)) := rfl

example (flag : Bool) : increment 0 none (some flag) = .halt .incomplete := rfl

example (count : Nat) : increment 0 (some count) none = .halt .incomplete := rfl

example : increment 1 none none = .done none := rfl

def checkCondition (self : Nat) (condition : Option Bool) : Proc actions Unit :=
  Participant.guard self 0 condition

example : checkCondition 0 (some true) = .done () := rfl

example : checkCondition 0 (some false) = .halt .reject := rfl

example : checkCondition 0 none = .halt .incomplete := rfl

example (condition : Option Bool) : checkCondition 1 condition = .done () := rfl

-- A rejecting or incomplete guard cannot run its suffix.
example (next : Unit → Proc actions Nat) :
    (checkCondition 0 (some false)).bind next = .halt .reject := rfl

example (next : Unit → Proc actions Nat) :
    (checkCondition 0 none).bind next = .halt .incomplete := rfl

example {A : Type} (value : Option A) : Participant.restrict true value = value := rfl

example {A : Type} (value : Option A) : Participant.restrict false value = none := rfl

example {A : Type} (selected : Bool) : Participant.restrict selected (none : Option A) = none := by
  cases selected <;> rfl

end Tests.ParticipantInterface
