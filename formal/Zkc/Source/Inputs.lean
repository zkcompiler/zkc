import Zkc.Source.Availability

set_option autoImplicit false
namespace PIR.SourceView
open Zkc.Source.Availability

inductive Slot (Role : Type) where
  | shared : Nat → Slot Role
  | owned : Role → Nat → Slot Role
  deriving DecidableEq

structure World (Role F H : Type) where
  publicInputs : Nat → Option F
  privateInputs : Role → Nat → Option F
  hidden : H

variable {Role F H : Type} [DecidableEq Role]

def permitted (actor : Role) : Slot Role → Prop
  | .shared _ => True
  | .owned owner _ => owner = actor

/-- Availability and value are both part of the actor's permitted input view.
    Provider state H is never an input to this read operation. -/
def read (actor : Role) (w : World Role F H) : Slot Role → Option F
  | .shared i => w.publicInputs i
  | .owned owner i => if owner = actor then w.privateInputs actor i else none

def env (actor : Role) (bindings : List (Slot Role)) (w : World Role F H) : Env F :=
  fun i => (bindings[i]?).bind (read actor w)

def SameView (actor : Role) (w v : World Role F H) : Prop :=
  w.publicInputs = v.publicInputs ∧ w.privateInputs actor = v.privateInputs actor

theorem read_agrees (actor : Role) (w v : World Role F H)
    (agree : SameView actor w v) (slot : Slot Role) : read actor w slot = read actor v slot := by
  cases slot with
  | shared i => exact congrFun agree.1 i
  | owned owner i => simp only [read,agree.2]

theorem read_permitted (actor : Role) (w : World Role F H) (slot : Slot Role)
    (value : F) (present : read actor w slot = some value) : permitted actor slot := by
  cases slot with
  | shared i => trivial
  | owned owner i =>
    by_cases h : owner = actor
    · exact h
    · simp [read,h] at present

end PIR.SourceView
