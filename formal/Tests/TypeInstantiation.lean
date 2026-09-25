import Zkc.Source.TypeInstantiation
import Zkc.Source.Requirements

set_option autoImplicit false

namespace Tests.TypeInstantiation
open Zkc.Source PIR

inductive Symbolic where
  | condition | first | second
  deriving DecidableEq

inductive Concrete where
  | condition | natural
  deriving DecidableEq

abbrev select : Symbolic → Concrete
  | .condition => .condition
  | .first | .second => .natural

abbrev generic : Language where
  Ty := Symbolic
  Op := Unit
  arguments _ := [.first, .second]
  result _ := .first
  condition := .condition

abbrev Value : Concrete → Type
  | .condition => Bool
  | .natural => Nat

abbrev interface : Signature := ⟨Nat, fun _ => Nat⟩

abbrev selected : Interpretation (generic.instantiate select) interface where
  Value := Value
  condition := id
  operation _ args := match args with
    | .cons a (.cons b .nil) => .call (a + b) .done

def body : Region generic [.first, .second, .condition] .first :=
  .letOp () (.cons .here (.cons (.there .here) .nil))
    (.branch (.there (.there (.there .here)))
      (.iterate 2 .here (.ret .here) (.bind (.ret .here) (.ret .here)))
      (.stop .reject))

def arguments (a b : Nat) (enabled : Bool) :
    Values Value ([Symbolic.first, .second, .condition].map select) :=
  .cons a (.cons b (.cons enabled .nil))

/-- Failure records its changed state; instantiation must preserve that too. -/
def handler : Handler interface Nat Nat := fun value state =>
  ⟨if value == 0 then .stopped .exhausted else .returned value, state + 1, [value]⟩

def run (a b : Nat) (enabled : Bool) : Execution Nat Nat Nat :=
  ((body.instantiate select).denote (ty := .natural) selected
    (arguments a b enabled).get).run handler 0

example : run 3 4 true = ⟨.returned 7, 1, [7]⟩ := rfl
example : run 3 4 false = ⟨.stopped .reject, 1, [7]⟩ := rfl
example : run 0 0 true = ⟨.stopped .exhausted, 1, [0]⟩ := rfl

example (a b state : Nat) (enabled : Bool) :
    ((body.instantiate select).denote selected (arguments a b enabled).get).run handler state =
      (body.denote (selected.pullback select)
        (Environment.pullback select (arguments a b enabled).get)).run handler state :=
  body.run_instantiate select selected handler (arguments a b enabled).get state

-- A non-injective type substitution preserves positions. It must not identify
-- different arguments merely because their selected types are now equal.
example : (Var.instantiate select
    (.there .here : Var [Symbolic.first, .second] .second)).index = 1 := rfl

end Tests.TypeInstantiation
