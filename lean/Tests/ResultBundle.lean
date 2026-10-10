import Zkc.Source.ResultBundle
import Zkc.Source.TypeInstantiation

set_option autoImplicit false

namespace Tests.ResultBundle
open Zkc.Source PIR
open Zkc.Source.ResultBundle

inductive Ty where
  | field | authority | condition
  deriving DecidableEq

inductive Op where
  | draw | guard | pair

abbrev signature : ResultBundle.Signature where
  Ty := Ty
  Op := Op
  arguments
    | .draw => [.authority]
    | .guard => [.condition]
    | .pair => [.field, .field]
  results
    | .draw => [.field, .authority]
    | .guard => []
    | .pair => [.field, .field]
  condition := .condition

abbrev Value : Ty → Type
  | .field | .authority => Nat
  | .condition => Bool

inductive Request where
  | draw (generation : Nat)
  | guard (allowed : Bool)
  deriving DecidableEq, Repr

abbrev interface : PIR.Signature := ⟨Request, fun _ => Nat⟩

abbrev meaning : Meaning signature interface where
  Value := Value
  condition := id
  operation
    | .draw, .cons generation .nil =>
        .call (.draw generation) fun random => .done (.cons random (.cons (generation + 1) .nil))
    | .guard, .cons allowed .nil => .call (.guard allowed) fun _ => .done .nil
    | .pair, .cons a (.cons b .nil) => .done (.cons b (.cons a .nil))

def handler : Handler interface Nat Request := fun request state =>
  match request with
  | .draw generation =>
      ⟨if generation == state then .returned 17 else .stopped .exhausted,
        state + 1, [request]⟩
  | .guard allowed => ⟨if allowed then .returned 0 else .stopped .reject, state, [request]⟩

-- Return both the random value and its successor authority. The unit-returning
-- guard must run, and its stop must preserve the preceding consumed draw.
def drawThenGuard : Region (language signature) [[.authority], [.condition]] [.field, .authority] :=
  invoke .draw (.cons .here .nil)
    (invoke .guard (.cons (.there (.there (.there (.there .here)))) .nil)
      (.ret (.there (.there (.there .here)))))

def arguments (generation : Nat) (allowed : Bool) :
    Values (Values Value) [[.authority], [.condition]] :=
  .cons (.cons generation .nil) (.cons (.cons allowed .nil) .nil)

def run (generation : Nat) (allowed : Bool) : Execution Nat Request (Values Value [.field, .authority]) :=
  (drawThenGuard.denote meaning.interpretation (arguments generation allowed).get).run handler 0

example : run 0 true = ⟨.returned (.cons 17 (.cons 1 .nil)), 1, [.draw 0, .guard true]⟩ := rfl
example : run 0 false = ⟨.stopped .reject, 1, [.draw 0, .guard false]⟩ := rfl
example : run 3 true = ⟨.stopped .exhausted, 1, [.draw 3]⟩ := rfl

-- Two equal result types remain two distinct ordered bindings. Return the first
-- projected result after exchanging the two values in the primitive.
def ordered : Region (language signature) [[.field], [.field]] [.field] :=
  invoke .pair (.cons .here (.cons (.there .here) .nil)) (.ret .here)

example : (ordered.denote meaning.interpretation
    (Values.cons (Values.cons 3 .nil) (.cons (.cons 8 .nil) .nil)).get).run handler 0 =
      ⟨.returned (.cons 8 .nil), 0, []⟩ := rfl

-- Bundles use the ordinary structured substitution theorem. No new control
-- representation or second instantiation proof is required.
example {Target : Type} (select : List Ty → Target)
    (selected : Interpretation ((language signature).instantiate select) interface)
    (env : Environment selected.Value ([[Ty.authority], [Ty.condition]].map select)) :
    (drawThenGuard.instantiate select).denote selected env =
      drawThenGuard.denote (selected.pullback select) (env.pullback select) :=
  drawThenGuard.denote_instantiate select selected env

end Tests.ResultBundle
