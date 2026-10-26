module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Semantics.Interaction

@[expose] public section

/-! What every value a process returns satisfies.

`Yields property process` holds when every value `process` can return, for
every reply to every action on the way, satisfies `property`; a stop returns
nothing. A continuation then matters only at such values (`Yields.bind_congr`),
and a counted invariant that one step preserves holds after any number of
repeated steps (`Yields.repeatN`).
-/

set_option autoImplicit false

namespace PIR

/-- Every value a process can return satisfies `property`. -/
def Yields {I : Signature} {A : Type} (property : A → Prop) : Process I A → Prop
  | .done value => property value
  | .halt _ => True
  | .call _ next => ∀ reply, Yields property (next reply)

theorem Yields.bind_congr {I : Signature} {A B : Type} {property : A → Prop}
    {process : Process I A} (yields : Yields property process) {first second : A → Process I B}
    (same : ∀ value, property value → first value = second value) :
    process.bind first = process.bind second := by
  induction process with
  | done value => exact same value yields
  | halt reason => rfl
  | call operation next ih =>
      simp only [Process.bind]
      congr 1
      funext reply
      exact ih reply (yields reply)

theorem Yields.bind {I : Signature} {A B : Type} {property : A → Prop} {result : B → Prop}
    {process : Process I A} (yields : Yields property process) {next : A → Process I B}
    (nextYields : ∀ value, property value → Yields result (next value)) :
    Yields result (process.bind next) := by
  induction process with
  | done value => exact nextYields value yields
  | halt reason => trivial
  | call operation continuation ih => exact fun reply => ih reply (yields reply)

theorem Yields.mono {I : Signature} {A : Type} {property weaker : A → Prop}
    {process : Process I A} (yields : Yields property process)
    (implies : ∀ value, property value → weaker value) : Yields weaker process := by
  induction process with
  | done value => exact implies value yields
  | halt reason => trivial
  | call operation continuation ih => exact fun reply => ih reply (yields reply)

/-- Repeated steps preserve a counted invariant. -/
theorem Yields.repeatN {I : Signature} {A : Type} {invariant : Nat → A → Prop}
    {step : A → Process I A}
    (preserved : ∀ index value, invariant index value → Yields (invariant (index + 1)) (step value)) :
    ∀ (count index : Nat) (value : A), invariant index value →
      Yields (invariant (index + count)) (PIR.repeatN count step value)
  | 0, _, _, holds => holds
  | count + 1, index, value, holds =>
      (preserved index value holds).bind fun next nextHolds => by
        have rest := Yields.repeatN preserved count (index + 1) next nextHolds
        rwa [Nat.add_right_comm, Nat.add_assoc] at rest

end PIR

-- Own generated equations here, before independent clients request them.
-- Their proofs remain kernel checked and retain a single stored provider.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getUnfoldEqnFor? ``PIR.Yields
  discard <| Lean.Meta.getEqnsFor? ``PIR.Yields
