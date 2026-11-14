import Zkc.Tests.Core.Runs
import Zkc.Core.VocabularyObserved

/-! What each role of a run did, read beside the executor.

A protocol of three roles: the first role sends a field element to the second, the third draws
a coin that the first and the second hear, and the second samples. The observed run gives, for
each role, what it did in order, and it ends as the run does.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core Zkc.Core.Concrete Zkc.Core.Execute Zkc.Core.Vocabulary

namespace Observed

def law : Operation :=
  ⟨⟨Name.ofString "law.uniform", [.type (.nominal 0)]⟩, ⟨[], [.nominal 0], .sampling⟩⟩

/-- Role 0 sends its input to role 1; role 2 draws, and roles 0 and 1 hear; role 1 samples. -/
def package : Raw.Package :=
  ⟨[⟨Name.ofString "bls12-381.fr", []⟩], [], [], [law], [],
    [⟨false, 3, [⟨.nominal 0, 0⟩], [⟨.nominal 0, 1⟩, ⟨.nominal 0, 0⟩, ⟨.nominal 0, 1⟩], [],
      .step (.exchange 0 1 0 0) <|
      .step (.draw 2 [0, 1] 1 0 []) <|
      .step (.sample 1 2 0 []) <|
      .ret [1, 3, 5]⟩], none⟩

def kinds (did : List Did) : List (Event.Kind × Nat) := did.map fun step => (step.kind, step.site.number)

#eval show IO Unit from do
  let typed ← match elaborateWritten package with
    | .ok typed => pure typed
    | .error refusal => throw (IO.userError s!"refused: {repr refusal}")
  let table := Vocabulary.table
  let some input := checked? table package (.nominal 0) (.number 5)
    | throw (IO.userError "the input is not a value")
  for seed in [1, 2] do
    let coins := seededCoins table package [seed]
    let observed ← IO.ofExcept (runRolesObserved table package typed typed.program.protocols
      Identities.written [0, 1, 2] [some input] coins)
    let plain ← IO.ofExcept (runRoles table package typed typed.program.protocols
      Identities.written [0, 1, 2] [some input] coins)
    -- the kinds and the sites of what each role did, in its own order
    let expected : List (List (Event.Kind × Nat)) :=
      [[(.sent, 0), (.heard, 1)], [(.received, 0), (.heard, 1), (.sampled, 2)], [(.drew, 1)]]
    unless observed.did.map kinds == expected do
      throw (IO.userError s!"seed {seed}: the roles did {repr (observed.did.map kinds)}")
    -- the value sent is the value received, and the coin drawn is the coin that both hear
    match observed.did with
    | [[sent, heardFirst], [received, heardSecond, _], [drew]] =>
      unless sent.value == .number 5 && received.value == sent.value &&
          heardFirst.value == drew.value && heardSecond.value == drew.value do
        throw (IO.userError s!"seed {seed}: the values of the events do not agree")
    | _ => throw (IO.userError s!"seed {seed}: the shape of the events")
    -- the observed run ends as the run
    let describe (outcomes : List (Outcome (List Datum))) : List String :=
      outcomes.map (·.describe reprStr)
    unless describe observed.outcomes == describe plain.outcomes do
      throw (IO.userError s!"seed {seed}: the observed run ends {describe observed.outcomes}; the run {describe plain.outcomes}")

#print axioms finishObserved_fst
#print axioms observeAlone_fst
#print axioms runRolesObserved_outcomes
#print axioms runRoleObserved_outcome

end Observed
