import Zkc.Properties.Judgment
import Zkc.Semantics.Relation
import Zkc.Probability.Observation
import Mathlib.Logic.Equiv.Prod

/-! Relation families can be judgment subjects, while observation changes may
use distinct sample representations. Neither claim forces executable values
into a higher universe or supplies an absent security premise.
-/

set_option autoImplicit false

namespace Tests.PropertyContexts

open PIR.Properties PIR.Relation

/-- A valid instance supplies an actual statement, even when the relation itself
packages the statement and witness types in `Type 1`. -/
def inhabitedStatement : Conditional Family (fun family => Nonempty family.Statement) where
  requires family := ∃ statement witness, family.holds statement witness
  valid _ proof := by
    obtain ⟨statement, _, _⟩ := proof
    exact ⟨statement⟩

abbrev evenRelation : Family := ⟨Nat, Nat, fun statement witness => witness + witness = statement⟩

example : inhabitedStatement.requires evenRelation := ⟨4, 2, rfl⟩

example : Nonempty evenRelation.Statement :=
  inhabitedStatement.use evenRelation ⟨4, 2, rfl⟩

abbrev emptyRelation : Family := ⟨Empty, Unit, fun _ _ => True⟩

example : ¬ inhabitedStatement.requires emptyRelation := by
  rintro ⟨statement, _, _⟩
  nomatch statement

example :
    (Zkc.Probability.Observation.fiberEquiv (Equiv.prodComm Nat Bool)
      Prod.fst Prod.snd (fun _ => rfl) 3 ⟨(3, true), rfl⟩).val = (true, 3) := rfl

end Tests.PropertyContexts
