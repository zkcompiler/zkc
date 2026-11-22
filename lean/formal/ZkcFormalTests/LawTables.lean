import ZkcFormal.Written.ArithmeticDraws

/-!
The tables of the laws with a sampler, and the samplers that the models give.

The standard model, over any algebra, draws a position. The arithmetic model, over a field that
can be sampled, draws a scalar and a sequence of scalars as well. Each table is checked at laws
that it has and at laws that it has not, and the sampler of a coin is read from its law, its
payload and its type alone.
-/

open Zkc Zkc.Core ZkcFormal.Written OracleComp

namespace ZkcFormalTests.LawTables

abbrev scalarLaw : Standard.LawKey := .uniform (.nominal (.field .bls12381Fr))
abbrev scalarsLaw (n : ℕ) : Standard.LawKey := .uniform (.seq (.nominal (.field .bls12381Fr)) (some n))
abbrev positionLaw (n : ℕ) : Standard.LawKey := .uniform (.fin n)
abbrev pointLaw : Standard.LawKey := .uniform (.nominal (.group .g1))

/-! The table of the standard model: positions, and nothing of the scalars. -/

example : StandardModel.sampled (positionLaw 8) (.fin 8) = true := by decide
example : StandardModel.sampled (positionLaw 8) (.fin 9) = false := by decide
example : StandardModel.sampled (positionLaw 0) (.fin 0) = false := by decide
example : StandardModel.sampled scalarLaw scalarTy = false := by decide
example : StandardModel.sampled (scalarsLaw 2) (.seq scalarTy (some 2)) = false := by decide

/-! The table of the arithmetic model: positions, a scalar, a sequence of scalars of its size. -/

example : ArithmeticModel.sampled (positionLaw 8) (.fin 8) = true := by decide
example : ArithmeticModel.sampled scalarLaw scalarTy = true := by decide
example : ArithmeticModel.sampled (scalarsLaw 2) (.seq scalarTy (some 2)) = true := by decide
example : ArithmeticModel.sampled (scalarsLaw 2) (.seq scalarTy (some 3)) = false := by decide
example : ArithmeticModel.sampled (scalarsLaw 2) (.seq scalarTy none) = false := by decide
example : ArithmeticModel.sampled scalarLaw (.seq scalarTy (some 1)) = false := by decide
example : ArithmeticModel.sampled pointLaw pointTy = false := by decide
example : ArithmeticModel.sampled (.uniform .bool) .bool = false := by decide

section
variable (F G : Type) [Field F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G]
  [DecidableEq G]

/-! The sampler of a coin, read from its law and its type: the same under every audience and at
every occurrence. -/

example (peers : List Role) (at_ : Occurrence) :
    lawSamplers (ArithmeticModel.model F G) (ArithmeticModel.draws F G)
      (.own (.coin (scalarsLaw 2)) peers at_ [] .nil (.seq scalarTy (some 2))) =
        some (drawVector F 2) := rfl

example (peers : List Role) (at_ : Occurrence) :
    lawSamplers (ArithmeticModel.model F G) (ArithmeticModel.draws F G)
      (.own (.coin scalarLaw) peers at_ [] .nil scalarTy) = some ($ᵗ F) := rfl

example (peers : List Role) (at_ : Occurrence) :
    lawSamplers (ArithmeticModel.model F G) (ArithmeticModel.draws F G)
      (.own (.coin (positionLaw 8)) peers at_ [] .nil (.fin 8)) = some (drawPosition 7) := rfl

example (peers : List Role) (at_ : Occurrence) :
    lawSamplers (ArithmeticModel.model F G) (ArithmeticModel.draws F G)
      (.own (.coin pointLaw) peers at_ [] .nil pointTy) = none := rfl

/-- A law outside the table has no sampler, over every field. -/
example : (ArithmeticModel.draws F G pointLaw [] .nil pointTy).isSome = false :=
  (ArithmeticModel.sampled_iff_draws F G pointLaw pointTy).symm.trans (by decide)

/-- The standard draws, over the algebra of a field, have no sampler for a scalar. -/
example (peers : List Role) (at_ : Occurrence) :
    lawSamplers (ArithmeticModel.model F G) (StandardModel.draws (ArithmeticModel.data F G))
      (.own (.coin scalarLaw) peers at_ [] .nil scalarTy) = none := rfl

end

/-- info: 'ZkcFormal.Written.prEvent_drawVector_le_of_linear_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prEvent_drawVector_le_of_linear_form

/-- info: 'ZkcFormal.Written.ArithmeticModel.draws_permitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ArithmeticModel.draws_permitted

/-- info: 'ZkcFormal.Written.ArithmeticModel.sampled_iff_draws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ArithmeticModel.sampled_iff_draws

end ZkcFormalTests.LawTables
