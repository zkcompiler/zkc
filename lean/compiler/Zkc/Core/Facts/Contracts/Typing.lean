module

public import Zkc.Core.Facts.Body.Statements

@[expose] public section

namespace Zkc.Core.BodyAnalysis

/-- Every operation exposed to the expression checker is admissible and total on inputs of
its advertised types. All its returned ports have their advertised types. -/
structure AssertionTypes.Lawful {D : Dialect} {Raw : Type} (σ : Setting D Raw)
    (types : AssertionTypes D.Ty Raw) : Prop where
  admissible : ∀ {op ins outs}, types.signature op ins = some outs → σ.cfg.rules.assertable op = true
  total : ∀ {op ins outs}, types.signature op ins = some outs → ∀ args,
    ArgumentsMatch (TypedValue σ.sem σ.Valid) args ins →
    ∃ values, σ.Runs op args values ∧ ArgumentsMatch (TypedValue σ.sem σ.Valid) values outs
  boolean : ∀ {t}, types.boolean t = true → ∀ v, TypedValue σ.sem σ.Valid v t →
    ∃ b, σ.R.bool v = some b

end Zkc.Core.BodyAnalysis
