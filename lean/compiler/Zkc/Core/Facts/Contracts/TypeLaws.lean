module

public import Zkc.Core.Facts.Contracts.Typing
public import Zkc.Core.Facts.Body.EnteringSound

@[expose] public section

namespace Zkc.Core.BodyAnalysis

theorem ArgumentsMatch.lookup {T V : Type} {R : V → T → Prop} {vs : List V} {ts : List T}
    (matched : ArgumentsMatch R vs ts) {i : Nat} {t : T} (atType : ts[i]? = some t) :
    ∃ v, vs[i]? = some v ∧ R v t := by
  induction matched generalizing i with
  | nil => simp at atType
  | cons first _ ih =>
    cases i with
    | zero => cases atType; exact ⟨_, rfl, first⟩
    | succ i => exact ih atType

section
variable {D : Dialect} {Raw : Type} {σ : Setting D Raw}
    {types : AssertionTypes D.Ty Raw} (laws : types.Lawful σ)
    {context : List D.Ty} {args : List σ.sem.Dyn}
    (actual : ArgumentsMatch (TypedValue σ.sem σ.Valid) args context)

set_option linter.unusedSectionVars false in
include laws actual in
mutual
  theorem AssertionTypes.infer_sound : ∀ (expr : Expr Raw) {t}, types.infer context expr = some t →
      ∃ v, Expr.Denotes σ.Runs args expr v ∧ TypedValue σ.sem σ.Valid v t
    | .arg i, _, typed => by
        obtain ⟨v, read, ht⟩ := actual.lookup typed
        exact ⟨v, .arg read, ht⟩
    | .apply op operands result, _, typed => by
        cases inferred : types.inferAll context operands with
        | none => simp [AssertionTypes.infer, inferred] at typed
        | some ins =>
          cases signature : types.signature op ins with
          | none => simp [AssertionTypes.infer, inferred, signature] at typed
          | some outs =>
            simp [AssertionTypes.infer, inferred, signature] at typed
            obtain ⟨xs, den, matched⟩ := AssertionTypes.inferAll_sound operands inferred
            obtain ⟨ys, ran, matchedOut⟩ := laws.total signature xs matched
            obtain ⟨v, read, ht⟩ := matchedOut.lookup typed
            exact ⟨v, .apply den ran read, ht⟩
  theorem AssertionTypes.inferAll_sound : ∀ (exprs : Exprs Raw) {ts}, types.inferAll context exprs = some ts →
      ∃ vs, Exprs.Denote σ.Runs args exprs vs ∧ ArgumentsMatch (TypedValue σ.sem σ.Valid) vs ts
    | .nil, _, typed => by cases typed; exact ⟨[], .nil, .nil⟩
    | .cons first rest, _, typed => by
        cases head : types.infer context first with
        | none => simp [AssertionTypes.inferAll, head] at typed
        | some t =>
          cases tail : types.inferAll context rest with
          | none => simp [AssertionTypes.inferAll, head, tail] at typed
          | some ts =>
            simp [AssertionTypes.inferAll, head, tail] at typed
            subst typed
            obtain ⟨x, den, ht⟩ := AssertionTypes.infer_sound first head
            obtain ⟨xs, dens, hts⟩ := AssertionTypes.inferAll_sound rest tail
            exact ⟨x :: xs, .cons den dens, .cons ht hts⟩
end


include laws in
theorem AssertionTypes.defined {expr : Expr Raw} {t} (checked : types.infer context expr = some t) :
    Expr.Defined σ context expr := by
  intro xs valid
  obtain ⟨v, den, _⟩ := AssertionTypes.infer_sound laws (ArgumentsMatch.ofValues xs valid) expr checked
  exact ⟨v, den⟩

end
end Zkc.Core.BodyAnalysis
