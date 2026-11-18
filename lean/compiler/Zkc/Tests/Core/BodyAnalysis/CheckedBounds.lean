import Zkc.Core.Facts.Contracts.StoredLaws
import Zkc.Core.Facts.Knowledge.Functions
import Zkc.Core.Facts.Body.Verdicts

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {fns : List (FnHeader V)}

private abbrev withKnowledge (cfg : Config (localDialect V fns) (LocalRaw V)) :=
  {cfg with explain := fun _ _ _ _ _ => [], domain := Knowledge.domain (localKnowledgeTypes V) (KnowledgeOperations.ofFacts (localOpFacts fns))}

private def trueAt (id : Ident) := FactCheck.Known.empty.addTruth id.key true

/-- Asking the same Boolean condition on the same table distinguishes a known upper bound,
including zero, from an unbounded natural. -/
example (cfg : Config (localDialect V fns) (LocalRaw V)) :
    clauseTruth (withKnowledge cfg) [some (.leaf 0)] (some (.arg 0)) (Values.empty localPlace)
      (trueAt (.leaf 1)) (.leaf 1) = none := by rfl'

example (cfg : Config (localDialect V fns) (LocalRaw V)) :
    clauseTruth (withKnowledge cfg) [some (.leaf 0)] (some (.arg 0)) (Values.empty localPlace)
      ((trueAt (.leaf 1)).addRange (Ident.leaf 0).key ⟨0,some 0⟩) (.leaf 1) = some true := by rfl'

example (cfg : Config (localDialect V fns) (LocalRaw V)) :
    clauseTruth (withKnowledge cfg) [some (.leaf 0)] none (Values.empty localPlace)
      (trueAt (.leaf 1)) (.leaf 1) = some true := by rfl'

/-- Success with a static demand witnesses an actual upper answer for its resolved identifier. -/
theorem clauseTruth_bound {D : Dialect} {Raw : Type} [DecidableEq Raw] {cfg : Config D Raw}
    {pos expr v k id} (ok : clauseTruth cfg pos (some expr) v k id = some true) :
    ∃ x vs state n, enterExpr cfg pos expr v k = some (x,vs,state) ∧
      (cfg.domain.answers state).upper x = some n := by
  cases truth : cfg.domain.truth Asks.nobody v.table k id with
  | none => simp [clauseTruth, truth] at ok
  | some b =>
    cases b with
    | false => simp [clauseTruth, truth] at ok
    | true =>
      cases entered : enterExpr cfg pos expr v k with
      | none => simp [clauseTruth, truth, entered] at ok
      | some found =>
        obtain ⟨x,vs,state⟩ := found
        cases bound : (cfg.domain.answers state).upper x with
        | none => simp [clauseTruth,truth,entered,bound,guard] at ok; cases ok
        | some n => exact ⟨x,vs,state,n,rfl,bound⟩

#print axioms clauseTruth_bound
end Zkc.Core.BodyAnalysis
