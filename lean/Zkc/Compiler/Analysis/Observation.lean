/-! Sound summaries of selected observations, without an exact-recovery demand.

To analyze a lowered representation, compose its summarizer with the actual
encoding. The concrete observation remains fixed. These laws require neither a
universal lattice nor an inverse of the encoding and do not erase protocol checks.
-/

namespace Zkc.Compiler.Analysis

variable {S O A B : Type}

def SummarySound (observe : S → O) (summarize : S → A) (means : A → O → Prop) : Prop :=
  ∀ source, means (summarize source) (observe source)

theorem SummarySound.use {observe : S → O} {summarize : S → A} {means : A → O → Prop}
    (sound : SummarySound observe summarize means) (source : S) (property : O → Prop)
    (established : ∀ o, means (summarize source) o → property o) : property (observe source) :=
  established _ (sound source)

theorem SummarySound.weaken {observe : S → O} {summarize : S → A} {means : A → O → Prop}
    (sound : SummarySound observe summarize means) (weaken : A → B) (coarse : B → O → Prop)
    (law : ∀ a o, means a o → coarse (weaken a) o) :
    SummarySound observe (weaken ∘ summarize) coarse :=
  fun source => law _ _ (sound source)

/-- Two summaries of the same actual observation can be combined by
conjunction of their meanings. This is not a merge of alternative entries. -/
theorem SummarySound.combine {observe : S → O} {first : S → A} {second : S → B}
    {firstMeans : A → O → Prop} {secondMeans : B → O → Prop}
    (left : SummarySound observe first firstMeans)
    (right : SummarySound observe second secondMeans) :
    SummarySound observe (fun s => (first s, second s))
      (fun summary o => firstMeans summary.1 o ∧ secondMeans summary.2 o) :=
  fun source => ⟨left source, right source⟩

end Zkc.Compiler.Analysis
