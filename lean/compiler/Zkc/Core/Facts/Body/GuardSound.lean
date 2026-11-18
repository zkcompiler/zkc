module

public import Zkc.Core.Facts.Body.StepSound

@[expose] public section

/-!
The three properties of a guard: `GuardGrowsStatement`, `GuardRunsStatement`,
`GuardSoundStatement`. A guard makes no leaf and returns no value: when its condition holds, the
rest runs from the same leaves, with the condition known true; when it does not, it stops.
-/

namespace Zkc.Core.BodyAnalysis

/-! ## A guard -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw]

/-- **A guard grows the state**: its annotations add only refusals, and it makes no leaf. -/
theorem guardGrows (cfg : Config D Raw) (notes : Annotations Raw) :
    GuardGrowsStatement cfg notes := by
  intro cursor key Γ t w c ok why ids s k wf
  simp only [walkInstr, guardStep, Instr.leafCount]
  exact Grew.of_entered cfg _ (atEntry_entered cfg notes (.instruction cursor key) ids s k wf)

variable (σ : Setting D Raw)

/-- **A guard runs its entry of the skeleton**: when its condition holds, it returns no value and
the rest runs from the same leaves; when it does not, the process stops at its occurrence. -/
theorem guardRuns : GuardRunsStatement σ := by
  intro cursor key Γ t w c ok why path ρ ids env s k table mid₀ outs rest after cont
  dsimp only
  intro scope sub notUndefined next
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k scope.wf
  have condition := scope.idOf_reads c
  rw [Instr.denote_guard] at notUndefined ⊢
  simp only [walkInstr, guardStep, Skel.stepOf] at sub next ⊢
  have read := Reads.mono (entry.1.1.trans sub) (fun _ _ h => h) condition
  cases holds : σ.sem.holds ok (env.get c) with
  | true =>
      simp only [holds, Bool.cond_true, Process.bind] at notUndefined ⊢
      exact Skel.Runs.guardHolds (env.get c) read holds
        (next ρ .nil (fun _ _ h => h)
          (fun n above => scope.fresh n (by rw [← entry.2.1]; exact above)) .nil notUndefined)
  | false =>
      simp only [Bool.cond_false, Process.bind]
      exact Skel.Runs.guardStops (env.get c) read holds

/-- **A guard is sound**: when its condition holds, it returns no value and the domain's state,
told that the condition is true, means the table and the leaves; when it does not, it stops, and
the stop of a guard is not `undefined`. -/
theorem guardSound : GuardSoundStatement σ := by
  intro laws cursor key Γ t w c ok why path ρ ids env s k
  dsimp only
  intro inv steps _ facts _ unchanged
  have entryInv := atEntry_inv σ laws cursor key (.guard w c ok why) (path := path) inv steps facts
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k inv.wf
  have condition := inv.toScope.idOf_reads c
  have truth := laws.rules.condition ok (env.get c) (Reads.valid inv.valid condition)
  rw [Instr.denote_guard]
  simp only [walkInstr, guardStep] at unchanged ⊢
  have inv₁ := entryInv unchanged
  refine ⟨?_, trivial, trivial, fun _ _ _ => trivial⟩
  cases holds : σ.sem.holds ok (env.get c) with
  | true =>
      rw [holds] at truth
      simp only [Bool.cond_true, Process.Every]
      exact ⟨ρ, fun _ _ h => h, ⟨inv₁.toScope, inv₁.valid,
        σ.domain.assume inv₁.wf.slots (Asks.nobody_sound _ _ _ _) inv₁.means
          (Reads.mono entry.1.1 (fun _ _ h => h) condition) truth⟩, .nil⟩
  | false =>
      simp only [Bool.cond_false, Process.Every]
      exact laws.rules.stop w why _

#print axioms guardGrows
#print axioms guardRuns
#print axioms guardSound

end

end Zkc.Core.BodyAnalysis
