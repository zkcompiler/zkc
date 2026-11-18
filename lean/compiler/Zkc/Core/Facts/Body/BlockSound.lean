module

public import Zkc.Core.Facts.Body.CasesSound

@[expose] public section

/-!
The three properties of a block from those of its body: `BlockGrowsStatement`,
`BlockRunsStatement`, `BlockSoundStatement`. A block has no leaf of its own: what it returns is what
its body returns, and its body runs under its frame, followed by the block's rest.
-/

namespace Zkc.Core.BodyAnalysis

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw) (notes : Annotations Raw)

/-- **A block grows the state when its body does**, by its body's leaves, adding bounds at its
body's addresses. -/
theorem blockGrows : BlockGrowsStatement cfg notes := by
  intro cursor key Γ mid number body growsBody ids s k wf
  have entry := atEntry_entered cfg notes (.block cursor key number) ids s k wf
  simp only [walkInstr, Instr.leafCount, Instr.addresses]
  exact ((Grew.of_entered cfg _ entry).trans
    (Grew.discount (atEntry cfg notes (.block cursor key number) ids s k).2
      (growsBody ids _ (atEntry cfg notes (.block cursor key number) ids s k).2 entry.wf))).count (Nat.zero_add _)

end

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

/-- **A block runs its entry of the skeleton when its body runs its skeleton**: the body runs under
the block's frame, followed by the block's rest under the path outside it, from the leaves at the
body's exit. -/
theorem blockRuns : BlockRunsStatement σ := by
  intro cursor key Γ mid number body runsBody
  intro path ρ ids env s k table mid₀ outs rest after cont
  dsimp only
  intro scope sub notUndefined next
  have entry := atEntry_entered σ.cfg σ.notes (.block cursor key number) ids s k scope.wf
  rw [Instr.denote_block] at notUndefined ⊢
  simp only [walkInstr, Skel.stepOf, discount_values, discount_leaves] at sub next ⊢
  exact Skel.Runs.block (runsBody (path ++ [.iteration key number]) ρ ids env
    (atEntry σ.cfg σ.notes (.block cursor key number) ids s k).1 (atEntry σ.cfg σ.notes (.block cursor key number) ids s k).2 table
    (.cons path rest after) cont (scope.grow entry.1 (Nat.le_of_eq entry.2.1.symm)) sub notUndefined
    fun ρ' values le fresh reads undefined => .resume (next ρ' values le fresh reads undefined))

/-- **A block is sound when its body is**, under the block's frame: the state at the body's entry
means the leaves, so it is not dead and the body's refusals count; what the block returns is what
its body returns. -/
theorem blockSound : BlockSoundStatement σ := by
  intro laws cursor key Γ mid number body growsBody soundBody
  intro path ρ ids env s k
  dsimp only
  intro inv steps defined facts everyFact unchanged
  have entry := atEntry_entered σ.cfg σ.notes (.block cursor key number) ids s k inv.wf
  have entryInv := fun unchanged => atEntry_inv σ laws cursor key (.block number body)
    (path := path) inv steps facts unchanged
  rw [Instr.denote_block]
  simp only [walkInstr, Instr.addresses] at unchanged ⊢
  simp only [Instr.site] at entryInv
  generalize atEntry σ.cfg σ.notes (.block cursor key number) ids s k = e at entry entryInv unchanged ⊢
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry entryInv unchanged ⊢
  have bodyGrew := growsBody ids E Ek entry.wf
  have soundB := soundBody (path ++ [.iteration key number]) ρ ids env E Ek
  generalize walk σ.cfg σ.notes (cursor.block key number) body ids E Ek = inner
    at bodyGrew soundB unchanged ⊢
  obtain ⟨entryUnchanged, -⟩ :=
    refusals_split entry.2.2.2 (Grew.discount Ek bodyGrew).2.2.2.2.1 unchanged
  have inv₁ := entryInv entryUnchanged
  rw [discount_alive (σ.alive inv₁.means)] at unchanged ⊢
  obtain ⟨-, innerUnchanged⟩ := refusals_split entry.2.2.2 bodyGrew.2.2.2.2.1 unchanged
  simp only [Instr.EveryFact, Instr.EveryStep] at everyFact
  obtain ⟨every, required, loops⟩ := soundB inv₁ defined everyFact innerUnchanged
  simp only [Instr.EveryRequired, Instr.EveryStep, Instr.EveryLoop]
  refine ⟨every, trivial, required, fun nodup apart recorded => loops nodup ?_ recorded⟩
  rw [BoundsApart, entry.2.2.1]
  exact apart

#print axioms blockGrows
#print axioms blockRuns
#print axioms blockSound

end

end Zkc.Core.BodyAnalysis
