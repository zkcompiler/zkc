module

public import Zkc.Core.Program.Term

@[expose] public section

/-! Typed instruction prefixes, their composition and splitting. -/

namespace Zkc.Core

section
variable {D : Dialect}

/-! ## Prefixes -/

/-- Steps without an exit, from the context `Γ` to the context `Δ` that their names bind. -/
inductive Prefix (D : Dialect) : Ctx D.Ty → Ctx D.Ty → Type where
  | nil {Γ} : Prefix D Γ Γ
  | step {Γ Δ mid} (key : Key) (i : Instr D Γ mid) (results : Names mid)
      (rest : Prefix D (Γ.extend results) Δ) : Prefix D Γ Δ

/-- The term with a prefix before it. -/
def Prefix.fill {outs : List D.Ty} : {Γ Δ : Ctx D.Ty} → Prefix D Γ Δ → Term D Δ outs →
    Term D Γ outs
  | _, _, .nil, t => t
  | _, _, .step key i results rest, t => .step key i results (rest.fill t)

/-- One prefix, then another. -/
def Prefix.append : {Γ Δ Θ : Ctx D.Ty} → Prefix D Γ Δ → Prefix D Δ Θ → Prefix D Γ Θ
  | _, _, _, .nil, q => q
  | _, _, _, .step key i results rest, q => .step key i results (rest.append q)

/-- Two prefixes, one after the other, filled with a term, are the first filled with the second
filled with the term. -/
theorem Prefix.fill_append {outs : List D.Ty} {Γ Δ Θ : Ctx D.Ty} (p : Prefix D Γ Δ)
    (q : Prefix D Δ Θ) (t : Term D Θ outs) : (p.append q).fill t = p.fill (q.fill t) := by
  induction p with
  | nil => rfl
  | step key i results rest ih => simp only [Prefix.append, Prefix.fill, ih]

/-- A term, as its first `n` steps and what follows them. With fewer steps, all of them. -/
def Term.splitPrefix {outs : List D.Ty} : Nat → {Γ : Ctx D.Ty} → Term D Γ outs →
    (Δ : Ctx D.Ty) × Prefix D Γ Δ × Term D Δ outs
  | 0, Γ, t => ⟨Γ, .nil, t⟩
  | _ + 1, Γ, .ret exit => ⟨Γ, .nil, .ret exit⟩
  | n + 1, _, .step key i results rest =>
      let after := Term.splitPrefix n rest
      ⟨after.1, .step key i results after.2.1, after.2.2⟩

/-- A term is its first steps filled with what follows them. -/
theorem Term.fill_splitPrefix {outs : List D.Ty} (n : Nat) {Γ : Ctx D.Ty}
    (t : Term D Γ outs) : (t.splitPrefix n).2.1.fill (t.splitPrefix n).2.2 = t := by
  induction n generalizing Γ with
  | zero => rfl
  | succ n ih => cases t <;> simp only [Term.splitPrefix, Prefix.fill, ih]

end

end Zkc.Core
