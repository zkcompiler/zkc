module

public import Zkc.Core.Program.Term

@[expose] public section

/-!
The term in steps: an exit, or one instruction followed by the rest.

Every constructor of `Term` but the exit carries "and then the rest". The term in steps
(`Stepped.Term`) has one constructor that does, `step key i results rest`: an instruction (`i`),
the names of the values that it returns, and the rest in the context extended by them. What an
instruction is (`Stepped.Instr`) carries no continuation: an operation, a guard, a choice, a case
analysis, a loop, a block or an attempt, whose regions (the branches of a choice, the arms of a
case analysis, the body of a loop, a block or an attempt) are terms in steps. The key is on the
step: every instruction has exactly one, its address with the blocks around it. A guard returns no
value (`Stepped.Instr D Γ []`): its step binds `.nil`, and its rest is in `Γ.extend .nil`, which
reduces to `Γ`. Nothing here is per dialect; the information is that of `Term`, every field of
every constructor of `Term` being a field of the step or of the instruction.

The term in steps stands beside `Term`, which every other module uses. The translations each way
(`Term.toStepped`, `Stepped.Term.toTerm`) are inverse (`Term.toStepped_toTerm`,
`Stepped.Term.toTerm_toStepped`); back, an instruction is translated with its names and its
already translated rest (`Stepped.Instr.toTerm`). That they keep the meaning is in
`Meaning/Stepped.lean`.

A run of consecutive instructions is a unit: a prefix (`Prefix D Γ Δ`) is steps with no exit, from
the context `Γ` to the context `Δ` that their names bind. A prefix is filled with a term
(`Prefix.fill`), prefixes compose (`Prefix.append`, `Prefix.fill_append`), and a term is its first
steps filled with what follows them (`Stepped.Term.splitAt`, `Stepped.Term.fill_splitAt`).
-/

namespace Zkc.Core

namespace Stepped

mutual
  /-- A term in steps: an exit, or one instruction, the names of what it returns, and the
  rest. -/
  inductive Term (D : Dialect) : Ctx D.Ty → List D.Ty → Type where
    | ret {Γ outs} (exit : HList (Var Γ) outs) : Term D Γ outs
    | step {Γ outs mid} (key : Key) (i : Instr D Γ mid) (results : Names mid)
        (rest : Term D (Γ.extend results) outs) : Term D Γ outs
  /-- One instruction, without what follows it: what it runs, returning values of `mid`. -/
  inductive Instr (D : Dialect) : Ctx D.Ty → List D.Ty → Type where
    | op {Γ ins res} (o : D.Op ins res) (operands : HList (Var Γ) ins) : Instr D Γ res
    /-- They check a condition, and stop when it is false; it returns nothing. -/
    | guard {Γ t} (w : D.Who) (c : Var Γ t) (ok : D.Condition w t) (why : Reason) :
        Instr D Γ []
    | choose {Γ mid t} (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
        (gives : ∀ a, a ∈ mid → D.Gives w a) (onTrue onFalse : Term D Γ mid) : Instr D Γ mid
    | cases {Γ mid t payloads} (w : D.Who) (x : Var Γ t) (ok : D.Alternatives w t payloads)
        (gives : ∀ a, a ∈ mid → D.Gives w a) (arms : Arms D Γ mid payloads) : Instr D Γ mid
    /-- They repeat a region as often as `times` says. The region has the iteration number
    and the carried values; it returns the carried values and one value of each collected
    type. The loop gives the last carried values and a sequence per collected type. -/
    | loop {Γ carried each} (w : D.Who) (times : Times D w Γ)
        (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (initial : HList (Var Γ) carried)
        (inputs : Names (D.index w :: carried))
        (body : Term D (Γ.extend inputs) (carried ++ each)) :
        Instr D Γ (carried ++ each.map (D.collected times.size))
    /-- One iteration of a loop whose iterations differ in type, written out. -/
    | block {Γ mid} (number : Nat) (body : Term D Γ mid) : Instr D Γ mid
    /-- An attempt that `w` own: the body runs with the number of the attempt. -/
    | attempt {Γ mid} (w : D.Who) (owns : D.Attempt w) (inputs : Names [D.index w])
        (body : Term D (Γ.extend inputs) mid) : Instr D Γ mid
  /-- A region per alternative, each with the name of its payload. -/
  inductive Arms (D : Dialect) : Ctx D.Ty → List D.Ty → List D.Ty → Type where
    | nil {Γ mid} : Arms D Γ mid []
    | cons {Γ mid payload payloads} (inputs : Names [payload])
        (arm : Term D (Γ.extend inputs) mid) (rest : Arms D Γ mid payloads) :
        Arms D Γ mid (payload :: payloads)
end

end Stepped

section
variable {D : Dialect}

/-! ## Prefixes -/

/-- Steps without an exit, from the context `Γ` to the context `Δ` that their names bind. -/
inductive Prefix (D : Dialect) : Ctx D.Ty → Ctx D.Ty → Type where
  | nil {Γ} : Prefix D Γ Γ
  | step {Γ Δ mid} (key : Key) (i : Stepped.Instr D Γ mid) (results : Names mid)
      (rest : Prefix D (Γ.extend results) Δ) : Prefix D Γ Δ

/-- The term with a prefix before it. -/
def Prefix.fill {outs : List D.Ty} : {Γ Δ : Ctx D.Ty} → Prefix D Γ Δ → Stepped.Term D Δ outs →
    Stepped.Term D Γ outs
  | _, _, .nil, t => t
  | _, _, .step key i results rest, t => .step key i results (rest.fill t)

/-- One prefix, then another. -/
def Prefix.append : {Γ Δ Θ : Ctx D.Ty} → Prefix D Γ Δ → Prefix D Δ Θ → Prefix D Γ Θ
  | _, _, _, .nil, q => q
  | _, _, _, .step key i results rest, q => .step key i results (rest.append q)

/-- Two prefixes, one after the other, filled with a term, are the first filled with the second
filled with the term. -/
theorem Prefix.fill_append {outs : List D.Ty} {Γ Δ Θ : Ctx D.Ty} (p : Prefix D Γ Δ)
    (q : Prefix D Δ Θ) (t : Stepped.Term D Θ outs) : (p.append q).fill t = p.fill (q.fill t) := by
  induction p with
  | nil => rfl
  | step key i results rest ih => simp only [Prefix.append, Prefix.fill, ih]

/-- A term, as its first `n` steps and what follows them. With fewer steps, all of them. -/
def Stepped.Term.splitAt {outs : List D.Ty} : Nat → {Γ : Ctx D.Ty} → Stepped.Term D Γ outs →
    (Δ : Ctx D.Ty) × Prefix D Γ Δ × Stepped.Term D Δ outs
  | 0, Γ, t => ⟨Γ, .nil, t⟩
  | _ + 1, Γ, .ret exit => ⟨Γ, .nil, .ret exit⟩
  | n + 1, _, .step key i results rest =>
      let after := Stepped.Term.splitAt n rest
      ⟨after.1, .step key i results after.2.1, after.2.2⟩

/-- A term is its first steps filled with what follows them. -/
theorem Stepped.Term.fill_splitAt {outs : List D.Ty} (n : Nat) {Γ : Ctx D.Ty}
    (t : Stepped.Term D Γ outs) : (t.splitAt n).2.1.fill (t.splitAt n).2.2 = t := by
  induction n generalizing Γ with
  | zero => rfl
  | succ n ih => cases t <;> simp only [Stepped.Term.splitAt, Prefix.fill, ih]

/-! ## The translations -/

mutual
  /-- The term, in steps. -/
  def Term.toStepped : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs →
      Stepped.Term D Γ outs
    | _, _, .ret exit => .ret exit
    | _, _, .op key o operands results rest =>
        .step key (.op o operands) results (Term.toStepped rest)
    | _, _, .guard key w c ok why rest => .step key (.guard w c ok why) .nil (Term.toStepped rest)
    | _, _, .choose key w c ok gives onTrue onFalse results rest =>
        .step key (.choose w c ok gives (Term.toStepped onTrue) (Term.toStepped onFalse)) results
          (Term.toStepped rest)
    | _, _, .cases key w x ok gives arms results rest =>
        .step key (.cases w x ok gives (Arms.toStepped arms)) results (Term.toStepped rest)
    | _, _, .loop key w times gives initial inputs body results rest =>
        .step key (.loop w times gives initial inputs (Term.toStepped body)) results
          (Term.toStepped rest)
    | _, _, .block key number body results rest =>
        .step key (.block number (Term.toStepped body)) results (Term.toStepped rest)
    | _, _, .attempt key w owns inputs body results rest =>
        .step key (.attempt w owns inputs (Term.toStepped body)) results (Term.toStepped rest)
  /-- The arms of a case analysis, in steps. -/
  def Arms.toStepped : {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads →
      Stepped.Arms D Γ mid payloads
    | _, _, _, .nil => .nil
    | _, _, _, .cons inputs arm rest => .cons inputs (Term.toStepped arm) (Arms.toStepped rest)
end

mutual
  /-- The term in steps, as a term. -/
  def Stepped.Term.toTerm : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Stepped.Term D Γ outs →
      Zkc.Core.Term D Γ outs
    | _, _, .ret exit => .ret exit
    | _, _, .step key i results rest =>
        Stepped.Instr.toTerm key i results (Stepped.Term.toTerm rest)
  /-- An instruction at a key, with its names and what follows it, as a term. A guard's names
  are `.nil` by its type, so that what follows it is in its own context. -/
  def Stepped.Instr.toTerm (key : Key) : {Γ : Ctx D.Ty} → {mid outs : List D.Ty} →
      Stepped.Instr D Γ mid → (results : Names mid) → Zkc.Core.Term D (Γ.extend results) outs →
      Zkc.Core.Term D Γ outs
    | _, _, _, .op o operands, results, rest => .op key o operands results rest
    | _, _, _, .guard w c ok why, .nil, rest => .guard key w c ok why rest
    | _, _, _, .choose w c ok gives onTrue onFalse, results, rest =>
        .choose key w c ok gives (Stepped.Term.toTerm onTrue) (Stepped.Term.toTerm onFalse)
          results rest
    | _, _, _, .cases w x ok gives arms, results, rest =>
        .cases key w x ok gives (Stepped.Arms.toArms arms) results rest
    | _, _, _, .loop w times gives initial inputs body, results, rest =>
        .loop key w times gives initial inputs (Stepped.Term.toTerm body) results rest
    | _, _, _, .block number body, results, rest =>
        .block key number (Stepped.Term.toTerm body) results rest
    | _, _, _, .attempt w owns inputs body, results, rest =>
        .attempt key w owns inputs (Stepped.Term.toTerm body) results rest
  /-- The arms of a case analysis in steps, as arms. -/
  def Stepped.Arms.toArms : {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} →
      Stepped.Arms D Γ mid payloads → Zkc.Core.Arms D Γ mid payloads
    | _, _, _, .nil => .nil
    | _, _, _, .cons inputs arm rest =>
        .cons inputs (Stepped.Term.toTerm arm) (Stepped.Arms.toArms rest)
end

/-! ## Each is the inverse of the other -/

mutual
  /-- **A term in steps and back is the term.** -/
  theorem Term.toStepped_toTerm : ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs),
      t.toStepped.toTerm = t
    | _, _, .ret _ => rfl
    | _, _, .op _ _ _ _ rest => by
        simp only [Term.toStepped, Stepped.Term.toTerm, Stepped.Instr.toTerm,
          Term.toStepped_toTerm rest]
    | _, _, .guard key w c ok why rest =>
        -- The rest of the step is in `Γ.extend .nil`, which `rw` does not see through.
        congrArg (Term.guard key w c ok why) (Term.toStepped_toTerm rest)
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest => by
        simp only [Term.toStepped, Stepped.Term.toTerm, Stepped.Instr.toTerm,
          Term.toStepped_toTerm onTrue, Term.toStepped_toTerm onFalse, Term.toStepped_toTerm rest]
    | _, _, .cases _ _ _ _ _ arms _ rest => by
        simp only [Term.toStepped, Stepped.Term.toTerm, Stepped.Instr.toTerm,
          Arms.toStepped_toArms arms, Term.toStepped_toTerm rest]
    | _, _, .loop _ _ _ _ _ _ body _ rest => by
        simp only [Term.toStepped, Stepped.Term.toTerm, Stepped.Instr.toTerm,
          Term.toStepped_toTerm body, Term.toStepped_toTerm rest]
    | _, _, .block _ _ body _ rest => by
        simp only [Term.toStepped, Stepped.Term.toTerm, Stepped.Instr.toTerm,
          Term.toStepped_toTerm body, Term.toStepped_toTerm rest]
    | _, _, .attempt _ _ _ _ body _ rest => by
        simp only [Term.toStepped, Stepped.Term.toTerm, Stepped.Instr.toTerm,
          Term.toStepped_toTerm body, Term.toStepped_toTerm rest]
  /-- Arms in steps and back are the arms. -/
  theorem Arms.toStepped_toArms : ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
      (arms : Arms D Γ mid payloads), arms.toStepped.toArms = arms
    | _, _, _, .nil => rfl
    | _, _, _, .cons _ arm rest => by
        simp only [Arms.toStepped, Stepped.Arms.toArms, Term.toStepped_toTerm arm,
          Arms.toStepped_toArms rest]
end

mutual
  /-- **A term in steps, as a term and back in steps, is the term in steps.** -/
  theorem Stepped.Term.toTerm_toStepped : ∀ {Γ : Ctx D.Ty} {outs : List D.Ty}
      (t : Stepped.Term D Γ outs), t.toTerm.toStepped = t
    | _, _, .ret _ => rfl
    | _, _, .step key i results rest => by
        simp only [Stepped.Term.toTerm, Stepped.Instr.toTerm_toStepped key i results,
          Stepped.Term.toTerm_toStepped rest]
  /-- An instruction as a term with any rest, back in steps, is the step of the instruction with
  the rest in steps. -/
  theorem Stepped.Instr.toTerm_toStepped (key : Key) : ∀ {Γ : Ctx D.Ty} {mid outs : List D.Ty}
      (i : Stepped.Instr D Γ mid) (results : Names mid)
      (rest : Zkc.Core.Term D (Γ.extend results) outs),
      (Stepped.Instr.toTerm key i results rest).toStepped = .step key i results rest.toStepped
    | _, _, _, .op _ _, _, _ => rfl
    | _, _, _, .guard _ _ _ _, .nil, _ => rfl
    | _, _, _, .choose _ _ _ _ onTrue onFalse, _, _ => by
        simp only [Stepped.Instr.toTerm, Term.toStepped, Stepped.Term.toTerm_toStepped onTrue,
          Stepped.Term.toTerm_toStepped onFalse]
    | _, _, _, .cases _ _ _ _ arms, _, _ => by
        simp only [Stepped.Instr.toTerm, Term.toStepped, Stepped.Arms.toArms_toStepped arms]
    | _, _, _, .loop _ _ _ _ _ body, _, _ => by
        simp only [Stepped.Instr.toTerm, Term.toStepped, Stepped.Term.toTerm_toStepped body]
    | _, _, _, .block _ body, _, _ => by
        simp only [Stepped.Instr.toTerm, Term.toStepped, Stepped.Term.toTerm_toStepped body]
    | _, _, _, .attempt _ _ _ body, _, _ => by
        simp only [Stepped.Instr.toTerm, Term.toStepped, Stepped.Term.toTerm_toStepped body]
  /-- Arms in steps, as arms and back in steps, are the arms in steps. -/
  theorem Stepped.Arms.toArms_toStepped : ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
      (arms : Stepped.Arms D Γ mid payloads), arms.toArms.toStepped = arms
    | _, _, _, .nil => rfl
    | _, _, _, .cons _ arm rest => by
        simp only [Stepped.Arms.toArms, Arms.toStepped, Stepped.Term.toTerm_toStepped arm,
          Stepped.Arms.toArms_toStepped rest]
end

end

end Zkc.Core
