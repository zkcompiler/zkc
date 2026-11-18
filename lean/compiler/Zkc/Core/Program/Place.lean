module

public import Zkc.Core.Program.Erase
public import Zkc.Core.Program.Stepped

@[expose] public section

/-!
Places inside a term, as terms.

The one structural rule on contexts, for terms: a term in a context is a term in every context
that has at least the same names at the same types (`Term.reindex`), with its names, keys and
operations unchanged, so that its erased form is the same (`eraseBody_reindex`). Weakening,
exchanging two bindings and inserting a binding with a fresh name are this rule.

A term with one place left open (`Hole`): the place is after some instructions, or inside a
region of an instruction, at any depth. `Hole.fill` puts a term there; a term is its first
instructions with what follows them left open, filled with what follows them
(`Term.splitAt`, `Term.fill_splitAt`).

The names that a term reads from its context (`Term.reads`): those it uses that it does not bind
itself.

What a run does at a place, and that terms with the same meaning there may replace each other,
is in `Meaning/Place.lean`.
-/

namespace Zkc.Core

section
variable {D : Dialect}

/-! ## The structural rule on contexts -/

/-- How often a loop runs, in a context that has the count. -/
def Times.reindex {w : D.Who} {Γ Δ : Ctx D.Ty} (keeps : Γ.Within Δ) : Times D w Γ → Times D w Δ
  | .fixed n => .fixed n
  | .value count ok => .value (count.reindex keeps) ok

mutual
  /-- A term, in a context that has at least the names of its own at the same types. Its names,
  keys and operations are unchanged. -/
  def Term.reindex : {Γ Δ : Ctx D.Ty} → {outs : List D.Ty} → Γ.Within Δ → Term D Γ outs →
      Term D Δ outs
    | _, _, _, keeps, .ret exit => .ret (HList.reindex keeps exit)
    | _, _, _, keeps, .step key i results rest =>
        .step key (i.reindex keeps) results (rest.reindex (keeps.extend results))
  def Instr.reindex : {Γ Δ : Ctx D.Ty} → {mid : List D.Ty} → Γ.Within Δ → Instr D Γ mid →
      Instr D Δ mid
    | _, _, _, keeps, .op o operands => .op o (HList.reindex keeps operands)
    | _, _, _, keeps, .guard w c ok why => .guard w (c.reindex keeps) ok why
    | _, _, _, keeps, .choose w c ok gives onTrue onFalse =>
        .choose w (c.reindex keeps) ok gives (onTrue.reindex keeps) (onFalse.reindex keeps)
    | _, _, _, keeps, .cases w x ok gives arms => .cases w (x.reindex keeps) ok gives (arms.reindex keeps)
    | _, _, _, keeps, .loop w (.fixed n) gives initial inputs body =>
        .loop w (.fixed n) gives (HList.reindex keeps initial) inputs (body.reindex (keeps.extend inputs))
    | _, _, _, keeps, .loop w (.value count ok) gives initial inputs body =>
        .loop w (.value (count.reindex keeps) ok) gives (HList.reindex keeps initial) inputs
          (body.reindex (keeps.extend inputs))
    | _, _, _, keeps, .block number body => .block number (body.reindex keeps)
    | _, _, _, keeps, .attempt w owns inputs body => .attempt w owns inputs (body.reindex (keeps.extend inputs))
  /-- The arms of a case analysis, in a context that has at least the names of their own. -/
  def Arms.reindex : {Γ Δ : Ctx D.Ty} → {mid payloads : List D.Ty} → Γ.Within Δ →
      Arms D Γ mid payloads → Arms D Δ mid payloads
    | _, _, _, _, _, .nil => .nil
    | _, _, _, _, keeps, .cons inputs arm rest =>
        .cons inputs (arm.reindex (keeps.extend inputs)) (rest.reindex keeps)
end

/-- The size of a loop does not depend on the context of its count. -/
theorem Times.size_reindex {w : D.Who} {Γ Δ : Ctx D.Ty} (keeps : Γ.Within Δ) (times : Times D w Γ) :
    (times.reindex keeps).size = times.size := by
  cases times <;> rfl

/-- How often a loop runs, in a wider context, erases to the same names. -/
theorem eraseTimes_reindex {w : D.Who} {Γ Δ : Ctx D.Ty} (keeps : Γ.Within Δ) :
    ∀ times : Times D w Γ, eraseTimes (times.reindex keeps) = eraseTimes times
  | .fixed _ => rfl
  | .value _ _ => rfl

mutual
  /-- A term in a wider context erases to the same program by names. -/
  theorem eraseBody_reindex {Raw Who : Type}
      (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who) :
      ∀ {Γ Δ : Ctx D.Ty} {outs : List D.Ty} (keeps : Γ.Within Δ) (t : Term D Γ outs),
        eraseBody printOp printWho (t.reindex keeps) = eraseBody printOp printWho t
    | _, _, _, keeps, .ret exit => by
        simp only [Term.reindex, eraseBody, HList.names_reindex]
    | _, _, _, keeps, .step key i results rest => by
        simp only [Term.reindex, eraseBody, eraseInstr_reindex printOp printWho keeps key i results,
          eraseBody_reindex printOp printWho (keeps.extend results) rest]
  theorem eraseInstr_reindex {Raw Who : Type}
      (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who) :
      ∀ {Γ Δ : Ctx D.Ty} {mid : List D.Ty} (keeps : Γ.Within Δ) (key : Key) (i : Instr D Γ mid)
        (results : Names mid), eraseInstr printOp printWho key (i.reindex keeps) results =
          eraseInstr printOp printWho key i results
    | _, _, _, keeps, _, .op o args, _ => by simp only [Instr.reindex, eraseInstr, HList.names_reindex]
    | _, _, _, _, _, .guard .., _ => rfl
    | _, _, _, keeps, _, .choose _ _ _ _ t f, _ => by
        simp only [Instr.reindex, eraseInstr, Var.reindex, eraseBody_reindex printOp printWho keeps t,
          eraseBody_reindex printOp printWho keeps f]
    | _, _, _, keeps, _, .cases _ _ _ _ arms, _ => by
        simp only [Instr.reindex, eraseInstr, Var.reindex, eraseArms_reindex printOp printWho keeps arms]
    | _, _, _, keeps, _, .loop _ (.fixed _) _ _ inputs body, _ => by
        simp only [Instr.reindex, eraseInstr, HList.names_reindex,
          eraseBody_reindex printOp printWho (keeps.extend inputs) body]
        rfl
    | _, _, _, keeps, _, .loop _ (.value ..) _ _ inputs body, _ => by
        simp only [Instr.reindex, eraseInstr, HList.names_reindex, eraseTimes, Var.reindex,
          eraseBody_reindex printOp printWho (keeps.extend inputs) body]
        rfl
    | _, _, _, keeps, _, .block _ body, _ => by
        simp only [Instr.reindex, eraseInstr, eraseBody_reindex printOp printWho keeps body]
    | _, _, _, keeps, _, .attempt _ _ inputs body, _ => by
        simp only [Instr.reindex, eraseInstr, eraseBody_reindex printOp printWho (keeps.extend inputs) body]
  /-- The arms of a case analysis in a wider context erase to the same regions by names. -/
  theorem eraseArms_reindex {Raw Who : Type}
      (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who) :
      ∀ {Γ Δ : Ctx D.Ty} {mid payloads : List D.Ty} (keeps : Γ.Within Δ)
        (arms : Arms D Γ mid payloads),
        eraseArms printOp printWho (arms.reindex keeps) = eraseArms printOp printWho arms
    | _, _, _, _, _, .nil => rfl
    | _, _, _, _, keeps, .cons inputs arm rest => by
        simp only [Arms.reindex, eraseArms,
          eraseBody_reindex printOp printWho (keeps.extend inputs) arm,
          eraseArms_reindex printOp printWho keeps rest]
end

/-! ## A term with one place left open -/

mutual
  /-- A term in the context `Γ` giving `outs`, with one place left open for a term in the
  context `Δ` giving `mid`. The place is what follows some instructions (`here` after the
  constructors that pass an instruction), or inside a region of an instruction. -/
  inductive Hole (D : Dialect) : Ctx D.Ty → List D.Ty → Ctx D.Ty → List D.Ty → Type where
    /-- The place itself. -/
    | here {Γ outs} : Hole D Γ outs Γ outs
    /-- After an instruction returns and binds its results. -/
    | step {Γ outs Δ mid inner} (key : Key) (i : Instr D Γ inner) (results : Names inner)
        (rest : Hole D (Γ.extend results) outs Δ mid) : Hole D Γ outs Δ mid
    /-- Inside the region of a choice that runs when its condition holds. -/
    | inTrue {Γ outs Δ mid inner t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
        (gives : ∀ a, a ∈ inner → D.Gives w a) (onTrue : Hole D Γ inner Δ mid)
        (onFalse : Term D Γ inner) (results : Names inner)
        (rest : Term D (Γ.extend results) outs) : Hole D Γ outs Δ mid
    /-- Inside the region of a choice that runs when its condition does not hold. -/
    | inFalse {Γ outs Δ mid inner t} (key : Key) (w : D.Who) (c : Var Γ t)
        (ok : D.Condition w t) (gives : ∀ a, a ∈ inner → D.Gives w a) (onTrue : Term D Γ inner)
        (onFalse : Hole D Γ inner Δ mid) (results : Names inner)
        (rest : Term D (Γ.extend results) outs) : Hole D Γ outs Δ mid
    /-- Inside an arm of a case analysis. -/
    | inArm {Γ outs Δ mid inner t payloads} (key : Key) (w : D.Who) (x : Var Γ t)
        (ok : D.Alternatives w t payloads) (gives : ∀ a, a ∈ inner → D.Gives w a)
        (arms : ArmsHole D Γ inner payloads Δ mid) (results : Names inner)
        (rest : Term D (Γ.extend results) outs) : Hole D Γ outs Δ mid
    /-- Inside the body of a loop. -/
    | inLoop {Γ outs Δ mid carried each} (key : Key) (w : D.Who) (times : Times D w Γ)
        (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (initial : HList (Var Γ) carried)
        (inputs : Names (D.index w :: carried))
        (body : Hole D (Γ.extend inputs) (carried ++ each) Δ mid)
        (results : Names (carried ++ each.map (D.collected times.size)))
        (rest : Term D (Γ.extend results) outs) : Hole D Γ outs Δ mid
    /-- Inside the body of a block. -/
    | inBlock {Γ outs Δ mid inner} (key : Key) (number : Nat) (body : Hole D Γ inner Δ mid)
        (results : Names inner) (rest : Term D (Γ.extend results) outs) : Hole D Γ outs Δ mid
    /-- Inside the body of an attempt. -/
    | inAttempt {Γ outs Δ mid inner} (key : Key) (w : D.Who) (owns : D.Attempt w)
        (inputs : Names [D.index w]) (body : Hole D (Γ.extend inputs) inner Δ mid)
        (results : Names inner) (rest : Term D (Γ.extend results) outs) : Hole D Γ outs Δ mid
  /-- The arms of a case analysis with one place left open in one of them. -/
  inductive ArmsHole (D : Dialect) :
      Ctx D.Ty → List D.Ty → List D.Ty → Ctx D.Ty → List D.Ty → Type where
    /-- In the first arm. -/
    | first {Γ inner payload payloads Δ mid} (inputs : Names [payload])
        (arm : Hole D (Γ.extend inputs) inner Δ mid) (rest : Arms D Γ inner payloads) :
        ArmsHole D Γ inner (payload :: payloads) Δ mid
    /-- In a later arm. -/
    | later {Γ inner payload payloads Δ mid} (inputs : Names [payload])
        (arm : Term D (Γ.extend inputs) inner) (rest : ArmsHole D Γ inner payloads Δ mid) :
        ArmsHole D Γ inner (payload :: payloads) Δ mid
end

mutual
  /-- The term with another term at its open place. -/
  def Hole.fill : {Γ : Ctx D.Ty} → {outs : List D.Ty} → {Δ : Ctx D.Ty} → {mid : List D.Ty} →
      Hole D Γ outs Δ mid → Term D Δ mid → Term D Γ outs
    | _, _, _, _, .here, t => t
    | _, _, _, _, .step key i results rest, t => .step key i results (rest.fill t)
    | _, _, _, _, .inTrue key w c ok gives onTrue onFalse results rest, t =>
        .choose key w c ok gives (onTrue.fill t) onFalse results rest
    | _, _, _, _, .inFalse key w c ok gives onTrue onFalse results rest, t =>
        .choose key w c ok gives onTrue (onFalse.fill t) results rest
    | _, _, _, _, .inArm key w x ok gives arms results rest, t =>
        .cases key w x ok gives (arms.fill t) results rest
    | _, _, _, _, .inLoop key w times gives initial inputs body results rest, t =>
        .loop key w times gives initial inputs (body.fill t) results rest
    | _, _, _, _, .inBlock key number body results rest, t =>
        .block key number (body.fill t) results rest
    | _, _, _, _, .inAttempt key w owns inputs body results rest, t =>
        .attempt key w owns inputs (body.fill t) results rest
  /-- The arms with a term at their open place. -/
  def ArmsHole.fill : {Γ : Ctx D.Ty} → {inner payloads : List D.Ty} → {Δ : Ctx D.Ty} →
      {mid : List D.Ty} → ArmsHole D Γ inner payloads Δ mid → Term D Δ mid →
      Arms D Γ inner payloads
    | _, _, _, _, _, .first inputs arm rest, t => .cons inputs (arm.fill t) rest
    | _, _, _, _, _, .later inputs arm rest, t => .cons inputs arm (rest.fill t)
end

/-! ## What follows some instructions -/

/-- The place immediately following a prefix. -/
def Prefix.hole {outs : List D.Ty} : {Γ Δ : Ctx D.Ty} → Prefix D Γ Δ → Hole D Γ outs Δ outs
  | _, _, .nil => .here
  | _, _, .step key i results rest => .step key i results rest.hole

theorem Prefix.fill_hole {Γ Δ : Ctx D.Ty} {outs : List D.Ty} (p : Prefix D Γ Δ)
    (t : Term D Δ outs) : p.hole.fill t = p.fill t := by
  induction p with
  | nil => rfl
  | step key i results rest ih => exact congrArg (Term.step key i results) (ih t)

/-- Split at the place after the first `n` instructions, or at the exit. -/
def Term.splitAt (n : Nat) {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) :
    (Δ : Ctx D.Ty) × Hole D Γ outs Δ outs × Term D Δ outs :=
  let after := t.splitPrefix n
  ⟨after.1, after.2.1.hole, after.2.2⟩

theorem Term.fill_splitAt (n : Nat) {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) :
    (t.splitAt n).2.1.fill (t.splitAt n).2.2 = t :=
  (Prefix.fill_hole _ _).trans (Term.fill_splitPrefix n t)

/-! ## The names that a term reads -/

/-- The name that a loop reads to know how often it runs, if any. -/
def Times.reads {w : D.Who} {Γ : Ctx D.Ty} : Times D w Γ → List Name
  | .fixed _ => []
  | .value count _ => [count.name]

mutual
  /-- The names that a term reads from its context: those it uses that it does not bind itself.
  A region of an instruction captures the names that it reads. -/
  def Term.reads : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List Name
    | _, _, .ret exit => HList.names exit
    | _, _, .op _ _ operands results rest =>
        HList.names operands ++ results.unbound (Term.reads rest)
    | _, _, .guard _ _ c _ _ rest => c.name :: Term.reads rest
    | _, _, .choose _ _ c _ _ onTrue onFalse results rest =>
        c.name :: (Term.reads onTrue ++ (Term.reads onFalse ++ results.unbound (Term.reads rest)))
    | _, _, .cases _ _ x _ _ arms results rest =>
        x.name :: (Arms.reads arms ++ results.unbound (Term.reads rest))
    | _, _, .loop _ _ times _ initial inputs body results rest =>
        times.reads ++ (HList.names initial ++
          (inputs.unbound (Term.reads body) ++ results.unbound (Term.reads rest)))
    | _, _, .block _ _ body results rest =>
        Term.reads body ++ results.unbound (Term.reads rest)
    | _, _, .attempt _ _ _ inputs body results rest =>
        inputs.unbound (Term.reads body) ++ results.unbound (Term.reads rest)
  /-- The names that the arms of a case analysis read from the context around them. -/
  def Arms.reads : {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads →
      List Name
    | _, _, _, .nil => []
    | _, _, _, .cons inputs arm rest => inputs.unbound (Term.reads arm) ++ Arms.reads rest
end

end

end Zkc.Core
