module

public import Zkc.Core.Program.Erase

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
    | _, _, _, keeps, .op key o operands results rest =>
        .op key o (HList.reindex keeps operands) results (rest.reindex (keeps.extend results))
    | _, _, _, keeps, .guard key w c ok why rest =>
        .guard key w (c.reindex keeps) ok why (rest.reindex keeps)
    | _, _, _, keeps, .choose key w c ok gives onTrue onFalse results rest =>
        .choose key w (c.reindex keeps) ok gives (onTrue.reindex keeps) (onFalse.reindex keeps)
          results (rest.reindex (keeps.extend results))
    | _, _, _, keeps, .cases key w x ok gives arms results rest =>
        .cases key w (x.reindex keeps) ok gives (arms.reindex keeps) results
          (rest.reindex (keeps.extend results))
    | _, _, _, keeps, .loop key w (.fixed n) gives initial inputs body results rest =>
        .loop key w (.fixed n) gives (HList.reindex keeps initial) inputs
          (body.reindex (keeps.extend inputs)) results (rest.reindex (keeps.extend results))
    | _, _, _, keeps, .loop key w (.value count ok) gives initial inputs body results rest =>
        .loop key w (.value (count.reindex keeps) ok) gives (HList.reindex keeps initial) inputs
          (body.reindex (keeps.extend inputs)) results (rest.reindex (keeps.extend results))
    | _, _, _, keeps, .block key number body results rest =>
        .block key number (body.reindex keeps) results (rest.reindex (keeps.extend results))
    | _, _, _, keeps, .attempt key w owns inputs body results rest =>
        .attempt key w owns inputs (body.reindex (keeps.extend inputs)) results
          (rest.reindex (keeps.extend results))
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
    | _, _, _, keeps, .op key o operands results rest => by
        simp only [Term.reindex, eraseBody, HList.names_reindex,
          eraseBody_reindex printOp printWho (keeps.extend results) rest]
    | _, _, _, keeps, .guard key w c ok why rest => by
        simp only [Term.reindex, eraseBody, Var.reindex,
          eraseBody_reindex printOp printWho keeps rest]
    | _, _, _, keeps, .choose key w c ok gives onTrue onFalse results rest => by
        simp only [Term.reindex, eraseBody, Var.reindex,
          eraseBody_reindex printOp printWho keeps onTrue,
          eraseBody_reindex printOp printWho keeps onFalse,
          eraseBody_reindex printOp printWho (keeps.extend results) rest]
    | _, _, _, keeps, .cases key w x ok gives arms results rest => by
        simp only [Term.reindex, eraseBody, Var.reindex,
          eraseArms_reindex printOp printWho keeps arms,
          eraseBody_reindex printOp printWho (keeps.extend results) rest]
    | _, _, _, keeps, .loop key w (.fixed n) gives initial inputs body results rest => by
        -- The context of the reindexed `rest` names the size of the loop at the wider context,
        -- equal to it only by unfolding `Times.size`, so this rewrite is up to unfolding.
        simp only [Term.reindex, eraseBody, HList.names_reindex,
          eraseBody_reindex printOp printWho (keeps.extend inputs) body]
        erw [eraseBody_reindex printOp printWho (keeps.extend results) rest]
        rfl
    | _, _, _, keeps, .loop key w (.value count ok) gives initial inputs body results rest => by
        simp only [Term.reindex, eraseBody, HList.names_reindex, eraseTimes, Var.reindex,
          eraseBody_reindex printOp printWho (keeps.extend inputs) body]
        erw [eraseBody_reindex printOp printWho (keeps.extend results) rest]
        rfl
    | _, _, _, keeps, .block key number body results rest => by
        simp only [Term.reindex, eraseBody,
          eraseBody_reindex printOp printWho keeps body,
          eraseBody_reindex printOp printWho (keeps.extend results) rest]
    | _, _, _, keeps, .attempt key w owns inputs body results rest => by
        simp only [Term.reindex, eraseBody,
          eraseBody_reindex printOp printWho (keeps.extend inputs) body,
          eraseBody_reindex printOp printWho (keeps.extend results) rest]
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
    /-- After an operation. -/
    | op {Γ outs Δ mid ins res} (key : Key) (o : D.Op ins res) (operands : HList (Var Γ) ins)
        (results : Names res) (rest : Hole D (Γ.extend results) outs Δ mid) : Hole D Γ outs Δ mid
    /-- After a guard. -/
    | guard {Γ outs Δ mid t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
        (why : Reason) (rest : Hole D Γ outs Δ mid) : Hole D Γ outs Δ mid
    /-- After a choice. -/
    | choose {Γ outs Δ mid inner t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
        (gives : ∀ a, a ∈ inner → D.Gives w a) (onTrue onFalse : Term D Γ inner)
        (results : Names inner) (rest : Hole D (Γ.extend results) outs Δ mid) :
        Hole D Γ outs Δ mid
    /-- After a case analysis. -/
    | cases {Γ outs Δ mid inner t payloads} (key : Key) (w : D.Who) (x : Var Γ t)
        (ok : D.Alternatives w t payloads) (gives : ∀ a, a ∈ inner → D.Gives w a)
        (arms : Arms D Γ inner payloads) (results : Names inner)
        (rest : Hole D (Γ.extend results) outs Δ mid) : Hole D Γ outs Δ mid
    /-- After a loop. -/
    | loop {Γ outs Δ mid carried each} (key : Key) (w : D.Who) (times : Times D w Γ)
        (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (initial : HList (Var Γ) carried)
        (inputs : Names (D.index w :: carried))
        (body : Term D (Γ.extend inputs) (carried ++ each))
        (results : Names (carried ++ each.map (D.collected times.size)))
        (rest : Hole D (Γ.extend results) outs Δ mid) : Hole D Γ outs Δ mid
    /-- After a block. -/
    | block {Γ outs Δ mid inner} (key : Key) (number : Nat) (body : Term D Γ inner)
        (results : Names inner) (rest : Hole D (Γ.extend results) outs Δ mid) :
        Hole D Γ outs Δ mid
    /-- After an attempt. -/
    | attempt {Γ outs Δ mid inner} (key : Key) (w : D.Who) (owns : D.Attempt w)
        (inputs : Names [D.index w]) (body : Term D (Γ.extend inputs) inner)
        (results : Names inner) (rest : Hole D (Γ.extend results) outs Δ mid) :
        Hole D Γ outs Δ mid
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
    | _, _, _, _, .op key o operands results rest, t => .op key o operands results (rest.fill t)
    | _, _, _, _, .guard key w c ok why rest, t => .guard key w c ok why (rest.fill t)
    | _, _, _, _, .choose key w c ok gives onTrue onFalse results rest, t =>
        .choose key w c ok gives onTrue onFalse results (rest.fill t)
    | _, _, _, _, .cases key w x ok gives arms results rest, t =>
        .cases key w x ok gives arms results (rest.fill t)
    | _, _, _, _, .loop key w times gives initial inputs body results rest, t =>
        .loop key w times gives initial inputs body results (rest.fill t)
    | _, _, _, _, .block key number body results rest, t =>
        .block key number body results (rest.fill t)
    | _, _, _, _, .attempt key w owns inputs body results rest, t =>
        .attempt key w owns inputs body results (rest.fill t)
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

/-- A term, as its first `n` instructions with what follows them left open, and what follows
them. With fewer instructions, all of them. -/
def Term.splitAt : (n : Nat) → {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs →
    (Δ : Ctx D.Ty) × Hole D Γ outs Δ outs × Term D Δ outs
  | 0, Γ, _, t => ⟨Γ, .here, t⟩
  | _ + 1, Γ, _, .ret exit => ⟨Γ, .here, .ret exit⟩
  | n + 1, _, _, .op key o operands results rest =>
      let after := Term.splitAt n rest
      ⟨after.1, .op key o operands results after.2.1, after.2.2⟩
  | n + 1, _, _, .guard key w c ok why rest =>
      let after := Term.splitAt n rest
      ⟨after.1, .guard key w c ok why after.2.1, after.2.2⟩
  | n + 1, _, _, .choose key w c ok gives onTrue onFalse results rest =>
      let after := Term.splitAt n rest
      ⟨after.1, .choose key w c ok gives onTrue onFalse results after.2.1, after.2.2⟩
  | n + 1, _, _, .cases key w x ok gives arms results rest =>
      let after := Term.splitAt n rest
      ⟨after.1, .cases key w x ok gives arms results after.2.1, after.2.2⟩
  | n + 1, _, _, .loop key w times gives initial inputs body results rest =>
      let after := Term.splitAt n rest
      ⟨after.1, .loop key w times gives initial inputs body results after.2.1, after.2.2⟩
  | n + 1, _, _, .block key number body results rest =>
      let after := Term.splitAt n rest
      ⟨after.1, .block key number body results after.2.1, after.2.2⟩
  | n + 1, _, _, .attempt key w owns inputs body results rest =>
      let after := Term.splitAt n rest
      ⟨after.1, .attempt key w owns inputs body results after.2.1, after.2.2⟩

/-- A term is its first instructions with what follows them filled in. -/
theorem Term.fill_splitAt (n : Nat) {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) :
    (t.splitAt n).2.1.fill (t.splitAt n).2.2 = t := by
  induction n generalizing Γ with
  | zero => rfl
  | succ n ih => cases t <;> simp only [Term.splitAt, Hole.fill, ih]

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
