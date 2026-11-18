module

public import Zkc.Core.Evidence.Claim
public import Zkc.Core.Meaning.Place
public import Zkc.Core.Process.Same

@[expose] public section

/-!
Facts at a place, the relation "same meaning" in a scope, and what moves along it.

A fact at a place holds of every path and environment with which a run from an authorized start
reaches the place (`Fact`, by `Hole.Holds` of `Meaning/Place.lean`). Two terms mean the same in
a scope when, from every authorized start, their processes agree on every path of permitted
replies, stops included (`Equivalent`, by `Process.SameWhen`). The relation composes in one
scope (`Equivalent.trans`); a claim moves along it (`Equivalent.claim`), and so does being
assured (`Assured.transfer`): nothing is derived again. Two terms that mean the same where a
fact holds give wholes that mean the same, at any place where the fact holds
(`replace_with_fact`); a law with a premise is two terms that mean the same under it
(`ConditionalLaw`), applied at a place where its premise is a fact (`ConditionalLaw.apply`).
-/

namespace Zkc.Core

section
variable {D : Dialect} (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)

/-- A fact at a place: it holds of every path and environment with which a run from an
authorized start reaches the place. -/
def Fact {Γ : Ctx D.Ty} {outs : List D.Ty} {Δ : Ctx D.Ty} {mid : List D.Ty}
    (hole : Hole D Γ outs Δ mid) (filling : Term D Δ mid) (entry : Entry sem Γ)
    (fact : Entry sem Δ) : Prop :=
  ∀ path env, entry path env → hole.Holds sem permitted filling path env fact

/-- The relation "same meaning" in a scope: from every authorized start the two processes agree
on every path of permitted replies, stops included. -/
def Equivalent {Γ : Ctx D.Ty} {outs : List D.Ty} (t t' : Term D Γ outs) (entry : Entry sem Γ) :
    Prop :=
  ∀ path env, entry path env →
    Process.SameWhen permitted (t.denote sem path env) (t'.denote sem path env)

/-- Replacement under a fact, at any place of a term. -/
theorem replace_with_fact {Γ : Ctx D.Ty} {outs : List D.Ty} {Δ : Ctx D.Ty} {mid : List D.Ty}
    (hole : Hole D Γ outs Δ mid) (t t' : Term D Δ mid) (entry : Entry sem Γ)
    (fact : Entry sem Δ) (known : Fact sem permitted hole t entry fact)
    (same : Equivalent sem permitted t t' fact) :
    Equivalent sem permitted (hole.fill t) (hole.fill t') entry :=
  fun path env authorized =>
    Hole.fill_same sem permitted hole t t' path env fun path' env' reach =>
      same path' env' (known path env authorized path' env' reach)

/-- A claim moves along the relation, stops included. -/
theorem Equivalent.claim {Γ : Ctx D.Ty} {outs : List D.Ty} {t t' : Term D Γ outs}
    {entry : Entry sem Γ} (same : Equivalent sem permitted t t' entry)
    (returns : HList sem.Val outs → Prop) (stops : sem.H → Prop)
    (claim : Claim sem permitted t entry returns stops) :
    Claim sem permitted t' entry returns stops :=
  fun path env authorized => (same path env authorized).every (claim path env authorized)

/-- The relation composes in one scope. -/
theorem Equivalent.trans {Γ : Ctx D.Ty} {outs : List D.Ty} {t t' t'' : Term D Γ outs}
    {entry : Entry sem Γ} (first : Equivalent sem permitted t t' entry)
    (second : Equivalent sem permitted t' t'' entry) : Equivalent sem permitted t t'' entry :=
  fun path env authorized => (first path env authorized).trans (second path env authorized)

/-- A law with a premise, between two terms of one context. -/
structure ConditionalLaw {Γ : Ctx D.Ty} {outs : List D.Ty} (left right : Term D Γ outs) where
  premise : Entry sem Γ
  preserves : Equivalent sem permitted left right premise

/-- A law applied at a place where its premise is a fact. -/
theorem ConditionalLaw.apply {Γ : Ctx D.Ty} {outs : List D.Ty} {Δ : Ctx D.Ty} {mid : List D.Ty}
    {left right : Term D Δ mid} (law : ConditionalLaw sem permitted left right)
    (hole : Hole D Γ outs Δ mid) (entry : Entry sem Γ)
    (established : Fact sem permitted hole left entry law.premise) :
    Equivalent sem permitted (hole.fill left) (hole.fill right) entry :=
  replace_with_fact sem permitted hole left right entry law.premise established law.preserves

/-- A term that means the same as an assured one is assured: nothing is derived again. -/
theorem Assured.transfer {Valid : sem.Dyn → Prop} {undefined : sem.H → Prop} {Γ : Ctx D.Ty}
    {outs : List D.Ty} {t t' : Term D Γ outs} {entry : Entry sem Γ}
    (assured : Assured sem permitted Valid undefined t entry)
    (same : Equivalent sem permitted t t' entry) :
    Assured sem permitted Valid undefined t' entry :=
  ⟨same.claim sem permitted _ _ assured.holds⟩

end

end Zkc.Core
