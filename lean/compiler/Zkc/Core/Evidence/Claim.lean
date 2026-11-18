module

public import Zkc.Core.Meaning.Fold
public import Zkc.Core.Process.Handler

@[expose] public section

/-!
The scope of a statement about a term, claims, and what it is for a term to be assured.

A statement about a term is made for a semantics, for permitted replies of the world, and for
the starts that it authorizes: a predicate on the path and the environment at the entry
(`Entry`). A claim says, of every authorized start and every path of permitted replies, what the
term returns and how it stops (`Claim`). A claim under a handler is the same statement about the
process that the handler makes of the term's, whose returns and stops carry the observer's
state (`Claim.Under`): a quantity that the handler accumulates is claimed so.

A term is assured in a scope when, from every authorized start, it never stops in a way that the
interpretation calls undefined and returns valid values (`Assured`). Every theorem about what a
program does takes this as its premise; an analysis that accepts the term is one way to have it,
and a relation that transfers it is another (`Assured.transfer`, `Evidence/Relation.lean`).
Nothing here depends on an analysis.
-/

namespace Zkc.Core

section
variable {D : Dialect} (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)

/-- The starts of a term that a statement is made about: a predicate on the path and the
environment at its entry. -/
abbrev Entry (Γ : Ctx D.Ty) : Type := List Frame → Env sem.Val Γ → Prop

/-- A claim about a term: on every authorized start and every permitted reply, what it returns
and how it stops. -/
def Claim {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (entry : Entry sem Γ)
    (returns : HList sem.Val outs → Prop) (stops : sem.H → Prop) : Prop :=
  ∀ path env, entry path env → (t.denote sem path env).Every permitted returns stops

/-- A claim under a handler: the same statement about the process that the handler makes of the
term's, from authorized states of the observer. What is returned, and what a stop carries, has
the observer's state, so a quantity that the handler accumulates is claimed on a return and on
a stop alike. `allowed` says which replies the world below the handler may give. -/
def Claim.Under {T : Sig} {σ : Type} (h : Handler sem.S T sem.H σ) (retry : Retry sem.S T sem.H)
    (allowed : ∀ op, T.Reply op → Prop) {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs)
    (entry : Entry sem Γ) (start : σ → Prop) (returns : HList sem.Val outs × σ → Prop)
    (stops : sem.H × σ → Prop) : Prop :=
  ∀ path env state, entry path env → start state →
    (h.run retry (t.denote sem path env) state).Every allowed returns stops

/-- What it is for a term to be assured in a scope: from every authorized start, on permitted
replies, it never stops in a way that the interpretation calls undefined, and it returns valid
values. Every later theorem takes this as its premise; that an analysis accepted the term is
one way to have it. -/
structure Assured (Valid : sem.Dyn → Prop) (undefined : sem.H → Prop) {Γ : Ctx D.Ty}
    {outs : List D.Ty} (t : Term D Γ outs) (entry : Entry sem Γ) : Prop where
  holds : Claim sem permitted t entry (fun returned => ∀ v, v ∈ sem.dyns returned → Valid v)
    (fun stop => ¬ undefined stop)

end

end Zkc.Core
