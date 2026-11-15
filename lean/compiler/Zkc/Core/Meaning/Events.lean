module

public import Zkc.Core.Program.Typed
public import Zkc.Core.Process.Process

@[expose] public section

/-!
Events and what a role holds.

An event of a protocol names who takes part; an effect of a role is its part of an event, and
names its peers. A role holds the value of a located type when it is a holder, and nothing
otherwise. What the world may give is a valid value and, for a coin, one in the support of its
law.
-/

namespace Zkc.Core

/-- The process of a function. -/
abbrev Local (A : Type) : Type := Process NoSig Stop A

section
variable {V : Vocabulary} (M : Model V)

/-- An event of a protocol names who takes part. -/
inductive GOp where
  | flow (kind : FlowKind) (giver : Role) (getters : List Role) (at_ : Occurrence)
      (τ : V.Ty) (value : M.Val τ)
  | given (kind : GivenKind V) (owner : Role) (hearers : List Role) (at_ : Occurrence)
      (ins : List V.Ty) (payload : HList M.Val ins) (τ : V.Ty)

@[reducible] def GSig : Sig :=
  ⟨GOp M, fun | .flow .. => Unit | .given _ _ _ _ _ _ τ => M.Val τ⟩

/-- An effect of a role is its part of an event, and names its peers. -/
inductive ROp where
  | give (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty) (value : M.Val τ)
  | get (kind : FlowKind) (giver : Role) (at_ : Occurrence) (τ : V.Ty)
  | own (kind : GivenKind V) (hearers : List Role) (at_ : Occurrence)
      (ins : List V.Ty) (payload : HList M.Val ins) (τ : V.Ty)
  | hear (kind : GivenKind V) (owner : Role) (at_ : Occurrence) (τ : V.Ty)
  /-- The role begins an attempt that it owns; the reply is the number of the attempt. -/
  | begin (at_ : Occurrence)
  /-- The role ends the body of an attempt that it owns. -/
  | settle (at_ : Occurrence)

@[reducible] def RSig : Sig :=
  ⟨ROp M, fun
    | .give .. => Unit
    | .get _ _ _ τ => M.Val τ
    | .own _ _ _ _ _ τ => M.Val τ
    | .hear _ _ _ τ => M.Val τ
    | .begin _ => Nat
    | .settle _ => Unit⟩

/-- The process of a protocol: all its roles; a stop names the roles that stop. -/
abbrev Protocol (A : Type) : Type := Process (GSig M) (List Role × Stop) A

/-- The process of one role. -/
abbrev Program (B : Type) : Type := Process (RSig M) Stop B

end

/-! ## What a role holds -/

section
variable {V : Vocabulary} (M : Model V)

/-- The value of a located type, for the protocol. -/
abbrev LVal (a : LTy V) : Type := M.Val a.ty

/-- The value of a located type, for a role: the value when the role holds it, nothing
otherwise. -/
def RV (r : Role) (a : LTy V) : Type := if r ∈ a.holders then M.Val a.ty else Unit

def hide (r : Role) (a : LTy V) (v : LVal M a) : RV M r a :=
  if h : r ∈ a.holders then cast (by simp [RV, h]) v else cast (by simp [RV, h]) ()

def HList.map {α : Type} {F G : α → Type} (f : ∀ a, F a → G a) :
    {items : List α} → HList F items → HList G items
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (f _ v) (rest.map f)

/-- The part of the values of the protocol that a role holds. Honest roles have parts of one
input. -/
def hideAll (r : Role) {items : List (LTy V)} (vs : HList (LVal M) items) : HList (RV M r) items :=
  vs.map (hide M r)

/-- A value that a role holds is valid. -/
def RV.Valid (r : Role) (a : LTy V) (v : RV M r a) : Prop :=
  ∀ h : r ∈ a.holders, M.Valid a.ty (cast (by simp [RV, h]) v)

/-- What the world may give: a valid value and, for a coin, one in the support of its law
at its payload. -/
def Allows : (kind : GivenKind V) → (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) →
    M.Val τ → Prop
  | .coin law statics, ins, payload, τ, v =>
      M.Valid τ v ∧ ∃ (s : LawSignature V.TypeKey) (h : V.law law statics = some s)
        (ins_eq : s.ins = ins) (out_eq : s.out = τ),
        M.support law statics s h (cast (congrArg (HList M.Val) ins_eq.symm) payload)
          (cast (congrArg M.Val out_eq.symm) v)
  | _, _, _, τ, v => M.Valid τ v

/-- A reply that a role may get: what the world allows at an effect that it owns, a valid
value of its type at a message and at what it hears, any number at the beginning of an
attempt. -/
def Permitted : (op : ROp M) → (RSig M).Reply op → Prop
  | .give .., _ => True
  | .get _ _ _ τ, v => M.Valid τ v
  | .own kind _ _ ins payload τ, v => Allows M kind ins payload τ v
  | .hear _ _ _ τ, v => M.Valid τ v
  | .begin _, _ => True
  | .settle _, _ => True

end

end Zkc.Core
