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

/-- Whether a role is among the holders of a value, by the cases of the list. On a role and
holders that are written out it is decided by the reduction of reducible definitions alone. -/
@[reducible] def holdsAmong : Role → List Role → Bool
  | _, [] => false
  | r, holder :: rest =>
    match Nat.beq r holder with
    | true => true
    | false => holdsAmong r rest

@[simp] theorem holdsAmong_eq (r : Role) (holders : List Role) :
    holdsAmong r holders = decide (r ∈ holders) := by
  induction holders with
  | nil => simp [holdsAmong]
  | cons holder rest ih =>
    unfold holdsAmong
    cases same : Nat.beq r holder
    · have differ : r ≠ holder := fun eq => by simp [eq] at same
      simp [ih, differ]
    · have eq : r = holder := Nat.eq_of_beq_eq_true same
      simp [eq]

/-- A type where a condition holds, `Unit` where it does not. -/
@[reducible] def HeldType : Bool → Type → Type
  | true, T => T
  | false, _ => Unit

@[simp] theorem HeldType_true (T : Type) : HeldType true T = T := rfl

@[simp] theorem HeldType_false (T : Type) : HeldType false T = Unit := rfl

/-- The value of a located type, for a role: the value when the role holds it, nothing
otherwise. The type is reducible, and whether the role holds the value is decided by the cases
of the holders: for a role and a located type that are written out it is the value's type or
`Unit` without unfolding anything else, which is how a tactic compares types. So a value of a
role's program is used at its own type: a boolean as a boolean, a number as a number. -/
@[reducible] def RV (r : Role) (a : LTy V) : Type := HeldType (holdsAmong r a.holders) (M.Val a.ty)

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
  | .coin law, ins, payload, τ, v =>
      M.Valid τ v ∧ ∃ (s : LawSignature V.TypeKey) (h : V.law law = some s)
        (ins_eq : s.ins = ins) (out_eq : s.out = τ),
        M.support law s h (cast (congrArg (HList M.Val) ins_eq.symm) payload)
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
