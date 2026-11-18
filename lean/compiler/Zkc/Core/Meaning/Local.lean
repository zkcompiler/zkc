module

public import Zkc.Core.Meaning.Fold
public import Zkc.Core.Meaning.Events

@[expose] public section

/-!
The meaning of a function: the semantics of the local dialect.

A function is a process with no effect, which may stop. A row of the vocabulary is the
model's; outside the domain of a restricted row the process stops `undefined`. The operations
that the core owns have the core's meaning; the seven with a domain stop `undefined` outside
it. A literal is read from its data. A call runs the callee's process from the table
of functions.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

/-! ## Literals -/

/-- Reads as often as a count says, keeping what each read gives. -/
def readMany {α : Type} (read : List Nat → Option (α × List Nat)) :
    Nat → List Nat → Option (List α × List Nat)
  | 0, data => some ([], data)
  | n + 1, data =>
      (read data).bind fun first =>
        (readMany read n first.2).map fun more => (first.1 :: more.1, more.2)

mutual
  /-- The value that a type reads from the front of the data, and what is left. It reads as
  `Ty.scan` does: a sequence without a size starts with its length, a variant with the
  position of its alternative, a natural of a nominal type is a literal of the vocabulary and
  the model gives its value. -/
  def Ty.read : (τ : V.Ty) → List Nat → Option (M.Val τ × List Nat)
    | .bool, n :: rest => if n < 2 then some (n == 1, rest) else none
    | .nat, n :: rest => some (n, rest)
    | .fin bound, n :: rest => if n < bound then some (n, rest) else none
    | .seq item (some size), data => readMany (Ty.read item) size data
    | .seq item none, size :: data => readMany (Ty.read item) size data
    | .tuple items, data => Tys.read items data
    | .record _ _ fields, data => Tys.read fields data
    | .variant _ alternatives, position :: data => Tys.readAt alternatives position data
    | .nominal key, n :: rest =>
        if V.literal key n then (M.literal key n).map fun v => (v, rest)
        else none
    | _, _ => none
  /-- One value of each type, read in order. -/
  def Tys.read : (τs : Tys V.TypeKey) → List Nat → Option (τs.Val M.toCarriers × List Nat)
    | .nil, data => some ((), data)
    | .cons head rest, data =>
        (Ty.read head data).bind fun first =>
          (Tys.read rest first.2).map fun more => ((first.1, more.1), more.2)
  /-- A value of the type at a position. -/
  def Tys.readAt : (τs : Tys V.TypeKey) → Nat → List Nat →
      Option (τs.Choice M.toCarriers × List Nat)
    | .nil, _, _ => none
    | .cons head _, 0, data => (Ty.read head data).map fun first => (.inl first.1, first.2)
    | .cons _ rest, position + 1, data =>
        (Tys.readAt rest position data).map fun more => (.inr more.1, more.2)
end

theorem readMany_of_scanMany {α : Type} {scan : List Nat → Option (List Nat)}
    {read : List Nat → Option (α × List Nat)}
    (h : ∀ data rest, scan data = some rest → ∃ v, read data = some (v, rest)) :
    ∀ n data rest, scanMany scan n data = some rest → ∃ vs, readMany read n data = some (vs, rest)
  | 0, data, rest, e => ⟨[], by simp only [scanMany, Option.some.injEq] at e; simp [readMany, e]⟩
  | n + 1, data, rest, e => by
      simp only [scanMany] at e
      cases hs : scan data with
      | none => simp [hs] at e
      | some mid =>
          simp only [hs, Option.bind_some] at e
          obtain ⟨v, hv⟩ := h data mid hs
          obtain ⟨vs, hvs⟩ := readMany_of_scanMany h n mid rest e
          exact ⟨v :: vs, by simp [readMany, hv, hvs]⟩

mutual
  /-- Where the data scans as a type, it reads as a value of the type, with the same rest. -/
  theorem Ty.read_of_scan : ∀ (τ : V.Ty) (data rest : List Nat),
      Ty.scan V τ data = some rest → ∃ v, Ty.read M τ data = some (v, rest)
    | .bool, [], _, e => by simp [Ty.scan] at e
    | .bool, n :: data, rest, e => by
        by_cases lt : n < 2
        · simp only [Ty.scan, lt, ↓reduceIte, Option.some.injEq] at e
          subst e
          exact ⟨n == 1, by simp [Ty.read, lt]⟩
        · simp [Ty.scan, lt] at e
    | .nat, [], _, e => by simp [Ty.scan] at e
    | .nat, n :: data, rest, e => by
        simp only [Ty.scan, Option.some.injEq] at e
        subst e
        exact ⟨n, rfl⟩
    | .fin _, [], _, e => by simp [Ty.scan] at e
    | .fin bound, n :: data, rest, e => by
        by_cases lt : n < bound
        · simp only [Ty.scan, lt, ↓reduceIte, Option.some.injEq] at e
          subst e
          exact ⟨n, by simp [Ty.read, lt]⟩
        · simp [Ty.scan, lt] at e
    | .seq item (some size), data, rest, e =>
        readMany_of_scanMany (fun d r h => Ty.read_of_scan item d r h) size data rest e
    | .seq _ none, [], _, e => by simp [Ty.scan] at e
    | .seq item none, size :: data, rest, e =>
        readMany_of_scanMany (fun d r h => Ty.read_of_scan item d r h) size data rest e
    | .tuple items, data, rest, e => Tys.read_of_scan items data rest e
    | .record _ _ fields, data, rest, e => Tys.read_of_scan fields data rest e
    | .variant _ _, [], _, e => by simp [Ty.scan] at e
    | .variant _ alternatives, position :: data, rest, e =>
        Tys.readAt_of_scan alternatives position data rest e
    | .nominal _, [], _, e => by simp [Ty.scan] at e
    | .nominal key, n :: data, rest, e => by
        by_cases lit : V.literal key n = true
        · simp only [Ty.scan, lit, ↓reduceIte, Option.some.injEq] at e
          subst e
          obtain ⟨v, hv, _⟩ := M.literals key n lit
          exact ⟨v, by simp [Ty.read, lit, hv]⟩
        · simp [Ty.scan, lit] at e
  theorem Tys.read_of_scan : ∀ (τs : Tys V.TypeKey) (data rest : List Nat),
      Tys.scan V τs data = some rest → ∃ v, Tys.read M τs data = some (v, rest)
    | .nil, data, rest, e => by
        simp only [Tys.scan, Option.some.injEq] at e
        subst e
        exact ⟨(), rfl⟩
    | .cons head tail, data, rest, e => by
        simp only [Tys.scan] at e
        cases hs : Ty.scan V head data with
        | none => simp [hs] at e
        | some mid =>
            simp only [hs, Option.bind_some] at e
            obtain ⟨v, hv⟩ := Ty.read_of_scan head data mid hs
            obtain ⟨vs, hvs⟩ := Tys.read_of_scan tail mid rest e
            exact ⟨(v, vs), by simp [Tys.read, hv, hvs]⟩
  theorem Tys.readAt_of_scan : ∀ (τs : Tys V.TypeKey) (position : Nat) (data rest : List Nat),
      Tys.scanAt V τs position data = some rest → ∃ v, Tys.readAt M τs position data = some (v, rest)
    | .nil, _, _, _, e => by simp [Tys.scanAt] at e
    | .cons head _, 0, data, rest, e => by
        simp only [Tys.scanAt] at e
        obtain ⟨v, hv⟩ := Ty.read_of_scan head data rest e
        exact ⟨.inl v, by simp [Tys.readAt, hv]⟩
    | .cons _ tail, position + 1, data, rest, e => by
        simp only [Tys.scanAt] at e
        obtain ⟨v, hv⟩ := Tys.readAt_of_scan tail position data rest e
        exact ⟨.inr v, by simp [Tys.readAt, hv]⟩
end

/-- The value of a literal: the data reads as the type, and nothing is left. -/
def Ty.readLiteral (τ : V.Ty) (data : List Nat) (reads : V.Reads τ data) : M.Val τ :=
  match h : Ty.read M τ data with
  | some (v, _) => v
  | none => False.elim (by
      obtain ⟨v, e⟩ := Ty.read_of_scan M τ data [] reads
      rw [h] at e
      cases e)

theorem Ty.read_readLiteral (τ : V.Ty) (data : List Nat) (reads : V.Reads τ data) :
    Ty.read M τ data = some (Ty.readLiteral M τ data reads, []) := by
  obtain ⟨v, e⟩ := Ty.read_of_scan M τ data [] reads
  unfold Ty.readLiteral
  split
  · next v' rest h =>
      rw [e] at h
      cases h
      exact e
  · next h =>
      rw [e] at h
      cases h

/-! ## The operations that the core owns -/

/-- The fields of a record, from one value per field. -/
def Tys.ofHList : (fields : Tys V.TypeKey) → HList M.Val fields.toList → fields.Val M.toCarriers
  | .nil, _ => ()
  | .cons _ rest, .cons v vs => (v, Tys.ofHList rest vs)

/-- One value per field, from the fields of a record. -/
def Tys.toHList : (fields : Tys V.TypeKey) → fields.Val M.toCarriers → HList M.Val fields.toList
  | .nil, _ => .nil
  | .cons _ rest, (v, vs) => .cons v (Tys.toHList rest vs)

/-- The field at a position. -/
def Tys.getAt : (fields : Tys V.TypeKey) → {τ : V.Ty} → Member fields.toList τ →
    fields.Val M.toCarriers → M.Val τ
  | .nil, _, position, _ => nomatch position
  | .cons _ _, _, .head, (v, _) => v
  | .cons _ rest, _, .tail position, (_, vs) => Tys.getAt rest position vs

/-- A value as the alternative at its position. -/
def Tys.injectAt : (alternatives : Tys V.TypeKey) → {τ : V.Ty} → Member alternatives.toList τ →
    M.Val τ → alternatives.Choice M.toCarriers
  | .nil, _, position, _ => nomatch position
  | .cons _ _, _, .head, v => .inl v
  | .cons _ rest, _, .tail position, v => .inr (Tys.injectAt rest position v)

/-- The items of a sequence, from one value per item. -/
def HList.toItems {item : V.Ty} : (count : Nat) → HList M.Val (List.replicate count item) →
    List (M.Val item)
  | 0, _ => []
  | count + 1, .cons v vs => v :: HList.toItems count vs

end

/-- Whether a length is a size: the size, when there is one. -/
def fitsSize : Option Nat → Nat → Bool
  | some size, length => Nat.beq length size
  | none, _ => true

section
variable {V : Vocabulary} (M : Model V)

/-- The meaning of an operation that the core owns. Positions count from zero; a slice
excludes its upper bound; a concatenation puts the first first; a division rounds down; a
number to the power zero is one. Outside its domain an operation stops `undefined`; a refining
or widening operation returns its operand. -/
def ownedOp : {ins outs : List V.Ty} → OwnedOp V ins outs → HList M.Val ins →
    Local (HList M.Val outs)
  | _, _, .natAdd, .cons a (.cons b .nil) =>
      let a : Nat := a
      let b : Nat := b
      .done (.cons (a + b) .nil)
  | _, _, .natSub, .cons a (.cons b .nil) =>
      let a : Nat := a
      let b : Nat := b
      if b ≤ a then .done (.cons (a - b) .nil) else .halt .undefined
  | _, _, .natMul, .cons a (.cons b .nil) =>
      let a : Nat := a
      let b : Nat := b
      .done (.cons (a * b) .nil)
  | _, _, .natDiv, .cons a (.cons b .nil) =>
      let a : Nat := a
      let b : Nat := b
      if 1 ≤ b then .done (.cons (a / b) .nil) else .halt .undefined
  | _, _, .natRem, .cons a (.cons b .nil) =>
      let a : Nat := a
      let b : Nat := b
      if 1 ≤ b then .done (.cons (a % b) .nil) else .halt .undefined
  | _, _, .natPow, .cons a (.cons b .nil) =>
      let a : Nat := a
      let b : Nat := b
      .done (.cons (a ^ b) .nil)
  | _, _, .natEqual, .cons a (.cons b .nil) =>
      let a : Nat := a
      let b : Nat := b
      .done (.cons (Nat.beq a b) .nil)
  | _, _, .natLess, .cons a (.cons b .nil) =>
      let a : Nat := a
      let b : Nat := b
      .done (.cons (Nat.blt a b) .nil)
  | _, _, .boolAnd, .cons a (.cons b .nil) =>
      let a : Bool := a
      let b : Bool := b
      .done (.cons (a && b) .nil)
  | _, _, .boolOr, .cons a (.cons b .nil) =>
      let a : Bool := a
      let b : Bool := b
      .done (.cons (a || b) .nil)
  | _, _, .boolNot, .cons b .nil =>
      let b : Bool := b
      .done (.cons (!b) .nil)
  | _, _, .boolEqual, .cons a (.cons b .nil) =>
      let a : Bool := a
      let b : Bool := b
      .done (.cons (a == b) .nil)
  | _, _, .seqLength item _ _, .cons xs .nil =>
      let xs : List (M.Val item) := xs
      .done (.cons xs.length .nil)
  | _, _, .seqAt item _ _, .cons xs (.cons i .nil) =>
      let xs : List (M.Val item) := xs
      let i : Nat := i
      match xs[i]? with
      | some v => .done (.cons v .nil)
      | none => .halt .undefined
  | _, _, .seqSlice item _ result _, .cons xs (.cons first (.cons second .nil)) =>
      let xs : List (M.Val item) := xs
      let first : Nat := first
      let second : Nat := second
      if first ≤ second ∧ second ≤ xs.length ∧ fitsSize result (second - first) = true then
        .done (.cons ((xs.drop first).take (second - first)) .nil)
      else .halt .undefined
  | _, _, .seqConcat item _ _, .cons xs (.cons ys .nil) =>
      let xs : List (M.Val item) := xs
      let ys : List (M.Val item) := ys
      .done (.cons (xs ++ ys) .nil)
  | _, _, .seqFill _ count _, .cons v .nil => .done (.cons (List.replicate count v) .nil)
  | _, _, .seqSized item size _, .cons xs .nil =>
      let xs : List (M.Val item) := xs
      if xs.length = size then .done (.cons xs .nil) else .halt .undefined
  | _, _, .natBelow bound, .cons n .nil =>
      let n : Nat := n
      if n < bound then .done (.cons n .nil) else .halt .undefined
  | _, _, .seqUnsized item _, .cons xs .nil =>
      let xs : List (M.Val item) := xs
      .done (.cons xs .nil)
  | _, _, .finToNat _, .cons n .nil =>
      let n : Nat := n
      .done (.cons n .nil)
  | _, _, .finWiden _ _ _, .cons n .nil =>
      let n : Nat := n
      .done (.cons n .nil)
  | _, _, .makeSeq _ count, vs => .done (.cons (HList.toItems M count vs) .nil)
  | _, _, .makeTuple items, vs => .done (.cons (Tys.ofHList M items vs) .nil)
  | _, _, .makeRecord _ _ fields, vs => .done (.cons (Tys.ofHList M fields vs) .nil)
  | _, _, .getTuple items position _, .cons v .nil =>
      .done (.cons (Tys.getAt M items position v) .nil)
  | _, _, .getRecord _ fields position _, .cons v .nil =>
      .done (.cons (Tys.getAt M fields position v) .nil)
  | _, _, .takeTuple items, .cons v .nil => .done (Tys.toHList M items v)
  | _, _, .takeRecord _ _ fields, .cons v .nil => .done (Tys.toHList M fields v)
  | _, _, .variant _ alternatives position, .cons v .nil =>
      .done (.cons (Tys.injectAt M alternatives position v) .nil)

/-! ## Functions -/

/-- The processes of the functions that a body may call. -/
abbrev FnTable (fns : List (FnHeader V)) : Type :=
  ∀ hdr, Member fns hdr → HList M.Val hdr.ins → Local (HList M.Val hdr.outs)

/-- The meaning of a local operation. -/
def localOp {fns : List (FnHeader V)} (table : FnTable M fns) :
    {ins res : List V.Ty} → LocalOp V fns ins res → HList M.Val ins → Local (HList M.Val res)
  | _, _, .row key signature known, args =>
      match M.apply key signature known args with
      | some outs => .done outs
      | none => .halt .undefined
  | _, _, .owned o, args => ownedOp M o args
  | _, _, .literal τ data reads, _ => .done (.cons (Ty.readLiteral M τ data reads) .nil)
  | _, _, .call callee, args => table _ callee args

/-! ## Reading a condition, a variant and a count -/

/-- A value of a type that is `bool`. -/
def asBool {τ : V.Ty} (h : τ = .bool) (v : M.Val τ) : Bool := cast (congrArg M.Val h) v

/-- A value of a type that is `nat`. -/
def asNat {τ : V.Ty} (h : τ = .nat) (v : M.Val τ) : Nat := cast (congrArg M.Val h) v

end

/-- The key of a variant type. -/
def Ty.variantKey {K : Type} : Ty K → Key
  | .variant key _ => key
  | _ => ⟨0⟩

/-- The alternatives of a variant type. -/
def Ty.alternatives {K : Type} : Ty K → Tys K
  | .variant _ alternatives => alternatives
  | _ => .nil

theorem Ty.eq_variant {K : Type} {τ : Ty K} {P : Tys K → Prop}
    (h : ∃ key alternatives, τ = .variant key alternatives ∧ P alternatives) :
    τ = .variant τ.variantKey τ.alternatives := by
  obtain ⟨_, _, e, _⟩ := h
  subst e
  rfl

theorem Ty.alternatives_of {K : Type} {τ : Ty K} {key : Key} {alternatives : Tys K}
    (e : τ = .variant key alternatives) : τ.alternatives = alternatives := by
  subst e
  rfl

section
variable {V : Vocabulary} (M : Model V)

/-- The alternative of a value of a variant, with its payload. -/
def Tys.pick : (alternatives : Tys V.TypeKey) → alternatives.Choice M.toCarriers →
    Pick M.Val alternatives.toList
  | .nil, v => nomatch v
  | .cons _ _, .inl v => .here v
  | .cons _ rest, .inr v => .there (Tys.pick rest v)

/-- The alternative of a variant, for a function. -/
def localPick {t : V.Ty} {payloads : List V.Ty}
    (h : ∃ key alternatives, t = .variant key alternatives ∧ payloads = alternatives.toList)
    (v : M.Val t) : Pick M.Val payloads :=
  cast
    (congrArg (Pick M.Val) (by
      obtain ⟨_, _, e, p⟩ := h
      rw [Ty.alternatives_of e, p]))
    (Tys.pick M t.alternatives (cast (congrArg M.Val (Ty.eq_variant h)) v))

/-- The semantics of the local dialect: values of the model, no effects, a stop with its
reason. -/
@[reducible] def localSem (fns : List (FnHeader V)) (table : FnTable M fns) :
    Semantics (localDialect V fns) where
  Val := M.Val
  S := NoSig
  H := Stop
  op := fun {_ _} _ o _ args => localOp M table o args
  holds := fun {_ _} h v => asBool M h v
  stop := fun _ why at_ => .declared why at_
  pick := fun {_ _ _} h v => localPick M h v
  count := fun {_ _} h v => asNat M h v
  index := fun _ i => i
  begin := fun _ _ _ => .done (0 : Nat)
  settle := fun _ _ _ => .done ()
  collect := fun _ _ vs => vs

end

end Zkc.Core
