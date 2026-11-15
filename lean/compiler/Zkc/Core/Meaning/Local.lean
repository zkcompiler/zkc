module

public import Zkc.Core.Meaning.Fold

@[expose] public section

/-!
The meaning of a function: the semantics of the local dialect.

A function is a process with no effect, which may stop. A row of the vocabulary is the
model's; outside the domain of a restricted row the process stops `undefined`. The operations
that the core owns have the core's meaning; `natSub` and `seqAt` stop `undefined` outside
their domains. A literal is read from its data. A call runs the callee's process from the table
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
    | .nominal key statics, n :: rest =>
        if V.literal key statics n then (M.literal key statics n).map fun v => (v, rest)
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
    | .nominal _ _, [], _, e => by simp [Ty.scan] at e
    | .nominal key statics, n :: data, rest, e => by
        by_cases lit : V.literal key statics n = true
        · simp only [Ty.scan, lit, ↓reduceIte, Option.some.injEq] at e
          subst e
          obtain ⟨v, hv, _⟩ := M.literals key statics n lit
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

/-- A value as the alternative at its position. -/
def Tys.injectAt : (alternatives : Tys V.TypeKey) → {τ : V.Ty} → Var alternatives.toList τ →
    M.Val τ → alternatives.Choice M.toCarriers
  | .nil, _, position, _ => nomatch position
  | .cons _ _, _, .head, v => .inl v
  | .cons _ rest, _, .tail position, v => .inr (Tys.injectAt rest position v)

/-- The meaning of an operation that the core owns. -/
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
  | _, _, .natLe, .cons a (.cons b .nil) =>
      let a : Nat := a
      let b : Nat := b
      .done (.cons (decide (a ≤ b)) .nil)
  | _, _, .boolNot, .cons b .nil =>
      let b : Bool := b
      .done (.cons (!b) .nil)
  | _, _, .seqLength item _, .cons xs .nil =>
      let xs : List (M.Val item) := xs
      .done (.cons xs.length .nil)
  | _, _, .seqAt item _, .cons xs (.cons i .nil) =>
      let xs : List (M.Val item) := xs
      let i : Nat := i
      match xs[i]? with
      | some v => .done (.cons v .nil)
      | none => .halt .undefined
  | _, _, .make _ _ fields, vs => .done (.cons (Tys.ofHList M fields vs) .nil)
  | _, _, .take _ _ fields, .cons v .nil => .done (Tys.toHList M fields v)
  | _, _, .inject _ alternatives position, .cons v .nil =>
      .done (.cons (Tys.injectAt M alternatives position v) .nil)

/-! ## Functions -/

/-- The processes of the functions that a body may call. -/
abbrev FnTable (fns : List (FnHeader V)) : Type :=
  ∀ hdr, Var fns hdr → HList M.Val hdr.ins → Local (HList M.Val hdr.outs)

/-- The meaning of a local operation. -/
def localOp {fns : List (FnHeader V)} (table : FnTable M fns) :
    {ins res : List V.Ty} → LocalOp V fns ins res → HList M.Val ins → Local (HList M.Val res)
  | _, _, .row key statics signature known, args =>
      match M.apply key statics signature known args with
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

#print axioms Zkc.Core.Ty.read_of_scan
#print axioms Zkc.Core.Ty.read_readLiteral
#print axioms Zkc.Core.localSem
