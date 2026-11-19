module

public import Zkc.Core.Program.Identity
public import Zkc.Core.Program.Lists

@[expose] public section

/-!
Types, the vocabulary and its models.

The core is parameterised by a vocabulary: the keys of nominal types, of rows and of laws,
and the signature and the kind of each at its key. A key says everything that tells one type,
row or law from another, so nothing stands beside it. The values of `bool`, of
naturals, of sequences, tuples, records and variants, and the operations on them, are the
core's own. A model gives each nominal type a carrier and says which values are valid; every
row keeps validity. Positions in a list and lists of values of types, which are about no
vocabulary, are in `Lists.lean`.
-/

namespace Zkc.Core

/-! ## Types -/

mutual
  /-- The types of the core, over the keys `K` of nominal types. No type mentions a value. -/
  inductive Ty (K : Type) where
    | bool
    | nat
    | fin (n : Nat)
    /-- A sequence; with a size, of exactly that length. -/
    | seq (item : Ty K) (size : Option Nat)
    | tuple (items : Tys K)
    /-- A record, by the key of its declaration, whether it is linear, and its fields in
    order. Two declarations with the same fields are two types. -/
    | record (key : Key) (linear : Bool) (fields : Tys K)
    /-- A variant, by the key of its declaration, with the payload of each alternative; an
    alternative without a payload has the empty tuple. -/
    | variant (key : Key) (alternatives : Tys K)
    | nominal (key : K)
  inductive Tys (K : Type) where
    | nil
    | cons (head : Ty K) (rest : Tys K)
end

deriving instance DecidableEq for Ty, Tys

/-! ## The vocabulary -/

inductive RowKind (R : Type) where
  /-- A total function of its inputs. -/
  | pure
  /-- A function on a domain, which a pure row with the same inputs decides. -/
  | restricted (domain : R)
deriving DecidableEq

structure RowSignature (K R : Type) where
  ins : List (Ty K)
  outs : List (Ty K)
  kind : RowKind R
deriving DecidableEq

/-- A sampling law: a distribution on its one output. -/
structure LawSignature (K : Type) where
  ins : List (Ty K)
  out : Ty K

structure Vocabulary where
  TypeKey : Type
  RowKey : Type
  LawKey : Type
  [decTypeKey : DecidableEq TypeKey]
  [decRowKey : DecidableEq RowKey]
  [decLawKey : DecidableEq LawKey]
  /-- The signature and the kind of a row; `none` when the key names no row. -/
  row : RowKey → Option (RowSignature TypeKey RowKey)
  /-- The signature of a law; `none` when the key names no law. -/
  law : LawKey → Option (LawSignature TypeKey)
  /-- Whether a natural is a literal of a nominal type. -/
  literal : TypeKey → Nat → Bool
  /-- Whether a nominal type is linear: none is, unless said. -/
  linear : TypeKey → Bool := fun _ => false
  /-- The domain row of a restricted row: pure, with the same inputs, giving one truth value. -/
  decided : ∀ key signature domain, row key = some signature →
    signature.kind = .restricted domain → row domain = some ⟨signature.ins, [.bool], .pure⟩

attribute [instance] Vocabulary.decTypeKey Vocabulary.decRowKey Vocabulary.decLawKey

abbrev Vocabulary.Ty (V : Vocabulary) : Type := Zkc.Core.Ty V.TypeKey

mutual
  /-- A type is linear: a record marked so, a nominal type that the vocabulary says is, or a
  type with a linear component. -/
  def Ty.isLinear (V : Vocabulary) : V.Ty → Bool
    | .bool => false
    | .nat => false
    | .fin _ => false
    | .seq item _ => Ty.isLinear V item
    | .tuple items => Tys.anyLinear V items
    | .record _ linear fields => linear || Tys.anyLinear V fields
    | .variant _ alternatives => Tys.anyLinear V alternatives
    | .nominal key => V.linear key
  /-- One of the types is linear. -/
  def Tys.anyLinear (V : Vocabulary) : Tys V.TypeKey → Bool
    | .nil => false
    | .cons head rest => Ty.isLinear V head || Tys.anyLinear V rest
end

mutual
  /-- A type has no value: `fin 0`; a sized sequence of a positive size whose items have none; a
  tuple or a record with a component that has none; a variant all of whose alternatives have
  none, one without alternatives among them. A nominal type is never said to have none. -/
  def Ty.noValue {K : Type} : Ty K → Bool
    | .fin bound => bound == 0
    | .seq item (some (_ + 1)) => Ty.noValue item
    | .tuple items => Tys.someNoValue items
    | .record _ _ fields => Tys.someNoValue fields
    | .variant _ alternatives => Tys.allNoValue alternatives
    | _ => false
  /-- One of the types has no value. -/
  def Tys.someNoValue {K : Type} : Tys K → Bool
    | .nil => false
    | .cons head rest => Ty.noValue head || Tys.someNoValue rest
  /-- Every one of the types has no value. -/
  def Tys.allNoValue {K : Type} : Tys K → Bool
    | .nil => true
    | .cons head rest => Ty.noValue head && Tys.allNoValue rest
end

/-- Reads as often as a count says. -/
def scanMany (scan : List Nat → Option (List Nat)) : Nat → List Nat → Option (List Nat)
  | 0, data => some data
  | n + 1, data => (scan data).bind (scanMany scan n)

mutual
  /-- The data of a literal of a type is naturals, read in order: what is left of the data
  when a value of the type reads from its front. A sequence without a size starts with its
  length, a variant with the position of its alternative. -/
  def Ty.scan (V : Vocabulary) : Ty V.TypeKey → List Nat → Option (List Nat)
    | .bool, n :: rest => if n < 2 then some rest else none
    | .nat, _ :: rest => some rest
    | .fin bound, n :: rest => if n < bound then some rest else none
    | .seq item (some size), data => scanMany (Ty.scan V item) size data
    | .seq item none, size :: data => scanMany (Ty.scan V item) size data
    | .tuple items, data => Tys.scan V items data
    | .record _ _ fields, data => Tys.scan V fields data
    | .variant _ alternatives, position :: data => Tys.scanAt V alternatives position data
    | .nominal key, n :: rest => if V.literal key n then some rest else none
    | _, _ => none
  def Tys.scan (V : Vocabulary) : Tys V.TypeKey → List Nat → Option (List Nat)
    | .nil, data => some data
    | .cons head rest, data => (Ty.scan V head data).bind (Tys.scan V rest)
  def Tys.scanAt (V : Vocabulary) : Tys V.TypeKey → Nat → List Nat → Option (List Nat)
    | .nil, _, _ => none
    | .cons head _, 0, data => Ty.scan V head data
    | .cons _ rest, position + 1, data => Tys.scanAt V rest position data
end

/-- The data is a literal of the type: it reads, and nothing is left. -/
def Vocabulary.Reads (V : Vocabulary) (τ : V.Ty) (data : List Nat) : Prop :=
  Ty.scan V τ data = some []

/-! ## Models -/

/-- What a model chooses: a carrier for each nominal type, and which of its values are
valid. The values of the other types are the core's. -/
structure Carriers (V : Vocabulary) where
  Carrier : V.TypeKey → Type
  valid : ∀ key, Carrier key → Prop
  /-- The value of a literal. -/
  literal : ∀ key, Nat → Option (Carrier key)

mutual
  /-- The values of a type. -/
  @[reducible] def Ty.Val {V : Vocabulary} (C : Carriers V) : Ty V.TypeKey → Type
    | .bool => Bool
    | .nat => Nat
    | .fin _ => Nat
    | .seq item _ => List (item.Val C)
    | .tuple items => items.Val C
    | .record _ _ fields => fields.Val C
    | .variant _ alternatives => alternatives.Choice C
    | .nominal key => C.Carrier key
  /-- One value of each type. -/
  @[reducible] def Tys.Val {V : Vocabulary} (C : Carriers V) : Tys V.TypeKey → Type
    | .nil => Unit
    | .cons head rest => head.Val C × rest.Val C
  /-- A value of one of the types. -/
  @[reducible] def Tys.Choice {V : Vocabulary} (C : Carriers V) : Tys V.TypeKey → Type
    | .nil => Empty
    | .cons head rest => head.Val C ⊕ rest.Choice C
end

mutual
  /-- A value is valid: of a nominal type, as the carriers say; of the other types, when its
  parts are, when it is below its bound and of its size. -/
  def Ty.Valid {V : Vocabulary} (C : Carriers V) : (τ : Ty V.TypeKey) → τ.Val C → Prop
    | .bool, _ => True
    | .nat, _ => True
    | .fin n, v => v < n
    | .seq item size, vs =>
        (∀ v, v ∈ vs → item.Valid C v) ∧ (∀ n, size = some n → vs.length = n)
    | .tuple items, vs => items.Valid C vs
    | .record _ _ fields, vs => fields.Valid C vs
    | .variant _ alternatives, v => alternatives.ValidChoice C v
    | .nominal key, v => C.valid key v
  def Tys.Valid {V : Vocabulary} (C : Carriers V) : (τs : Tys V.TypeKey) → τs.Val C → Prop
    | .nil, _ => True
    | .cons head rest, (v, vs) => head.Valid C v ∧ rest.Valid C vs
  def Tys.ValidChoice {V : Vocabulary} (C : Carriers V) :
      (τs : Tys V.TypeKey) → τs.Choice C → Prop
    | .nil, v => nomatch v
    | .cons head _, .inl v => head.Valid C v
    | .cons _ rest, .inr v => rest.ValidChoice C v
end

/-- A model of a vocabulary. -/
structure Model (V : Vocabulary) extends Carriers V where
  /-- A row; `none` outside the domain of a restricted row. -/
  apply : ∀ (row : V.RowKey) (signature : RowSignature V.TypeKey V.RowKey),
    V.row row = some signature →
    HList (Ty.Val toCarriers) signature.ins → Option (HList (Ty.Val toCarriers) signature.outs)
  /-- Whether the inputs are in the domain of a row. -/
  inDomain : ∀ (row : V.RowKey) (signature : RowSignature V.TypeKey V.RowKey),
    V.row row = some signature → HList (Ty.Val toCarriers) signature.ins → Bool
  /-- A row gives its outputs exactly on its domain. -/
  defined : ∀ row signature (h : V.row row = some signature) args,
    (apply row signature h args).isSome = inDomain row signature h args
  /-- A pure row is everywhere in its domain. -/
  total : ∀ row signature (h : V.row row = some signature) args,
    signature.kind = .pure → inDomain row signature h args = true
  /-- The domain of a restricted row is what its domain row gives at the same inputs. -/
  decides : ∀ row signature (h : V.row row = some signature) domain
    (kind : signature.kind = .restricted domain) args,
    apply domain ⟨signature.ins, [.bool], .pure⟩ (V.decided row signature domain h kind) args =
      some (.cons (inDomain row signature h args) .nil)
  /-- Every row keeps validity. -/
  keeps : ∀ row signature (h : V.row row = some signature) args outs,
    args.All (Ty.Valid toCarriers) → apply row signature h args = some outs →
      outs.All (Ty.Valid toCarriers)
  /-- A literal of the vocabulary has a value, and the value is valid. -/
  literals : ∀ key n, V.literal key n = true →
    ∃ v, toCarriers.literal key n = some v ∧ toCarriers.valid key v
  /-- The support of a law at its inputs. -/
  support : ∀ (law : V.LawKey) (signature : LawSignature V.TypeKey),
    V.law law = some signature →
    HList (Ty.Val toCarriers) signature.ins → signature.out.Val toCarriers → Prop
  /-- What a law gives is valid. -/
  supported : ∀ law signature (h : V.law law = some signature) args out,
    args.All (Ty.Valid toCarriers) → support law signature h args out → Ty.Valid toCarriers _ out

abbrev Model.Val {V : Vocabulary} (M : Model V) (τ : V.Ty) : Type := τ.Val M.toCarriers

end Zkc.Core

namespace Zkc.Core

abbrev Model.Valid {V : Vocabulary} (M : Model V) (τ : V.Ty) (v : M.Val τ) : Prop :=
  Ty.Valid M.toCarriers τ v

section
variable {V : Vocabulary} {M : Model V}

theorem all_append : ∀ {as bs : List V.Ty} (xs : HList M.Val as) (ys : HList M.Val bs),
    (xs.append ys).All M.Valid ↔ xs.All M.Valid ∧ ys.All M.Valid
  | [], _, .nil, _ => by simp [HList.append, HList.All]
  | _ :: _, _, .cons x xs, ys => by
      simp only [HList.append, HList.all_cons, all_append xs ys, and_assoc]

end

end Zkc.Core
