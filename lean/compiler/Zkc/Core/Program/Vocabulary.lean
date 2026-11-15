module

public import Zkc.Core.Program.Identity

@[expose] public section

/-!
Types, the vocabulary and its models.

The core is parameterised by a vocabulary: the keys of nominal types, of rows and of laws,
and the signature and the kind of each at its static arguments. The values of `bool`, of
naturals, of sequences, tuples, records and variants, and the operations on them, are the
core's own. A model gives each nominal type a carrier and says which values are valid; every
row keeps validity.
-/

namespace Zkc.Core

/-! ## Contexts and environments -/

inductive Var {α : Type} : List α → α → Type where
  | head {a : α} {rest : List α} : Var (a :: rest) a
  | tail {a b : α} {rest : List α} : Var rest a → Var (b :: rest) a

inductive HList {α : Type} (V : α → Type) : List α → Type where
  | nil : HList V []
  | cons {a : α} {rest : List α} : V a → HList V rest → HList V (a :: rest)

def HList.All {α : Type} {V : α → Type} (P : ∀ a, V a → Prop) :
    {items : List α} → HList V items → Prop
  | [], .nil => True
  | _ :: _, .cons v rest => P _ v ∧ rest.All P

def Env {α : Type} (V : α → Type) (Γ : List α) : Type := ∀ a, Var Γ a → V a

/-! ## Types -/

/-- A static argument of a nominal type, of a row or of a law: in an instance every size is
a literal. -/
inductive Static where
  | nat (n : Nat)
  | key (k : Key)
deriving DecidableEq, Repr

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
    | nominal (key : K) (statics : List Static)
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

structure RowSignature (K R : Type) where
  ins : List (Ty K)
  outs : List (Ty K)
  kind : RowKind R

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
  /-- The signature and the kind of a row at its static arguments; `none` when the row has
  no instance there. -/
  row : RowKey → List Static → Option (RowSignature TypeKey RowKey)
  law : LawKey → List Static → Option (LawSignature TypeKey)
  /-- Whether a nominal type has an instance at the static arguments. -/
  type : TypeKey → List Static → Bool
  /-- Whether a natural is a literal of a nominal type. -/
  literal : TypeKey → List Static → Nat → Bool
  /-- Whether a nominal type is linear at the static arguments: none is, unless said. -/
  linear : TypeKey → List Static → Bool := fun _ _ => false

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
    | .nominal key statics => V.linear key statics
  /-- One of the types is linear. -/
  def Tys.anyLinear (V : Vocabulary) : Tys V.TypeKey → Bool
    | .nil => false
    | .cons head rest => Ty.isLinear V head || Tys.anyLinear V rest
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
    | .nominal key statics, n :: rest => if V.literal key statics n then some rest else none
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
  Carrier : V.TypeKey → List Static → Type
  valid : ∀ key statics, Carrier key statics → Prop
  /-- The value of a literal. -/
  literal : ∀ key statics, Nat → Option (Carrier key statics)

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
    | .nominal key statics => C.Carrier key statics
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
    | .nominal key statics, v => C.valid key statics v
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
  /-- A row at its static arguments; `none` outside the domain of a restricted row. -/
  apply : ∀ (row : V.RowKey) (statics : List Static) (signature : RowSignature V.TypeKey V.RowKey),
    V.row row statics = some signature →
    HList (Ty.Val toCarriers) signature.ins → Option (HList (Ty.Val toCarriers) signature.outs)
  /-- Whether the inputs are in the domain of a row. -/
  inDomain : ∀ (row : V.RowKey) (statics : List Static) (signature : RowSignature V.TypeKey V.RowKey),
    V.row row statics = some signature → HList (Ty.Val toCarriers) signature.ins → Bool
  /-- A row gives its outputs exactly on its domain. -/
  defined : ∀ row statics signature (h : V.row row statics = some signature) args,
    (apply row statics signature h args).isSome = inDomain row statics signature h args
  /-- A pure row is everywhere in its domain. -/
  total : ∀ row statics signature (h : V.row row statics = some signature) args,
    signature.kind = .pure → inDomain row statics signature h args = true
  /-- The domain of a row restricted by `domain` is what `domain` gives at the same static
  arguments and the same inputs, when its signature has those inputs and one `bool`
  output. -/
  decides : ∀ row statics signature (h : V.row row statics = some signature)
    (domain : V.RowKey) (decider : RowSignature V.TypeKey V.RowKey)
    (hd : V.row domain statics = some decider) (ins : decider.ins = signature.ins)
    (outs : decider.outs = [.bool]) args,
    signature.kind = .restricted domain →
    apply domain statics decider hd (cast (congrArg (HList (Ty.Val toCarriers)) ins.symm) args) =
      some (cast (congrArg (HList (Ty.Val toCarriers)) outs.symm)
        (.cons (inDomain row statics signature h args) .nil))
  /-- Every row keeps validity. -/
  keeps : ∀ row statics signature (h : V.row row statics = some signature) args outs,
    args.All (Ty.Valid toCarriers) → apply row statics signature h args = some outs → outs.All (Ty.Valid toCarriers)
  /-- A literal of the vocabulary has a value, and the value is valid. -/
  literals : ∀ key statics n, V.literal key statics n = true →
    ∃ v, toCarriers.literal key statics n = some v ∧ toCarriers.valid key statics v
  /-- The support of a law at its inputs. -/
  support : ∀ (law : V.LawKey) (statics : List Static) (signature : LawSignature V.TypeKey),
    V.law law statics = some signature →
    HList (Ty.Val toCarriers) signature.ins → signature.out.Val toCarriers → Prop
  /-- What a law gives is valid. -/
  supported : ∀ law statics signature (h : V.law law statics = some signature) args out,
    args.All (Ty.Valid toCarriers) → support law statics signature h args out → Ty.Valid toCarriers _ out

abbrev Model.Val {V : Vocabulary} (M : Model V) (τ : V.Ty) : Type := τ.Val M.toCarriers

end Zkc.Core

namespace Zkc.Core

abbrev Model.Valid {V : Vocabulary} (M : Model V) (τ : V.Ty) (v : M.Val τ) : Prop :=
  Ty.Valid M.toCarriers τ v

end Zkc.Core
