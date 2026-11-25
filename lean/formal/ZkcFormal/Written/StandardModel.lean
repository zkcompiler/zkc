module

public import ZkcFormal.Written.StandardDefaults

@[expose] public section
set_option autoImplicit false

namespace ZkcFormal.Written.StandardModel
open Zkc.Core StandardDefaults

/-- Evaluation data for the standard rows used by the group and pair-round consumers.
A caller supplies operations on its carriers. The model constructs the typed rows, guards,
and proofs of preservation once for all such callers. -/
structure Data (F G : Type) extends Operations F G where
  scalarAdd : F → F → F
  zeroPoint : G
  unit : {x : F // x ≠ zero}
  literal : Nat → F
  literalZero : literal 0 = zero
  invNonzero : ∀ x, x ≠ zero → inv x ≠ zero

variable {F G : Type} (D : Data F G) [DecidableEq F] [DecidableEq G]

/-- The carriers implemented by the standard model. Refined scalars carry their proof. -/
abbrev carrierEntry : Standard.TypeKey → Option Type
  | .inl (.field .bls12381Fr) => some F
  | .inl (.nonzero .bls12381Fr) => some { x : F // x ≠ D.zero }
  | .inl (.group .g1) => some G
  | _ => none

/-- The total interpretation uses a singleton for a nominal sort without a carrier entry. -/
abbrev Carrier (k : Standard.TypeKey) : Type :=
  match carrierEntry D k with
  | some ty => ty
  | none => Unit

/-- The small test fields may have a different characteristic from the source field.
The scalar literals used by the examples are 0 and 1. Every admitted refined literal must
still denote an inhabitant, even if its natural representative vanishes in this field. -/
def nominalLiteral : (k : Standard.TypeKey) → Nat → Carrier D k
  | .inl (.field .bls12381Fr), n => (D.literal n)
  | .inl (.nonzero .bls12381Fr), n => if h : (D.literal n) = D.zero then D.unit else ⟨D.literal n,h⟩
  | .inl (.group .g1), _ => D.zeroPoint
  | .inl (.group .g2), _ | .inl (.group .gt), _
  | .inl (.field .koalaBear), _ | .inl (.field .koalaBear4), _
  | .inl (.nonzero .koalaBear), _ | .inl (.nonzero .koalaBear4), _ | .inr _, _ => ()

abbrev carriers : Carriers Standard where
  Carrier := Carrier D
  valid _ _ := True
  literal k n := if Standard.literal k n then some (nominalLiteral D k n) else none

def defaultNominal (k : Standard.TypeKey) : Sample (carriers D) (.nominal k) :=
  ⟨nominalLiteral D k 0, trivial⟩

abbrev Sig := RowSignature Standard.TypeKey Standard.RowKey

structure Output (sig : Sig) (args : HList (Ty.Val (carriers D)) sig.ins) where
  values : HList (Ty.Val (carriers D)) sig.outs
  keeps : args.All (Ty.Valid (carriers D)) → values.All (Ty.Valid (carriers D))

def domain (k : Standard.RowKey) (sig : Sig) (known : Standard.row k = some sig)
    (args : HList (Ty.Val (carriers D)) sig.ins) : Bool :=
  if h : k = fr .nonzero then by
    subst k; cases known; cases args; rename_i x tail; cases tail
    change F at x
    exact decide (x ≠ D.zero)
  else true

abbrev Row (k : Standard.RowKey) :=
  (sig : Sig) → (h : Standard.row k = some sig) →
    (args : HList (Ty.Val (carriers D)) sig.ins) → domain D k sig h args = true → Output D sig args

def defaultRow (k : Standard.RowKey) : Row D k := fun sig h _ _ ↦
  let sample := rowSamples (defaultNominal D) k sig h
  ⟨sample.values, fun _ ↦ sample.valid⟩

abbrev scalarSeq (op : Zkc.Vocabulary.SeqRow) (size : Option Nat) : Standard.RowKey :=
  .inl (.seq op (.atom (.field .bls12381Fr)) size)

/-- The output is specified on all inputs. Preservation only assumes the source signature's
input validity, including the lengths of sized sequences. -/
def vectorBinary (f : F → F → F) (n : Nat) {k : Standard.RowKey}
    (typed : Standard.row k = some ⟨[.seq scalarTy (some n), .seq scalarTy (some n)],
      [.seq scalarTy (some n)], .pure⟩) : Row D k := by
  intro sig known args permitted
  rw [typed] at known
  cases known
  cases args; rename_i xs tail; cases tail; rename_i ys tail; cases tail
  refine ⟨.cons (List.zipWith f xs ys) .nil, ?_⟩
  rintro ⟨⟨_, lenX⟩, ⟨_, lenY⟩, _⟩
  refine ⟨⟨fun _ _ ↦ trivial, ?_⟩, trivial⟩
  intro _ eq
  cases eq
  change (List.zipWith f (xs : List F) ys).length = n
  rw [List.length_zipWith, lenX n rfl, lenY n rfl, Nat.min_self]

def vectorScale (n : Nat) : Row D (scalarSeq .scale (some n)) := by
  intro sig known args permitted
  cases known
  cases args; rename_i xs tail; cases tail; rename_i r tail; cases tail
  change List F at xs
  change F at r
  refine ⟨.cons (List.map (fun (v : F) ↦ D.mul v r) xs) .nil, ?_⟩
  rintro ⟨⟨_, len⟩, _⟩
  exact ⟨⟨fun _ _ ↦ trivial, fun n eq ↦ (List.length_map ..).trans (len n eq)⟩, trivial⟩

def vectorSum (size : Option Nat) : Row D (scalarSeq .sum size) := by
  intro sig known args permitted
  cases known
  cases args; rename_i xs tail; cases tail
  exact ⟨.cons (List.foldr D.scalarAdd D.zero xs) .nil, fun _ ↦ ⟨trivial, trivial⟩⟩

/-- Two sequences of field elements are equal: entry by entry, and of one length. -/
def vectorEqual (size : Option Nat) : Row D (scalarSeq .equal size) := by
  intro sig known args permitted
  cases known
  cases args; rename_i xs tail; cases tail; rename_i ys tail; cases tail
  change List F at xs
  change List F at ys
  exact ⟨.cons (decide (xs = ys)) .nil, fun _ ↦ ⟨trivial, trivial⟩⟩

local macro "unary_row " f:term : term => `(by
  intro sig known args permitted; cases known; cases args; rename_i x tail; cases tail
  exact ⟨.cons ($f x) .nil, fun _ ↦ ⟨trivial, trivial⟩⟩)
local macro "binary_row " f:term : term => `(by
  intro sig known args permitted; cases known; cases args; rename_i x tail; cases tail; rename_i y tail; cases tail
  exact ⟨.cons ($f x y) .nil, fun _ ↦ ⟨trivial, trivial⟩⟩)

/-- The rows that the model interprets, each with its meaning; none for every other row of the
vocabulary. This is the one table of the interpreted rows: the meaning of a row (`row`) and
whether a row is interpreted (`interprets`) are both read from it. Typed dispatch transports
arguments and results together. -/
def arm : (k : Standard.RowKey) → Option (Row D k)
  | .inl (.group .scale (.group .g1)) => some (binary_row D.scale)
  | .inl (.group .add (.group .g1)) => some (binary_row D.add)
  | .inl (.group .equal (.group .g1)) => some (binary_row (fun (p q : G) ↦ decide (p = q)))
  | .inl (.field .add .bls12381Fr .all) => some (binary_row D.scalarAdd)
  | .inl (.field .sub .bls12381Fr .all) => some (binary_row D.sub)
  | .inl (.field .mul .bls12381Fr .all) => some (binary_row D.mul)
  | .inl (.field .neg .bls12381Fr .all) => some (unary_row (fun (x : F) ↦ D.sub D.zero x))
  | .inl (.field .equal .bls12381Fr .all) => some (binary_row (fun (x y : F) ↦ decide (x = y)))
  | .inl (.field .nonzero .bls12381Fr .all) => some (by
    intro sig known args permitted
    cases known; cases args; rename_i x tail; cases tail
    change F at x
    have nz : x ≠ D.zero := of_decide_eq_true permitted
    exact ⟨.cons ⟨x,nz⟩ .nil, fun _ ↦ ⟨trivial, trivial⟩⟩)
  | .inl (.field .isNonzero .bls12381Fr .all) => some (unary_row (fun (x : F) ↦ decide (x ≠ D.zero)))
  | .inl (.field .inverse .bls12381Fr .nonzero) => some
    (unary_row (fun (x : {x : F // x ≠ D.zero}) ↦ (⟨D.inv x.val, D.invNonzero x.val x.property⟩ : {x : F // x ≠ D.zero})))
  | .inl (.field .fromNonzero .bls12381Fr .nonzero) => some (unary_row (fun (x : {x : F // x ≠ D.zero}) ↦ x.val))
  | .inl (.seq .add (.atom (.field .bls12381Fr)) (some n)) => some (vectorBinary D D.scalarAdd n rfl)
  | .inl (.seq .sub (.atom (.field .bls12381Fr)) (some n)) => some (vectorBinary D D.sub n rfl)
  | .inl (.seq .scale (.atom (.field .bls12381Fr)) (some n)) => some (vectorScale D n)
  | .inl (.seq .sum (.atom (.field .bls12381Fr)) n) => some (vectorSum D n)
  | .inl (.seq .equal (.atom (.field .bls12381Fr)) n) => some (vectorEqual D n)
  | _ => none

/-- Meaning at semantic row keys: the arm of the table, and for a row that the table does not
have, a constant (`defaultRow`), which is a meaning and not the intended one. -/
def row (k : Standard.RowKey) : Row D k := (arm D k).getD (defaultRow D k)

/-- A row outside the table is given the default. -/
theorem row_eq_default (k : Standard.RowKey) (outside : arm D k = none) :
    row D k = defaultRow D k := by
  simp [row, outside]

/-- The algebra of two elements, at which the table is read: whether a row has an arm does not
depend on the algebra. -/
def tableData : Data Bool Bool where
  zero := false
  sub := xor
  mul := and
  inv := id
  add := xor
  scale := and
  scalarAdd := xor
  zeroPoint := false
  unit := ⟨true, by decide⟩
  literal n := n % 2 == 1
  literalZero := rfl
  invNonzero := by intro x h; exact h

/-- The rows that the standard model interprets: those that the table (`arm`) has. A result
over the model is about a program whose rows are all interpreted. -/
def interprets (k : Standard.RowKey) : Bool := (arm tableData k).isSome

/-- **The table is one.** For every algebra, a row has an arm in the model exactly when it is
interpreted: an entry of the table is an arm of the model, and an arm is an entry. -/
theorem interprets_iff_arm (k : Standard.RowKey) : interprets k = (arm D k).isSome := by
  unfold interprets arm
  split <;> rfl

def model : Model Standard := {
  carriers D with
  apply := fun k s h args ↦ if granted : domain D k s h args then
    some (row D k s h args granted).values else none
  inDomain := domain D
  defined := by intros; split <;> simp_all
  total := by
    intro k s h args pureRow
    unfold domain; split
    · subst k; cases h; cases pureRow
    · rfl
  decides := by
    intro k s h d hk args
    obtain ⟨f,rfl,rfl⟩ := restricted h hk
    cases f <;> cases h <;> cases args with | cons x tail => cases tail; rfl
  keeps := by
    intro k s h args values valid ran
    split at ran
    · rename_i granted
      cases ran; exact (row D k s h args granted).keeps valid
    · contradiction
  literals := by intro k n accepted; exact ⟨_, ite_eq_left accepted, trivial⟩
  support := fun _ s _ _ v ↦ s.out.Valid (carriers D) v
  supported := by intros; assumption }

instance : DecidableEq ((model D).Val pointTy) := inferInstanceAs (DecidableEq G)
instance : DecidableEq ((model D).Val scalarTy) := inferInstanceAs (DecidableEq F)

theorem groupRows : GroupRows (model D) (D.toOperations) where
  scale := by intros; rfl
  add := by intros; rfl
  equal := by intros; rfl

def functionRows : FunctionRows (model D) (D.toOperations) where
  pack x h := ⟨x,h⟩
  unpack := Subtype.val
  invert := fun x ↦ ⟨D.inv x.val, D.invNonzero x.val x.property⟩
  sub := by intros; rfl
  mul := by intros; rfl
  equal := by intros; rfl
  test := by intros; rfl
  refine := by
    intro x
    change F at x
    change (if nz : decide (x ≠ D.zero) = true then some (.cons ⟨x, of_decide_eq_true nz⟩ .nil) else none :
      Option (HList (Ty.Val (carriers D)) [nzTy])) =
        if h : x = D.zero then none else some (.cons ⟨x,h⟩ .nil)
    by_cases h : x = D.zero <;> simp [h]
  inverse := by intros; rfl
  forget := by intros; rfl
  roundTrip := by intros; rfl
  inverseScalar := by intros; rfl
  zero := by intro h; exact D.literalZero

theorem unpack_ne_zero (v : (model D).Val nzTy) :
    (functionRows D).unpack v ≠ D.zero := v.property

end ZkcFormal.Written.StandardModel
