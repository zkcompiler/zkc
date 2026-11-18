module

public import Zkc.Formal.Written.FunctionMeaning

@[expose] public section
set_option autoImplicit false

namespace Zkc.Formal.Written.FiniteModel
open Core

/-- A small interpretation for executable nonvacuity checks. All nominal carriers have two
values. Unused standard rows supply valid defaults. The three verifier rows are interpreted
in the additive group and scalar field of order two. -/
def carriers : Carriers Standard where
  Carrier _ := Bool
  valid _ _ := True
  literal _ n := some (n % 2 == 1)

structure Sample (t : Standard.Ty) where
  value : t.Val carriers
  valid : t.Valid carriers value

def truth : Sample (.bool : Standard.Ty) := ⟨true, trivial⟩
def nominal (k : Standard.TypeKey) : Sample (.nominal k) := ⟨false, trivial⟩
def bounded (n : Nat) (h : 0 < n) : Sample (.fin n : Standard.Ty) := ⟨0, h⟩
def sequence {t : Standard.Ty} (s : Sample t) (size : Option Nat) : Sample (.seq t size) where
  value := List.replicate (size.getD 0) s.value
  valid := by
    constructor
    · intro v h
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp h
      exact s.valid
    · intro n eq
      simp [eq]

abbrev lifted (t : Zkc.Vocabulary.Ty) : Standard.Ty := t.mapNominal Sum.inl

def atomSample (a : Zkc.Vocabulary.Atom) : Sample (lifted a.ty) := by
  cases a <;> exact nominal _

def elementSample : (item : Zkc.Vocabulary.Element) → Sample (lifted item.ty)
  | .atom a => atomSample a
  | .sized item n => sequence (elementSample item) (some n)

structure Samples (ts : List Standard.Ty) where
  values : HList (Ty.Val carriers) ts
  valid : values.All (Ty.Valid carriers)

def single {t : Standard.Ty} (v : Sample t) : Samples [t] := ⟨.cons v.value .nil, v.valid, trivial⟩

macro "default_output" : tactic => `(tactic| first
  | exact single truth
  | exact single (nominal _)
  | exact single (bounded _ (by decide))
  | exact single (sequence (nominal _) _)
  | exact single (sequence (bounded _ (by decide)) _))

set_option maxHeartbeats 2000000 in
/-- Every output signature admitted by the linked standard table has a valid inhabitant. -/
def rowSamples (k : Standard.RowKey) (sig : RowSignature Standard.TypeKey Standard.RowKey)
    (h : Standard.row k = some sig) : Samples sig.outs := by
  cases k with
  | inr => cases h
  | inl key =>
    cases key with
    | field op f among =>
      cases op <;> cases f <;> cases among <;> cases h <;> default_output
    | group op a =>
      cases op <;> cases a <;> try rename_i g
      all_goals first | cases h <;> default_output | cases g <;> cases h <;> default_output
    | seq op item size =>
      let sample := elementSample item
      cases op <;> cases size <;> first
        | cases h <;> exact single sample
        | cases h <;> exact single (sequence sample _)
        | cases h <;> default_output
        | cases item with
          | sized => cases h
          | atom a => cases a <;> cases h <;> default_output
    | hash kind => cases kind <;> cases h <;> default_output
    | pair => cases h; default_output

def sameBit (a b : Bool) := decide (a = b)

abbrev Matches (key : Standard.RowKey) (row : Zkc.Vocabulary.RowKey) :=
  key = (.inl row : Standard.RowKey)

instance (k : Standard.RowKey) (r : Zkc.Vocabulary.RowKey) : Decidable (Matches k r) :=
  Standard.decRowKey k (.inl r)

def interpreted (k : Standard.RowKey) (sig : RowSignature Standard.TypeKey Standard.RowKey)
    (ok : Standard.row k = some sig) (args : HList (Ty.Val carriers) sig.ins) : Samples sig.outs :=
  if h : Matches k (.group .scale (.group .g1)) then by
    unfold Matches at h
    subst k; cases ok
    match args with | .cons p (.cons x .nil) => exact ⟨.cons (p && x) .nil, trivial, trivial⟩
  else if h : Matches k (.group .add (.group .g1)) then by
    unfold Matches at h
    subst k; cases ok
    match args with | .cons p (.cons q .nil) => exact ⟨.cons (xor p q) .nil, trivial, trivial⟩
  else if h : Matches k (.group .equal (.group .g1)) then by
    unfold Matches at h
    subst k; cases ok
    match args with | .cons p (.cons q .nil) => exact ⟨.cons (sameBit p q) .nil, trivial, trivial⟩
  else if h : Matches k (.field .sub .bls12381Fr .all) then by
    unfold Matches at h; subst k; cases ok
    match args with | (.cons x (.cons y .nil)) => exact ⟨.cons (xor x y) .nil, trivial, trivial⟩
  else if h : Matches k (.field .mul .bls12381Fr .all) then by
    unfold Matches at h; subst k; cases ok
    match args with | (.cons x (.cons y .nil)) => exact ⟨.cons (x && y) .nil, trivial, trivial⟩
  else if h : Matches k (.field .equal .bls12381Fr .all) then by
    unfold Matches at h; subst k; cases ok
    match args with | (.cons x (.cons y .nil)) => exact ⟨.cons (sameBit x y) .nil, trivial, trivial⟩
  else if h : Matches k (.field .isNonzero .bls12381Fr .all) then by
    unfold Matches at h; subst k; cases ok
    match args with | (.cons x .nil) => exact ⟨.cons (x) .nil, trivial, trivial⟩
  else if h : Matches k (.field .nonzero .bls12381Fr .all) then by
    unfold Matches at h; subst k; cases ok
    match args with | (.cons x .nil) => exact ⟨.cons (x) .nil, trivial, trivial⟩
  else if h : Matches k (.field .inverse .bls12381Fr .nonzero) then by
    unfold Matches at h; subst k; cases ok
    match args with | (.cons x .nil) => exact ⟨.cons (x) .nil, trivial, trivial⟩
  else if h : Matches k (.field .fromNonzero .bls12381Fr .nonzero) then by
    unfold Matches at h; subst k; cases ok
    match args with | (.cons x .nil) => exact ⟨.cons (x) .nil, trivial, trivial⟩
  else rowSamples k sig ok

private theorem restricted {k : Standard.RowKey} {sig : RowSignature Standard.TypeKey Standard.RowKey}
    {d} (h : Standard.row k = some sig) (hk : sig.kind = .restricted d) :
    ∃ f, k = .inl (.field .nonzero f .all) ∧ d = .inl (.field .isNonzero f .all) := by
  cases k with
  | inr => cases h
  | inl key =>
    cases key with
    | field op f among => cases op <;> cases f <;> cases among <;> cases h <;> cases hk <;> exact ⟨_, rfl, rfl⟩
    | group op a => cases op <;> cases a <;> first | cases h <;> cases hk | rename_i g; cases g <;> cases h <;> cases hk
    | seq op item size =>
      cases op <;> cases size <;> first
        | cases h <;> cases hk
        | cases item with
          | sized => cases h
          | atom a => cases a <;> cases h <;> cases hk
    | hash kind => cases kind <;> cases h <;> cases hk
    | pair => cases h; cases hk

def domain (k : Standard.RowKey) (sig : RowSignature Standard.TypeKey Standard.RowKey)
    (ok : Standard.row k = some sig) (args : HList (Ty.Val carriers) sig.ins) : Bool :=
  if h : Matches k (.field .nonzero .bls12381Fr .all) then by
    unfold Matches at h; subst k; cases ok
    match args with | .cons x .nil => exact x
  else true

def model : Model Standard := {
  carriers with
  apply := fun k sig h args => if domain k sig h args then some (interpreted k sig h args).values else none
  inDomain := domain
  defined := by intros; split <;> simp_all
  total := by
    intro k sig ok args pureRow
    unfold domain
    split
    · rename_i key; unfold Matches at key; subst k; cases ok; cases pureRow
    · rfl
  decides := by
    intro k sig h d hk args
    obtain ⟨f,rfl,rfl⟩ := restricted h hk
    cases f <;> cases h
    all_goals cases args with | cons x tail => cases tail; cases x <;> rfl
  keeps := by
    intro k sig h args vals _ eq
    split at eq
    · cases eq; exact (interpreted k sig h args).valid
    · contradiction
  literals := by intro k n _; exact ⟨_, rfl, trivial⟩
  support := fun _ sig _ _ v => sig.out.Valid carriers v
  supported := by intros; assumption }

def ops : Operations Bool Bool := ⟨false, xor, and, id, xor, and⟩

def laws : ActionLaws ops where
  one := true
  difference := xor
  sub_zero := by decide
  cancel_left := by decide
  scale_sub := by decide
  scale_mul := by decide
  scale_one := by decide
  mul_inv := by decide

instance pointEq : DecidableEq (model.Val pointTy) := inferInstanceAs (DecidableEq Bool)
instance scalarEq : DecidableEq (model.Val scalarTy) := inferInstanceAs (DecidableEq Bool)

theorem rows : GroupRows model ops where
  scale := by intros; rfl
  add := by intros; rfl
  equal := by intro p q; cases p <;> cases q <;> rfl

def functionRows : FunctionRows model ops where
  pack := fun x _ => x
  unpack := id
  invert := id
  sub := by intros; rfl
  mul := by intros; rfl
  equal := by intro x y; cases x <;> cases y <;> rfl
  test := by intro x; cases x <;> rfl
  refine := by intro x; cases x <;> rfl
  inverse := by intros; rfl
  forget := by intros; rfl
  roundTrip := by intros; rfl
  inverseScalar := by intros; rfl
  zero := by intros; rfl

end Zkc.Formal.Written.FiniteModel
