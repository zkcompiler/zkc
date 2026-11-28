module

public import Zkc.Vocabulary.Project
public import Zkc.Runtime.Crypto.Suites
public import Zkc.Core.Format.Canonical

@[expose] public section
set_option autoImplicit false

/-!
Concrete `Core.Model` instances for both the standard vocabulary (`standardModel`) and any
project-linked vocabulary (`linkedModel?`):
- `standardModel : Core.Model Zkc.Vocabulary.standard`: implements every field, group, sequence,
  hash (`sha256`, `keccak256`, `shake128`, `shake256`), and pairing row with proved validity
  preservation (`keeps`), totality (`total`), domain agreement (`decides`), and literal/law support.
- `linkedModel? (b : Project.Bindings) : Except String (Core.Model b.vocabulary)`: lifts
  `standardModel` onto `.inl` rows and implements all runtime suite, layout, and signature
  primitives bound in `b` (`Merlin 1.0`, `CFRG SHAKE128 / TurboSHAKE128`, `Poseidon2-KoalaBear`,
  `layout.canonical`, `signature.*`, `group.to_bytes`).
-/

namespace Zkc.Runtime

open Zkc.Core
open Zkc.Vocabulary
open Zkc.Vocabulary.Project
open Zkc.Runtime.Crypto

/-! ## Concrete carriers for `Zkc.Vocabulary.standard` -/

/-- Carrier types for nominal types of `Zkc.Vocabulary.standard`. -/
abbrev StandardCarrier : TypeKey → Type
  | .field .koalaBear => Nat
  | .field .koalaBear4 => List Nat
  | .field .bls12381Fr => Nat
  | .nonzero .koalaBear => Nat
  | .nonzero .koalaBear4 => List Nat
  | .nonzero .bls12381Fr => Nat
  | .group .g1 => G1Point
  | .group .g2 => Nat
  | .group .gt => Nat

/-- Coordinate-level validity for affine BLS12-381 `G1` points (full curve & subgroup checks are
enforced strictly on wire deserialization in `decompressG1`). -/
def G1CoordValid : G1Point → Prop
  | none => True
  | some (x, y) => x < bls12381FqOrder ∧ y < bls12381FqOrder

/-- Validity predicate for nominal carriers of `Zkc.Vocabulary.standard`. -/
abbrev StandardValid : (k : TypeKey) → StandardCarrier k → Prop
  | .field .koalaBear, v => v < koalaBearOrder
  | .field .koalaBear4, v => Ext4Valid v
  | .field .bls12381Fr, v => v < bls12381FrOrder
  | .nonzero .koalaBear, v => 0 < v ∧ v < koalaBearOrder
  | .nonzero .koalaBear4, v => Ext4Valid v ∧ ext4IsNonzero v = true
  | .nonzero .bls12381Fr, v => 0 < v ∧ v < bls12381FrOrder
  | .group .g1, p => G1CoordValid p
  | .group .g2, v => v < bls12381FrOrder
  | .group .gt, v => v < bls12381FrOrder

def standardLiteral : (k : TypeKey) → Nat → Option (StandardCarrier k)
  | .field .koalaBear, n => if n < koalaBearOrder then some n else none
  | .field .koalaBear4, n => if n < koalaBearOrder then some (ext4OfNat n) else none
  | .field .bls12381Fr, n => if n < bls12381FrOrder then some n else none
  | .nonzero .koalaBear, n => if 0 < n ∧ n < koalaBearOrder then some n else none
  | .nonzero .koalaBear4, n => if 0 < n ∧ n < koalaBearOrder then some (ext4OfNat n) else none
  | .nonzero .bls12381Fr, n => if 0 < n ∧ n < bls12381FrOrder then some n else none
  | .group _, _ => none

@[reducible] def standardCarriers : Carriers standard where
  Carrier := StandardCarrier
  valid := StandardValid
  literal := standardLiteral

/-! ## Field, group, and sequence operations on `standardCarriers` -/

theorem koalaBearOrder_pos : 0 < koalaBearOrder := by decide
theorem koalaBearOrder_gt1 : 1 < koalaBearOrder := by decide
theorem bls12381FrOrder_pos : 0 < bls12381FrOrder := by decide
theorem bls12381FrOrder_gt1 : 1 < bls12381FrOrder := by decide
theorem bls12381FqOrder_pos : 0 < bls12381FqOrder := by decide

theorem g1Neg_coordValid : ∀ p, G1CoordValid (g1Neg p)
  | none => trivial
  | some (_, _) => ⟨Nat.mod_lt _ bls12381FqOrder_pos, Nat.mod_lt _ bls12381FqOrder_pos⟩

theorem g1Add_coordValid : ∀ p q, G1CoordValid p → G1CoordValid q → G1CoordValid (g1Add p q)
  | none, _, _, hq => hq
  | some (_, _), none, hp, _ => hp
  | some (_, _), some (_, _), _, _ => by
      unfold g1Add
      dsimp only
      split
      · trivial
      · exact ⟨Nat.mod_lt _ bls12381FqOrder_pos, Nat.mod_lt _ bls12381FqOrder_pos⟩

theorem g1Sub_coordValid (p q : G1Point) (hp : G1CoordValid p) :
    G1CoordValid (g1Sub p q) :=
  g1Add_coordValid p (g1Neg q) hp (g1Neg_coordValid q)

theorem g1OfJac_coordValid (j : G1Jac) : G1CoordValid (g1OfJac j) := by
  rcases j with ⟨_, _, _⟩
  unfold g1OfJac
  dsimp only
  split
  · trivial
  · exact ⟨Nat.mod_lt _ bls12381FqOrder_pos, Nat.mod_lt _ bls12381FqOrder_pos⟩

theorem g1Scale_coordValid (p : G1Point) (s : Nat) : G1CoordValid (g1Scale p s) := by
  unfold g1Scale
  dsimp only
  split
  · trivial
  · exact g1OfJac_coordValid _

theorem g1Generator_coordValid : G1CoordValid g1Generator := by
  unfold g1Generator G1CoordValid bls12381FqOrder
  decide

def nzPrime (v order : Nat) : Nat :=
  let r := v % order
  if r == 0 then 1 else r

theorem nzPrime_valid (v order : Nat) (h : 1 < order) :
    0 < nzPrime v order ∧ nzPrime v order < order := by
  unfold nzPrime
  dsimp only
  split
  · omega
  · next hne =>
      have hne' : v % order ≠ 0 := by simpa using hne
      have hlt : v % order < order := Nat.mod_lt _ (by omega)
      omega

def nzExt4 (v : List Nat) : List Nat :=
  let n := ext4Norm v
  if ext4IsNonzero n then n else ext4One

theorem ext4One_isNonzero : ext4IsNonzero ext4One = true := by decide

theorem nzExt4_valid (v : List Nat) : Ext4Valid (nzExt4 v) ∧ ext4IsNonzero (nzExt4 v) = true := by
  unfold nzExt4
  dsimp only
  split
  · next h => exact ⟨ext4Norm_valid v, h⟩
  · exact ⟨ext4One_valid, ext4One_isNonzero⟩

/-- Field zero element in `StandardCarrier`. -/
def fieldZero : (f : Field) → StandardCarrier (.field f)
  | .koalaBear => 0
  | .koalaBear4 => ext4Zero
  | .bls12381Fr => 0

theorem fieldZero_valid : ∀ (f : Field), StandardValid (.field f) (fieldZero f)
  | .koalaBear => koalaBearOrder_pos
  | .koalaBear4 => ext4Zero_valid
  | .bls12381Fr => bls12381FrOrder_pos

/-- Field one element in `StandardCarrier`. -/
def fieldOne : (f : Field) → StandardCarrier (.field f)
  | .koalaBear => 1
  | .koalaBear4 => ext4One
  | .bls12381Fr => 1

theorem fieldOne_valid : ∀ (f : Field), StandardValid (.field f) (fieldOne f)
  | .koalaBear => koalaBearOrder_gt1
  | .koalaBear4 => ext4One_valid
  | .bls12381Fr => bls12381FrOrder_gt1

def fieldAdd : (f : Field) → StandardCarrier (.field f) → StandardCarrier (.field f) → StandardCarrier (.field f)
  | .koalaBear, a, b => addMod a b koalaBearOrder
  | .koalaBear4, a, b => ext4Add a b
  | .bls12381Fr, a, b => addMod a b bls12381FrOrder

theorem fieldAdd_valid : ∀ (f : Field) a b, StandardValid (.field f) (fieldAdd f a b)
  | .koalaBear, _, _ => Nat.mod_lt _ koalaBearOrder_pos
  | .koalaBear4, _, _ => ext4Add_valid ..
  | .bls12381Fr, _, _ => Nat.mod_lt _ bls12381FrOrder_pos

def fieldSub : (f : Field) → StandardCarrier (.field f) → StandardCarrier (.field f) → StandardCarrier (.field f)
  | .koalaBear, a, b => subMod a b koalaBearOrder
  | .koalaBear4, a, b => ext4Sub a b
  | .bls12381Fr, a, b => subMod a b bls12381FrOrder

theorem fieldSub_valid : ∀ (f : Field) a b, StandardValid (.field f) (fieldSub f a b)
  | .koalaBear, _, _ => Nat.mod_lt _ koalaBearOrder_pos
  | .koalaBear4, _, _ => ext4Sub_valid ..
  | .bls12381Fr, _, _ => Nat.mod_lt _ bls12381FrOrder_pos

def fieldMul : (f : Field) → StandardCarrier (.field f) → StandardCarrier (.field f) → StandardCarrier (.field f)
  | .koalaBear, a, b => mulMod a b koalaBearOrder
  | .koalaBear4, a, b => ext4Mul a b
  | .bls12381Fr, a, b => mulMod a b bls12381FrOrder

theorem fieldMul_valid : ∀ (f : Field) a b, StandardValid (.field f) (fieldMul f a b)
  | .koalaBear, _, _ => Nat.mod_lt _ koalaBearOrder_pos
  | .koalaBear4, _, _ => ext4Mul_valid ..
  | .bls12381Fr, _, _ => Nat.mod_lt _ bls12381FrOrder_pos

def fieldNeg : (f : Field) → StandardCarrier (.field f) → StandardCarrier (.field f)
  | .koalaBear, a => negMod a koalaBearOrder
  | .koalaBear4, a => ext4Neg a
  | .bls12381Fr, a => negMod a bls12381FrOrder

theorem fieldNeg_valid : ∀ (f : Field) a, StandardValid (.field f) (fieldNeg f a)
  | .koalaBear, _ => Nat.mod_lt _ koalaBearOrder_pos
  | .koalaBear4, _ => ext4Neg_valid ..
  | .bls12381Fr, _ => Nat.mod_lt _ bls12381FrOrder_pos

def fieldPow : (f : Field) → StandardCarrier (.field f) → Nat → StandardCarrier (.field f)
  | .koalaBear, a, e => modPow a e koalaBearOrder
  | .koalaBear4, a, e => ext4Pow a e
  | .bls12381Fr, a, e => modPow a e bls12381FrOrder

theorem fieldPow_valid : ∀ (f : Field) a e, StandardValid (.field f) (fieldPow f a e)
  | .koalaBear, a, e => modPow_lt a e koalaBearOrder koalaBearOrder_pos
  | .koalaBear4, a, e => ext4Pow_valid a e
  | .bls12381Fr, a, e => modPow_lt a e bls12381FrOrder bls12381FrOrder_pos

def fieldEqual : (f : Field) → StandardCarrier (.field f) → StandardCarrier (.field f) → Bool
  | .koalaBear, a, b => a % koalaBearOrder == b % koalaBearOrder
  | .koalaBear4, a, b => ext4Norm a == ext4Norm b
  | .bls12381Fr, a, b => a % bls12381FrOrder == b % bls12381FrOrder

def fieldIsNonzero : (f : Field) → StandardCarrier (.field f) → Bool
  | .koalaBear, a => a % koalaBearOrder != 0
  | .koalaBear4, a => ext4IsNonzero a
  | .bls12381Fr, a => a % bls12381FrOrder != 0

def fieldFromNat : (f : Field) → Nat → StandardCarrier (.field f)
  | .koalaBear, n => n % koalaBearOrder
  | .koalaBear4, n => ext4OfNat n
  | .bls12381Fr, n => n % bls12381FrOrder

theorem fieldFromNat_valid : ∀ (f : Field) n, StandardValid (.field f) (fieldFromNat f n)
  | .koalaBear, _ => Nat.mod_lt _ koalaBearOrder_pos
  | .koalaBear4, n => ext4OfNat_valid n
  | .bls12381Fr, _ => Nat.mod_lt _ bls12381FrOrder_pos

def fieldRoot : (f : Field) → Nat → StandardCarrier (.nonzero f)
  | .koalaBear, k => nzPrime (primeTwoAdicRoot koalaBearTwoAdicGen 24 koalaBearOrder k) koalaBearOrder
  | .koalaBear4, k => nzExt4 (ext4TwoAdicRoot k)
  | .bls12381Fr, k => nzPrime (primeTwoAdicRoot bls12381FrTwoAdicGen 32 bls12381FrOrder k) bls12381FrOrder

theorem fieldRoot_valid : ∀ (f : Field) k, StandardValid (.nonzero f) (fieldRoot f k)
  | .koalaBear, _ => nzPrime_valid _ _ koalaBearOrder_gt1
  | .koalaBear4, _ => nzExt4_valid _
  | .bls12381Fr, _ => nzPrime_valid _ _ bls12381FrOrder_gt1

def atomZero : (a : Atom) → a.ty.Val standardCarriers
  | .field f => fieldZero f
  | .group .g1 => (none : G1Point)
  | .group .g2 => (0 : Nat)
  | .group .gt => (0 : Nat)

theorem atomZero_valid : ∀ (a : Atom), a.ty.Valid standardCarriers (atomZero a)
  | .field f => fieldZero_valid f
  | .group .g1 => trivial
  | .group .g2 => bls12381FrOrder_pos
  | .group .gt => bls12381FrOrder_pos

def atomAdd : (a : Atom) → a.ty.Val standardCarriers → a.ty.Val standardCarriers → a.ty.Val standardCarriers
  | .field f, x, y => fieldAdd f x y
  | .group .g1, x, y => g1Add x y
  | .group .g2, x, y => addMod x y bls12381FrOrder
  | .group .gt, x, y => addMod x y bls12381FrOrder

theorem atomAdd_valid : ∀ (a : Atom) x y,
    a.ty.Valid standardCarriers x → a.ty.Valid standardCarriers y →
    a.ty.Valid standardCarriers (atomAdd a x y)
  | .field f, x, y, _, _ => fieldAdd_valid f x y
  | .group .g1, x, y, hx, hy => g1Add_coordValid x y hx hy
  | .group .g2, _, _, _, _ => Nat.mod_lt _ bls12381FrOrder_pos
  | .group .gt, _, _, _, _ => Nat.mod_lt _ bls12381FrOrder_pos

def atomNeg : (a : Atom) → a.ty.Val standardCarriers → a.ty.Val standardCarriers
  | .field f, x => fieldNeg f x
  | .group .g1, x => g1Neg x
  | .group .g2, x => negMod x bls12381FrOrder
  | .group .gt, x => negMod x bls12381FrOrder

theorem atomNeg_valid : ∀ (a : Atom) x, a.ty.Valid standardCarriers (atomNeg a x)
  | .field f, x => fieldNeg_valid f x
  | .group .g1, x => g1Neg_coordValid x
  | .group .g2, _ => Nat.mod_lt _ bls12381FrOrder_pos
  | .group .gt, _ => Nat.mod_lt _ bls12381FrOrder_pos

def atomSub (a : Atom) (x y : a.ty.Val standardCarriers) : a.ty.Val standardCarriers :=
  atomAdd a x (atomNeg a y)

theorem atomSub_valid (a : Atom) (x y : a.ty.Val standardCarriers)
    (hx : a.ty.Valid standardCarriers x) : a.ty.Valid standardCarriers (atomSub a x y) :=
  atomAdd_valid a x (atomNeg a y) hx (atomNeg_valid a y)

def atomScale : (a : Atom) → a.ty.Val standardCarriers → a.scalar.ty.Val standardCarriers → a.ty.Val standardCarriers
  | .field f, x, s => fieldMul f x s
  | .group .g1, x, s => g1Scale x s
  | .group .g2, x, s => mulMod x s bls12381FrOrder
  | .group .gt, x, s => mulMod x s bls12381FrOrder

theorem atomScale_valid : ∀ (a : Atom) x s, a.ty.Valid standardCarriers (atomScale a x s)
  | .field f, x, s => fieldMul_valid f x s
  | .group .g1, x, s => g1Scale_coordValid x s
  | .group .g2, _, _ => Nat.mod_lt _ bls12381FrOrder_pos
  | .group .gt, _, _ => Nat.mod_lt _ bls12381FrOrder_pos

def atomEqual : (a : Atom) → a.ty.Val standardCarriers → a.ty.Val standardCarriers → Bool
  | .field f, x, y => fieldEqual f x y
  | .group .g1, x, y =>
      let x : G1Point := x
      let y : G1Point := y
      x == y
  | .group .g2, x, y =>
      let x : Nat := x
      let y : Nat := y
      x % bls12381FrOrder == y % bls12381FrOrder
  | .group .gt, x, y =>
      let x : Nat := x
      let y : Nat := y
      x % bls12381FrOrder == y % bls12381FrOrder

/-! ### Recursive `Element` operations for `SeqRow` -/

def elemZero : (e : Element) → e.ty.Val standardCarriers
  | .atom a => atomZero a
  | .sized item size => List.replicate size (elemZero item)

theorem elemZero_valid : ∀ (e : Element), e.ty.Valid standardCarriers (elemZero e)
  | .atom a => atomZero_valid a
  | .sized item size => by
      refine ⟨?_, fun n hn => by cases hn; simp [elemZero]⟩
      intro v hv
      rw [elemZero, List.mem_replicate] at hv
      rw [hv.2]
      exact elemZero_valid item

def zipWithLen {α β γ : Type} (f : α → β → γ) (defA : α) (defB : β) :
    Nat → List α → List β → List γ
  | 0, _, _ => []
  | n + 1, [], [] => f defA defB :: zipWithLen f defA defB n [] []
  | n + 1, a :: as, [] => f a defB :: zipWithLen f defA defB n as []
  | n + 1, [], b :: bs => f defA b :: zipWithLen f defA defB n [] bs
  | n + 1, a :: as, b :: bs => f a b :: zipWithLen f defA defB n as bs

theorem zipWithLen_length {α β γ : Type} (f : α → β → γ) (da : α) (db : β) :
    ∀ n as bs, (zipWithLen f da db n as bs).length = n
  | 0, _, _ => rfl
  | n + 1, [], [] => congrArg Nat.succ (zipWithLen_length f da db n [] [])
  | n + 1, _ :: as, [] => congrArg Nat.succ (zipWithLen_length f da db n as [])
  | n + 1, [], _ :: bs => congrArg Nat.succ (zipWithLen_length f da db n [] bs)
  | n + 1, _ :: as, _ :: bs => congrArg Nat.succ (zipWithLen_length f da db n as bs)

theorem zipWithLen_all {α β γ : Type} {PA : α → Prop} {PB : β → Prop} {PC : γ → Prop}
    {f : α → β → γ} {da : α} {db : β}
    (hf : ∀ a b, PA a → PB b → PC (f a b)) (hda : PA da) (hdb : PB db) :
    ∀ n as bs, (∀ a ∈ as, PA a) → (∀ b ∈ bs, PB b) →
      ∀ c ∈ zipWithLen f da db n as bs, PC c
  | 0, _, _, _, _, _, hc => nomatch hc
  | n + 1, [], [], _, _, c, hc => by
      rcases List.mem_cons.mp hc with rfl | hm
      · exact hf da db hda hdb
      · exact zipWithLen_all hf hda hdb n [] [] (fun _ h => nomatch h) (fun _ h => nomatch h) c hm
  | n + 1, a :: as, [], has, _, c, hc => by
      rcases List.mem_cons.mp hc with rfl | hm
      · exact hf a db (has a List.mem_cons_self) hdb
      · exact zipWithLen_all hf hda hdb n as []
          (fun x hx => has x (List.mem_cons_of_mem _ hx)) (fun _ h => nomatch h) c hm
  | n + 1, [], b :: bs, _, hbs, c, hc => by
      rcases List.mem_cons.mp hc with rfl | hm
      · exact hf da b hda (hbs b List.mem_cons_self)
      · exact zipWithLen_all hf hda hdb n [] bs
          (fun _ h => nomatch h) (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) c hm
  | n + 1, a :: as, b :: bs, has, hbs, c, hc => by
      rcases List.mem_cons.mp hc with rfl | hm
      · exact hf a b (has a List.mem_cons_self) (hbs b List.mem_cons_self)
      · exact zipWithLen_all hf hda hdb n as bs
          (fun x hx => has x (List.mem_cons_of_mem _ hx))
          (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) c hm

def elemAdd : (e : Element) → e.ty.Val standardCarriers → e.ty.Val standardCarriers → e.ty.Val standardCarriers
  | .atom a, x, y => atomAdd a x y
  | .sized item size, xs, ys => zipWithLen (elemAdd item) (elemZero item) (elemZero item) size xs ys

theorem elemAdd_valid : ∀ (e : Element) x y,
    e.ty.Valid standardCarriers x → e.ty.Valid standardCarriers y →
    e.ty.Valid standardCarriers (elemAdd e x y)
  | .atom a, x, y, hx, hy => atomAdd_valid a x y hx hy
  | .sized item size, xs, ys, hx, hy =>
      ⟨zipWithLen_all (elemAdd_valid item) (elemZero_valid item) (elemZero_valid item)
          size xs ys hx.1 hy.1,
       fun n hn => by cases hn; exact zipWithLen_length ..⟩

def elemSub : (e : Element) → e.ty.Val standardCarriers → e.ty.Val standardCarriers → e.ty.Val standardCarriers
  | .atom a, x, y => atomSub a x y
  | .sized item size, xs, ys => zipWithLen (elemSub item) (elemZero item) (elemZero item) size xs ys

theorem elemSub_valid : ∀ (e : Element) x y,
    e.ty.Valid standardCarriers x → e.ty.Valid standardCarriers y →
    e.ty.Valid standardCarriers (elemSub e x y)
  | .atom a, x, y, hx, _ => atomSub_valid a x y hx
  | .sized item size, xs, ys, hx, hy =>
      ⟨zipWithLen_all (elemSub_valid item) (elemZero_valid item) (elemZero_valid item)
          size xs ys hx.1 hy.1,
       fun n hn => by cases hn; exact zipWithLen_length ..⟩

def elemScale : (e : Element) → e.ty.Val standardCarriers → e.scalar.ty.Val standardCarriers → e.ty.Val standardCarriers
  | .atom a, x, s => atomScale a x s
  | .sized item size, xs, s =>
      (List.range size).map fun i => elemScale item (xs.getD i (elemZero item)) s

theorem list_getD_valid {α : Type} {P : α → Prop} {xs : List α} {d : α}
    (hxs : ∀ x ∈ xs, P x) (hd : P d) (i : Nat) : P (xs.getD i d) := by
  simp only [List.getD]
  cases h : xs[i]? with
  | none => exact hd
  | some v => exact hxs v (List.mem_of_getElem? h)

theorem elemScale_valid : ∀ (e : Element) x s,
    e.ty.Valid standardCarriers x →
    e.ty.Valid standardCarriers (elemScale e x s)
  | .atom a, x, s, _ => atomScale_valid a x s
  | .sized item size, xs, s, hx => by
      refine ⟨?_, fun n hn => by cases hn; simp [elemScale]⟩
      intro v hv
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact elemScale_valid item _ s (list_getD_valid hx.1 (elemZero_valid item) i)

def elemEqual : (e : Element) → e.ty.Val standardCarriers → e.ty.Val standardCarriers → Bool
  | .atom a, x, y => atomEqual a x y
  | .sized item _, xs, ys =>
      xs.length == ys.length && (xs.zip ys).all fun (a, b) => elemEqual item a b

def listFoldAdd (e : Element) (xs : List (e.ty.Val standardCarriers)) : e.ty.Val standardCarriers :=
  xs.foldl (elemAdd e) (elemZero e)

theorem listFoldAdd_valid (e : Element) :
    ∀ (xs : List (e.ty.Val standardCarriers)) (acc : e.ty.Val standardCarriers),
      e.ty.Valid standardCarriers acc → (∀ x ∈ xs, e.ty.Valid standardCarriers x) →
      e.ty.Valid standardCarriers (xs.foldl (elemAdd e) acc)
  | [], _, hacc, _ => hacc
  | x :: xs, acc, hacc, hxs =>
      listFoldAdd_valid e xs (elemAdd e acc x)
        (elemAdd_valid e acc x hacc (hxs x List.mem_cons_self))
        (fun y hy => hxs y (List.mem_cons_of_mem _ hy))

def listFoldMul (f : Field) (xs : List (StandardCarrier (.field f))) : StandardCarrier (.field f) :=
  xs.foldl (fieldMul f) (fieldOne f)

theorem listFoldMul_valid (f : Field) :
    ∀ (xs : List (StandardCarrier (.field f))) (acc : StandardCarrier (.field f)),
      StandardValid (.field f) acc →
      StandardValid (.field f) (xs.foldl (fieldMul f) acc)
  | [], _, hacc => hacc
  | x :: xs, acc, _ => listFoldMul_valid f xs (fieldMul f acc x) (fieldMul_valid f acc x)

def listInner (e : Element) :
    List (e.ty.Val standardCarriers) → List (e.scalar.ty.Val standardCarriers) → e.ty.Val standardCarriers
  | [], _ => elemZero e
  | _, [] => elemZero e
  | x :: xs, s :: ss => elemAdd e (elemScale e x s) (listInner e xs ss)

theorem listInner_valid (e : Element) :
    ∀ xs ss, (∀ x ∈ xs, e.ty.Valid standardCarriers x) →
      e.ty.Valid standardCarriers (listInner e xs ss)
  | [], _, _ => elemZero_valid e
  | _ :: _, [], _ => elemZero_valid e
  | x :: xs, s :: ss, hxs =>
      elemAdd_valid e _ _
        (elemScale_valid e x s (hxs x List.mem_cons_self))
        (listInner_valid e xs ss (fun y hy => hxs y (List.mem_cons_of_mem _ hy)))

/-! ## `standardModel : Core.Model Zkc.Vocabulary.standard` -/

theorem ext4Norm_isNonzero_eq (a : List Nat) :
    ext4IsNonzero (ext4Norm a) = ext4IsNonzero a := by
  unfold ext4IsNonzero
  have h : ext4Norm (ext4Norm a) = ext4Norm a := by
    simp [ext4Norm, List.getD]
  rw [h]

/-- Pure-row evaluator returning valid outputs bundled with their validity proof. -/
abbrev ValidOut (sig : RowSignature TypeKey RowKey)
    (args : HList (Ty.Val standardCarriers) sig.ins) : Type :=
  { outs : HList (Ty.Val standardCarriers) sig.outs //
    args.All (Ty.Valid standardCarriers) → outs.All (Ty.Valid standardCarriers) }

def evalFieldPure (f : Field) (row : FieldRow) (among : Among)
    (sig : RowSignature TypeKey RowKey) (h : fieldRow f row among = some sig)
    (hp : sig.kind = .pure) (args : HList (Ty.Val standardCarriers) sig.ins) :
    ValidOut sig args := by
  cases row <;> cases among <;> simp only [fieldRow] at h
  · cases h; rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    exact ⟨.cons (fieldAdd f a b) .nil, fun _ => ⟨fieldAdd_valid f a b, trivial⟩⟩
  · cases h
  · cases h; rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    exact ⟨.cons (fieldSub f a b) .nil, fun _ => ⟨fieldSub_valid f a b, trivial⟩⟩
  · cases h
  · cases h; rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    exact ⟨.cons (fieldMul f a b) .nil, fun _ => ⟨fieldMul_valid f a b, trivial⟩⟩
  · cases h; rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    cases f with
    | koalaBear => exact ⟨.cons (nzPrime (mulMod a b koalaBearOrder) koalaBearOrder) .nil,
        fun _ => ⟨nzPrime_valid _ _ koalaBearOrder_gt1, trivial⟩⟩
    | koalaBear4 => exact ⟨.cons (nzExt4 (ext4Mul a b)) .nil,
        fun _ => ⟨nzExt4_valid _, trivial⟩⟩
    | bls12381Fr => exact ⟨.cons (nzPrime (mulMod a b bls12381FrOrder) bls12381FrOrder) .nil,
        fun _ => ⟨nzPrime_valid _ _ bls12381FrOrder_gt1, trivial⟩⟩
  · cases h; rcases args with _ | ⟨a, _ | _⟩
    exact ⟨.cons (fieldNeg f a) .nil, fun _ => ⟨fieldNeg_valid f a, trivial⟩⟩
  · cases h; rcases args with _ | ⟨a, _ | _⟩
    cases f with
    | koalaBear => exact ⟨.cons (nzPrime (negMod a koalaBearOrder) koalaBearOrder) .nil,
        fun _ => ⟨nzPrime_valid _ _ koalaBearOrder_gt1, trivial⟩⟩
    | koalaBear4 => exact ⟨.cons (nzExt4 (ext4Neg a)) .nil,
        fun _ => ⟨nzExt4_valid _, trivial⟩⟩
    | bls12381Fr => exact ⟨.cons (nzPrime (negMod a bls12381FrOrder) bls12381FrOrder) .nil,
        fun _ => ⟨nzPrime_valid _ _ bls12381FrOrder_gt1, trivial⟩⟩
  · cases h
  · cases h; rcases args with _ | ⟨a, _ | _⟩
    cases f with
    | koalaBear => exact ⟨.cons (nzPrime (modInv a koalaBearOrder) koalaBearOrder) .nil,
        fun _ => ⟨nzPrime_valid _ _ koalaBearOrder_gt1, trivial⟩⟩
    | koalaBear4 => exact ⟨.cons (nzExt4 (ext4Inv a)) .nil,
        fun _ => ⟨nzExt4_valid _, trivial⟩⟩
    | bls12381Fr => exact ⟨.cons (nzPrime (modInv a bls12381FrOrder) bls12381FrOrder) .nil,
        fun _ => ⟨nzPrime_valid _ _ bls12381FrOrder_gt1, trivial⟩⟩
  · cases h; rcases args with _ | ⟨a, _ | ⟨e, _ | _⟩⟩
    exact ⟨.cons (fieldPow f a e) .nil, fun _ => ⟨fieldPow_valid f a e, trivial⟩⟩
  · cases h; rcases args with _ | ⟨a, _ | ⟨e, _ | _⟩⟩
    cases f with
    | koalaBear => exact ⟨.cons (nzPrime (modPow a e koalaBearOrder) koalaBearOrder) .nil,
        fun _ => ⟨nzPrime_valid _ _ koalaBearOrder_gt1, trivial⟩⟩
    | koalaBear4 => exact ⟨.cons (nzExt4 (ext4Pow a e)) .nil,
        fun _ => ⟨nzExt4_valid _, trivial⟩⟩
    | bls12381Fr => exact ⟨.cons (nzPrime (modPow a e bls12381FrOrder) bls12381FrOrder) .nil,
        fun _ => ⟨nzPrime_valid _ _ bls12381FrOrder_gt1, trivial⟩⟩
  · cases h; rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    exact ⟨.cons (fieldEqual f a b) .nil, fun _ => ⟨trivial, trivial⟩⟩
  · cases h
  · cases h; rcases args with _ | ⟨a, _ | _⟩
    exact ⟨.cons (fieldIsNonzero f a) .nil, fun _ => ⟨trivial, trivial⟩⟩
  · cases h
  · cases h; cases hp
  · cases h
  · cases h
  · cases h; rcases args with _ | ⟨a, _ | _⟩
    cases f with
    | koalaBear =>
        let a : Nat := a
        exact ⟨.cons (a % koalaBearOrder) .nil, fun _ => ⟨Nat.mod_lt _ koalaBearOrder_pos, trivial⟩⟩
    | koalaBear4 => exact ⟨.cons (ext4Norm a) .nil, fun _ => ⟨ext4Norm_valid a, trivial⟩⟩
    | bls12381Fr =>
        let a : Nat := a
        exact ⟨.cons (a % bls12381FrOrder) .nil, fun _ => ⟨Nat.mod_lt _ bls12381FrOrder_pos, trivial⟩⟩
  · cases h; rcases args with _ | ⟨n, _ | _⟩
    exact ⟨.cons (fieldFromNat f n) .nil, fun _ => ⟨fieldFromNat_valid f n, trivial⟩⟩
  · cases h
  · cases f with
    | koalaBear =>
        cases h; rcases args with _ | ⟨a, _ | _⟩
        let a : Nat := a
        exact ⟨.cons (a % koalaBearOrder) .nil, fun _ => ⟨Nat.mod_lt _ (by decide), trivial⟩⟩
    | koalaBear4 => cases h
    | bls12381Fr =>
        cases h; rcases args with _ | ⟨a, _ | _⟩
        let a : Nat := a
        exact ⟨.cons (a % bls12381FrOrder) .nil, fun _ => ⟨Nat.mod_lt _ (by decide), trivial⟩⟩
  · cases h
  · cases h; rcases args with _ | ⟨a, _ | _⟩
    cases f with
    | koalaBear =>
        let a : Nat := a
        exact ⟨.cons [a % koalaBearOrder] .nil, fun _ =>
          ⟨⟨fun v hv => by rcases List.mem_singleton.mp hv with rfl; exact Nat.mod_lt _ koalaBearOrder_pos,
            fun n hn => by cases hn; rfl⟩, trivial⟩⟩
    | koalaBear4 => exact ⟨.cons (ext4Norm a) .nil, fun _ =>
        ⟨⟨(ext4Norm_valid a).2, fun n hn => by cases hn; exact (ext4Norm_valid a).1⟩, trivial⟩⟩
    | bls12381Fr =>
        let a : Nat := a
        exact ⟨.cons [a % bls12381FrOrder] .nil, fun _ =>
          ⟨⟨fun v hv => by rcases List.mem_singleton.mp hv with rfl; exact Nat.mod_lt _ bls12381FrOrder_pos,
            fun n hn => by cases hn; rfl⟩, trivial⟩⟩
  · cases h
  · cases h; rcases args with _ | ⟨cs, _ | _⟩
    cases f with
    | koalaBear =>
        let cs : List Nat := cs
        exact ⟨.cons (cs.headD 0 % koalaBearOrder) .nil, fun _ => ⟨Nat.mod_lt _ koalaBearOrder_pos, trivial⟩⟩
    | koalaBear4 => exact ⟨.cons (ext4Norm cs) .nil, fun _ => ⟨ext4Norm_valid cs, trivial⟩⟩
    | bls12381Fr =>
        let cs : List Nat := cs
        exact ⟨.cons (cs.headD 0 % bls12381FrOrder) .nil, fun _ => ⟨Nat.mod_lt _ bls12381FrOrder_pos, trivial⟩⟩
  · cases h
  · cases f with
    | koalaBear => cases h
    | koalaBear4 => cases h; rcases args with _ | ⟨a, _ | _⟩
                    exact ⟨.cons (ext4Embed a) .nil, fun _ => ⟨ext4OfNat_valid a, trivial⟩⟩
    | bls12381Fr => cases h
  · cases f with
    | koalaBear => cases h
    | koalaBear4 => cases h; rcases args with _ | ⟨a, _ | _⟩
                    exact ⟨.cons (nzExt4 (ext4Embed a)) .nil, fun _ => ⟨nzExt4_valid _, trivial⟩⟩
    | bls12381Fr => cases h
  · cases f with
    | koalaBear => cases h
    | koalaBear4 => cases h; rcases args with _ | ⟨a, _ | _⟩
                    exact ⟨.cons (ext4Norm a) .nil, fun _ =>
                      ⟨⟨(ext4Norm_valid a).2, fun n hn => by cases hn; exact (ext4Norm_valid a).1⟩, trivial⟩⟩
    | bls12381Fr => cases h
  · cases h
  · cases f with
    | koalaBear => cases h
    | koalaBear4 => cases h; rcases args with _ | ⟨cs, _ | _⟩
                    exact ⟨.cons (ext4Norm cs) .nil, fun _ => ⟨ext4Norm_valid cs, trivial⟩⟩
    | bls12381Fr => cases h
  · cases h
  · cases h; rcases args with _ | ⟨k, _ | _⟩
    exact ⟨.cons (fieldRoot f k) .nil, fun _ => ⟨fieldRoot_valid f k, trivial⟩⟩
  · cases h

def evalGroupPure (atom : Atom) (row : GroupRow)
    (sig : RowSignature TypeKey RowKey) (h : groupRow atom row = some sig)
    (args : HList (Ty.Val standardCarriers) sig.ins) : ValidOut sig args := by
  cases row <;> simp only [groupRow] at h
  · cases h; exact ⟨.cons (atomZero atom) .nil, fun _ => ⟨atomZero_valid atom, trivial⟩⟩
  · cases h; rcases args with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
    exact ⟨.cons (atomAdd atom x y) .nil, fun ha => ⟨atomAdd_valid atom x y ha.1 ha.2.1, trivial⟩⟩
  · cases h; rcases args with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
    exact ⟨.cons (atomSub atom x y) .nil, fun ha => ⟨atomSub_valid atom x y ha.1, trivial⟩⟩
  · cases h; rcases args with _ | ⟨x, _ | _⟩
    exact ⟨.cons (atomNeg atom x) .nil, fun _ => ⟨atomNeg_valid atom x, trivial⟩⟩
  · cases h; rcases args with _ | ⟨x, _ | ⟨s, _ | _⟩⟩
    exact ⟨.cons (atomScale atom x s) .nil, fun _ => ⟨atomScale_valid atom x s, trivial⟩⟩
  · cases h; rcases args with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
    exact ⟨.cons (atomEqual atom x y) .nil, fun _ => ⟨trivial, trivial⟩⟩
  · cases atom with
    | field _ => cases h
    | group g =>
        cases g with
        | g1 => cases h; exact ⟨.cons g1Generator .nil, fun _ => ⟨g1Generator_coordValid, trivial⟩⟩
        | g2 => cases h; exact ⟨.cons (1 : Nat) .nil, fun _ => ⟨bls12381FrOrder_gt1, trivial⟩⟩
        | gt => cases h

def evalSeqPure (item : Element) (size : Option Nat) (row : SeqRow)
    (sig : RowSignature TypeKey RowKey) (h : seqRow item size row = some sig)
    (args : HList (Ty.Val standardCarriers) sig.ins) : ValidOut sig args := by
  cases row <;> simp only [seqRow] at h
  · cases size with
    | none => cases h
    | some n =>
        cases h; rcases args with _ | ⟨xs, _ | ⟨ys, _ | _⟩⟩
        exact ⟨.cons (zipWithLen (elemAdd item) (elemZero item) (elemZero item) n xs ys) .nil,
          fun ha => ⟨⟨zipWithLen_all (elemAdd_valid item) (elemZero_valid item) (elemZero_valid item)
                        n xs ys ha.1.1 ha.2.1.1,
                      fun k hk => by cases hk; exact zipWithLen_length ..⟩, trivial⟩⟩
  · cases size with
    | none => cases h
    | some n =>
        cases h; rcases args with _ | ⟨xs, _ | ⟨ys, _ | _⟩⟩
        exact ⟨.cons (zipWithLen (elemSub item) (elemZero item) (elemZero item) n xs ys) .nil,
          fun ha => ⟨⟨zipWithLen_all (elemSub_valid item) (elemZero_valid item) (elemZero_valid item)
                        n xs ys ha.1.1 ha.2.1.1,
                      fun k hk => by cases hk; exact zipWithLen_length ..⟩, trivial⟩⟩
  · cases size with
    | none => cases h
    | some n =>
        cases h; rcases args with _ | ⟨xs, _ | ⟨s, _ | _⟩⟩
        exact ⟨.cons ((List.range n).map fun i => elemScale item (xs.getD i (elemZero item)) s) .nil,
          fun ha => ⟨⟨fun v hv => by
                        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
                        exact elemScale_valid item _ s (list_getD_valid ha.1.1 (elemZero_valid item) i),
                      fun k hk => by cases hk; simp⟩, trivial⟩⟩
  · cases h; rcases args with _ | ⟨xs, _ | _⟩
    exact ⟨.cons (listFoldAdd item xs) .nil,
      fun ha => ⟨listFoldAdd_valid item xs (elemZero item) (elemZero_valid item) ha.1.1, trivial⟩⟩
  · cases item with
    | atom a =>
        cases a with
        | field f =>
            cases h; rcases args with _ | ⟨xs, _ | _⟩
            exact ⟨.cons (listFoldMul f xs) .nil,
              fun _ => ⟨listFoldMul_valid f xs (fieldOne f) (fieldOne_valid f), trivial⟩⟩
        | group _ => cases h
    | sized _ _ => cases h
  · cases size with
    | none => cases h
    | some _ =>
        cases h; rcases args with _ | ⟨xs, _ | ⟨ss, _ | _⟩⟩
        exact ⟨.cons (listInner item xs ss) .nil, fun ha => ⟨listInner_valid item xs ss ha.1.1, trivial⟩⟩
  · cases h; rcases args with _ | ⟨xs, _ | ⟨ys, _ | _⟩⟩
    exact ⟨.cons (xs.length == ys.length && (xs.zip ys).all fun (a, b) => elemEqual item a b) .nil,
      fun _ => ⟨trivial, trivial⟩⟩

def evalHashPure (hash : Zkc.Vocabulary.Hash)
    (sig : RowSignature TypeKey RowKey) (h : hashRow hash = some sig)
    (args : HList (Ty.Val standardCarriers) sig.ins) : ValidOut sig args := by
  cases hash with
  | sha256 =>
      simp only [hashRow] at h; cases h; rcases args with _ | ⟨bs, _ | _⟩
      exact ⟨.cons (sha256Bytes bs) .nil, fun _ =>
        let ⟨hl, hb⟩ := sha256Bytes_len_and_bytes bs
        ⟨⟨hb, fun n hn => by cases hn; exact hl⟩, trivial⟩⟩
  | keccak256 =>
      simp only [hashRow] at h; cases h; rcases args with _ | ⟨bs, _ | _⟩
      exact ⟨.cons (keccak256Bytes bs) .nil, fun _ =>
        let ⟨hl, hb⟩ := keccak256Bytes_len_and_bytes bs
        ⟨⟨hb, fun n hn => by cases hn; exact hl⟩, trivial⟩⟩
  | shake128 count =>
      simp only [hashRow] at h; cases h; rcases args with _ | ⟨bs, _ | _⟩
      exact ⟨.cons (shake128Bytes bs count) .nil, fun _ =>
        let ⟨hl, hb⟩ := shake128Bytes_len_and_bytes bs count
        ⟨⟨hb, fun n hn => by cases hn; exact hl⟩, trivial⟩⟩
  | shake256 count =>
      simp only [hashRow] at h; cases h; rcases args with _ | ⟨bs, _ | _⟩
      exact ⟨.cons (shake256Bytes bs count) .nil, fun _ =>
        let ⟨hl, hb⟩ := shake256Bytes_len_and_bytes bs count
        ⟨⟨hb, fun n hn => by cases hn; exact hl⟩, trivial⟩⟩

def evalStandard (key : RowKey) (sig : RowSignature TypeKey RowKey)
    (h : standard.row key = some sig) (args : HList (Ty.Val standardCarriers) sig.ins) :
    Option (ValidOut sig args) :=
  match hk : sig.kind with
  | .pure =>
      match key with
      | .field row f among => some (evalFieldPure f row among sig h hk args)
      | .group row atom => some (evalGroupPure atom row sig h args)
      | .seq row item size => some (evalSeqPure item size row sig h args)
      | .hash hash => some (evalHashPure hash sig h args)
      | .pair => by
          simp only [standard, Zkc.Vocabulary.row, Zkc.Vocabulary.pure, Option.some.injEq] at h
          subst h
          rcases args with _ | ⟨p1, _ | ⟨p2, _ | _⟩⟩
          let p2 : Nat := p2
          let h1 := fromBeBytes (sha256Bytes (compressG1 p1)) % bls12381FrOrder
          exact some ⟨.cons ((h1 * p2) % bls12381FrOrder) .nil,
            fun _ => ⟨Nat.mod_lt _ bls12381FrOrder_pos, trivial⟩⟩
  | .restricted _ =>
      match key with
      | .field .nonzero f .all => by
          simp only [standard, Zkc.Vocabulary.row, fieldRow, Option.some.injEq] at h
          subst h
          rcases args with _ | ⟨a, _ | _⟩
          cases f with
          | koalaBear =>
              let a : Nat := a
              exact if hnz : a % koalaBearOrder != 0 then
                some ⟨.cons (a % koalaBearOrder) .nil, fun _ =>
                  ⟨⟨Nat.pos_of_ne_zero (by simpa using hnz),
                    Nat.mod_lt _ koalaBearOrder_pos⟩, trivial⟩⟩
              else none
          | koalaBear4 =>
              let a : List Nat := a
              exact if hnz : ext4IsNonzero a = true then
                some ⟨.cons (ext4Norm a) .nil, fun _ =>
                  ⟨⟨ext4Norm_valid a, by rw [ext4Norm_isNonzero_eq]; exact hnz⟩, trivial⟩⟩
              else none
          | bls12381Fr =>
              let a : Nat := a
              exact if hnz : a % bls12381FrOrder != 0 then
                some ⟨.cons (a % bls12381FrOrder) .nil, fun _ =>
                  ⟨⟨Nat.pos_of_ne_zero (by simpa using hnz),
                    Nat.mod_lt _ bls12381FrOrder_pos⟩, trivial⟩⟩
              else none
      | _ => none

def standardApply (key : RowKey) (sig : RowSignature TypeKey RowKey)
    (h : standard.row key = some sig) (args : HList (Ty.Val standardCarriers) sig.ins) :
    Option (HList (Ty.Val standardCarriers) sig.outs) :=
  (evalStandard key sig h args).map Subtype.val

def standardInDomain (key : RowKey) (sig : RowSignature TypeKey RowKey)
    (h : standard.row key = some sig) (args : HList (Ty.Val standardCarriers) sig.ins) : Bool :=
  (standardApply key sig h args).isSome

theorem standard_total (key : RowKey) (sig : RowSignature TypeKey RowKey)
    (h : standard.row key = some sig) (args : HList (Ty.Val standardCarriers) sig.ins)
    (hp : sig.kind = .pure) : standardInDomain key sig h args = true := by
  unfold standardInDomain standardApply evalStandard
  split
  · cases key
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [standard, Zkc.Vocabulary.row, Zkc.Vocabulary.pure, Option.some.injEq] at h
      subst h
      rcases args with _ | ⟨_, _ | ⟨_, _ | _⟩⟩
      rfl
  · next hk => rw [hp] at hk; cases hk

theorem standard_decides (key : RowKey) (sig : RowSignature TypeKey RowKey)
    (h : standard.row key = some sig) (domain : RowKey) (hk : sig.kind = .restricted domain)
    (args : HList (Ty.Val standardCarriers) sig.ins) :
    standardApply domain ⟨sig.ins, [.bool], .pure⟩ (standard.decided key sig domain h hk) args =
      some (.cons (standardInDomain key sig h args) .nil) := by
  cases key with
  | field row f among =>
      cases row with
      | nonzero =>
          cases among with
          | all =>
              simp only [standard, Zkc.Vocabulary.row, fieldRow] at h
              cases h
              cases hk
              rcases args with _ | ⟨a, _ | _⟩
              cases f with
              | koalaBear =>
                  change Nat at a
                  by_cases h0 : a % koalaBearOrder = 0
                  · simp [standardApply, standardInDomain, evalStandard, evalFieldPure, fieldIsNonzero, h0]
                  · have h1 : (a % koalaBearOrder != 0) = true := bne_iff_ne.mpr h0
                    simp [standardApply, standardInDomain, evalStandard, evalFieldPure, fieldIsNonzero,
                      Option.isSome, h1]
              | koalaBear4 =>
                  change List Nat at a
                  cases h0 : ext4IsNonzero a <;>
                    simp [standardApply, standardInDomain, evalStandard, evalFieldPure, fieldIsNonzero,
                      Option.isSome, h0]
              | bls12381Fr =>
                  change Nat at a
                  by_cases h0 : a % bls12381FrOrder = 0
                  · simp [standardApply, standardInDomain, evalStandard, evalFieldPure, fieldIsNonzero, h0]
                  · have h1 : (a % bls12381FrOrder != 0) = true := bne_iff_ne.mpr h0
                    simp [standardApply, standardInDomain, evalStandard, evalFieldPure, fieldIsNonzero,
                      Option.isSome, h1]
          | nonzero =>
              simp only [standard, Zkc.Vocabulary.row, fieldRow] at h
              cases h
      | _ =>
          cases among <;> simp only [standard, Zkc.Vocabulary.row, fieldRow] at h
          all_goals first
            | (cases h; done)
            | (cases h; dsimp at hk; cases hk)
            | (cases f <;> cases h <;> (dsimp at hk; cases hk))
  | group row atom =>
      cases row <;> simp only [standard, Zkc.Vocabulary.row, groupRow] at h
      all_goals first
        | (cases h; dsimp at hk; cases hk)
        | (cases atom with | field _ => cases h | group g => cases g <;> cases h <;> (dsimp at hk; cases hk))
  | seq row item size =>
      cases row <;> simp only [standard, Zkc.Vocabulary.row, seqRow] at h
      all_goals first
        | (cases size <;> (try cases h) <;> (dsimp at hk; cases hk))
        | (cases h; dsimp at hk; cases hk)
        | (cases item with
           | atom a => cases a with | field _ => cases h; dsimp at hk; cases hk | group _ => cases h
           | sized _ _ => cases h)
  | hash hash => cases hash <;> simp only [standard, Zkc.Vocabulary.row, hashRow] at h <;> cases h <;> (dsimp at hk; cases hk)
  | pair => simp only [standard, Zkc.Vocabulary.row] at h; cases h; dsimp at hk; cases hk

theorem standard_keeps (key : RowKey) (sig : RowSignature TypeKey RowKey)
    (h : standard.row key = some sig) (args : HList (Ty.Val standardCarriers) sig.ins)
    (outs : HList (Ty.Val standardCarriers) sig.outs)
    (hargs : args.All (Ty.Valid standardCarriers))
    (happ : standardApply key sig h args = some outs) :
    outs.All (Ty.Valid standardCarriers) := by
  unfold standardApply at happ
  cases hev : evalStandard key sig h args with
  | none =>
      rw [hev] at happ
      cases happ
  | some pair =>
      rw [hev] at happ
      cases happ
      exact pair.2 hargs

theorem standard_literals (key : TypeKey) (n : Nat) (h : standard.literal key n = true) :
    ∃ v, standardCarriers.literal key n = some v ∧ standardCarriers.valid key v := by
  cases key with
  | field f =>
      cases f <;> (simp only [standard, Zkc.Vocabulary.literal, Field.characteristic] at h; have h' := of_decide_eq_true h)
      · exact ⟨n, by simp [standardCarriers, standardLiteral, koalaBearOrder, h'], h'⟩
      · exact ⟨ext4OfNat n, by simp [standardCarriers, standardLiteral, koalaBearOrder, h'], ext4OfNat_valid n⟩
      · exact ⟨n, by simp [standardCarriers, standardLiteral, bls12381FrOrder, h'], h'⟩
  | nonzero f =>
      cases f <;> (simp only [standard, Zkc.Vocabulary.literal, Field.characteristic] at h; have h' := of_decide_eq_true h)
      · exact ⟨n, by simp [standardCarriers, standardLiteral, koalaBearOrder, h'], h'⟩
      · refine ⟨ext4OfNat n, by simp [standardCarriers, standardLiteral, koalaBearOrder, h'],
          ext4OfNat_valid n, ?_⟩
        have hlt : n < koalaBearOrder := h'.2
        simp only [ext4IsNonzero, ext4Norm, ext4OfNat, List.getD, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, Nat.mod_eq_of_lt hlt,
          Nat.zero_mod, List.any_cons, Bool.or_eq_true, bne_iff_ne]
        exact Or.inl (Nat.ne_of_gt h'.1)
      · exact ⟨n, by simp [standardCarriers, standardLiteral, bls12381FrOrder, h'], h'⟩
  | group _ => simp [standard, Zkc.Vocabulary.literal] at h

/-- Concrete cryptographic `Core.Model` for `Zkc.Vocabulary.standard`. -/
def standardModel : Model standard where
  toCarriers := standardCarriers
  apply := standardApply
  inDomain := standardInDomain
  defined _ _ _ _ := rfl
  total := standard_total
  decides := standard_decides
  keeps := standard_keeps
  literals := standard_literals
  support _ sig _ _ out := Ty.Valid standardCarriers sig.out out
  supported _ _ _ _ _ _ hout := hout

/-! ## Project-linked runtime carriers, codecs, and `linkedModel?` -/

/-- Runtime carrier for opaque project-declared types (transcript states, labels, etc.). -/
inductive RuntimeOpaque where
  | unit
  | merlin (state : Merlin.State)
  | cfrg (state : Cfrg.Duplex)
  | poseidon2 (state : Poseidon2Suite.Duplex)
  | bytes (bs : List Nat)
  | nat (n : Nat)

abbrev LinkedCarrier : Sum TypeKey Parameter → Type
  | .inl k => StandardCarrier k
  | .inr _ => RuntimeOpaque

abbrev LinkedValid : (k : Sum TypeKey Parameter) → LinkedCarrier k → Prop
  | .inl k, v => StandardValid k v
  | .inr _, _ => True

def linkedLiteral : (k : Sum TypeKey Parameter) → Nat → Option (LinkedCarrier k)
  | .inl k, n => standardLiteral k n
  | .inr _, _ => none

/-- Carriers for any project-linked vocabulary `b.vocabulary`. -/
@[reducible] def linkedCarriers (b : Bindings) : Carriers b.vocabulary where
  Carrier := LinkedCarrier
  valid := LinkedValid
  literal := linkedLiteral

/-! ### Value transport between `standardCarriers` and `linkedCarriers b` -/

section BaseTransport
variable (b : Bindings)

mutual
  def liftStandardVal : (τ : Core.Ty TypeKey) → τ.Val standardCarriers →
      (τ.mapNominal Sum.inl).Val (linkedCarriers b)
    | .bool, v => v
    | .nat, v => v
    | .fin _, v => v
    | .seq item _, xs => xs.map (liftStandardVal item)
    | .tuple items, vs => liftStandardTys items vs
    | .record _ _ fields, vs => liftStandardTys fields vs
    | .variant _ alts, v => liftStandardChoice alts v
    | .nominal _, v => v

  def liftStandardTys : (τs : Core.Tys TypeKey) → τs.Val standardCarriers →
      (τs.mapNominal Sum.inl).Val (linkedCarriers b)
    | .nil, _ => ()
    | .cons head rest, (v, vs) => (liftStandardVal head v, liftStandardTys rest vs)

  def liftStandardChoice : (τs : Core.Tys TypeKey) → τs.Choice standardCarriers →
      (τs.mapNominal Sum.inl).Choice (linkedCarriers b)
    | .nil, v => nomatch v
    | .cons head _, .inl v => .inl (liftStandardVal head v)
    | .cons _ rest, .inr v => .inr (liftStandardChoice rest v)
end

mutual
  def lowerStandardVal : (τ : Core.Ty TypeKey) → (τ.mapNominal Sum.inl).Val (linkedCarriers b) →
      τ.Val standardCarriers
    | .bool, v => v
    | .nat, v => v
    | .fin _, v => v
    | .seq item _, xs => xs.map (lowerStandardVal item)
    | .tuple items, vs => lowerStandardTys items vs
    | .record _ _ fields, vs => lowerStandardTys fields vs
    | .variant _ alts, v => lowerStandardChoice alts v
    | .nominal _, v => v

  def lowerStandardTys : (τs : Core.Tys TypeKey) → (τs.mapNominal Sum.inl).Val (linkedCarriers b) →
      τs.Val standardCarriers
    | .nil, _ => ()
    | .cons head rest, (v, vs) => (lowerStandardVal head v, lowerStandardTys rest vs)

  def lowerStandardChoice : (τs : Core.Tys TypeKey) →
      (τs.mapNominal Sum.inl).Choice (linkedCarriers b) → τs.Choice standardCarriers
    | .nil, v => nomatch v
    | .cons head _, .inl v => .inl (lowerStandardVal head v)
    | .cons _ rest, .inr v => .inr (lowerStandardChoice rest v)
end

def liftStandardHList : {ts : List (Core.Ty TypeKey)} →
    HList (Ty.Val standardCarriers) ts →
    HList (Ty.Val (linkedCarriers b)) (ts.map (Ty.mapNominal Sum.inl))
  | [], .nil => .nil
  | τ :: _, .cons v vs => .cons (liftStandardVal b τ v) (liftStandardHList vs)

def lowerStandardHList : {ts : List (Core.Ty TypeKey)} →
    HList (Ty.Val (linkedCarriers b)) (ts.map (Ty.mapNominal Sum.inl)) →
    HList (Ty.Val standardCarriers) ts
  | [], .nil => .nil
  | τ :: _, .cons v vs => .cons (lowerStandardVal b τ v) (lowerStandardHList vs)

mutual
  theorem liftStandardVal_valid : ∀ (τ : Core.Ty TypeKey) (v : τ.Val standardCarriers),
      τ.Valid standardCarriers v → (τ.mapNominal Sum.inl).Valid (linkedCarriers b) (liftStandardVal b τ v)
    | .bool, _, _ => trivial
    | .nat, _, _ => trivial
    | .fin _, _, h => h
    | .seq item _, xs, ⟨hxs, hlen⟩ =>
        ⟨fun v hv => by
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
            exact liftStandardVal_valid item x (hxs x hx),
         fun n hn => (List.length_map _).trans (hlen n hn)⟩
    | .tuple items, vs, h => liftStandardTys_valid items vs h
    | .record _ _ fields, vs, h => liftStandardTys_valid fields vs h
    | .variant _ alts, v, h => liftStandardChoice_valid alts v h
    | .nominal _, _, h => h

  theorem liftStandardTys_valid : ∀ (τs : Core.Tys TypeKey) (vs : τs.Val standardCarriers),
      τs.Valid standardCarriers vs → (τs.mapNominal Sum.inl).Valid (linkedCarriers b) (liftStandardTys b τs vs)
    | .nil, _, _ => trivial
    | .cons head rest, (v, vs), ⟨hv, hvs⟩ =>
        ⟨liftStandardVal_valid head v hv, liftStandardTys_valid rest vs hvs⟩

  theorem liftStandardChoice_valid : ∀ (τs : Core.Tys TypeKey) (v : τs.Choice standardCarriers),
      τs.ValidChoice standardCarriers v →
      (τs.mapNominal Sum.inl).ValidChoice (linkedCarriers b) (liftStandardChoice b τs v)
    | .nil, v, _ => nomatch v
    | .cons head _, .inl v, hv => liftStandardVal_valid head v hv
    | .cons _ rest, .inr v, hv => liftStandardChoice_valid rest v hv
end

mutual
  theorem lowerStandardVal_valid : ∀ (τ : Core.Ty TypeKey) (v : (τ.mapNominal Sum.inl).Val (linkedCarriers b)),
      (τ.mapNominal Sum.inl).Valid (linkedCarriers b) v → τ.Valid standardCarriers (lowerStandardVal b τ v)
    | .bool, _, _ => trivial
    | .nat, _, _ => trivial
    | .fin _, _, h => h
    | .seq item _, xs, ⟨hxs, hlen⟩ =>
        ⟨fun v hv => by
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
            exact lowerStandardVal_valid item x (hxs x hx),
         fun n hn => (List.length_map _).trans (hlen n hn)⟩
    | .tuple items, vs, h => lowerStandardTys_valid items vs h
    | .record _ _ fields, vs, h => lowerStandardTys_valid fields vs h
    | .variant _ alts, v, h => lowerStandardChoice_valid alts v h
    | .nominal _, _, h => h

  theorem lowerStandardTys_valid : ∀ (τs : Core.Tys TypeKey) (vs : (τs.mapNominal Sum.inl).Val (linkedCarriers b)),
      (τs.mapNominal Sum.inl).Valid (linkedCarriers b) vs → τs.Valid standardCarriers (lowerStandardTys b τs vs)
    | .nil, _, _ => trivial
    | .cons head rest, (v, vs), ⟨hv, hvs⟩ =>
        ⟨lowerStandardVal_valid head v hv, lowerStandardTys_valid rest vs hvs⟩

  theorem lowerStandardChoice_valid : ∀ (τs : Core.Tys TypeKey)
      (v : (τs.mapNominal Sum.inl).Choice (linkedCarriers b)),
      (τs.mapNominal Sum.inl).ValidChoice (linkedCarriers b) v →
      τs.ValidChoice standardCarriers (lowerStandardChoice b τs v)
    | .nil, v, _ => nomatch v
    | .cons head _, .inl v, hv => lowerStandardVal_valid head v hv
    | .cons _ rest, .inr v, hv => lowerStandardChoice_valid rest v hv
end

theorem liftStandardHList_valid : ∀ {ts : List (Core.Ty TypeKey)} (vs : HList (Ty.Val standardCarriers) ts),
    vs.All (Ty.Valid standardCarriers) →
    (liftStandardHList b vs).All (Ty.Valid (linkedCarriers b))
  | [], .nil, _ => trivial
  | τ :: _, .cons v vs, h => ⟨liftStandardVal_valid b τ v h.1, liftStandardHList_valid vs h.2⟩

theorem lowerStandardHList_valid : ∀ {ts : List (Core.Ty TypeKey)}
    (vs : HList (Ty.Val (linkedCarriers b)) (ts.map (Ty.mapNominal Sum.inl))),
    vs.All (Ty.Valid (linkedCarriers b)) →
    (lowerStandardHList b vs).All (Ty.Valid standardCarriers)
  | [], .nil, _ => trivial
  | τ :: _, .cons v vs, h => ⟨lowerStandardVal_valid b τ v h.1, lowerStandardHList_valid vs h.2⟩

end BaseTransport

/-! ### Default valid values for inhabited `LinkedType`s -/

section LinkedOps
variable (b : Bindings)

def defaultValidNominal : (k : Sum TypeKey Parameter) → LinkedCarrier k
  | .inl (.field .koalaBear) => 0
  | .inl (.field .koalaBear4) => ext4Zero
  | .inl (.field .bls12381Fr) => 0
  | .inl (.nonzero .koalaBear) => 1
  | .inl (.nonzero .koalaBear4) => ext4One
  | .inl (.nonzero .bls12381Fr) => 1
  | .inl (.group .g1) => none
  | .inl (.group .g2) => 0
  | .inl (.group .gt) => 0
  | .inr _ => .unit

theorem defaultValidNominal_valid : ∀ k, LinkedValid k (defaultValidNominal k)
  | .inl (.field .koalaBear) => koalaBearOrder_pos
  | .inl (.field .koalaBear4) => ext4Zero_valid
  | .inl (.field .bls12381Fr) => bls12381FrOrder_pos
  | .inl (.nonzero .koalaBear) => ⟨Nat.zero_lt_one, koalaBearOrder_gt1⟩
  | .inl (.nonzero .koalaBear4) => ⟨ext4One_valid, ext4One_isNonzero⟩
  | .inl (.nonzero .bls12381Fr) => ⟨Nat.zero_lt_one, bls12381FrOrder_gt1⟩
  | .inl (.group .g1) => trivial
  | .inl (.group .g2) => bls12381FrOrder_pos
  | .inl (.group .gt) => bls12381FrOrder_pos
  | .inr _ => trivial

mutual
  /-- Construct a canonical valid value for any inhabited `LinkedType` (`τ.noValue = false`). -/
  def defaultValidVal : (τ : LinkedType) → τ.noValue = false → τ.Val (linkedCarriers b)
    | .bool, _ => false
    | .nat, _ => 0
    | .fin _, _ => 0
    | .seq _ none, _ => []
    | .seq _ (some 0), _ => []
    | .seq item (some (n + 1)), h => List.replicate (n + 1) (defaultValidVal item h)
    | .tuple items, h => defaultValidTys items h
    | .record _ _ fields, h => defaultValidTys fields h
    | .variant _ alts, h => defaultValidChoice alts h
    | .nominal k, _ => defaultValidNominal k

  def defaultValidTys : (τs : Core.Tys (Sum TypeKey Parameter)) →
      τs.someNoValue = false → τs.Val (linkedCarriers b)
    | .nil, _ => ()
    | .cons head rest, h =>
        have hp := Bool.or_eq_false_iff.mp h
        (defaultValidVal head hp.1, defaultValidTys rest hp.2)

  def defaultValidChoice : (τs : Core.Tys (Sum TypeKey Parameter)) →
      τs.allNoValue = false → τs.Choice (linkedCarriers b)
    | .nil, h => by simp [Tys.allNoValue] at h
    | .cons head rest, h =>
        if hh : head.noValue = false then .inl (defaultValidVal head hh)
        else
          have hht : head.noValue = true := by cases hnv : head.noValue <;> simp_all
          .inr (defaultValidChoice rest (by simpa [Tys.allNoValue, hht] using h))
end

mutual
  theorem defaultValidVal_valid : ∀ (τ : LinkedType) (h : τ.noValue = false),
      τ.Valid (linkedCarriers b) (defaultValidVal b τ h)
    | .bool, _ => trivial
    | .nat, _ => trivial
    | .fin bound, h => by
        simp only [Ty.noValue, beq_eq_false_iff_ne] at h
        exact Nat.pos_of_ne_zero h
    | .seq _ none, _ => ⟨(fun _ hm => nomatch hm), (fun _ hn => nomatch hn)⟩
    | .seq _ (some 0), _ => ⟨(fun _ hm => nomatch hm), (fun n hn => by cases hn; rfl)⟩
    | .seq item (some (n + 1)), h => by
        refine ⟨?_, fun k hk => by cases hk; simp [defaultValidVal]⟩
        intro v hv
        rw [defaultValidVal, List.mem_replicate] at hv
        rw [hv.2]
        exact defaultValidVal_valid item h
    | .tuple items, h => defaultValidTys_valid items h
    | .record _ _ fields, h => defaultValidTys_valid fields h
    | .variant _ alts, h => defaultValidChoice_valid alts h
    | .nominal k, _ => defaultValidNominal_valid k

  theorem defaultValidTys_valid : ∀ (τs : Core.Tys (Sum TypeKey Parameter)) (h : τs.someNoValue = false),
      τs.Valid (linkedCarriers b) (defaultValidTys b τs h)
    | .nil, _ => trivial
    | .cons head rest, h => by
        have hp := Bool.or_eq_false_iff.mp h
        exact ⟨defaultValidVal_valid head hp.1, defaultValidTys_valid rest hp.2⟩

  theorem defaultValidChoice_valid : ∀ (τs : Core.Tys (Sum TypeKey Parameter)) (h : τs.allNoValue = false),
      τs.ValidChoice (linkedCarriers b) (defaultValidChoice b τs h)
    | .nil, h => by simp [Tys.allNoValue] at h
    | .cons head rest, h => by
        unfold defaultValidChoice
        split
        · next hh => exact defaultValidVal_valid head hh
        · next hh =>
            have hht : head.noValue = true := by cases hnv : head.noValue <;> simp_all
            exact defaultValidChoice_valid rest (by simpa [Tys.allNoValue, hht] using h)
end

def defaultValidHList : (ts : List LinkedType) → (∀ τ ∈ ts, τ.noValue = false) →
    HList (Ty.Val (linkedCarriers b)) ts
  | [], _ => .nil
  | τ :: rest, h =>
      .cons (defaultValidVal b τ (h τ List.mem_cons_self))
        (defaultValidHList rest fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem defaultValidHList_valid : ∀ (ts : List LinkedType) (h : ∀ τ ∈ ts, τ.noValue = false),
    (defaultValidHList b ts h).All (Ty.Valid (linkedCarriers b))
  | [], _ => trivial
  | τ :: rest, h =>
      ⟨defaultValidVal_valid b τ (h τ List.mem_cons_self),
       defaultValidHList_valid rest fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

/-! ### Generic canonical serialization, deserialization, and equality on `linkedCarriers b` -/

def writeNominalBytes : (k : Sum TypeKey Parameter) → LinkedCarrier k → List Nat
  | .inl (.field .koalaBear), v => leBytes 4 (v % koalaBearOrder)
  | .inl (.field .koalaBear4), v =>
      let cs := ext4Norm v
      leBytes 4 (cs.getD 0 0) ++ leBytes 4 (cs.getD 1 0) ++
        leBytes 4 (cs.getD 2 0) ++ leBytes 4 (cs.getD 3 0)
  | .inl (.field .bls12381Fr), v => leBytes 32 (v % bls12381FrOrder)
  | .inl (.nonzero .koalaBear), v => leBytes 4 (v % koalaBearOrder)
  | .inl (.nonzero .koalaBear4), v =>
      let cs := ext4Norm v
      leBytes 4 (cs.getD 0 0) ++ leBytes 4 (cs.getD 1 0) ++
        leBytes 4 (cs.getD 2 0) ++ leBytes 4 (cs.getD 3 0)
  | .inl (.nonzero .bls12381Fr), v => leBytes 32 (v % bls12381FrOrder)
  | .inl (.group .g1), p => compressG1 p
  | .inl (.group .g2), v => leBytes 32 (v % bls12381FrOrder)
  | .inl (.group .gt), v => leBytes 32 (v % bls12381FrOrder)
  | .inr _, .bytes bs => formatNat.write bs.length ++ bs.map (· % 256)
  | .inr _, .nat n => formatNat.write n
  | .inr _, _ => []

def readKoalaBear4Bytes (bs : List Nat) : Option (List Nat × List Nat) :=
  match readFixed 4 bs with
  | some (c0, r0) =>
      match readFixed 4 r0 with
      | some (c1, r1) =>
          match readFixed 4 r1 with
          | some (c2, r2) =>
              match readFixed 4 r2 with
              | some (c3, r3) =>
                  if c0 < koalaBearOrder && c1 < koalaBearOrder &&
                      c2 < koalaBearOrder && c3 < koalaBearOrder then
                    some ([c0, c1, c2, c3], r3)
                  else none
              | none => none
          | none => none
      | none => none
  | none => none

theorem readKoalaBear4Bytes_valid (bs v rest) (h : readKoalaBear4Bytes bs = some (v, rest)) :
    Ext4Valid v := by
  simp only [readKoalaBear4Bytes] at h
  cases h0 : readFixed 4 bs with
  | none => simp [h0] at h
  | some p0 =>
      simp only [h0] at h
      cases h1 : readFixed 4 p0.2 with
      | none => simp [h1] at h
      | some p1 =>
          simp only [h1] at h
          cases h2 : readFixed 4 p1.2 with
          | none => simp [h2] at h
          | some p2 =>
              simp only [h2] at h
              cases h3 : readFixed 4 p2.2 with
              | none => simp [h3] at h
              | some p3 =>
                  simp only [h3] at h
                  split at h
                  · next hlt =>
                      cases h
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
                      refine ⟨rfl, fun c hc => ?_⟩
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
                      rcases hc with rfl | rfl | rfl | rfl
                      · exact hlt.1.1.1
                      · exact hlt.1.1.2
                      · exact hlt.1.2
                      · exact hlt.2
                  · cases h

def readNominalBytes : (k : Sum TypeKey Parameter) → List Nat →
    Option (LinkedCarrier k × List Nat)
  | .inl (.field .koalaBear), bs =>
      match readFixed 4 bs with
      | some (v, rest) => if v < koalaBearOrder then some (v, rest) else none
      | none => none
  | .inl (.field .koalaBear4), bs => readKoalaBear4Bytes bs
  | .inl (.field .bls12381Fr), bs =>
      match readFixed 32 bs with
      | some (v, rest) => if v < bls12381FrOrder then some (v, rest) else none
      | none => none
  | .inl (.nonzero .koalaBear), bs =>
      match readFixed 4 bs with
      | some (v, rest) => if 0 < v && v < koalaBearOrder then some (v, rest) else none
      | none => none
  | .inl (.nonzero .koalaBear4), bs =>
      match readKoalaBear4Bytes bs with
      | some (cs, rest) => if ext4IsNonzero cs then some (cs, rest) else none
      | none => none
  | .inl (.nonzero .bls12381Fr), bs =>
      match readFixed 32 bs with
      | some (v, rest) => if 0 < v && v < bls12381FrOrder then some (v, rest) else none
      | none => none
  | .inl (.group .g1), bs =>
      if bs.length < 48 then none
      else
        match decompressG1 (bs.take 48) with
        | some p => some (p, bs.drop 48)
        | none => none
  | .inl (.group .g2), bs =>
      match readFixed 32 bs with
      | some (v, rest) => if v < bls12381FrOrder then some (v, rest) else none
      | none => none
  | .inl (.group .gt), bs =>
      match readFixed 32 bs with
      | some (v, rest) => if v < bls12381FrOrder then some (v, rest) else none
      | none => none
  | .inr _, _ => none

theorem readNominalBytes_valid : ∀ k bs v rest,
    readNominalBytes k bs = some (v, rest) → LinkedValid k v
  | .inl (.field .koalaBear), bs, v, rest, h => by
      simp only [readNominalBytes] at h
      cases h1 : readFixed 4 bs with
      | none => simp [h1] at h
      | some p =>
          simp only [h1] at h
          split at h
          · cases h; assumption
          · cases h
  | .inl (.field .koalaBear4), bs, v, rest, h => readKoalaBear4Bytes_valid bs v rest h
  | .inl (.field .bls12381Fr), bs, v, rest, h => by
      simp only [readNominalBytes] at h
      cases h1 : readFixed 32 bs with
      | none => simp [h1] at h
      | some p =>
          simp only [h1] at h
          split at h
          · cases h; assumption
          · cases h
  | .inl (.nonzero .koalaBear), bs, v, rest, h => by
      simp only [readNominalBytes] at h
      cases h1 : readFixed 4 bs with
      | none => simp [h1] at h
      | some p =>
          simp only [h1] at h
          split at h
          · next hlt => cases h; simpa using hlt
          · cases h
  | .inl (.nonzero .koalaBear4), bs, v, rest, h => by
      simp only [readNominalBytes] at h
      cases h1 : readKoalaBear4Bytes bs with
      | none => simp [h1] at h
      | some p =>
          simp only [h1] at h
          split at h
          · next hnz =>
              cases h
              exact ⟨readKoalaBear4Bytes_valid bs p.1 p.2 h1, hnz⟩
          · cases h
  | .inl (.nonzero .bls12381Fr), bs, v, rest, h => by
      simp only [readNominalBytes] at h
      cases h1 : readFixed 32 bs with
      | none => simp [h1] at h
      | some p =>
          simp only [h1] at h
          split at h
          · next hlt => cases h; simpa using hlt
          · cases h
  | .inl (.group .g1), bs, v, rest, h => by
      simp only [readNominalBytes] at h
      split at h
      · cases h
      · cases hd : decompressG1 (bs.take 48) with
        | none => simp [hd] at h
        | some p =>
            simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have hg := (decompressG1_canonical hd).1
            simp only [g1InGroup, Bool.and_eq_true] at hg
            cases p with
            | none => trivial
            | some xy =>
                simp only [g1OnCurve, Bool.and_eq_true, decide_eq_true_eq] at hg
                exact ⟨hg.1.1.1, hg.1.1.2⟩
  | .inl (.group .g2), bs, v, rest, h => by
      simp only [readNominalBytes] at h
      cases h1 : readFixed 32 bs with
      | none => simp [h1] at h
      | some p =>
          simp only [h1] at h
          split at h
          · cases h; assumption
          · cases h
  | .inl (.group .gt), bs, v, rest, h => by
      simp only [readNominalBytes] at h
      cases h1 : readFixed 32 bs with
      | none => simp [h1] at h
      | some p =>
          simp only [h1] at h
          split at h
          · cases h; assumption
          · cases h
  | .inr _, _, _, _, h => by cases h

mutual
  /-- Write any `LinkedType` value in canonical byte format (`< 256`). -/
  def writeCanonicalVal : (τ : LinkedType) → τ.Val (linkedCarriers b) → List Nat
    | .bool, v => formatBool.write v
    | .nat, v => formatNat.write v
    | .fin bound, v => (formatFin bound).write v
    | .seq item (some _), xs => writeCanonicalMany (writeCanonicalVal item) xs
    | .seq item none, xs => formatNat.write xs.length ++ writeCanonicalMany (writeCanonicalVal item) xs
    | .tuple items, vs => writeCanonicalTys items vs
    | .record _ _ fields, vs => writeCanonicalTys fields vs
    | .variant _ alts, v =>
        let (tag, payload) := writeCanonicalChoice alts v
        (formatFin alts.length).write tag ++ payload
    | .nominal k, v => writeNominalBytes k v

  def writeCanonicalTys : (τs : Core.Tys (Sum TypeKey Parameter)) → τs.Val (linkedCarriers b) → List Nat
    | .nil, _ => []
    | .cons head rest, (v, vs) => writeCanonicalVal head v ++ writeCanonicalTys rest vs

  def writeCanonicalChoice : (alts : Core.Tys (Sum TypeKey Parameter)) →
      alts.Choice (linkedCarriers b) → Nat × List Nat
    | .nil, v => nomatch v
    | .cons head _, .inl v => (0, writeCanonicalVal head v)
    | .cons _ rest, .inr v =>
        let (t, p) := writeCanonicalChoice rest v
        (t + 1, p)
end

private theorem writeNominalBytes_bytes : ∀ k v c, c ∈ writeNominalBytes k v → c < 256
  | .inl (.field .koalaBear), _, c, hc => leBytes_bytes 4 _ c hc
  | .inl (.field .koalaBear4), _, c, hc => by
      simp only [writeNominalBytes, List.mem_append] at hc
      rcases hc with ((h | h) | h) | h <;> exact leBytes_bytes 4 _ c h
  | .inl (.field .bls12381Fr), _, c, hc => leBytes_bytes 32 _ c hc
  | .inl (.nonzero .koalaBear), _, c, hc => leBytes_bytes 4 _ c hc
  | .inl (.nonzero .koalaBear4), _, c, hc => by
      simp only [writeNominalBytes, List.mem_append] at hc
      rcases hc with ((h | h) | h) | h <;> exact leBytes_bytes 4 _ c h
  | .inl (.nonzero .bls12381Fr), _, c, hc => leBytes_bytes 32 _ c hc
  | .inl (.group .g1), p, c, hc => compressG1_bytes p c hc
  | .inl (.group .g2), _, c, hc => leBytes_bytes 32 _ c hc
  | .inl (.group .gt), _, c, hc => leBytes_bytes 32 _ c hc
  | .inr _, .bytes bs, c, hc => by
      simp only [writeNominalBytes, List.mem_append] at hc
      rcases hc with h | h
      · exact writeNat_bytes bs.length c h
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h; omega
  | .inr _, .nat n, c, hc => writeNat_bytes n c hc
  | .inr _, .unit, _, hc => nomatch hc
  | .inr _, .merlin _, _, hc => nomatch hc
  | .inr _, .cfrg _, _, hc => nomatch hc
  | .inr _, .poseidon2 _, _, hc => nomatch hc

private theorem writeCanonicalMany_bytes_raw {A : Type} {f : A → List Nat}
    (hf : ∀ x c, c ∈ f x → c < 256) : ∀ xs c, c ∈ writeCanonicalMany f xs → c < 256
  | [], _, hc => nomatch hc
  | x :: xs, c, hc => by
      simp only [writeCanonicalMany, List.mem_append] at hc
      rcases hc with h | h
      · exact hf x c h
      · exact writeCanonicalMany_bytes_raw hf xs c h

mutual
  theorem writeCanonicalVal_bytes : ∀ (τ : LinkedType) (v : τ.Val (linkedCarriers b)) c,
      c ∈ writeCanonicalVal b τ v → c < 256
    | .bool, v, c, hc => formatBool_lawful.bytes v trivial c hc
    | .nat, v, c, hc => writeNat_bytes v c hc
    | .fin bound, v, c, hc => writeFixed_bytes (byteWidth bound) v c hc
    | .seq item (some _), xs, c, hc =>
        writeCanonicalMany_bytes_raw (writeCanonicalVal_bytes item) xs c hc
    | .seq item none, xs, c, hc => by
        simp only [writeCanonicalVal, List.mem_append] at hc
        rcases hc with h | h
        · exact writeNat_bytes xs.length c h
        · exact writeCanonicalMany_bytes_raw (writeCanonicalVal_bytes item) xs c h
    | .tuple items, vs, c, hc => writeCanonicalTys_bytes items vs c hc
    | .record _ _ fields, vs, c, hc => writeCanonicalTys_bytes fields vs c hc
    | .variant _ alts, v, c, hc => by
        simp only [writeCanonicalVal, List.mem_append] at hc
        rcases hc with h | h
        · exact writeFixed_bytes (byteWidth alts.length) _ c h
        · exact writeCanonicalChoice_bytes alts v c h
    | .nominal k, v, c, hc => writeNominalBytes_bytes k v c hc

  theorem writeCanonicalTys_bytes : ∀ (τs : Core.Tys (Sum TypeKey Parameter))
      (vs : τs.Val (linkedCarriers b)) c, c ∈ writeCanonicalTys b τs vs → c < 256
    | .nil, _, _, hc => nomatch hc
    | .cons head rest, (v, vs), c, hc => by
        simp only [writeCanonicalTys, List.mem_append] at hc
        rcases hc with h | h
        · exact writeCanonicalVal_bytes head v c h
        · exact writeCanonicalTys_bytes rest vs c h

  theorem writeCanonicalChoice_bytes : ∀ (alts : Core.Tys (Sum TypeKey Parameter))
      (v : alts.Choice (linkedCarriers b)) c, c ∈ (writeCanonicalChoice b alts v).2 → c < 256
    | .nil, v, _, _ => nomatch v
    | .cons head _, .inl v, c, hc => writeCanonicalVal_bytes head v c hc
    | .cons _ rest, .inr v, c, hc => writeCanonicalChoice_bytes rest v c hc
end

mutual
  /-- Read a canonical byte-encoded value of `τ` from `bs`, rejecting any non-canonical or invalid encoding. -/
  def readCanonicalVal : (τ : LinkedType) → List Nat → Option (τ.Val (linkedCarriers b) × List Nat)
    | .bool, bs => formatBool.read bs
    | .nat, bs => formatNat.read bs
    | .fin bound, bs => (formatFin bound).read bs
    | .seq item (some count), bs => readCanonicalMany (readCanonicalVal item) count bs
    | .seq item none, bs =>
        match formatNat.read bs with
        | some (len, mid) => readCanonicalMany (readCanonicalVal item) len mid
        | none => none
    | .tuple items, bs => readCanonicalTys items bs
    | .record _ _ fields, bs => readCanonicalTys fields bs
    | .variant _ alts, bs =>
        match (formatFin alts.length).read bs with
        | some (tag, mid) => readCanonicalChoice alts tag mid
        | none => none
    | .nominal k, bs => readNominalBytes k bs

  def readCanonicalTys : (τs : Core.Tys (Sum TypeKey Parameter)) → List Nat →
      Option (τs.Val (linkedCarriers b) × List Nat)
    | .nil, bs => some ((), bs)
    | .cons head rest, bs =>
        match readCanonicalVal head bs with
        | some (v, mid) =>
            match readCanonicalTys rest mid with
            | some (vs, tail) => some ((v, vs), tail)
            | none => none
        | none => none

  def readCanonicalChoice : (alts : Core.Tys (Sum TypeKey Parameter)) → Nat → List Nat →
      Option (alts.Choice (linkedCarriers b) × List Nat)
    | .nil, _, _ => none
    | .cons head _, 0, bs =>
        match readCanonicalVal head bs with
        | some (v, rest) => some (.inl v, rest)
        | none => none
    | .cons _ rest, tag + 1, bs =>
        match readCanonicalChoice rest tag bs with
        | some (v, tail) => some (.inr v, tail)
        | none => none
end

private theorem readCanonicalMany_valid {A : Type} {P : A → Prop}
    {r : List Nat → Option (A × List Nat)}
    (hr : ∀ bs a rest, r bs = some (a, rest) → P a) :
    ∀ count bs xs rest, readCanonicalMany r count bs = some (xs, rest) →
      (∀ x ∈ xs, P x) ∧ xs.length = count
  | 0, _, xs, _, h => by
      simp only [readCanonicalMany, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨(fun _ hx => nomatch hx), rfl⟩
  | count + 1, bs, xs, rest, h => by
      simp only [readCanonicalMany] at h
      cases h1 : r bs with
      | none => simp [h1] at h
      | some p1 =>
          simp only [h1] at h
          cases h2 : readCanonicalMany r count p1.2 with
          | none => simp [h2] at h
          | some p2 =>
              simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, _⟩ := h
              have hv1 := hr bs p1.1 p1.2 h1
              have ⟨hv2, hlen⟩ := readCanonicalMany_valid hr count p1.2 p2.1 p2.2 h2
              refine ⟨fun x hx => ?_, by simp [hlen]⟩
              rcases List.mem_cons.mp hx with rfl | hm
              · exact hv1
              · exact hv2 x hm

mutual
  theorem readCanonicalVal_valid : ∀ (τ : LinkedType) bs v rest,
      readCanonicalVal b τ bs = some (v, rest) → τ.Valid (linkedCarriers b) v
    | .bool, _, _, _, _ => trivial
    | .nat, _, _, _, _ => trivial
    | .fin bound, bs, v, rest, h => ((formatFin_lawful bound).written bs v rest h).1
    | .seq item (some count), bs, xs, rest, h => by
        have ⟨hxs, hlen⟩ := readCanonicalMany_valid (readCanonicalVal_valid item) count bs xs rest h
        exact ⟨hxs, fun n hn => by cases hn; exact hlen⟩
    | .seq item none, bs, xs, rest, h => by
        simp only [readCanonicalVal] at h
        cases h1 : formatNat.read bs with
        | none => simp [h1] at h
        | some p =>
            simp only [h1] at h
            have ⟨hxs, _⟩ := readCanonicalMany_valid (readCanonicalVal_valid item) p.1 p.2 xs rest h
            exact ⟨hxs, fun _ hn => nomatch hn⟩
    | .tuple items, bs, vs, rest, h => readCanonicalTys_valid items bs vs rest h
    | .record _ _ fields, bs, vs, rest, h => readCanonicalTys_valid fields bs vs rest h
    | .variant _ alts, bs, v, rest, h => by
        simp only [readCanonicalVal] at h
        cases h1 : (formatFin alts.length).read bs with
        | none => simp [h1] at h
        | some p =>
            simp only [h1] at h
            exact readCanonicalChoice_valid alts p.1 p.2 v rest h
    | .nominal k, bs, v, rest, h => readNominalBytes_valid k bs v rest h

  theorem readCanonicalTys_valid : ∀ (τs : Core.Tys (Sum TypeKey Parameter)) bs vs rest,
      readCanonicalTys b τs bs = some (vs, rest) → τs.Valid (linkedCarriers b) vs
    | .nil, _, _, _, _ => trivial
    | .cons head restTys, bs, vs, rest, h => by
        simp only [readCanonicalTys] at h
        cases h1 : readCanonicalVal b head bs with
        | none => simp [h1] at h
        | some p1 =>
            simp only [h1] at h
            cases h2 : readCanonicalTys b restTys p1.2 with
            | none => simp [h2] at h
            | some p2 =>
                simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, _⟩ := h
                exact ⟨readCanonicalVal_valid head bs p1.1 p1.2 h1,
                       readCanonicalTys_valid restTys p1.2 p2.1 p2.2 h2⟩

  theorem readCanonicalChoice_valid : ∀ (alts : Core.Tys (Sum TypeKey Parameter)) tag bs v rest,
      readCanonicalChoice b alts tag bs = some (v, rest) → alts.ValidChoice (linkedCarriers b) v
    | .nil, _, _, _, _, h => by simp [readCanonicalChoice] at h
    | .cons head _, 0, bs, v, rest, h => by
        simp only [readCanonicalChoice] at h
        cases h1 : readCanonicalVal b head bs with
        | none => simp [h1] at h
        | some p =>
            simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact readCanonicalVal_valid head bs p.1 p.2 h1
    | .cons _ restAlts, tag + 1, bs, v, rest, h => by
        simp only [readCanonicalChoice] at h
        cases h1 : readCanonicalChoice b restAlts tag bs with
        | none => simp [h1] at h
        | some p =>
            simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact readCanonicalChoice_valid restAlts tag bs p.1 p.2 h1
end

/-! ### Generic equality on `linkedCarriers b` (`LayoutSlot.equal`) -/

def eqNominalVal : (k : Sum TypeKey Parameter) →
    LinkedCarrier k → LinkedCarrier k → Bool
  | .inl (.field f), x, y => fieldEqual f x y
  | .inl (.nonzero f), x, y =>
      match f with
      | .koalaBear => (x : Nat) % koalaBearOrder == (y : Nat) % koalaBearOrder
      | .koalaBear4 => ext4Norm x == ext4Norm y
      | .bls12381Fr => (x : Nat) % bls12381FrOrder == (y : Nat) % bls12381FrOrder
  | .inl (.group g), x, y => atomEqual (.group g) x y
  | .inr _, .bytes xs, .bytes ys => xs == ys
  | .inr _, .nat x, .nat y => x == y
  | .inr _, .unit, .unit => true
  | .inr _, _, _ => false

mutual
  def eqLinkedVal : (τ : LinkedType) → τ.Val (linkedCarriers b) → τ.Val (linkedCarriers b) → Bool
    | .bool, x, y => x == y
    | .nat, x, y => x == y
    | .fin _, x, y => x == y
    | .seq item _, xs, ys => eqLinkedList item xs ys
    | .tuple items, xs, ys => eqLinkedTys items xs ys
    | .record _ _ fields, xs, ys => eqLinkedTys fields xs ys
    | .variant _ alts, x, y => eqLinkedChoice alts x y
    | .nominal k, x, y => eqNominalVal k x y

  def eqLinkedList (item : LinkedType) :
      List (item.Val (linkedCarriers b)) → List (item.Val (linkedCarriers b)) → Bool
    | [], [] => true
    | x :: xs, y :: ys => eqLinkedVal item x y && eqLinkedList item xs ys
    | _, _ => false

  def eqLinkedTys : (τs : Core.Tys (Sum TypeKey Parameter)) →
      τs.Val (linkedCarriers b) → τs.Val (linkedCarriers b) → Bool
    | .nil, _, _ => true
    | .cons head rest, (x, xs), (y, ys) => eqLinkedVal head x y && eqLinkedTys rest xs ys

  def eqLinkedChoice : (alts : Core.Tys (Sum TypeKey Parameter)) →
      alts.Choice (linkedCarriers b) → alts.Choice (linkedCarriers b) → Bool
    | .nil, v, _ => nomatch v
    | .cons head _, .inl x, .inl y => eqLinkedVal head x y
    | .cons _ rest, .inr x, .inr y => eqLinkedChoice rest x y
    | .cons _ _, .inl _, .inr _ => false
    | .cons _ _, .inr _, .inl _ => false
end

/-! ### Native KoalaBear field-unit encoding & decoding (`Poseidon2KoalaBear`) -/

def writeKoalaUnitsVal (τ : LinkedType) (v : τ.Val (linkedCarriers b)) : List Nat :=
  match τ, v with
  | .nominal (.inl (.field .koalaBear)), x => [x % koalaBearOrder]
  | .nominal (.inl (.nonzero .koalaBear)), x => [x % koalaBearOrder]
  | .nominal (.inl (.field .koalaBear4)), xs => ext4Norm xs
  | .nominal (.inl (.nonzero .koalaBear4)), xs => ext4Norm xs
  | .seq (.nominal (.inl (.field .koalaBear))) (some _), xs => xs.map (· % koalaBearOrder)
  | .seq (.nominal (.inl (.field .koalaBear))) none, xs =>
      (xs.length % koalaBearOrder) :: xs.map (· % koalaBearOrder)
  | τ', v' =>
      let bs := writeCanonicalVal b τ' v'
      Poseidon2Suite.packBytesToFields (formatNat.write bs.length ++ bs)

private theorem packBytesToFields_lt : ∀ bs c, c ∈ Poseidon2Suite.packBytesToFields bs → c < koalaBearOrder := by
  intro bs
  unfold Poseidon2Suite.packBytesToFields
  induction bs using Poseidon2Suite.packBytesToFields.go.induct with
  | case1 => intro _ h; nomatch h
  | case2 b0 =>
      intro c hc
      simp only [Poseidon2Suite.packBytesToFields.go, List.mem_singleton] at hc
      subst hc; unfold koalaBearOrder; omega
  | case3 b0 b1 =>
      intro c hc
      simp only [Poseidon2Suite.packBytesToFields.go, List.mem_singleton] at hc
      subst hc; unfold koalaBearOrder; omega
  | case4 b0 b1 b2 rest ih =>
      intro c hc
      simp only [Poseidon2Suite.packBytesToFields.go, List.mem_cons] at hc
      rcases hc with rfl | hm
      · unfold koalaBearOrder; omega
      · exact ih c hm

theorem writeKoalaUnitsVal_valid (τ : LinkedType) (v : τ.Val (linkedCarriers b)) :
    ∀ c ∈ writeKoalaUnitsVal b τ v, c < koalaBearOrder := by
  unfold writeKoalaUnitsVal
  split
  · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact Nat.mod_lt _ koalaBearOrder_pos
  · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact Nat.mod_lt _ koalaBearOrder_pos
  · exact (ext4Norm_valid _).2
  · exact (ext4Norm_valid _).2
  · intro c hc; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc; exact Nat.mod_lt _ koalaBearOrder_pos
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hm
    · exact Nat.mod_lt _ koalaBearOrder_pos
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm; exact Nat.mod_lt _ koalaBearOrder_pos
  · exact packBytesToFields_lt _

/-! ### Generic transcript challenge derivation for any `LinkedType` (`SuiteSlot.derive`) -/

/-- Extract the raw `sessionTag` from Core's `resolveSessionBytes` encoding `1 :: encodeList encodeNat tag ++ ...`. -/
def extractSessionTag? (sessBytes : List Nat) : Option (List Nat) :=
  match sessBytes with
  | 1 :: rest =>
      match formatNat.read rest with
      | some (len, tail) =>
          match readCanonicalMany formatNat.read len tail with
          | some (tag, _) => some tag
          | none => none
      | none => none
  | _ => none

/- Generic byte-stream challenge decoder for any inhabited `LinkedType` (used by Merlin, CFRG,
and deterministic PRNG `Source`). Takes a byte squeezer `nextBytes : Nat → S → List Nat × S`. -/
section GenericDerive
variable {S : Type} (nextBytes : Nat → S → List Nat × S) (cfrgExactFin : Bool)

def deriveNominalVal (st : S) : (k : Sum TypeKey Parameter) → LinkedCarrier k × S
  | .inl (.field .koalaBear) =>
      let (bs, st') := nextBytes 16 st
      (fromLeBytes bs % koalaBearOrder, st')
  | .inl (.field .koalaBear4) =>
      let (bs, st') := nextBytes 64 st
      ([fromLeBytes (bs.take 16) % koalaBearOrder,
        fromLeBytes ((bs.drop 16).take 16) % koalaBearOrder,
        fromLeBytes ((bs.drop 32).take 16) % koalaBearOrder,
        fromLeBytes (bs.drop 48) % koalaBearOrder], st')
  | .inl (.field .bls12381Fr) =>
      let (bs, st') := nextBytes (if cfrgExactFin then 48 else 64) st
      let v := if cfrgExactFin then fromLeBytes bs % bls12381FrOrder else fromBeBytes bs % bls12381FrOrder
      (v, st')
  | .inl (.nonzero .koalaBear) =>
      let (bs, st') := nextBytes 16 st
      (nzPrime (fromLeBytes bs) koalaBearOrder, st')
  | .inl (.nonzero .koalaBear4) =>
      let (bs, st') := nextBytes 64 st
      (nzExt4 [fromLeBytes (bs.take 16) % koalaBearOrder,
               fromLeBytes ((bs.drop 16).take 16) % koalaBearOrder,
               fromLeBytes ((bs.drop 32).take 16) % koalaBearOrder,
               fromLeBytes (bs.drop 48) % koalaBearOrder], st')
  | .inl (.nonzero .bls12381Fr) =>
      let (bs, st') := nextBytes 64 st
      (nzPrime (fromBeBytes bs) bls12381FrOrder, st')
  | .inl (.group .g1) =>
      let (bs, st') := nextBytes 64 st
      (g1OfScalar (fromBeBytes bs % bls12381FrOrder), st')
  | .inl (.group .g2) =>
      let (bs, st') := nextBytes 64 st
      (fromBeBytes bs % bls12381FrOrder, st')
  | .inl (.group .gt) =>
      let (bs, st') := nextBytes 64 st
      (fromBeBytes bs % bls12381FrOrder, st')
  | .inr _ => (.unit, st)

theorem deriveNominalVal_valid (st : S) : ∀ k,
    LinkedValid k (deriveNominalVal nextBytes cfrgExactFin st k).1
  | .inl (.field .koalaBear) => Nat.mod_lt _ koalaBearOrder_pos
  | .inl (.field .koalaBear4) => by
      unfold deriveNominalVal
      refine ⟨rfl, fun c hc => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ koalaBearOrder_pos
  | .inl (.field .bls12381Fr) => by
      unfold deriveNominalVal
      dsimp only
      split <;> exact Nat.mod_lt _ bls12381FrOrder_pos
  | .inl (.nonzero .koalaBear) => nzPrime_valid _ _ koalaBearOrder_gt1
  | .inl (.nonzero .koalaBear4) => nzExt4_valid _
  | .inl (.nonzero .bls12381Fr) => nzPrime_valid _ _ bls12381FrOrder_gt1
  | .inl (.group .g1) => g1Scale_coordValid ..
  | .inl (.group .g2) => Nat.mod_lt _ bls12381FrOrder_pos
  | .inl (.group .gt) => Nat.mod_lt _ bls12381FrOrder_pos
  | .inr _ => trivial

mutual
  def deriveVal (st : S) : (τ : LinkedType) → τ.noValue = false → τ.Val (linkedCarriers b) × S
    | .bool, _ =>
        let (bs, st') := nextBytes 1 st
        (bs.headD 0 % 2 == 1, st')
    | .nat, _ =>
        let (bs, st') := nextBytes 8 st
        (fromLeBytes bs, st')
    | .fin bound, _ =>
        let count := if cfrgExactFin then byteWidth bound else 16
        let (bs, st') := nextBytes count st
        (if bound == 0 then 0 else fromLeBytes bs % bound, st')
    | .seq _ none, _ => ([], st)
    | .seq _ (some 0), _ => ([], st)
    | .seq item (some (n + 1)), h => deriveSeq item h (n + 1) st
    | .tuple items, h => deriveTys st items h
    | .record _ _ fields, h => deriveTys st fields h
    | .variant _ alts, h => (defaultValidChoice b alts h, st)
    | .nominal k, _ => deriveNominalVal nextBytes cfrgExactFin st k

  def deriveSeq (item : LinkedType) (h : item.noValue = false) :
      Nat → S → List (item.Val (linkedCarriers b)) × S
    | 0, st => ([], st)
    | n + 1, st =>
        let (v, st1) := deriveVal st item h
        let (vs, st2) := deriveSeq item h n st1
        (v :: vs, st2)

  def deriveTys (st : S) : (τs : Core.Tys (Sum TypeKey Parameter)) →
      τs.someNoValue = false → τs.Val (linkedCarriers b) × S
    | .nil, _ => ((), st)
    | .cons head rest, h =>
        have hp := Bool.or_eq_false_iff.mp h
        let (v, st1) := deriveVal st head hp.1
        let (vs, st2) := deriveTys st1 rest hp.2
        ((v, vs), st2)
end

mutual
  theorem deriveVal_valid (st : S) : ∀ (τ : LinkedType) (h : τ.noValue = false),
      τ.Valid (linkedCarriers b) (deriveVal b nextBytes cfrgExactFin st τ h).1
    | .bool, _ => trivial
    | .nat, _ => trivial
    | .fin bound, h => by
        simp only [Ty.noValue, beq_eq_false_iff_ne] at h
        unfold deriveVal
        dsimp only
        have hb : (bound == 0) = false := beq_false_of_ne h
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)
    | .seq _ none, _ => by
        rw [deriveVal]
        exact ⟨(fun _ hm => nomatch hm), (fun _ hn => nomatch hn)⟩
    | .seq _ (some 0), _ => by
        rw [deriveVal]
        exact ⟨(fun _ hm => nomatch hm), (fun n hn => by cases hn; rfl)⟩
    | .seq item (some (n + 1)), h => by
        rw [deriveVal]
        have ⟨hxs, hlen⟩ := deriveSeq_valid item h (n + 1) st
        exact ⟨hxs, fun k hk => by cases hk; exact hlen⟩
    | .tuple items, h => by rw [deriveVal]; exact deriveTys_valid st items h
    | .record _ _ fields, h => by rw [deriveVal]; exact deriveTys_valid st fields h
    | .variant _ alts, h => by rw [deriveVal]; exact defaultValidChoice_valid b alts h
    | .nominal k, _ => by rw [deriveVal]; exact deriveNominalVal_valid nextBytes cfrgExactFin st k

  theorem deriveSeq_valid (item : LinkedType) (h : item.noValue = false) :
      ∀ n st,
        (∀ x ∈ (deriveSeq b nextBytes cfrgExactFin item h n st).1, item.Valid (linkedCarriers b) x) ∧
        (deriveSeq b nextBytes cfrgExactFin item h n st).1.length = n
    | 0, _ => by rw [deriveSeq]; exact ⟨(fun _ hm => nomatch hm), rfl⟩
    | n + 1, st => by
        rw [deriveSeq]
        have hv := deriveVal_valid st item h
        have ⟨hvs, hlen⟩ := deriveSeq_valid item h n (deriveVal b nextBytes cfrgExactFin st item h).2
        refine ⟨fun x hx => ?_, by change _ + 1 = n + 1; rw [hlen]⟩
        rcases List.mem_cons.mp hx with rfl | hm
        · exact hv
        · exact hvs x hm

  theorem deriveTys_valid (st : S) : ∀ (τs : Core.Tys (Sum TypeKey Parameter))
      (h : τs.someNoValue = false),
      τs.Valid (linkedCarriers b) (deriveTys b nextBytes cfrgExactFin st τs h).1
    | .nil, _ => trivial
    | .cons head rest, h => by
        have hp := Bool.or_eq_false_iff.mp h
        rw [deriveTys]
        exact ⟨deriveVal_valid st head hp.1,
               deriveTys_valid (deriveVal b nextBytes cfrgExactFin st head hp.1).2 rest hp.2⟩
end

end GenericDerive

/-- Derive a challenge from Poseidon2-KoalaBear duplex natively (using native field squeezes for
`koala-bear` and `koala-bear.ext4`, and byte-packed squeezes for other types). -/
def derivePoseidon2Val (st : Poseidon2Suite.Duplex) (lbl : List Nat)
    (τ : LinkedType) (h : τ.noValue = false) : τ.Val (linkedCarriers b) × Poseidon2Suite.Duplex :=
  match τ, h with
  | .nominal (.inl (.field .koalaBear)), _ => Poseidon2Suite.deriveKoalaBear st lbl
  | .nominal (.inl (.field .koalaBear4)), _ => Poseidon2Suite.deriveKoalaBear4 st lbl
  | .nominal (.inl (.field .bls12381Fr)), _ => Poseidon2Suite.deriveFr st lbl
  | .bool, _ => Poseidon2Suite.deriveBool st lbl
  | .fin bound, _ => Poseidon2Suite.deriveFin st lbl bound
  | τ', h' =>
      let d1 := Poseidon2Suite.absorbFields st (4 :: Poseidon2Suite.packBytesToFields lbl)
      let nextB := fun (n : Nat) (d : Poseidon2Suite.Duplex) =>
        let (fs, d') := Poseidon2Suite.squeezeFields d ((n + 2) / 3)
        let bs := fs.flatMap fun x => [x % 256, (x / 256) % 256, (x / 65536) % 256]
        (bs.take n, d')
      deriveVal b nextB false d1 τ' h'

theorem derivePoseidon2Val_valid (st : Poseidon2Suite.Duplex) (lbl : List Nat)
    (τ : LinkedType) (h : τ.noValue = false) :
    τ.Valid (linkedCarriers b) (derivePoseidon2Val b st lbl τ h).1 := by
  unfold derivePoseidon2Val
  split
  · exact Nat.mod_lt _ koalaBearOrder_pos
  · exact ext4Norm_valid _
  · exact Nat.mod_lt _ bls12381FrOrder_pos
  · trivial
  · next bound h' =>
      simp only [Ty.noValue, beq_eq_false_iff_ne] at h'
      unfold Poseidon2Suite.deriveFin
      dsimp only
      have hb : (bound == 0) = false := beq_false_of_ne h'
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact Nat.mod_lt _ (Nat.pos_of_ne_zero h')
  · exact deriveVal_valid b _ false _ _ _

/-! ### Helper to extract `Fr` and `G1` values from runtime argument lists -/

def findFirstFr : {ts : List LinkedType} → HList (Ty.Val (linkedCarriers b)) ts → Option Nat
  | [], .nil => none
  | .nominal (.inl (.field .bls12381Fr)) :: _, .cons v _ => some v
  | .nominal (.inl (.nonzero .bls12381Fr)) :: _, .cons v _ => some v
  | _ :: _, .cons _ rest => findFirstFr rest

def collectG1s : {ts : List LinkedType} → HList (Ty.Val (linkedCarriers b)) ts → List G1Point
  | [], .nil => []
  | .nominal (.inl (.group .g1)) :: _, .cons p rest => p :: collectG1s rest
  | _ :: _, .cons _ rest => collectG1s rest

def collectFrs : {ts : List LinkedType} → HList (Ty.Val (linkedCarriers b)) ts → List Nat
  | [], .nil => []
  | .nominal (.inl (.field .bls12381Fr)) :: _, .cons s rest => s :: collectFrs rest
  | _ :: _, .cons _ rest => collectFrs rest

def collectBytesSeqs : {ts : List LinkedType} → HList (Ty.Val (linkedCarriers b)) ts → List (List Nat)
  | [], .nil => []
  | .seq (.fin 256) none :: _, .cons bs rest => bs :: collectBytesSeqs rest
  | _ :: _, .cons _ rest => collectBytesSeqs rest

def collectNats : {ts : List LinkedType} → HList (Ty.Val (linkedCarriers b)) ts → List Nat
  | [], .nil => []
  | .nat :: _, .cons n rest => n :: collectNats rest
  | _ :: _, .cons _ rest => collectNats rest

/-! ### Project-row dispatcher for `linkedModel?` -/

/-- Check that every project-bound primitive output type in `b` is inhabited (`noValue = false`). -/
def outputsInhabited (b : Bindings) : Bool :=
  b.rows.all fun (_, sig) => sig.outputs.all fun τ => !τ.noValue

private theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {v : β}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by cases h
  | (k', v') :: rest, k, v, h => by
      simp only [List.lookup] at h
      split at h
      · next heq =>
          cases h
          have : k = k' := eq_of_beq heq
          subst this
          exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)

theorem outputsInhabited_lookup {b : Bindings} (hOk : outputsInhabited b = true)
    {k : PrimitiveName} {sig : PrimitiveSignature} (hSig : b.signature k = some sig) :
    ∀ τ ∈ sig.outputs, τ.noValue = false := by
  intro τ hτ
  have hmem : (k, sig) ∈ b.rows := mem_of_lookup_eq_some hSig
  unfold outputsInhabited at hOk
  have hrow := List.all_eq_true.mp hOk (k, sig) hmem
  have hout := List.all_eq_true.mp hrow τ hτ
  cases hnv : τ.noValue <;> simp_all

/-- Dispatch Merlin 1.0 & `signature::Suite` rows. -/
def evalMerlinRow (b : Bindings) (name : String) (ins outs : List LinkedType)
    (hOuts : ∀ τ ∈ outs, τ.noValue = false)
    (args : HList (Ty.Val (linkedCarriers b)) ins) :
    { vs : HList (Ty.Val (linkedCarriers b)) outs // vs.All (Ty.Valid (linkedCarriers b)) } :=
  match name, ins, outs, args, hOuts with
  | "suite.merlin3.start", [.seq (.fin 256) none], [.nominal (.inr _)], .cons idBytes .nil, _
  | "suite.schnorr-signature.start", [.seq (.fin 256) none], [.nominal (.inr _)], .cons idBytes .nil, _ =>
      ⟨.cons (.merlin (Merlin.start idBytes)) .nil, ⟨trivial, trivial⟩⟩
  | "suite.merlin3.absorb", [.nominal (.inr _), .seq (.fin 256) none, .seq (.fin 256) none],
      [.nominal (.inr _)], .cons st (.cons lbl (.cons data .nil)), _
  | "suite.schnorr-signature.absorb", [.nominal (.inr _), .seq (.fin 256) none, .seq (.fin 256) none],
      [.nominal (.inr _)], .cons st (.cons lbl (.cons data .nil)), _ =>
      let ms := match st with | .merlin s => s | _ => Merlin.start []
      ⟨.cons (.merlin (Merlin.absorb ms lbl data)) .nil, ⟨trivial, trivial⟩⟩
  | "suite.merlin3.encode", [τ], [.seq (.fin 256) none], .cons v .nil, _
  | "suite.schnorr-signature.encode", [τ], [.seq (.fin 256) none], .cons v .nil, _ =>
      let bs := writeCanonicalVal b τ v
      ⟨.cons bs .nil, ⟨⟨writeCanonicalVal_bytes b τ v, fun _ hn => nomatch hn⟩, trivial⟩⟩
  | "suite.merlin3.derive", [.nominal (.inr _), .seq (.fin 256) none], [τ, .nominal (.inr _)],
      .cons st (.cons lbl .nil), hOuts
  | "suite.schnorr-signature.derive", [.nominal (.inr _), .seq (.fin 256) none], [τ, .nominal (.inr _)],
      .cons st (.cons lbl .nil), hOuts =>
      let ms := match st with | .merlin s => s | _ => Merlin.start []
      have hτ : τ.noValue = false := hOuts τ List.mem_cons_self
      let nextB := fun n s => Merlin.challengeBytes s lbl n
      let res := deriveVal b nextB false ms τ hτ
      ⟨.cons res.1 (.cons (.merlin res.2) .nil),
       ⟨deriveVal_valid b nextB false ms τ hτ, ⟨trivial, trivial⟩⟩⟩
  | _, _, outs, _, hOuts =>
      ⟨defaultValidHList b outs hOuts, defaultValidHList_valid b outs hOuts⟩

/-- Dispatch CFRG draft-04 SHAKE128 & TurboSHAKE128 rows (derived session ID & raw 32-byte tag). -/
def evalCfrgRow (b : Bindings) (name : String) (ins outs : List LinkedType)
    (hOuts : ∀ τ ∈ outs, τ.noValue = false)
    (args : HList (Ty.Val (linkedCarriers b)) ins) :
    { vs : HList (Ty.Val (linkedCarriers b)) outs // vs.All (Ty.Valid (linkedCarriers b)) } :=
  let isTurbo := name.startsWith "suite.cfrg.turboshake128"
  let isRaw := name.startsWith "suite.cfrg.shake128.raw." || name.startsWith "suite.cfrg.turboshake128.raw."
  let xof : Cfrg.Variant := if isTurbo then .turboShake128 else .shake128
  let action := (name.splitOn ".").getLastD ""
  match action, ins, outs, args, hOuts with
  | "start", [.seq (.fin 256) none], [.nominal (.inr _)], .cons idBytes .nil, _ =>
      let st :=
        if isRaw then
          match extractSessionTag? idBytes with
          | some tag => if tag.length == 32 then Cfrg.startRaw xof tag else Cfrg.start xof tag
          | none => Cfrg.start xof idBytes
        else Cfrg.start xof idBytes
      ⟨.cons (.cfrg st) .nil, ⟨trivial, trivial⟩⟩
  | "absorb", [.nominal (.inr _), .seq (.fin 256) none, .seq (.fin 256) none],
      [.nominal (.inr _)], .cons st (.cons lbl (.cons data .nil)), _ =>
      let cs := match st with | .cfrg d => d | _ => Cfrg.start xof []
      ⟨.cons (.cfrg (Cfrg.absorb cs lbl data)) .nil, ⟨trivial, trivial⟩⟩
  | "encode", [τ], [.seq (.fin 256) none], .cons v .nil, _ =>
      let bs := writeCanonicalVal b τ v
      ⟨.cons bs .nil, ⟨⟨writeCanonicalVal_bytes b τ v, fun _ hn => nomatch hn⟩, trivial⟩⟩
  | "derive", [.nominal (.inr _), .seq (.fin 256) none], [τ, .nominal (.inr _)],
      .cons st (.cons _ .nil), hOuts =>
      let cs := match st with | .cfrg d => d | _ => Cfrg.start xof []
      have hτ : τ.noValue = false := hOuts τ List.mem_cons_self
      let nextB := fun n d => Cfrg.squeeze d n
      let res := deriveVal b nextB true cs τ hτ
      ⟨.cons res.1 (.cons (.cfrg res.2) .nil),
       ⟨deriveVal_valid b nextB true cs τ hτ, ⟨trivial, trivial⟩⟩⟩
  | _, _, outs, _, hOuts =>
      ⟨defaultValidHList b outs hOuts, defaultValidHList_valid b outs hOuts⟩

/-- Dispatch Poseidon2-KoalaBear duplex rows (native KoalaBear field-element units). -/
def evalPoseidon2Row (b : Bindings) (name : String) (ins outs : List LinkedType)
    (hOuts : ∀ τ ∈ outs, τ.noValue = false)
    (args : HList (Ty.Val (linkedCarriers b)) ins) :
    { vs : HList (Ty.Val (linkedCarriers b)) outs // vs.All (Ty.Valid (linkedCarriers b)) } :=
  match name, ins, outs, args, hOuts with
  | "suite.poseidon2.start", [.seq (.fin 256) none], [.nominal (.inr _)], .cons idBytes .nil, _ =>
      ⟨.cons (.poseidon2 (Poseidon2Suite.start idBytes)) .nil, ⟨trivial, trivial⟩⟩
  | "suite.poseidon2.absorb",
      [.nominal (.inr _), .seq (.fin 256) none, .seq (.nominal (.inl (.field .koalaBear))) none],
      [.nominal (.inr _)], .cons st (.cons lbl (.cons units .nil)), _ =>
      let ps := match st with | .poseidon2 d => d | _ => Poseidon2Suite.start []
      ⟨.cons (.poseidon2 (Poseidon2Suite.absorb ps lbl units)) .nil, ⟨trivial, trivial⟩⟩
  | "suite.poseidon2.encode", [τ], [.seq (.nominal (.inl (.field .koalaBear))) none], .cons v .nil, _ =>
      let us := writeKoalaUnitsVal b τ v
      ⟨.cons us .nil, ⟨⟨writeKoalaUnitsVal_valid b τ v, fun _ hn => nomatch hn⟩, trivial⟩⟩
  | "suite.poseidon2.derive", [.nominal (.inr _), .seq (.fin 256) none], [τ, .nominal (.inr _)],
      .cons st (.cons lbl .nil), hOuts =>
      let ps := match st with | .poseidon2 d => d | _ => Poseidon2Suite.start []
      have hτ : τ.noValue = false := hOuts τ List.mem_cons_self
      let res := derivePoseidon2Val b ps lbl τ hτ
      ⟨.cons res.1 (.cons (.poseidon2 res.2) .nil),
       ⟨derivePoseidon2Val_valid b ps lbl τ hτ, ⟨trivial, trivial⟩⟩⟩
  | _, _, outs, _, hOuts =>
      ⟨defaultValidHList b outs hOuts, defaultValidHList_valid b outs hOuts⟩

/-- Dispatch `layout.canonical.*` rows. -/
def evalCanonicalLayoutRow (b : Bindings) (name : String) (ins outs : List LinkedType)
    (hOuts : ∀ τ ∈ outs, τ.noValue = false)
    (args : HList (Ty.Val (linkedCarriers b)) ins) :
    { vs : HList (Ty.Val (linkedCarriers b)) outs // vs.All (Ty.Valid (linkedCarriers b)) } :=
  match name, ins, outs, args, hOuts with
  | "layout.canonical.write", [τ], [.seq (.fin 256) none], .cons v .nil, _ =>
      let bs := writeCanonicalVal b τ v
      ⟨.cons bs .nil, ⟨⟨writeCanonicalVal_bytes b τ v, fun _ hn => nomatch hn⟩, trivial⟩⟩
  | "layout.canonical.try_read", [.seq (.fin 256) none, .nat], [.bool, τ, .nat],
      .cons buf (.cons off .nil), hOuts =>
      have hτ : τ.noValue = false := hOuts τ (List.mem_cons_of_mem _ List.mem_cons_self)
      if off ≤ buf.length then
        let slice := buf.drop off
        match hr : readCanonicalVal b τ slice with
        | some (v, rest) =>
            let consumed := slice.length - rest.length
            ⟨.cons true (.cons v (.cons (off + consumed) .nil)),
             ⟨trivial, ⟨readCanonicalVal_valid b τ slice v rest hr, ⟨trivial, trivial⟩⟩⟩⟩
        | none =>
            ⟨.cons false (.cons (defaultValidVal b τ hτ) (.cons off .nil)),
             ⟨trivial, ⟨defaultValidVal_valid b τ hτ, ⟨trivial, trivial⟩⟩⟩⟩
      else
        ⟨.cons false (.cons (defaultValidVal b τ hτ) (.cons off .nil)),
         ⟨trivial, ⟨defaultValidVal_valid b τ hτ, ⟨trivial, trivial⟩⟩⟩⟩
  | "layout.canonical.equal", [τ₁, τ₂], [.bool], .cons v1 (.cons v2 .nil), _ =>
      if hEq : τ₁ = τ₂ then
        ⟨.cons (eqLinkedVal b τ₁ v1 (hEq ▸ v2)) .nil, ⟨trivial, trivial⟩⟩
      else
        ⟨.cons false .nil, ⟨trivial, trivial⟩⟩
  | _, _, outs, _, hOuts =>
      ⟨defaultValidHList b outs hOuts, defaultValidHList_valid b outs hOuts⟩

/-- Dispatch `group.to_bytes` and `signature.*` rows. -/
def evalSignatureRow (b : Bindings) (name : String) (ins outs : List LinkedType)
    (hOuts : ∀ τ ∈ outs, τ.noValue = false)
    (args : HList (Ty.Val (linkedCarriers b)) ins) :
    { vs : HList (Ty.Val (linkedCarriers b)) outs // vs.All (Ty.Valid (linkedCarriers b)) } :=
  match name, ins, outs, args, hOuts with
  | "group.to_bytes", [.nominal (.inl (.group .g1))], [.seq (.fin 256) none], .cons pt .nil, _ =>
      ⟨.cons (compressG1 pt) .nil, ⟨⟨compressG1_bytes pt, fun _ hn => nomatch hn⟩, trivial⟩⟩
  | "signature.nonce", [.nominal (.inl (.field .bls12381Fr)), .seq (.fin 256) none, .nat, .nat],
      [.seq (.fin 256) (some 64)], .cons sk (.cons ctx (.cons site (.cons tries .nil))), _ =>
      let bs := Signature.nonceBytes sk ctx site tries
      have ⟨hlen, hbytes⟩ := shake256Bytes_len_and_bytes
        (utf8Bytes "zkc.signature.nonce/0" ++ leBytes 32 (sk % bls12381FrOrder) ++
         leBytes 8 ctx.length ++ ctx ++ leBytes 8 site ++ leBytes 8 tries) 64
      ⟨.cons bs .nil, ⟨⟨hbytes, fun n hn => by cases hn; exact hlen⟩, trivial⟩⟩
  | "signature.nonce_scalar", _, [.nominal (.inl (.field .bls12381Fr))], args, _ =>
      let sk := (findFirstFr b args).getD 1
      let bseqs := collectBytesSeqs b args
      let nats := collectNats b args
      let sessBytes := bseqs.getD (bseqs.length - 2) []
      let siteBytes := bseqs.getD (bseqs.length - 1) []
      let attempt := nats.getD (nats.length - 2) 0
      let callSeq := nats.getD (nats.length - 1) 0
      let r := Signature.nonceScalar sk sessBytes siteBytes attempt callSeq
      have hr : r < bls12381FrOrder := by
        dsimp only [r]
        unfold Signature.nonceScalar
        dsimp only
        split
        · exact bls12381FrOrder_gt1
        · exact Nat.mod_lt _ bls12381FrOrder_pos
      ⟨.cons r .nil, ⟨hr, trivial⟩⟩
  | "signature.commitment", [.seq (.fin 256) none, .nominal (.inl (.field .bls12381Fr)),
      .nominal (.inl (.field .bls12381Fr))], [.nominal (.inl (.group .g1))],
      .cons stmtBytes (.cons c (.cons z .nil)), _ =>
      let pt := (Signature.recoverCommitmentFromStatementBytes stmtBytes c z).getD none
      have hpt : G1CoordValid pt := by
        dsimp only [pt]
        cases h : Signature.recoverCommitmentFromStatementBytes stmtBytes c z with
        | none => trivial
        | some p =>
            unfold Signature.recoverCommitmentFromStatementBytes at h
            cases h1 : decompressG1 (stmtBytes.take 48) with
            | none => simp [h1] at h
            | some base =>
                cases h2 : decompressG1 ((stmtBytes.drop 48).take 48) with
                | none => simp [h1, h2] at h
                | some point =>
                    simp [h1, h2] at h
                    cases h
                    exact g1Sub_coordValid _ _ (g1Scale_coordValid base z)
      ⟨.cons pt .nil, ⟨hpt, trivial⟩⟩
  | "signature.recover_commitment", _, [.nominal (.inl (.group .g1))], args, _ =>
      let g1s := collectG1s b args
      let frs := collectFrs b args
      let base := g1s.getD 0 none
      let point := g1s.getD 1 none
      let challenge := frs.getD (frs.length - 2) 0
      let response := frs.getD (frs.length - 1) 0
      let pt := Signature.recoverCommitment base point challenge response
      ⟨.cons pt .nil, ⟨g1Sub_coordValid _ _ (g1Scale_coordValid base response), trivial⟩⟩
  | "signature.keygen", [.seq (.fin 256) (some 32)],
      [.tuple (.cons (.nominal (.inl (.field .bls12381Fr))) (.cons (.nominal (.inl (.group .g1))) .nil))],
      .cons seed .nil, _ =>
      let sk := (Signature.keygen seed).1
      let pk := (Signature.keygen seed).2
      have hsk : sk < bls12381FrOrder := by
        dsimp only [sk]
        unfold Signature.keygen
        dsimp only
        split
        · exact bls12381FrOrder_gt1
        · exact Nat.mod_lt _ bls12381FrOrder_pos
      have hpk : G1CoordValid pk := by
        dsimp only [pk]
        unfold Signature.keygen
        dsimp only
        exact g1Scale_coordValid g1Generator _
      ⟨.cons (sk, (pk, ())) .nil, ⟨⟨hsk, ⟨hpk, trivial⟩⟩, trivial⟩⟩
  | _, _, outs, _, hOuts =>
      ⟨defaultValidHList b outs hOuts, defaultValidHList_valid b outs hOuts⟩

/-- Dispatch Mersenne31 Sumcheck helpers (`cfrg.m31.*`) for CFRG draft-04 C.5.1/C.5.2 vectors. -/
def evalCfrgM31Row (b : Bindings) (name : String) (ins outs : List LinkedType)
    (hOuts : ∀ τ ∈ outs, τ.noValue = false)
    (args : HList (Ty.Val (linkedCarriers b)) ins) :
    { vs : HList (Ty.Val (linkedCarriers b)) outs // vs.All (Ty.Valid (linkedCarriers b)) } :=
  match name, ins, outs, args, hOuts with
  | "cfrg.m31.round_poly", [.seq (.fin _) (some _)],
      [.tuple (.cons (.fin p0) (.cons (.fin p1) .nil))], .cons w .nil, hOuts =>
      if h0 : 0 < p0 then
        if h1 : 0 < p1 then
          let m31 : Nat := 2147483647
          let evenSum := (w.zipIdx.filter (fun q => q.2 % 2 == 0)).foldl (fun acc q => (acc + q.1) % m31) 0
          let oddSum := (w.zipIdx.filter (fun q => q.2 % 2 == 1)).foldl (fun acc q => (acc + q.1) % m31) 0
          let a0 := (evenSum % m31) % p0
          let a1 := ((oddSum % m31 + m31 - evenSum % m31) % m31) % p1
          ⟨.cons (a0, (a1, ())) .nil, ⟨⟨Nat.mod_lt _ h0, ⟨Nat.mod_lt _ h1, trivial⟩⟩, trivial⟩⟩
        else
          ⟨defaultValidHList b _ hOuts, defaultValidHList_valid b _ hOuts⟩
      else
        ⟨defaultValidHList b _ hOuts, defaultValidHList_valid b _ hOuts⟩
  | "cfrg.m31.fold", [.seq (.fin _) (some _), .fin _],
      [.seq (.fin pOut) (some m)], .cons w (.cons r .nil), hOuts =>
      if hp : 0 < pOut then
        let m31 : Nat := 2147483647
        let nextW := (List.range m).map fun i =>
          let x0 := w.getD (2 * i) 0 % m31
          let x1 := w.getD (2 * i + 1) 0 % m31
          let diff := (x1 + m31 - x0) % m31
          ((x0 + r * diff) % m31) % pOut
        have hvalid : (∀ x ∈ nextW, x < pOut) ∧ ∀ k, some m = some k → nextW.length = k := by
          refine ⟨fun x hx => ?_, fun k hk => by cases hk; simp [nextW]⟩
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
          exact Nat.mod_lt _ hp
        ⟨.cons nextW .nil, ⟨hvalid, trivial⟩⟩
      else
        ⟨defaultValidHList b _ hOuts, defaultValidHList_valid b _ hOuts⟩
  | "cfrg.m31.check_sum", [.fin _,
      .tuple (.cons (.fin _) (.cons (.fin _) .nil))], [.bool],
      .cons s (.cons (a0, (a1, ())) .nil), _ =>
      let m31 : Nat := 2147483647
      ⟨.cons ((2 * a0 + a1) % m31 == s % m31) .nil, ⟨trivial, trivial⟩⟩
  | "cfrg.m31.eval_lin",
      [.tuple (.cons (.fin _) (.cons (.fin _) .nil)), .fin _],
      [.fin pOut], .cons (a0, (a1, ())) (.cons r .nil), hOuts =>
      if hp : 0 < pOut then
        let m31 : Nat := 2147483647
        ⟨.cons (((a0 + a1 * r) % m31) % pOut) .nil, ⟨Nat.mod_lt _ hp, trivial⟩⟩
      else
        ⟨defaultValidHList b _ hOuts, defaultValidHList_valid b _ hOuts⟩
  | "cfrg.m31.head", [.seq (.fin _) (some _)], [.fin pOut], .cons w .nil, hOuts =>
      if hp : 0 < pOut then
        let m31 : Nat := 2147483647
        ⟨.cons ((w.headD 0 % m31) % pOut) .nil, ⟨Nat.mod_lt _ hp, trivial⟩⟩
      else
        ⟨defaultValidHList b _ hOuts, defaultValidHList_valid b _ hOuts⟩
  | _, _, outs, _, hOuts =>
      ⟨defaultValidHList b outs hOuts, defaultValidHList_valid b outs hOuts⟩

/-- Dispatch a project-bound primitive row in `linkedModel?`, returning both the output `HList`
and a proof that every output value is valid. -/
def evalProjectRow (b : Bindings) (p : PrimitiveName) (ins outs : List LinkedType)
    (hOuts : ∀ τ ∈ outs, τ.noValue = false)
    (args : HList (Ty.Val (linkedCarriers b)) ins) :
    { vs : HList (Ty.Val (linkedCarriers b)) outs // vs.All (Ty.Valid (linkedCarriers b)) } :=
  if p.name.startsWith "suite.merlin3." || p.name.startsWith "suite.schnorr-signature." then
    evalMerlinRow b p.name ins outs hOuts args
  else if p.name.startsWith "suite.cfrg." then
    evalCfrgRow b p.name ins outs hOuts args
  else if p.name.startsWith "suite.poseidon2." then
    evalPoseidon2Row b p.name ins outs hOuts args
  else if p.name.startsWith "layout.canonical." then
    evalCanonicalLayoutRow b p.name ins outs hOuts args
  else if p.name.startsWith "signature." || p.name == "group.to_bytes" then
    evalSignatureRow b p.name ins outs hOuts args
  else if p.name.startsWith "cfrg.m31." then
    evalCfrgM31Row b p.name ins outs hOuts args
  else
    ⟨defaultValidHList b outs hOuts, defaultValidHList_valid b outs hOuts⟩

end LinkedOps

/-! ## `linkedModel? (b : Bindings) : Except String (Core.Model b.vocabulary)` -/

/-- Row application function for `linkedModel? b`, separating standard (`.inl`) and project (`.inr`) rows. -/
def linkedApply (b : Bindings) (hInhab : outputsInhabited b = true) :
    (key : b.vocabulary.RowKey) → (sig : RowSignature b.vocabulary.TypeKey b.vocabulary.RowKey) →
    b.vocabulary.row key = some sig →
    HList (Ty.Val (linkedCarriers b)) sig.ins →
    Option (HList (Ty.Val (linkedCarriers b)) sig.outs)
  | .inl k, sig, h, args =>
      match hStd : standard.row k with
      | none =>
          False.elim (by simp [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row, hStd] at h)
      | some stdSig =>
          have hEq : PurePrimitives.baseRow stdSig = sig := by
            simp only [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row, hStd,
              Option.map_some] at h
            exact Option.some.inj h
          match sig, hEq, args with
          | _, rfl, args =>
              (standardApply k stdSig hStd (lowerStandardHList b args)).map (liftStandardHList b)
  | .inr p, sig, h, args =>
      match hSig : b.signature p with
      | none =>
          False.elim (by simp [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row,
            Bindings.primitives, hSig] at h)
      | some ps =>
          have hEq : ({ ins := ps.inputs, outs := ps.outputs, kind := .pure } :
              RowSignature b.vocabulary.TypeKey b.vocabulary.RowKey) = sig := by
            simp only [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row,
              Bindings.primitives, hSig, Option.map_some] at h
            exact Option.some.inj h
          match sig, hEq, args with
          | _, rfl, args =>
              some (evalProjectRow b p ps.inputs ps.outputs
                (outputsInhabited_lookup hInhab hSig) args).1

theorem linkedApply_inl (b : Bindings) (hInhab : outputsInhabited b = true)
    (k : standard.RowKey) (stdSig : RowSignature standard.TypeKey standard.RowKey)
    (hStd : standard.row k = some stdSig)
    (h : b.vocabulary.row (.inl k) = some (PurePrimitives.baseRow stdSig))
    (args : HList (Ty.Val (linkedCarriers b)) (stdSig.ins.map (Ty.mapNominal Sum.inl))) :
    linkedApply b hInhab (.inl k) (PurePrimitives.baseRow stdSig) h args =
      (standardApply k stdSig hStd (lowerStandardHList b args)).map (liftStandardHList b) := by
  dsimp only [linkedApply]
  split
  · next h' => rw [hStd] at h'; cases h'
  · next stdSig' h' =>
      rw [hStd] at h'
      cases h'
      rfl

theorem linkedApply_inr (b : Bindings) (hInhab : outputsInhabited b = true)
    (p : PrimitiveName) (ps : PrimitiveSignature) (hSig : b.signature p = some ps)
    (h : b.vocabulary.row (.inr p) = some { ins := ps.inputs, outs := ps.outputs, kind := .pure })
    (args : HList (Ty.Val (linkedCarriers b)) ps.inputs) :
    linkedApply b hInhab (.inr p) { ins := ps.inputs, outs := ps.outputs, kind := .pure } h args =
      some (evalProjectRow b p ps.inputs ps.outputs (outputsInhabited_lookup hInhab hSig) args).1 := by
  dsimp only [linkedApply]
  split
  · next h' => rw [hSig] at h'; cases h'
  · next ps' h' =>
      rw [hSig] at h'
      cases h'
      rfl

/-- Build a verified `Core.Model b.vocabulary` for any project `Bindings` whose primitive outputs
are inhabited (`outputsInhabited b = true`). -/
def linkedModel? (b : Bindings) : Except String (Model b.vocabulary) :=
  if hInhab : outputsInhabited b = true then
    .ok {
      toCarriers := linkedCarriers b
      apply := linkedApply b hInhab
      inDomain := fun key sig h args => (linkedApply b hInhab key sig h args).isSome
      defined := fun _ _ _ _ => rfl
      total := fun key sig h args hp => by
        cases key with
        | inl k =>
            cases hStd : standard.row k with
            | none =>
                simp [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row, hStd] at h
            | some stdSig =>
                have hEq : PurePrimitives.baseRow stdSig = sig := by
                  simp only [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row, hStd,
                    Option.map_some] at h
                  exact Option.some.inj h
                subst hEq
                rw [linkedApply_inl b hInhab k stdSig hStd h args]
                have hpStd : stdSig.kind = .pure := by
                  cases hk : stdSig.kind with
                  | pure => rfl
                  | restricted _ => simp [PurePrimitives.baseRow, hk] at hp
                have ht := standard_total k stdSig hStd (lowerStandardHList b args) hpStd
                simp only [standardInDomain, Option.isSome_iff_exists] at ht
                obtain ⟨outs, houts⟩ := ht
                rw [houts]
                rfl
        | inr p =>
            cases hSig : b.signature p with
            | none =>
                simp [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row,
                  Bindings.primitives, hSig] at h
            | some ps =>
                have hEq : ({ ins := ps.inputs, outs := ps.outputs, kind := .pure } :
                    RowSignature b.vocabulary.TypeKey b.vocabulary.RowKey) = sig := by
                  simp only [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row,
                    Bindings.primitives, hSig, Option.map_some] at h
                  exact Option.some.inj h
                subst hEq
                rw [linkedApply_inr b hInhab p ps hSig h args]
                rfl
      decides := fun key sig h domain hk args => by
        cases key with
        | inl k =>
            cases hStd : standard.row k with
            | none =>
                simp [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row, hStd] at h
            | some stdSig =>
                have hEq : PurePrimitives.baseRow stdSig = sig := by
                  simp only [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row, hStd,
                    Option.map_some] at h
                  exact Option.some.inj h
                subst hEq
                cases hKind : stdSig.kind with
                | pure => simp [PurePrimitives.baseRow, hKind] at hk
                | restricted d =>
                    simp only [PurePrimitives.baseRow, hKind] at hk
                    cases hk
                    have hDom := standard.decided k stdSig d hStd hKind
                    have hDec := standard_decides k stdSig hStd d hKind (lowerStandardHList b args)
                    rw [linkedApply_inl b hInhab k stdSig hStd h args]
                    have hDomLinked : b.vocabulary.row (.inl d) =
                        some (PurePrimitives.baseRow { ins := stdSig.ins, outs := [.bool], kind := .pure }) := by
                      simp [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row, hDom]
                    have hLhs := linkedApply_inl b hInhab d
                      { ins := stdSig.ins, outs := [.bool], kind := .pure } hDom hDomLinked args
                    have hLhs' : linkedApply b hInhab (.inl d)
                        { ins := (PurePrimitives.baseRow stdSig).ins, outs := [.bool], kind := .pure }
                        (by exact hDomLinked) args =
                        (standardApply d { ins := stdSig.ins, outs := [.bool], kind := .pure } hDom
                          (lowerStandardHList b args)).map (liftStandardHList b) := hLhs
                    rw [hLhs', hDec]
                    simp only [standardInDomain]
                    cases standardApply k stdSig hStd (lowerStandardHList b args) <;> rfl
        | inr p =>
            cases hSig : b.signature p with
            | none =>
                simp [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row,
                  Bindings.primitives, hSig] at h
            | some ps =>
                have hEq : ({ ins := ps.inputs, outs := ps.outputs, kind := .pure } :
                    RowSignature b.vocabulary.TypeKey b.vocabulary.RowKey) = sig := by
                  simp only [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row,
                    Bindings.primitives, hSig, Option.map_some] at h
                  exact Option.some.inj h
                subst hEq
                cases hk
      keeps := fun key sig h args outs hargs happ => by
        cases key with
        | inl k =>
            cases hStd : standard.row k with
            | none =>
                simp [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row, hStd] at h
            | some stdSig =>
                have hEq : PurePrimitives.baseRow stdSig = sig := by
                  simp only [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row, hStd,
                    Option.map_some] at h
                  exact Option.some.inj h
                subst hEq
                rw [linkedApply_inl b hInhab k stdSig hStd h args] at happ
                cases hApp : standardApply k stdSig hStd (lowerStandardHList b args) with
                | none => rw [hApp] at happ; cases happ
                | some stdOuts =>
                    rw [hApp] at happ
                    cases happ
                    exact liftStandardHList_valid b stdOuts
                      (standard_keeps k stdSig hStd (lowerStandardHList b args) stdOuts
                        (lowerStandardHList_valid b args hargs) hApp)
        | inr p =>
            cases hSig : b.signature p with
            | none =>
                simp [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row,
                  Bindings.primitives, hSig] at h
            | some ps =>
                have hEq : ({ ins := ps.inputs, outs := ps.outputs, kind := .pure } :
                    RowSignature b.vocabulary.TypeKey b.vocabulary.RowKey) = sig := by
                  simp only [Bindings.vocabulary, PurePrimitives.vocabulary, PurePrimitives.row,
                    Bindings.primitives, hSig, Option.map_some] at h
                  exact Option.some.inj h
                subst hEq
                rw [linkedApply_inr b hInhab p ps hSig h args] at happ
                cases happ
                exact (evalProjectRow b p ps.inputs ps.outputs
                  (outputsInhabited_lookup hInhab hSig) args).2
      literals := fun key n h => by
        cases key with
        | inl k => exact standard_literals k n h
        | inr _ => simp [Bindings.vocabulary, PurePrimitives.vocabulary, Bindings.primitives] at h
      support := fun _ sig _ _ out => Ty.Valid (linkedCarriers b) sig.out out
      supported := fun _ _ _ _ _ _ hout => hout
    }
  else
    .error "project bindings contain an uninhabited primitive output type"

/-- Every `Model` constructed by `linkedModel? b` uses `linkedCarriers b` as its carriers. -/
theorem linkedModel?_carriers {b : Bindings} {M : Model b.vocabulary}
    (h : linkedModel? b = .ok M) : M.toCarriers = linkedCarriers b := by
  unfold linkedModel? at h
  split at h
  · cases h; rfl
  · cases h

end Zkc.Runtime
