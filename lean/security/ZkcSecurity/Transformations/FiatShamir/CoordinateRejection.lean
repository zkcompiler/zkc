module

public import ZkcSecurity.Transformations.FiatShamir.Laws
public import Mathlib.Data.Vector.Basic

@[expose] public section

/-! Read the first requested number of accepted coordinates of a finite random
tape. Replacing the target tuple permutes the successful fibers. Rejections,
ignored word bits, and words after the final accepted coordinate stay in the
sample space. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.CoordinateRejection
open OracleComp

abbrev Word (Aux A Reject : Type) := Aux × (A ⊕ Reject)

def accepted {Aux A Reject : Type} (word : Word Aux A Reject) : Option A :=
  word.2.elim some (fun _ => none)

variable {Aux A Reject : Type} [DecidableEq A]

private def exchange (left right : List A) : List (Word Aux A Reject) → List (Word Aux A Reject)
  | [] => []
  | (tag, .inl value) :: tail => match left, right with
    | x :: xs, y :: ys => (tag, .inl (Equiv.swap x y value)) :: exchange xs ys tail
    | _, _ => (tag, .inl value) :: tail
  | (tag, .inr miss) :: tail => (tag, .inr miss) :: exchange left right tail

private theorem length_exchange (x y : List A) (tape : List (Word Aux A Reject)) :
    (exchange x y tape).length = tape.length := by
  induction tape generalizing x y with
  | nil => rfl
  | cons word tail ih =>
    obtain ⟨tag, value | miss⟩ := word
    · cases x <;> cases y <;> simp [exchange, ih]
    · simp [exchange, ih]

private theorem twice (x y : List A) (tape : List (Word Aux A Reject)) :
    exchange y x (exchange x y tape) = tape := by
  induction tape generalizing x y with
  | nil => rfl
  | cons word tail ih =>
    obtain ⟨tag, value | miss⟩ := word
    · cases x <;> cases y <;> simp [exchange, ih, Equiv.swap_comm]
    · simp [exchange, ih]

private theorem prefix_exchange (x y : List A) (same : x.length = y.length)
    (tape : List (Word Aux A Reject)) :
    y <+: (exchange x y tape).filterMap accepted ↔ x <+: tape.filterMap accepted := by
  induction tape generalizing x y with
  | nil =>
    cases x <;> cases y <;> simp_all [exchange]
  | cons word tail ih =>
    obtain ⟨tag, value | miss⟩ := word
    · cases x with
      | nil => cases y <;> simp_all
      | cons a xs =>
        cases y with
        | nil => simp at same
        | cons b ys =>
          simp only [List.length_cons, Nat.succ.injEq] at same
          simp only [exchange, List.filterMap_cons, accepted, Sum.elim_inl, List.cons_prefix_cons,
            ih xs ys same]
          have swapped : b = Equiv.swap a b value ↔ a = value := by
            constructor
            · intro same
              exact (Equiv.swap a b).injective ((Equiv.swap_apply_left a b).trans same)
            · rintro rfl
              exact (Equiv.swap_apply_left _ _).symm
          exact and_congr_left' swapped
    · simpa only [exchange, List.filterMap_cons, accepted, Sum.elim_inr] using ih x y same

abbrev Tape (Aux A Reject : Type) (n : Nat) := List.Vector (Word Aux A Reject) n

private def permutation {n : Nat} (x y : List A) : Equiv.Perm (Tape Aux A Reject n) where
  toFun t := ⟨exchange x y t.val, (length_exchange ..).trans t.property⟩
  invFun t := ⟨exchange y x t.val, (length_exchange ..).trans t.property⟩
  left_inv t := Subtype.ext (twice x y t.val)
  right_inv t := Subtype.ext (twice y x t.val)

/-- A short tape refuses. Enough accepted words determine the ordered tuple. -/
def decode {n : Nat} (k : Nat) (tape : Tape Aux A Reject n) : Option (Fin k → A) :=
  let first := (tape.val.filterMap accepted).take k
  if h : first.length = k then some (fun i => first[i.val]'(i.isLt.trans_eq h.symm)) else none

omit [DecidableEq A] in
theorem refused_iff {n k : Nat} (tape : Tape Aux A Reject n) :
    decode k tape = none ↔ (tape.val.filterMap accepted).length < k := by
  simp [decode, List.length_take]

omit [DecidableEq A] in
theorem decode_eq_iff {n k : Nat} (tape : Tape Aux A Reject n) (value : Fin k → A) :
    decode k tape = some value ↔ List.ofFn value <+: tape.val.filterMap accepted := by
  rw [List.prefix_iff_eq_take, List.length_ofFn]
  let first := (tape.val.filterMap accepted).take k
  change (if h : first.length = k then some (fun i : Fin k => first[i.val]'(i.isLt.trans_eq h.symm)) else none)
    = some value ↔ List.ofFn value = first
  split
  · rename_i size
    rw [Option.some.injEq, ← List.ofFn_inj]
    have equal : List.ofFn (fun i : Fin k => first[i.val]'(i.isLt.trans_eq size.symm)) = first := by
      apply List.ext_getElem <;> simp [size]
    rw [equal, eq_comm]
  · rename_i short
    simp only [reduceCtorEq, false_iff]
    exact fun equal => short ((congrArg List.length equal).symm.trans (List.length_ofFn (f := value)))

theorem exact {n k : Nat} [Fintype Aux] [Fintype A] [Fintype Reject]
    [SampleableType (Tape Aux A Reject n)] [SampleableType (Fin k → A)]
    (reference : Fin k → A) :
    Obligations.ExactWithRefusal (decode (A := A) (Aux := Aux) (Reject := Reject) (n := n) k) := by
  classical
  let fiber (value : Fin k → A) : Finset (Tape Aux A Reject n) :=
    Finset.univ.filter (fun t => decode k t = some value)
  apply exactWithRefusal_of_fibers _ (fiber reference).card
  intro value
  change (fiber value).card = (fiber reference).card
  let e : Equiv.Perm (Tape Aux A Reject n) := permutation (List.ofFn value) (List.ofFn reference)
  have maps (t : Tape Aux A Reject n) : e t ∈ fiber reference ↔ t ∈ fiber value := by
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, decode_eq_iff]
    exact prefix_exchange _ _ (by simp) t.val
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact { toFun := fun t => ⟨e t.val, (maps _).2 t.property⟩
          invFun := fun t => ⟨e.symm t.val, (maps _).1 (by rw [e.apply_symm_apply]; exact t.property)⟩
          left_inv := fun t => Subtype.ext (e.symm_apply_apply _)
          right_inv := fun t => Subtype.ext (e.apply_symm_apply _) }

/-- Reordering a uniform physical tape and interpreting accepted coordinates
in the advertised carrier preserves refusal mass and the full event law. -/
theorem transport {B C R S : Type} [SampleableType B] [SampleableType C]
    [SampleableType R] [SampleableType S] (input : B ≃ C) (output : R ≃ S)
    (read : C → Option R) (law : Obligations.ExactWithRefusal read) :
    Obligations.ExactWithRefusal (fun b => (read (input b)).map output) := by
  intro event
  let hit (c : C) := ∃ value, read c = some value ∧ event (output value)
  have eventMap (b : B) :
      (∃ s, (read (input b)).map output = some s ∧ event s) ↔ hit (input b) := by
    cases h : read (input b) <;> simp [hit, h]
  rw [prEvent_congr _ _ _ eventMap, SampleableType.prEvent_uniformSample_equiv input hit,
    show Pr{let c ← $ᵗ C}[hit c] = _ from law (fun x => event (output x)),
    SampleableType.prEvent_uniformSample_equiv output event]
  congr 1
  simp only [Option.isSome_map]
  exact (SampleableType.prEvent_uniformSample_equiv input (fun c => (read c).isSome)).symm

end ZkcSecurity.FiatShamir.CoordinateRejection
