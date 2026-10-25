module

public import ZkcSecurity.Examples.Components.GkrRoundsReference

@[expose] public section

/-! The split-variable layout used by `gkr::layer_gates`: the left wire
factor depends only on x, and the right wire factor only on y, in MSB-first
(x,y) order. No equation about circuit outputs or wiring truth is required.
The source caller's realization of this layout remains an explicit premise. -/

namespace ZkcSecurity.Examples.Components.GkrRoundsLayout
open Zkc.Polynomial.Multilinear
open GkrRoundsReference

variable {F : Type} [Field F]

def leading : (x y : Nat) → (Fin (y + x) → Bool) → Fin x → Bool
  | 0, _, _ => Fin.elim0
  | x + 1, y, bits => Fin.cons (bits 0) (leading x y (bits ∘ Fin.succ))

def trailing : (x y : Nat) → (Fin (y + x) → Bool) → Fin y → Bool
  | 0, _, bits => bits
  | x + 1, y, bits => trailing x y (bits ∘ Fin.succ)

def replicate (x y : Nat) (wire : Table F x) : Table F (y + x) :=
  fun bits => wire (leading x y bits)

def tile (x y : Nat) (wire : Table F y) : Table F (y + x) :=
  fun bits => wire (trailing x y bits)

def state {x y : Nat} (add mul : Table F (y + x))
    (left : Table F x) (right : Table F y) : State F (y + x) :=
  ⟨add, mul, replicate x y left, tile x y right⟩

theorem fix_replicate (x y : Nat) (wire : Table F (x + 1)) (r : F) :
    fixFirst (replicate (x + 1) y wire) r = replicate x y (fixFirst wire r) := by
  funext bits
  simp only [fixFirst, half, replicate, leading, Function.comp_def,
    Fin.cons_zero, Fin.cons_succ]

theorem fix_tile (x y : Nat) (wire : Table F y) (r : F) :
    fixFirst (tile (x + 1) y wire) r = tile x y wire := by
  funext bits
  simp only [fixFirst, half, tile, trailing, Function.comp_def, Fin.cons_succ]
  ring

theorem tile_independent (x y : Nat) (wire : Table F y) :
    ZkcSecurity.Families.Sumcheck.FactorReference.ActiveIndependent
      (fun r : F => fixFirst (tile (x + 1) y wire) r) := by
  intro r bits
  change fixFirst (tile (x + 1) y wire) r bits = fixFirst (tile (x + 1) y wire) 0 bits
  rw [fix_tile, fix_tile]

theorem constant_independent {n : Nat} (c : F) :
    ZkcSecurity.Families.Sumcheck.FactorReference.ActiveIndependent
      (fun r : F => fixFirst (fun _ : Fin (n + 1) → Bool => c) r) := by
  intro r bits
  simp only [fixFirst, half]
  ring

theorem fix_constant {n : Nat} (c r : F) :
    fixFirst (fun _ : Fin (n + 1) → Bool => c) r = fun _ => c := by
  funext bits
  simp only [fixFirst, half]
  ring

theorem constant_left_admissible {n : Nat} (s : State F n) (c : F)
    (constant : s.left = fun _ => c) : admissible s := by
  induction n with
  | zero => trivial
  | succ n ih =>
    constructor
    · left
      simpa only [constant] using constant_independent (n := n) c
    · intro r
      apply ih (restrict s r)
      change fixFirst s.left r = _
      rw [constant, fix_constant]

/-- At every left-variable round the right factor is inactive. Once all left
variables are fixed, the left factor is constant for every right-variable
round. Arbitrary field challenges, including off-cube values, are covered. -/
theorem admissible_state (x y : Nat) (add mul : Table F (y + x))
    (left : Table F x) (right : Table F y) :
    admissible (state add mul left right) := by
  induction x with
  | zero =>
    exact constant_left_admissible _ (left Fin.elim0) rfl
  | succ x ih =>
    constructor
    · right
      exact tile_independent x y right
    · intro r
      have same : restrict (state (x := x + 1) (y := y) add mul left right) r =
          state (fixFirst add r) (fixFirst mul r) (fixFirst left r) right := by
        unfold restrict state
        rw [fix_replicate, fix_tile]
      rw [same]
      exact ih _ _ _

/-- Explicit caller seam: the source's four decoded factors must be this
layout. This premise constrains representation, never payload truth. -/
def CallerLayout {x y : Nat} (s : State F (y + x)) : Prop :=
  ∃ left : Table F x, ∃ right : Table F y,
    s.left = replicate x y left ∧ s.right = tile x y right

theorem caller_admissible {x y : Nat} (s : State F (y + x))
    (layout : CallerLayout (x := x) (y := y) s) : admissible s := by
  obtain ⟨left, right, hl, hr⟩ := layout
  have same : s = state s.add s.mul left right := by
    cases s
    simp_all [state]
  rw [same]
  exact admissible_state x y _ _ left right

/-- The construction is concrete: MSB-first flat vectors decode to exactly
the four factors. No Boolean product table replaces those factors. -/
def encode {n : Nat} (table : Table F n) : List F :=
  List.ofFn (fun position : Fin (2 ^ n) => table (vertex n position))

omit [Field F] in
theorem decode_encode {n : Nat} (table : Table F n) :
    ofList? n (encode table) = some table := by
  rw [encode, ofList?_ofFn]
  congr 1
  funext bits
  exact congrArg table (vertex_index n bits)

theorem concrete_layout (x y : Nat) (add mul : Table F (y + x))
    (left : Table F x) (right : Table F y) :
    ofList? (y + x) (encode (replicate x y left)) = some (state add mul left right).left ∧
    ofList? (y + x) (encode (tile x y right)) = some (state add mul left right).right ∧
    admissible (state add mul left right) :=
  ⟨decode_encode _, decode_encode _, admissible_state x y add mul left right⟩

omit [Field F] in
theorem encode_halves {n : Nat} (table : Table F (n + 1)) :
    encode table = encode (half table false) ++ encode (half table true) := by
  apply List.ext_getElem
  · simp only [encode, List.length_ofFn, List.length_append, Nat.pow_succ]
    omega
  · intro i hi hj
    simp only [encode, List.getElem_ofFn, List.getElem_append, List.length_ofFn, vertex]
    split <;> rfl

omit [Field F] in
/-- `replicate`'s concrete flat construction is exactly the source caller's
repetition of each wire value over all y rows. -/
theorem encode_replicate (x y : Nat) (wire : Table F x) :
    encode (replicate x y wire) =
      (encode wire).flatMap (fun value => List.replicate (2 ^ y) value) := by
  induction x with
  | zero => simp [encode, replicate, leading, vertex, List.ofFn_const]
  | succ x ih =>
    rw [encode_halves]
    change encode (replicate x y (half wire false)) ++
      encode (replicate x y (half wire true)) = _
    rw [ih, ih, encode_halves wire, List.flatMap_append]

omit [Field F] in
/-- `tile`'s concrete flat construction is exactly the source caller's
concatenation of a complete y table once for each x row. -/
theorem encode_tile (x y : Nat) (wire : Table F y) :
    encode (tile x y wire) = (List.replicate (2 ^ x) (encode wire)).flatten := by
  induction x with
  | zero => change encode wire = (List.replicate 1 (encode wire)).flatten
            simp
  | succ x ih =>
    rw [encode_halves]
    change encode (tile x y wire) ++ encode (tile x y wire) = _
    rw [ih]
    have twice : 2 ^ (x + 1) = 2 ^ x + 2 ^ x := by rw [Nat.pow_succ]; omega
    rw [twice, List.replicate_add, List.flatten_append]

end ZkcSecurity.Examples.Components.GkrRoundsLayout
