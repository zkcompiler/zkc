module

public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

/-! Change of coefficient field for the existing ordered table semantics.
The map is an explicit ring homomorphism. Extension challenges need not lie in
its image: embed the table first, then restrict in the challenge field. -/
set_option autoImplicit false
namespace Zkc.Polynomial.Multilinear
namespace Embedding
variable {B E : Type} [CommRing B] [CommRing E]

def table (embedding : B →+* E) {n : Nat} (values : Table B n) : Table E n :=
  fun bits => embedding (values bits)

theorem booleanSum (embedding : B →+* E) {n : Nat} (values : Table B n) :
    Multilinear.booleanSum (table embedding values) = embedding (Multilinear.booleanSum values) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Multilinear.booleanSum (table embedding (half values false)) +
      Multilinear.booleanSum (table embedding (half values true)) = _
    rw [ih, ih, ← map_add]
    rfl

theorem extension (embedding : B →+* E) (n : Nat) (values : Table B n) (point : Fin n → B) :
    Multilinear.extension n (table embedding values) (fun i => embedding (point i)) =
      embedding (Multilinear.extension n values point) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (1 - embedding (point 0)) *
        Multilinear.extension n (table embedding (half values false))
          (fun i => embedding (point (Fin.succ i))) +
      embedding (point 0) * Multilinear.extension n (table embedding (half values true))
          (fun i => embedding (point (Fin.succ i))) = _
    rw [ih, ih]
    simp only [Multilinear.extension, map_add, map_mul, map_sub, map_one]
    rfl

theorem fixFirst (embedding : B →+* E) {n : Nat} (values : Table B (n + 1)) (r : B) :
    Multilinear.fixFirst (table embedding values) (embedding r) =
      table embedding (Multilinear.fixFirst values r) := by
  funext bits
  simp only [fixFirst_apply, table, half, map_add, map_mul, map_sub]

theorem fixPrefix (embedding : B →+* E) {n : Nat} (k : Nat)
    (values : Table B (n + k)) (point : Fin k → B) :
    Multilinear.fixPrefix k (table embedding values) (fun i => embedding (point i)) =
      table embedding (Multilinear.fixPrefix k values point) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Multilinear.fixPrefix, fixFirst]
    exact ih _ (point ∘ Fin.succ)

/-- Decode the original base list once, without padding or truncating it. -/
theorem ofList? (embedding : B →+* E) {n : Nat} (values : List B) (decoded : Table B n)
    (same : Multilinear.ofList? n values = some decoded) :
    Multilinear.ofList? n (values.map embedding) = some (table embedding decoded) := by
  unfold Multilinear.ofList? at same ⊢
  split at same
  · cases Option.some.inj same
    simp only [List.length_map]
    rw [dite_eq_left ‹values.length = 2 ^ n›]
    congr 1
    funext bits
    simp [ofVector, table]
  · contradiction

/-- The square for arbitrary extension challenges. There is no attempt to
restrict a base table by an extension element before embedding. -/
theorem restrictPrefix_decodes (embedding : B →+* E) {n : Nat} (values : List B)
    (point : List E) (decoded : Table B (n + point.length))
    (same : Multilinear.ofList? (n + point.length) values = some decoded) :
    Multilinear.ofList? n (restrictPrefixValues (values.map embedding) point) =
      some (Multilinear.fixPrefix point.length (table embedding decoded)
        (coordinates point.length point)) :=
  ofList?_restrictPrefixValues _ _ _ (ofList? embedding values decoded same)

/-- Evaluation of the residual is evaluation of the embedded original at the
concatenated extension-field point. -/
theorem extension_restrictPrefix (embedding : B →+* E) {n : Nat} (values : List B)
    (point : List E) (decoded : Table B (n + point.length)) (residual : Table E n)
    (same : Multilinear.ofList? (n + point.length) values = some decoded)
    (readback : Multilinear.ofList? n (restrictPrefixValues (values.map embedding) point) = some residual)
    (suffix : Fin n → E) :
    Multilinear.extension n residual suffix =
      Multilinear.extension (n + point.length) (table embedding decoded)
        (Quadratic.point point.length (coordinates point.length point) suffix) :=
  extension_restrictPrefixValues _ _ _ _ (ofList? embedding values decoded same) readback suffix

end Embedding
end Zkc.Polynomial.Multilinear
