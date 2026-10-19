module

public import Zkc.Polynomial.Multilinear.Prefix
public import Zkc.Protocols.Sumcheck.Multilinear.Round

@[expose] public section

/-! Mathematical contracts for reduction and complete public-table discharge.
An obligation binds a table, an ordered point, and a value. It is not an
acceptance certificate or a statement about an imported process.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Multilinear

open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F : Type} {n k : Nat}

/-- After `k` coordinates, the claim is the sum of the remaining `n`-variable table. -/
def ResidualClaim [Ring F] (k : Nat) (table : Table F (n + k))
    (point : Fin k → F) (claim : F) : Prop :=
  booleanSum (fixPrefix k table point) = claim

theorem residualClaim_zero [Ring F] (table : Table F n) (point : Fin 0 → F) (claim : F) :
    ResidualClaim 0 table point claim ↔ booleanSum table = claim := Iff.rfl

theorem residualClaim_succ [Ring F] (table : Table F (n + (k + 1)))
    (r : F) (point : Fin k → F) (claim : F) :
    ResidualClaim (k + 1) table (Fin.cons r point) claim ↔
      ResidualClaim k (fixFirst table r) point claim := Iff.rfl

variable [CommRing F]

theorem residualClaim_iff (table : Table F (n + k)) (point : Fin k → F) (claim : F) :
    ResidualClaim k table point claim ↔
      cubeSum n (fun suffix => extension (n + k) table (Quadratic.point k point suffix)) = claim := by
  unfold ResidualClaim
  rw [booleanSum_fixPrefix]

/-- Only an empty residual dimension turns this obligation into one evaluation.
`Quadratic.point` appends the empty suffix without reordering the fixed point. -/
theorem residualClaim_complete_iff (table : Table F (0 + k)) (point : Fin k → F) (claim : F) :
    ResidualClaim k table point claim ↔
      extension (0 + k) table (Quadratic.point k point Fin.elim0) = claim := by
  unfold ResidualClaim
  rw [booleanSum, fixPrefix_complete]

/-- Mathematical full-table checker: exact scalar shape followed by extension
evaluation. Native dimension limits and the source's staged failures are outside
this pure adapter. `check_complete_iff` relates it to the residual computation. -/
def check [DecidableEq F] (values : List F) (point : Fin n → F) (claim : F) : Bool :=
  match ofList? n values with
  | none => false
  | some table => decide (extension n table point = claim)

theorem check_eq_true_iff [DecidableEq F] (values : List F) (point : Fin n → F) (claim : F) :
    check values point claim = true ↔
      ∃ table, ofList? n values = some table ∧ extension n table point = claim := by
  unfold check
  split <;> simp_all

theorem check_wrong_shape [DecidableEq F] (values : List F) (point : Fin n → F) (claim : F)
    (wrong : values.length ≠ 2 ^ n) : check values point claim = false := by
  simp [check, ofList?, wrong]

theorem check_zero_iff [DecidableEq F] (values : List F) (claim : F) :
    check values (Fin.elim0 : Fin 0 → F) claim = true ↔ values = [claim] := by
  rw [check_eq_true_iff]
  cases values with
  | nil => simp [ofList?]
  | cons value rest =>
      cases rest with
      | nil => simp [ofList?, extension, ofVector]
      | cons next rest => simp [ofList?]

theorem check_complete_iff [DecidableEq F] (values : List F) (table : Table F (0 + k))
    (decoded : ofList? (0 + k) values = some table) (point : Fin k → F) (claim : F) :
    check values (Quadratic.point k point Fin.elim0) claim = true ↔
      ResidualClaim k table point claim := by
  rw [check, decoded]
  simp only [decide_eq_true_eq, residualClaim_complete_iff]

/-- An honest prover residual discharges a verifier's public table only with
explicit table and ordered-point agreement. No delivery agreement is inferred. -/
theorem check_of_residual [DecidableEq F] (valuesV : List F)
    (tableP tableV : Table F (0 + k)) (pointP pointV : Fin k → F) (claim : F)
    (decodedV : ofList? (0 + k) valuesV = some tableV)
    (tablesAgree : tableP = tableV) (pointsAgree : pointP = pointV)
    (truth : ResidualClaim k tableP pointP claim) :
    check valuesV (Quadratic.point k pointV Fin.elim0) claim = true := by
  subst tableP
  subst pointP
  exact (check_complete_iff valuesV tableV decodedV pointV claim).mpr truth

end Zkc.Protocols.Sumcheck.Multilinear
