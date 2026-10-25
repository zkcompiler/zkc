module

public import ZkcSecurity.Families.Sumcheck.Reference
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

/-! The degree-one reference uses the existing dimension-indexed table engine.
Exact powers of two, rather than one even-length check, give shape closure. -/

set_option autoImplicit false

namespace ZkcSecurity.Families.Sumcheck.TableReference

open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F : Type} [Field F]

noncomputable abbrev data (F : Type) [Field F] : Reference F where
  State := Table F
  total := booleanSum
  restrict := fixFirst
  polynomial table := Message.endpointPolynomial
    (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table)
  admissible _ := True

theorem laws : ReferenceLaws (data F) 1 where
  degree_le _ _ := Message.endpointPolynomial_degree _
  boundary_eq table _ := by
    change boundaryPoly ((Message.endpoints F).polynomial
      (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table)) = booleanSum table
    rw [← Message.endpoints_laws.boundary_eq]
    exact Zkc.Protocols.Sumcheck.Multilinear.boundary_honestMessage table
  evaluation_eq table r _ := by
    change (Message.endpointPolynomial
      (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table)).eval r = _
    rw [Message.endpointPolynomial_eval]
    exact Zkc.Protocols.Sumcheck.Multilinear.evaluate_honestMessage table r
  restriction_closed _ _ _ := trivial

/-- The existing table representation supplies the honest decoder equality. -/
theorem honest_polynomial {n : Nat} (table : Table F (n + 1)) :
    (Message.endpoints F).polynomial (Zkc.Protocols.Sumcheck.Multilinear.honestMessage table) =
      (data F).polynomial table := rfl

/-- The typed terminal state has one vertex. What a verifier checks against this
value is a separate caller theorem. -/
theorem terminal_total (table : Table F 0) : (data F).total table = table Fin.elim0 := rfl

theorem decoded_restriction_closed {n : Nat} (values : List F) (table : Table F (n + 1))
    (decoded : ofList? (n + 1) values = some table) (r : F) :
    ofList? n (restrictValues values r) = some ((data F).restrict table r) :=
  ofList?_restrictValues values table r decoded

/-- Every prefix retains exact residual shape, including a zero-length prefix
and the terminal one-entry table. This reuses core list/table decoding. -/
theorem decoded_prefix_closed {n : Nat} (values fixed : List F)
    (table : Table F (n + fixed.length))
    (decoded : ofList? (n + fixed.length) values = some table) :
    ofList? n (restrictPrefixValues values fixed) =
      some (fixPrefix fixed.length table (coordinates fixed.length fixed)) :=
  ofList?_restrictPrefixValues values fixed table decoded

theorem prefix_shape {n : Nat} (values fixed : List F)
    (shape : values.length = 2 ^ (n + fixed.length)) :
    (restrictPrefixValues values fixed).length = 2 ^ n :=
  restrictPrefixValues_length values fixed shape

end ZkcSecurity.Families.Sumcheck.TableReference
