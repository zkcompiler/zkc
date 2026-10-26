module

public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.SimSemantics.SimulateQ

@[expose] public section

/-! Request-fixed straight-line recovery from an immutable two-cell oracle.
This finite selected consumer proves a sum relation. It has no commitment
hardness, rewinding, witness search, or efficiency assertion about arbitrary
Lean functions. The executable recovery algorithm makes exactly the two
specified reads. -/

set_option autoImplicit false
namespace ZkcSecurity.Commitment.FiniteRecovery
open OracleComp OracleSpec

abbrev Access (F : Type) := Fin 2 →ₒ F

structure Request (F : Type) where
  expectedSum : F

variable {F : Type}

/-- Immutable access to both cells, in their fixed order. -/
def answers (cells : F × F) : QueryImpl (Access F) Id :=
  fun index => if index = 0 then cells.1 else cells.2

/-- The algorithm is part of the request's meaning, never an evidence field. -/
def Request.extract (_request : Request F) : OracleComp (Access F) (F × F) := do
  let first ← (Access F).query 0
  let second ← (Access F).query 1
  pure (first, second)

abbrev Request.Holds [Add F] (request : Request F) (witness : F × F) : Prop :=
  witness.1 + witness.2 = request.expectedSum

def Request.verifier [Add F] [DecidableEq F] (request : Request F) :
    OracleComp (Access F) Bool := do
  let recovered ← request.extract
  pure (decide (request.Holds recovered))

/-- Fixed access determines the exact extracted value, before any relation
assumption. No existential witness is chosen by a proof. -/
@[simp] theorem extract_eq (request : Request F) (cells : F × F) :
    evalWithAnswerFn (answers cells) request.extract = cells := by
  simp [Request.extract, answers, evalWithAnswerFn_bind]

@[simp] theorem verifier_eq [Add F] [DecidableEq F] (request : Request F) (cells : F × F) :
    evalWithAnswerFn (answers cells) request.verifier = decide (request.Holds cells) := by
  simp [Request.verifier]

theorem accepted_iff_extracted [Add F] [DecidableEq F] (request : Request F) (cells : F × F) :
    evalWithAnswerFn (answers cells) request.verifier = true ↔
      request.Holds (evalWithAnswerFn (answers cells) request.extract) := by simp

theorem extract_query_bound (request : Request F) : IsQueryBoundP request.extract (fun _ => True) 2 := by
  simp [Request.extract, isQueryBoundP_query_bind_iff]

end ZkcSecurity.Commitment.FiniteRecovery
