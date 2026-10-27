import ZkcSecurity.Claims.FiniteRecovery

/-! Controls at the closed typed finite-recovery registration boundary.
Substitution refusals use concrete counterexamples to the selected meaning,
independently of identifier lookup failures. -/

set_option autoImplicit false
namespace TestsSecurity.FiniteRecoveryRegistration
open OracleComp OracleSpec Zkc.Claims
open ZkcSecurity.Commitment.FiniteRecovery
open ZkcSecurity.Claims.FiniteRecovery

def request : Request Nat := ⟨3⟩
def validSender : ProbComp (Nat × Nat) := pure (1, 2)
def evaluated : Evaluation registry identifier request 2 := canonical request

example : evaluate registry identifier request 2 = .ok (.ok evaluated) := evaluate_canonical _
example : evaluated.meaning = Guarantee request 2 := evaluated.meaning_eq
theorem positive : evaluated.meaning := certify evaluated

example : evaluate ⟨[]⟩ identifier request 2 = .error (.unknownIdentifier identifier) := rfl
example : evaluate registry ⟨identifier.name, 1⟩ request 2 =
    .error (.unknownIdentifier ⟨identifier.name, 1⟩) := rfl
example : evaluate ⟨[profileEntry, profileEntry]⟩ identifier request 2 =
    .error (.conflict identifier) := rfl
example : registry.register profileEntry = .error (.conflict identifier) := rfl
example : (⟨[]⟩ : Registry Profile).register profileEntry = .ok registry := rfl
example : evaluate ⟨[{ profileEntry with definition := none }]⟩ identifier request 2 =
    .ok (.error ⟨[schema]⟩) := rfl
example : evaluate ⟨[{ profileEntry with schema := "other/0" }]⟩ identifier request 2 =
    .error (.schema "finite recovery profile schema mismatch") := rfl

/-- Even registering the token under the wrong version cannot reinterpret it. -/
example : evaluate ⟨[{ profileEntry with identifier := ⟨identifier.name, 1⟩ }]⟩
    ⟨identifier.name, 1⟩ request 2 =
      .error (.schema "finite recovery profile identifier mismatch") := rfl

example : evaluate registry identifier request 1 =
    .error (.schema "finite recovery requires exactly two cell queries") := rfl
example : evaluate registry identifier request 3 =
    .error (.schema "finite recovery requires exactly two cell queries") := rfl
theorem one_query_impossible : ¬ Guarantee request 1 := by
  intro evidence
  cases evidence.queriesFixed
example : ¬ IsQueryBoundP request.extract (fun _ => True) 1 := by
  rw [query_bound_iff]
  decide

/-- The evidence certifies this request's meaning; it cannot also certify the
claim that its sent valid pair satisfies a different sum relation. -/
def wrongRelation (cells : Nat × Nat) : Prop := cells.1 + cells.2 = 4

theorem relation_substitution_refused :
    ¬ ∀ cells, request.Holds cells ↔ wrongRelation cells := by
  intro replaced
  have bad := (replaced (1, 2)).mp (show request.Holds (1, 2) from rfl)
  norm_num [wrongRelation] at bad

theorem relation_event_substitution_refused :
    ¬ Pr{let observed ← run request validSender}[observed.2 = true] =
      Pr{let cells ← validSender}[wrongRelation cells] := by
  simp [run, validSender, wrongRelation, Request.Holds, request]

/-- A valid constant sum witness still fails the evaluated proposition's full
recovery equation on the actual oracle. -/
def constantWitness : OracleComp (Access Nat) (Nat × Nat) := pure (3, 0)
example : request.Holds (3, 0) := rfl
theorem algorithm_substitution_refused :
    ¬ ∀ cells, evalWithAnswerFn (answers cells) constantWitness =
      evalWithAnswerFn (answers cells) request.extract := by
  intro replaced
  have bad := replaced (1, 2)
  simp [constantWitness] at bad

/-- Returning the same pair is insufficient if the algorithm changes its
ordered reads or cost. Code equality, unlike output equality, detects this. -/
def reverseReads : OracleComp (Access Nat) (Nat × Nat) := do
  let second ← (Access Nat).query 1
  let first ← (Access Nat).query 0
  pure (first, second)

def firstRead : OracleComp (Access Nat) (Nat × Nat) → Option (Fin 2)
  | .pure _ => none
  | .queryBind index _ => some index

/-- Inspecting the first query distinguishes read order even though immutable
answer tables alone do not. The fixed programs themselves are different. -/
theorem ordered_algorithm_fixed : reverseReads ≠ request.extract := by
  intro same
  have bad := congrArg firstRead same
  contradiction

def firstCellOnly (cells : Nat × Nat) : QueryImpl (Access Nat) Id := fun _ => cells.1
theorem access_substitution_refused :
    ¬ ∀ cells, evalWithAnswerFn (firstCellOnly cells) request.extract =
      evalWithAnswerFn (answers cells) request.extract := by
  intro replaced
  have bad := replaced (1, 2)
  simp [Request.extract, firstCellOnly, evalWithAnswerFn_bind, answers] at bad

theorem access_event_substitution_refused :
    ¬ ∀ cells, evalWithAnswerFn (firstCellOnly cells) request.verifier =
      evalWithAnswerFn (answers cells) request.verifier := by
  intro replaced
  have bad := replaced (1, 2)
  simp [Request.verifier, Request.extract, firstCellOnly, evalWithAnswerFn_bind,
    answers, Request.Holds, request] at bad

/-- Changing the sum creates a different indexed request, even with the same
registered profile. The concrete success event changes. -/
example : run request validSender = pure ((1, 2), true) := by
  simp [run, validSender, Request.Holds, request]
example : run (⟨4⟩ : Request Nat) validSender = pure ((1, 2), false) := by
  simp [run, validSender, Request.Holds]

#print axioms positive
#print axioms ZkcSecurity.Claims.FiniteRecovery.Evaluation.meaning_eq
#print axioms ZkcSecurity.Claims.FiniteRecovery.query_bound_iff
end TestsSecurity.FiniteRecoveryRegistration
