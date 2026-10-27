module

public import ZkcSecurity.Claims.FiniteRecovery
public import ZkcArkLib.Knowledge.FiniteRecovery

@[expose] public section

/-! Optional transport of the closed finite-recovery meaning to the actual
pinned ArkLib runner. The model library owns the relation, access, algorithm,
sender interface and resource coordinate. This adapter supplies equalities,
not a replacement experiment or an executable-compiler receipt.
Upstream: ArkLib 1e0241333c18d8b22cb68f9522da5f9fb88f9a06. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcArkLib.Knowledge.RegisteredFiniteRecovery
open OracleComp OracleSpec Zkc.Claims
open ZkcSecurity.Commitment.FiniteRecovery
open ZkcSecurity.Claims.FiniteRecovery
open ZkcArkLib.Knowledge.FiniteRecovery

variable {F : Type} [Add F] [DecidableEq F]

/-- Preserve the sent cells and verdict, projecting only ArkLib's path wrapper
and unit sender output. `nativeRun_eq` uses the actual receive/access handler
and `closed_verifier`; recovery never receives a separately chosen oracle. -/
theorem observations_eq (request : Request F) (adversary : Sender F) :
    (fun observed => (observed.1.1, observed.2.2)) <$> nativeRun request adversary =
      run request adversary := by
  rw [nativeRun_eq]
  simp only [run, map_bind, map_pure, verifier_eq]

/-- Transport evidence for the evaluated model proposition to actual upstream
acceptance. The argument remains an arbitrary probabilistic sender. -/
theorem acceptance_of_evaluation {registrations : Registry Profile} {selected : Identifier}
    {request : Request F} {queries : Nat}
    (evaluation : Evaluation registrations selected request queries)
    (evidence : evaluation.meaning) (adversary : Sender F) :
    Pr{let observed ← nativeRun request adversary}[observed.2.2 = true] =
      Pr{let cells ← adversary}[request.Holds (evalWithAnswerFn (answers cells) request.extract)] := by
  rw [evaluation.meaning_eq] at evidence
  rw [← evidence.acceptance adversary, ← observations_eq]
  simp only [prEvent_map]

omit [DecidableEq F] in
/-- The same registered algorithm also equals upstream's same-path backward
map, without a validity premise. No witness is selected by the evidence. -/
theorem registered_extractor {registrations : Registry Profile} {selected : Identifier}
    {request : Request F} {queries : Nat}
    (_evaluation : Evaluation registrations selected request queries) (cells : F × F) :
    evalWithAnswerFn (answers cells) request.extract =
      (extractor request).extractWitness ⟨cells, PUnit.unit⟩ () :=
  extract_eq_native request cells

/-- The existing standalone native equality proves exactly the model's fixed
acceptance field. This reuses `acceptance_eq_recovery`, whose runner equation
closes the restricted verifier with the received immutable two-cell resource. -/
theorem certify_native {registrations : Registry Profile} {selected : Identifier}
    {request : Request F} {queries : Nat}
    (evaluation : Evaluation registrations selected request queries) : evaluation.meaning := by
  rw [evaluation.meaning_eq]
  refine ⟨evaluation.queriesFixed, query_bound_iff request, extract_eq request, ?_⟩
  intro adversary
  rw [← observations_eq]
  simp only [prEvent_map]
  exact acceptance_eq_recovery request adversary

end ZkcArkLib.Knowledge.RegisteredFiniteRecovery
