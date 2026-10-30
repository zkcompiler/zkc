module

public import ZkcSecurity.Stage.Commitment

@[expose] public section

/-! # Application events at a specified commitment checkpoint

An application may request the tables at a specified transcript key, rather than existentially
choose a table after a run. `pinned_implies_falseAcceptance` transports that event, provided the
actual verifier log contains that key. `first_query_logged` proves the elementary operational
fact used by clients that enforce the query syntactically. Neither lemma supplies relation
adequacy for an arbitrary public statement.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.Application

open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {J : PIR.Signature} {E P Shape Value Query Y A Stmt : Type} {Raw : E → Type}
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]

/-- Acceptance with a bad table at the application's specified key. The key's checkpoint is
before its first query by either party, including a prover query before verification. -/
def PinnedFailure (words : Words J Shape Value) (scheme : Extractable Shape Value Query Y)
    (roots : Stmt → List (Shape × Y)) (key : Stmt → TranscriptKey E Shape Y)
    (badTable : Stmt → List (Table Value) → Prop) (accepts : A → Prop)
    (result : JointRun Stmt P Value Y A (QueryLog (joint Raw Shape Y Query))) : Prop :=
  Accepted accepts result.outcome ∧ badTable result.statement
    (checkpointTables words scheme roots (result.proverLog ++ result.verifierLog)
      (key result.statement) result.statement)

/-- Event interpretation needs the actual requested key in the verifier log. -/
theorem pinned_implies_falseAcceptance (words : Words J Shape Value)
    (scheme : Extractable Shape Value Query Y) (roots : Stmt → List (Shape × Y))
    (key : Stmt → TranscriptKey E Shape Y) (badTable : Stmt → List (Table Value) → Prop)
    (accepts : A → Prop)
    (result : JointRun Stmt P Value Y A (QueryLog (joint Raw Shape Y Query)))
    (queried : ∃ entry ∈ result.verifierLog, entry.1 = .inl (key result.statement))
    (failure : PinnedFailure words scheme roots key badTable accepts result) :
    FalseAcceptance words scheme roots badTable accepts result := by
  obtain ⟨entry, member, same⟩ := queried
  exact ⟨failure.1, entry, member, key result.statement, same, failure.2⟩

/-- A syntactic first query is logged on every structural execution, even on a later rejection
or a cache hit. This is stronger than coverage only on accepted executions. -/
theorem first_query_logged {D B : Type} {R : D → Type} (key : D)
    (next : R key → OracleComp (OracleSpec.ofFn R) B)
    (result : B × QueryLog (OracleSpec.ofFn R))
    (member : result ∈ support
      (liftM ((OracleSpec.ofFn R).query key) >>= next).withQueryLog) :
    ∃ entry ∈ result.2, entry.1 = key := by
  rw [withQueryLog_bind, withQueryLog_query] at member
  simp only [bind_assoc, pure_bind, support_bind, Set.mem_iUnion, exists_prop,
    support_map, Set.mem_image] at member
  obtain ⟨answer, -, rest, -, rfl⟩ := member
  exact ⟨⟨key, answer⟩, List.mem_cons_self, rfl⟩

/-- An empty log cannot witness the bridge event, even when the application accepts. -/
theorem no_query_excludes_falseAcceptance (words : Words J Shape Value)
    (scheme : Extractable Shape Value Query Y) (roots : Stmt → List (Shape × Y))
    (badTable : Stmt → List (Table Value) → Prop) (accepts : A → Prop)
    (result : JointRun Stmt P Value Y A (QueryLog (joint Raw Shape Y Query)))
    (empty : result.verifierLog = []) :
    ¬ FalseAcceptance words scheme roots badTable accepts result :=
  ZkcSecurity.Stage.not_falseAcceptance_of_verifierLog_nil words scheme roots badTable accepts
    result empty

end ZkcSecurity.Commitment.Application
