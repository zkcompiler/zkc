module

public import ZkcSecurity.Commitment.Record

@[expose] public section

/-! # Replays and table runs of verifiers with committed tables

* `replay_append` splits a replay along a concatenation of events, and `replay_congr_answers`
  and `replay_congr_extracted` state what a replay reads: the transcript answers at histories
  shorter than the replayed one, and the extraction of the roots among the replayed events.
* `CommitBound` counts the commitments on every path; a replay absorbs at most that many roots
  (`replay_committed_le`).
* `runTable` is the concrete reading against a complete answer table, as a function returning
  the outcome and the keys queried; `run_table` identifies it with the oracle run's table
  evaluation and the keys of its table log.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {J : PIR.Signature} {E P Shape Value Query Y A : Type} {Raw : E → Type}

theorem settle_settle (tables : List (Table Value)) :
    ∀ process : PIR.Proc (committed J Shape Value) A,
      settle tables (settle tables process) = settle tables process
  | .done _ => rfl
  | .halt _ => rfl
  | .call (.base _) _ => rfl
  | .call (.commit _) _ => rfl
  | .call (.read handle position) next => by
      simp only [settle]
      cases lookup tables handle position with
      | none => rfl
      | some value => exact settle_settle tables (next value)

section Replay
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y]
variable (absorb : Typed.Interface J E P Raw) (words : Words J Shape Value)
variable (extracted : Shape → Y → Table Value) (answers : (key : TranscriptKey E Shape Y) → Raw key.2)

/-- A replay along nonempty events answers the reads at the head first. -/
theorem replay_settle (tables : List (Table Value)) (history : List (Absorbed E Shape Y))
    (observed : Absorbed E Shape Y) (rest : List (Absorbed E Shape Y)) :
    ∀ process : PIR.Proc (committed J Shape Value) A,
      replay absorb words extracted answers process tables history (observed :: rest) =
        replay absorb words extracted answers (settle tables process) tables history
          (observed :: rest)
  | .done _ => rfl
  | .halt _ => rfl
  | .call (.base _) _ => rfl
  | .call (.commit _) _ => rfl
  | .call (.read handle position) next => by
      simp only [replay, settle]
      cases lookup tables handle position with
      | none => rfl
      | some value => exact replay_settle tables history observed rest (next value)

/-- Replaying a concatenation replays the first part, then the second from the residual. -/
theorem replay_append (second : List (Absorbed E Shape Y)) :
    ∀ (first : List (Absorbed E Shape Y)) (process : PIR.Proc (committed J Shape Value) A)
      (tables : List (Table Value)) (history : List (Absorbed E Shape Y)),
      replay absorb words extracted answers process tables history (first ++ second) =
        (replay absorb words extracted answers process tables history first).bind fun result =>
          replay absorb words extracted answers result.1 result.2 (history ++ first) second := by
  intro first
  induction first with
  | nil =>
      intro process tables history
      cases second with
      | nil => simp [replay, settle_settle]
      | cons observed rest =>
          simp only [List.nil_append, replay, Option.bind_some, List.append_nil]
          exact replay_settle absorb words extracted answers tables history observed rest process
  | cons observed rest ih =>
      intro process
      induction process with
      | done _ => intro _ _; rfl
      | halt _ => intro _ _; rfl
      | call operation next inner =>
          intro tables history
          cases operation with
          | read handle position =>
              simp only [List.cons_append, replay]
              cases lookup tables handle position with
              | none => rfl
              | some value =>
                  simpa only [List.cons_append] using inner value tables history
          | base operation =>
              simp only [List.cons_append, replay]
              rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
                ⟨event, decode⟩ | _
              · cases observed with
                | root _ _ => rfl
                | event received =>
                    simp only
                    cases recover received with
                    | none => rfl
                    | some value =>
                        simp only
                        exact (ih _ _ _).trans (by simp [List.append_assoc])
              · simp only
                split
                · exact (ih _ _ _).trans (by simp [List.append_assoc])
                · rfl
              · simp only
                split
                · cases decode (answers (history, event)) with
                  | none => rfl
                  | some value =>
                      simp only
                      exact (ih _ _ _).trans (by simp [List.append_assoc])
                · rfl
              · rfl
          | commit shape =>
              simp only [List.cons_append, replay]
              cases observed with
              | event _ => rfl
              | root committedShape root =>
                  simp only
                  split
                  · exact (ih _ _ _).trans (by simp [List.append_assoc])
                  · rfl

/-- Replaying no events answers the reads at the head. -/
@[simp] theorem replay_nil (process : PIR.Proc (committed J Shape Value) A)
    (tables : List (Table Value)) (history : List (Absorbed E Shape Y)) :
    replay absorb words extracted answers process tables history [] =
      some (settle tables process, tables) := by
  cases process with
  | done _ => rfl
  | halt _ => rfl
  | call operation next => cases operation <;> rfl

/-- One received event. -/
theorem replay_receive {operation : J.Op}
    {next : J.Reply operation → PIR.Proc (committed J Shape Value) A} {event : P → E}
    {recover : E → Option (J.Reply operation)} (absorbed : absorb operation = .receive event recover)
    (tables : List (Table Value)) (history : List (Absorbed E Shape Y)) (received : E)
    {value : J.Reply operation} (recovered : recover received = some value) :
    replay absorb words extracted answers (.call (.base operation) next) tables history
        [.event received] = some (settle tables (next value), tables) := by
  rw [replay.eq_def]
  simp only [absorbed, recovered, replay_nil]

/-- One sent event. -/
theorem replay_send {operation : J.Op}
    {next : J.Reply operation → PIR.Proc (committed J Shape Value) A} {event : E}
    {value : J.Reply operation} (absorbed : absorb operation = .send event value)
    (tables : List (Table Value)) (history : List (Absorbed E Shape Y)) :
    replay absorb words extracted answers (.call (.base operation) next) tables history
        [.event event] = some (settle tables (next value), tables) := by
  rw [replay.eq_def]
  simp only [absorbed, ↓reduceIte, replay_nil]

/-- One query occurrence, answered by decoding the answer at its key. -/
theorem replay_query {operation : J.Op}
    {next : J.Reply operation → PIR.Proc (committed J Shape Value) A} {event : E}
    {decode : Raw event → Option (J.Reply operation)}
    (absorbed : absorb operation = .query event decode) (tables : List (Table Value))
    (history : List (Absorbed E Shape Y)) {value : J.Reply operation}
    (decoded : decode (answers (history, event)) = some value) :
    replay absorb words extracted answers (.call (.base operation) next) tables history
        [.event event] = some (settle tables (next value), tables) := by
  rw [replay.eq_def]
  simp only [absorbed, ↓reduceIte, decoded, replay_nil]

/-- One committed root, recorded as its normalized extraction. -/
theorem replay_commit {shape : Shape} {next : Unit → PIR.Proc (committed J Shape Value) A}
    (tables : List (Table Value)) (history : List (Absorbed E Shape Y)) (root : Y) :
    replay absorb words extracted answers (.call (.commit shape) next) tables history
        [.root shape root] =
      some (settle (tables ++ [normalized words extracted shape root]) (next ()),
        tables ++ [normalized words extracted shape root]) := by
  rw [replay.eq_def]
  simp only [↓reduceIte, replay_nil]

/-- A replay reads the transcript answers only at histories shorter than the replayed one. -/
theorem replay_congr_answers {other : (key : TranscriptKey E Shape Y) → Raw key.2} :
    ∀ (events : List (Absorbed E Shape Y)) (process : PIR.Proc (committed J Shape Value) A)
      (tables : List (Table Value)) (history : List (Absorbed E Shape Y)),
      (∀ key : TranscriptKey E Shape Y, key.1.length < history.length + events.length →
        answers key = other key) →
      replay absorb words extracted answers process tables history events =
        replay absorb words extracted other process tables history events := by
  intro events
  induction events with
  | nil => intro process tables history _; simp
  | cons observed rest ih =>
      intro process
      induction process with
      | done _ => intro _ _ _; rfl
      | halt _ => intro _ _ _; rfl
      | call operation next inner =>
          intro tables history agree
          have shifted : ∀ key : TranscriptKey E Shape Y,
              key.1.length < (history ++ [observed]).length + rest.length →
                answers key = other key := by
            intro key bound
            apply agree
            simp only [List.length_append, List.length_cons, List.length_nil] at bound ⊢
            omega
          cases operation with
          | read handle position =>
              simp only [replay]
              cases lookup tables handle position with
              | none => rfl
              | some value => exact inner value tables history agree
          | base operation =>
              simp only [replay]
              rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
                ⟨event, decode⟩ | _
              · cases observed with
                | root _ _ => rfl
                | event received =>
                    simp only
                    cases recover received with
                    | none => rfl
                    | some value => exact ih (next value) tables _ shifted
              · simp only
                split
                · exact ih (next value) tables _ shifted
                · rfl
              · simp only
                split
                · have agreeing : answers (history, event) = other (history, event) := by
                    apply agree
                    simp
                  rw [agreeing]
                  cases decode (other (history, event)) with
                  | none => rfl
                  | some value => exact ih (next value) tables _ shifted
                · rfl
              · rfl
          | commit shape =>
              simp only [replay]
              cases observed with
              | event _ => rfl
              | root committedShape root =>
                  simp only
                  split
                  · exact ih (next ()) _ _ shifted
                  · rfl

/-- A replay reads the extraction only at the roots among the replayed events. -/
theorem replay_congr_extracted {other : Shape → Y → Table Value} :
    ∀ (events : List (Absorbed E Shape Y)) (process : PIR.Proc (committed J Shape Value) A)
      (tables : List (Table Value)) (history : List (Absorbed E Shape Y)),
      (∀ shape root, Absorbed.root shape root ∈ events → extracted shape root = other shape root) →
      replay absorb words extracted answers process tables history events =
        replay absorb words other answers process tables history events := by
  intro events
  induction events with
  | nil => intro process tables history _; simp
  | cons observed rest ih =>
      intro process
      induction process with
      | done _ => intro _ _ _; rfl
      | halt _ => intro _ _ _; rfl
      | call operation next inner =>
          intro tables history agree
          have later : ∀ shape root, Absorbed.root shape root ∈ rest →
              extracted shape root = other shape root :=
            fun shape root member => agree shape root (List.mem_cons_of_mem _ member)
          cases operation with
          | read handle position =>
              simp only [replay]
              cases lookup tables handle position with
              | none => rfl
              | some value => exact inner value tables history agree
          | base operation =>
              simp only [replay]
              rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
                ⟨event, decode⟩ | _
              · cases observed with
                | root _ _ => rfl
                | event received =>
                    simp only
                    cases recover received with
                    | none => rfl
                    | some value => exact ih (next value) tables _ later
              · simp only
                split
                · exact ih (next value) tables _ later
                · rfl
              · simp only
                split
                · cases decode (answers (history, event)) with
                  | none => rfl
                  | some value => exact ih (next value) tables _ later
                · rfl
              · rfl
          | commit shape =>
              simp only [replay]
              cases observed with
              | event _ => rfl
              | root committedShape root =>
                  simp only
                  split
                  · rename_i same
                    subst same
                    have here : extracted committedShape root = other committedShape root :=
                      agree committedShape root List.mem_cons_self
                    simp only [normalized, here]
                    exact ih (next ()) _ _ later
                  · rfl

end Replay

/-- At most `budget` commitments on every path. -/
def CommitBound : PIR.Proc (committed J Shape Value) A → ℕ → Prop
  | .done _, _ => True
  | .halt _, _ => True
  | .call (.base _) next, budget => ∀ reply, CommitBound (next reply) budget
  | .call (.commit _) next, budget => 0 < budget ∧ CommitBound (next ()) (budget - 1)
  | .call (.read _ _) next, budget => ∀ value, CommitBound (next value) budget

section Committed
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y]
variable (absorb : Typed.Interface J E P Raw) (words : Words J Shape Value)
  (extracted : Shape → Y → Table Value) (answers : (key : TranscriptKey E Shape Y) → Raw key.2)

/-- A replay from a process with at most `budget` commitments absorbs at most `budget` roots. -/
theorem replay_committed_le :
    ∀ (events : List (Absorbed E Shape Y)) (process : PIR.Proc (committed J Shape Value) A)
      (budget : ℕ) (tables : List (Table Value)) (history : List (Absorbed E Shape Y))
      (result : PIR.Proc (committed J Shape Value) A × List (Table Value)),
      CommitBound process budget →
      replay absorb words extracted answers process tables history events = some result →
      (events.filterMap Absorbed.committed).length ≤ budget := by
  intro events
  induction events with
  | nil => intro _ _ _ _ _ _ _; simp
  | cons observed rest ih =>
      intro process
      induction process with
      | done _ => intro _ _ _ _ _ replayed; simp [replay] at replayed
      | halt _ => intro _ _ _ _ _ replayed; simp [replay] at replayed
      | call operation next inner =>
          intro budget tables history result bounded replayed
          cases operation with
          | read handle position =>
              simp only [replay] at replayed
              cases found : lookup tables handle position with
              | none => rw [found] at replayed; simp at replayed
              | some value =>
                  rw [found] at replayed
                  exact inner value budget tables history result (bounded value) replayed
          | base operation =>
              simp only [replay] at replayed
              rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
                ⟨event, decode⟩ | _
              · rw [absorbed] at replayed
                cases observed with
                | root _ _ => simp at replayed
                | event received =>
                    simp only at replayed
                    cases recovered : recover received with
                    | none => rw [recovered] at replayed; simp at replayed
                    | some value =>
                        rw [recovered] at replayed
                        simpa [List.filterMap_cons, Absorbed.committed] using
                          ih (next value) budget tables _ result (bounded value) replayed
              · rw [absorbed] at replayed
                simp only at replayed
                split at replayed
                · rename_i same
                  subst same
                  simpa [List.filterMap_cons, Absorbed.committed] using
                    ih (next value) budget tables _ result (bounded value) replayed
                · simp at replayed
              · rw [absorbed] at replayed
                simp only at replayed
                split at replayed
                · rename_i same
                  subst same
                  cases decoded : decode (answers (history, event)) with
                  | none => rw [decoded] at replayed; simp at replayed
                  | some value =>
                      rw [decoded] at replayed
                      simpa [List.filterMap_cons, Absorbed.committed] using
                        ih (next value) budget tables _ result (bounded value) replayed
                · simp at replayed
              · rw [absorbed] at replayed
                simp at replayed
          | commit shape =>
              simp only [replay] at replayed
              cases observed with
              | event _ => simp at replayed
              | root committedShape root =>
                  simp only at replayed
                  split at replayed
                  · obtain ⟨positive, later⟩ := bounded
                    have := ih (next ()) (budget - 1) _ _ result later replayed
                    simp only [List.filterMap_cons, Absorbed.committed, List.length_cons]
                    omega
                  · simp at replayed

end Committed

section Table
variable (absorb : Typed.Interface J E P Raw) (scheme : Extractable Shape Value Query Y)
  (table : JointTable Raw Shape Y Query)

/-- The concrete reading against a complete answer table: the outcome and the keys queried. -/
def runTable : PIR.Proc (committed J Shape Value) A → List (Absorbed E Shape Y) →
    List (Shape × Y) → List (Message P Y) → List (Opening Value Y) →
    PIR.Outcome A × List (JointKey E Shape Y Query)
  | .done value, _, _, _, _ => (.returned value, [])
  | .halt stop, _, _, _, _ => (.stopped stop, [])
  | .call (.base operation) next, history, roots, messages, openings =>
      match absorb operation with
      | .receive event recover =>
          match messages with
          | .plain message :: rest =>
              match recover (event message) with
              | some value =>
                  runTable (next value) (history ++ [.event (event message)]) roots rest openings
              | none => (.stopped .refused, [])
          | _ => (.stopped .refused, [])
      | .send event value =>
          runTable (next value) (history ++ [.event event]) roots messages openings
      | .query event decode =>
          match decode (table (.inl (history, event))) with
          | some value =>
              let result := runTable (next value) (history ++ [.event event]) roots messages openings
              (result.1, .inl (history, event) :: result.2)
          | none => (.stopped .exhausted, [.inl (history, event)])
      | .refuse => (.stopped .refused, [])
  | .call (.commit shape) next, history, roots, messages, openings =>
      match messages with
      | .root root :: rest =>
          runTable (next ()) (history ++ [.root shape root]) (roots ++ [(shape, root)]) rest openings
      | _ => (.stopped .refused, [])
  | .call (.read handle position) next, history, roots, messages, openings =>
      match roots[handle]?, openings with
      | some (shape, root), opening :: rest =>
          let calls := (tableQueryLog (scheme.authenticate shape root position opening)
            (hashAnswers table)).map fun entry => (.inr entry.1 : JointKey E Shape Y Query)
          match evalWithAnswerFn (QueryImpl.ofFn (hashAnswers table))
              (scheme.authenticate shape root position opening) with
          | true =>
              let result := runTable (next opening.value) history roots messages rest
              (result.1, calls ++ result.2)
          | false => (.stopped .reject, calls)
      | _, _ => (.stopped .refused, [])

/-- The oracle run against a complete answer table is `runTable`: the same outcome, and a table
log with the same keys. -/
theorem run_table :
    ∀ (process : PIR.Proc (committed J Shape Value) A) (history : List (Absorbed E Shape Y))
      (roots : List (Shape × Y)) (messages : List (Message P Y))
      (openings : List (Opening Value Y)),
      evalWithAnswerFn (QueryImpl.ofFn table)
          (run absorb scheme process history roots messages openings) =
        (runTable absorb scheme table process history roots messages openings).1 ∧
      (tableQueryLog (run absorb scheme process history roots messages openings) table).map
          Sigma.fst =
        (runTable absorb scheme table process history roots messages openings).2 := by
  intro process
  induction process with
  | done value => intro _ _ _ _; exact ⟨rfl, rfl⟩
  | halt stop => intro _ _ _ _; exact ⟨rfl, rfl⟩
  | call operation next ih =>
      intro history roots messages openings
      cases operation with
      | base operation =>
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · simp only [run, runTable, absorbed]
            match messages with
            | [] => exact ⟨rfl, rfl⟩
            | .root _ :: _ => exact ⟨rfl, rfl⟩
            | .plain message :: rest =>
                simp only
                cases recover (event message) with
                | none => exact ⟨rfl, rfl⟩
                | some value => exact ih value _ _ _ _
          · simp only [run, runTable, absorbed]
            exact ih value _ _ _ _
          · simp only [run, runTable, absorbed]
            rw [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
              tableQueryLog_query_bind, List.map_cons]
            cases decode (table (.inl (history, event))) with
            | none => exact ⟨rfl, rfl⟩
            | some value =>
                exact ⟨(ih value _ _ _ _).1, congrArg (List.cons _) (ih value _ _ _ _).2⟩
          · simp only [run, runTable, absorbed]
            exact ⟨rfl, rfl⟩
      | commit shape =>
          simp only [run, runTable]
          match messages with
          | [] => exact ⟨rfl, rfl⟩
          | .plain _ :: _ => exact ⟨rfl, rfl⟩
          | .root root :: rest => exact ih () _ _ _ _
      | read handle position =>
          rw [run.eq_def, runTable.eq_def]
          simp only
          match roots[handle]?, openings with
          | none, _ => exact ⟨rfl, rfl⟩
          | some _, [] => exact ⟨rfl, rfl⟩
          | some (shape, root), opening :: rest =>
              simp only
              refine ⟨?_, ?_⟩
              · rw [evalWithAnswerFn_bind, evalWithAnswerFn_liftHash]
                cases evalWithAnswerFn (QueryImpl.ofFn (hashAnswers table))
                    (scheme.authenticate shape root position opening) with
                | false => rfl
                | true => exact (ih opening.value _ _ _ _).1
              · rw [tableQueryLog_bind, List.map_append, tableQueryLog_liftHash,
                  evalWithAnswerFn_liftHash, List.map_map]
                cases evalWithAnswerFn (QueryImpl.ofFn (hashAnswers table))
                    (scheme.authenticate shape root position opening) with
                | false => simp
                | true => exact congrArg _ (ih opening.value _ _ _ _).2

end Table

end ZkcSecurity.Commitment
