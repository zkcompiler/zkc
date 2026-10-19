module

public import ZkcSecurity.Commitment.Experiment

@[expose] public section

/-! # Accepting concrete runs leave the doomed set at a transcript query

`runTable_escape` is the deterministic core of the joint argument. Fix a complete answer table
and one extraction for every committed root. Suppose every opening the run authenticates agrees
with the extraction (in the security argument, because the record is good), and the ideal reading
of the verifier on the extracted tables is doomed. Then an accepting concrete run reaches, at one
of its own transcript queries, a residual whose ideal reading is doomed and whose answer at that
query escapes, and the replay of the verifier along that query's history reaches the same
residual. The concrete run absorbs exactly the events the replay consumes: committed roots are
read as their extracted tables, and reads are answered by the authenticated openings, which agree
with those tables.

`runTable_history` states that every transcript key a run queries extends the run's starting
history.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {J : PIR.Signature} {E P Shape Value Query Y A : Type} {Raw : E → Type}

section History
variable (absorb : Typed.Interface J E P Raw) (scheme : Extractable Shape Value Query Y)
  (table : JointTable Raw Shape Y Query)

/-- Every transcript key a run queries extends the run's starting history. -/
theorem runTable_history :
    ∀ (process : PIR.Proc (committed J Shape Value) A) (history : List (Absorbed E Shape Y))
      (roots : List (Shape × Y)) (messages : List (Message P Y))
      (openings : List (Opening Value Y)) (key : TranscriptKey E Shape Y),
      (.inl key : JointKey E Shape Y Query) ∈
          (runTable absorb scheme table process history roots messages openings).2 →
        history <+: key.1 := by
  intro process
  induction process with
  | done _ => intro _ _ _ _ _ member; simp [runTable] at member
  | halt _ => intro _ _ _ _ _ member; simp [runTable] at member
  | call operation next ih =>
      intro history roots messages openings key member
      cases operation with
      | base operation =>
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · simp only [runTable, absorbed] at member
            match messages with
            | [] => simp at member
            | .root _ :: _ => simp at member
            | .plain message :: rest =>
                simp only at member
                cases recovered : recover (event message) with
                | none => rw [recovered] at member; simp at member
                | some value =>
                    rw [recovered] at member
                    exact (List.prefix_append _ _).trans (ih value _ _ _ _ key member)
          · simp only [runTable, absorbed] at member
            exact (List.prefix_append _ _).trans (ih value _ _ _ _ key member)
          · simp only [runTable, absorbed] at member
            cases decoded : decode (table (.inl (history, event))) with
            | none =>
                rw [decoded] at member
                simp only [List.mem_singleton, Sum.inl.injEq] at member
                subst member
                exact List.prefix_rfl
            | some value =>
                rw [decoded] at member
                rcases List.mem_cons.mp member with here | later
                · simp only [Sum.inl.injEq] at here
                  subst here
                  exact List.prefix_rfl
                · exact (List.prefix_append _ _).trans (ih value _ _ _ _ key later)
          · simp [runTable, absorbed] at member
      | commit shape =>
          simp only [runTable] at member
          match messages with
          | [] => simp at member
          | .plain _ :: _ => simp at member
          | .root root :: rest => exact (List.prefix_append _ _).trans (ih () _ _ _ _ key member)
      | read handle position =>
          rw [runTable.eq_def] at member
          simp only at member
          cases found : roots[handle]? with
          | none => rw [found] at member; simp at member
          | some pair =>
              obtain ⟨shape, root⟩ := pair
              rw [found] at member
              cases openings with
              | nil => simp at member
              | cons opening rest =>
                  simp only at member
                  cases authenticated : evalWithAnswerFn (QueryImpl.ofFn (hashAnswers table))
                      (scheme.authenticate shape root position opening) with
                  | false => rw [authenticated] at member; simp at member
                  | true =>
                      rw [authenticated] at member
                      simp only [List.mem_append, List.mem_map] at member
                      rcases member with ⟨_, _, impossible⟩ | later
                      · exact absurd impossible (by simp)
                      · exact ih opening.value _ _ _ _ key later

end History

section Tables
variable (words : Words J Shape Value) (extracted : Shape → Y → Table Value)

/-- The tables the ideal reading records for committed roots read as their extractions. -/
def rootTables (roots : List (Shape × Y)) : List (Table Value) :=
  roots.map fun pair => normalized words extracted pair.1 pair.2

theorem lookup_rootTables (roots : List (Shape × Y)) (handle position : ℕ) :
    lookup (rootTables words extracted roots) handle position =
      (roots[handle]?).bind fun pair => normalized words extracted pair.1 pair.2 position := by
  unfold lookup rootTables
  rw [List.getElem?_map]
  cases roots[handle]? <;> rfl

theorem settle_base (tables : List (Table Value)) (operation : J.Op)
    (next : J.Reply operation → PIR.Proc (committed J Shape Value) A) :
    settle tables (.call (.base operation) next) = .call (.base operation) next := rfl

theorem settle_commit (tables : List (Table Value)) (shape : Shape)
    (next : Unit → PIR.Proc (committed J Shape Value) A) :
    settle tables (.call (.commit shape) next) = .call (.commit shape) next := rfl

end Tables

section Escape
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [∀ key, SampleableType (Raw key)]
variable (absorb : Typed.Interface J E P Raw) (words : Words J Shape Value)
  (scheme : Extractable Shape Value Query Y) (table : JointTable Raw Shape Y Query)
  (extracted : Shape → Y → Table Value)

/-- An accepting concrete run from a doomed ideal reading escapes at one of its own transcript
queries, at a residual the replay reaches along that query's history. -/
theorem runTable_escape {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Typed.Certificate absorb accepts error)
    (commitReceives : ∀ shape, ∃ event recover, absorb (words.word shape) = .receive event recover)
    (carries : ∀ shape root position value, extracted shape root position = some value →
      normalized words extracted shape root position = some value)
    (keys : List (JointKey E Shape Y Query))
    (agrees : ∀ shape root position opening,
      (∀ entry ∈ tableQueryLog (scheme.authenticate shape root position opening) (hashAnswers table),
        (.inr entry.1 : JointKey E Shape Y Query) ∈ keys) →
      evalWithAnswerFn (QueryImpl.ofFn (hashAnswers table))
        (scheme.authenticate shape root position opening) = true →
      extracted shape root position = some opening.value)
    (start : PIR.Proc (committed J Shape Value) A) (startTables : List (Table Value))
    (initial : List (Absorbed E Shape Y)) :
    ∀ (process : PIR.Proc (committed J Shape Value) A) (events history : List (Absorbed E Shape Y))
      (roots : List (Shape × Y)) (messages : List (Message P Y))
      (openings : List (Opening Value Y)),
      replay absorb words extracted (fun key => table (.inl key)) start startTables initial events =
        some (settle (rootTables words extracted roots) process, rootTables words extracted roots) →
      history = initial ++ events →
      certificate.doomed (withTables words (rootTables words extracted roots) process) →
      (∀ key ∈ (runTable absorb scheme table process history roots messages openings).2,
        key ∈ keys) →
      Accepted accepts (runTable absorb scheme table process history roots messages openings).1 →
      ∃ key : TranscriptKey E Shape Y,
        (.inl key : JointKey E Shape Y Query) ∈
          (runTable absorb scheme table process history roots messages openings).2 ∧
        ∃ events' residual tables', key.1 = initial ++ events' ∧
          replay absorb words extracted (fun key => table (.inl key)) start startTables initial
            events' = some (residual, tables') ∧
          Escapes absorb words certificate.doomed residual tables' key.2 (table (.inl key)) := by
  intro process
  induction process with
  | done value =>
      intro _ _ _ _ _ _ _ doomed _ accepted
      have step := certificate.step _ doomed
      exact (step accepted).elim
  | halt stop => intro _ _ _ _ _ _ _ _ _ accepted; exact accepted.elim
  | call operation next ih =>
      intro events history roots messages openings replayed shape doomed included accepted
      cases operation with
      | base operation =>
          have step := certificate.step _ doomed
          simp only [withTables] at step
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · simp only [Typed.Step, absorbed] at step
            simp only [runTable, absorbed] at included accepted ⊢
            match messages with
            | [] => exact accepted.elim
            | .root _ :: _ => exact accepted.elim
            | .plain message :: rest =>
                simp only at included accepted ⊢
                cases recovered : recover (event message) with
                | none => rw [recovered] at accepted; exact accepted.elim
                | some value =>
                    rw [recovered] at included accepted
                    refine ih value (events ++ [.event (event message)]) _ roots rest openings
                      ?_ (by rw [shape, List.append_assoc]) (step value) included accepted
                    rw [replay_append absorb words extracted (fun key => table (.inl key))
                      [.event (event message)] events start startTables initial, replayed,
                      Option.bind_some, settle_base, ← shape]
                    exact replay_receive absorb words extracted _ absorbed _ _ _ recovered
          · simp only [Typed.Step, absorbed] at step
            simp only [runTable, absorbed] at included accepted ⊢
            refine ih value (events ++ [.event event]) _ roots messages openings
              ?_ (by rw [shape, List.append_assoc]) step included accepted
            rw [replay_append absorb words extracted (fun key => table (.inl key))
              [.event event] events start startTables initial, replayed,
              Option.bind_some, settle_base, ← shape]
            exact replay_send absorb words extracted _ absorbed _ _
          · simp only [runTable, absorbed] at included accepted ⊢
            cases decoded : decode (table (.inl (history, event))) with
            | none => rw [decoded] at accepted; exact accepted.elim
            | some value =>
                rw [decoded] at included accepted
                by_cases stays :
                    certificate.doomed (withTables words (rootTables words extracted roots)
                      (next value))
                · obtain ⟨key, member, rest⟩ := ih value (events ++ [.event event]) _ roots
                    messages openings (by
                      rw [replay_append absorb words extracted (fun key => table (.inl key))
                        [.event event] events start startTables initial, replayed,
                        Option.bind_some, settle_base, ← shape]
                      exact replay_query absorb words extracted _ absorbed _ _ decoded)
                    (by rw [shape, List.append_assoc]) stays
                    (fun key member => included key (List.mem_cons_of_mem _ member)) accepted
                  exact ⟨key, List.mem_cons_of_mem _ member, rest⟩
                · refine ⟨(history, event), List.mem_cons_self, events, .call (.base operation) next,
                    rootTables words extracted roots, shape, ?_, ?_⟩
                  · rw [replayed, settle_base]
                  · exact ⟨decode, absorbed, doomed, value, decoded, stays⟩
          · simp [runTable, absorbed] at accepted
            exact accepted.elim
      | commit committedShape =>
          have step := certificate.step _ doomed
          obtain ⟨commitEvent, commitRecover, receives⟩ := commitReceives committedShape
          simp only [withTables, Typed.Step, receives] at step
          simp only [runTable] at included accepted ⊢
          match messages with
          | [] => exact accepted.elim
          | .plain _ :: _ => exact accepted.elim
          | .root root :: rest =>
              have extended : rootTables words extracted (roots ++ [(committedShape, root)]) =
                  rootTables words extracted roots ++
                    [normalized words extracted committedShape root] := by
                simp [rootTables]
              refine ih () (events ++ [.root committedShape root]) _ (roots ++ [(committedShape, root)])
                rest openings ?_ (by rw [shape, List.append_assoc]) ?_ included accepted
              · rw [replay_append absorb words extracted (fun key => table (.inl key))
                  [.root committedShape root] events start startTables initial, replayed,
                  Option.bind_some, settle_commit, ← shape, extended]
                exact replay_commit absorb words extracted _ _ _ root
              · rw [extended]
                exact step (words.ofTable committedShape (extracted committedShape root))
      | read handle position =>
          rw [runTable.eq_def] at included accepted ⊢
          simp only at included accepted ⊢
          cases found : roots[handle]? with
          | none => rw [found] at accepted; exact accepted.elim
          | some pair =>
              obtain ⟨committedShape, root⟩ := pair
              rw [found] at included accepted
              cases openings with
              | nil => exact accepted.elim
              | cons opening rest =>
                  simp only at included accepted ⊢
                  cases authenticated : evalWithAnswerFn (QueryImpl.ofFn (hashAnswers table))
                      (scheme.authenticate committedShape root position opening) with
                  | false => rw [authenticated] at accepted; exact accepted.elim
                  | true =>
                      rw [authenticated] at included accepted
                      have agreed := agrees committedShape root position opening (by
                        intro entry member
                        exact included _ (List.mem_append_left _ (List.mem_map_of_mem member)))
                        authenticated
                      have looked : lookup (rootTables words extracted roots) handle position =
                          some opening.value := by
                        rw [lookup_rootTables, found]
                        exact carries _ _ _ _ agreed
                      obtain ⟨key, member, escaping⟩ := ih opening.value events history roots
                        messages rest (by rw [replayed]; simp [settle, looked]) shape
                        (by simpa [withTables, looked] using doomed)
                        (fun key member => included key (List.mem_append_right _ member)) accepted
                      exact ⟨key, List.mem_append_right _ member, escaping⟩

end Escape

end ZkcSecurity.Commitment
