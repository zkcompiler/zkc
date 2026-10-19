module

public import ZkcSecurity.HashChain.JointSimulator
public import ZkcSecurity.Commitment.Experiment

@[expose] public section

/-! # The concrete reading of a committed verifier over a hash chain

A verifier with committed tables (`ZkcSecurity.Commitment.run`) asks a joint oracle at transcript
keys and hash calls. Deployed over a hash-chain suite, both are calls of one byte hash. This module
states that deployment and the concrete experiment of the joint stage.

**The chain reading** (`chainRead`). The verifier runs with the chain: received and sent events
and committed roots are absorbed, one absorbing call each; a query occurrence is answered by the
counter blocks `0, …, width - 1` of a request at the current state and is then absorbed, and the
query's raw answer is those blocks; a read authenticates its opening with the hash calls of the
commitment scheme. The reading is generic in the monad and in how chain inputs and hash calls are
answered, and it logs, as the concrete reading logs its joint-oracle queries, every transcript key
with its raw answer and every hash call with its answer. `chainVerify` binds the first event of
the initial history and absorbs the rest first, as `ZkcSecurity.HashChain.chainRun` does. With
byte calls (`byteChain`, `byteHash`) it is the deployed verifier on the byte hash, and simulating
the byte hash by any implementation answers the chain inputs and hash calls through their bytes
(`simulateQ_chainVerify`).

**The concrete experiment** (`concreteExperiment`). The adversary calls the byte hash and outputs
a statement and a proof, with its calls logged; the deployed verifier then runs on the same byte
hash. The prover's log is read through the classification of the byte calls (`classifyLog`): a
call classified as a hash call is that call; a counter block below the width of a request whose
state has a recorded history `h` and whose occurrence is `.event e` is a query of the transcript
key `(h, e)`; and a fresh binding, or a fresh absorption at a state with a recorded history,
records the history its answer reaches, the first one kept. Each joint key is read at the first
call of its attempt only, as the joint simulator asks the joint oracle. The concrete failure is
the bridge's false acceptance on that run (`concreteFailure`): the verifier accepts and the
statement is false for its tables extracted, from the hash calls of this classified log, at the
checkpoint of one of the verifier's transcript keys.

**Skeletons.** The bridge's event reads the prover's log only through its keys and its hash
answers (`skeleton`), not through the raw answers of transcript keys
(`falseAcceptance_congr_skeleton`).
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain.Joint
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.Commitment
  ZkcSecurity.HashChain.Encoding

variable {J : PIR.Signature} {E P Shape Value Query S A Stmt : Type} {width : ℕ}

/-- The joint log entry of a hash call. -/
def hashEntry (entry : (_ : Query) × S) :
    (key : JointKey E Shape S Query) × Cells E Shape S Query width key :=
  ⟨.inr entry.1, entry.2⟩

section Collect
variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad n]

theorem collect_congr' {count : ℕ} {first second : Fin count → m S}
    (same : ∀ index, first index = second index) : collect count first = collect count second := by
  rw [funext same]

end Collect

section Reading
variable {m : Type → Type} [Monad m]

/-- The concrete reading of a verifier with committed tables over a hash chain, with chain inputs
answered by `chain` and hash calls by `hash`: absorbed events and roots advance the state, a query
reads the counter blocks of a request at the current state and absorbs its occurrence, and a read
authenticates its opening. It logs every transcript key with its raw answer and every hash call
with its answer. -/
def chainRead (absorb : Typed.Interface J E P (fun _ => Fin width → S))
    (scheme : Extractable Shape Value Query S) (chain : Input (Absorbed E Shape S) S Bytes → m S)
    (hash : QueryImpl (Query →ₒ S) m) :
    PIR.Proc (committed J Shape Value) A → S → List (Absorbed E Shape S) → List (Shape × S) →
      List (Message P S) → List (Opening Value S) →
        m (PIR.Outcome A × QueryLog (OracleSpec.ofFn (Cells E Shape S Query width)))
  | .done value, _, _, _, _, _ => pure (.returned value, [])
  | .halt stop, _, _, _, _, _ => pure (.stopped stop, [])
  | .call (.base operation) next, state, history, roots, messages, openings =>
      match absorb operation with
      | .receive event recover =>
          match messages with
          | .plain message :: rest =>
              match recover (event message) with
              | some value => do
                  let advanced ← chain (.absorb state (.event (event message)))
                  chainRead absorb scheme chain hash (next value) advanced
                    (history ++ [.event (event message)]) roots rest openings
              | none => pure (.stopped .refused, [])
          | _ => pure (.stopped .refused, [])
      | .send event value => do
          let advanced ← chain (.absorb state (.event event))
          chainRead absorb scheme chain hash (next value) advanced (history ++ [.event event]) roots
            messages openings
      | .query event decode => do
          let raw ← collect width fun block => chain (.request state (.event event) block.val)
          let advanced ← chain (.absorb state (.event event))
          match decode raw with
          | some value =>
              (fun result => (result.1, ⟨.inl (history, event), raw⟩ :: result.2)) <$>
                chainRead absorb scheme chain hash (next value) advanced (history ++ [.event event])
                  roots messages openings
          | none => pure (.stopped .exhausted, [⟨.inl (history, event), raw⟩])
      | .refuse => pure (.stopped .refused, [])
  | .call (.commit shape) next, state, history, roots, messages, openings =>
      match messages with
      | .root root :: rest => do
          let advanced ← chain (.absorb state (.root shape root))
          chainRead absorb scheme chain hash (next ()) advanced (history ++ [.root shape root])
            (roots ++ [(shape, root)]) rest openings
      | _ => pure (.stopped .refused, [])
  | .call (.read handle position) next, state, history, roots, messages, openings =>
      match roots[handle]?, openings with
      | some (shape, root), opening :: rest => do
          let authenticated ← simulateQ hash (scheme.authenticate shape root position opening).withQueryLog
          match authenticated.1 with
          | true =>
              (fun result => (result.1, authenticated.2.map hashEntry ++ result.2)) <$>
                chainRead absorb scheme chain hash (next opening.value) state history roots messages rest
          | false => pure (.stopped .reject, authenticated.2.map hashEntry)
      | _, _ => pure (.stopped .refused, [])

/-- Bind the first event of the initial history, absorb the rest, and read the verifier from the
resulting state. An empty initial history binds nothing and refuses. -/
def chainVerify (absorb : Typed.Interface J E P (fun _ => Fin width → S))
    (scheme : Extractable Shape Value Query S) (chain : Input (Absorbed E Shape S) S Bytes → m S)
    (hash : QueryImpl (Query →ₒ S) m) (verifier : PIR.Proc (committed J Shape Value) A)
    (initial : List (Absorbed E Shape S)) (roots : List (Shape × S)) (messages : List (Message P S))
    (openings : List (Opening Value S)) :
    m (PIR.Outcome A × QueryLog (OracleSpec.ofFn (Cells E Shape S Query width))) :=
  match initial with
  | [] => pure (.stopped .refused, [])
  | first :: rest => do
      let state ← chain (.bind first)
      let state ← absorbAll chain state rest
      chainRead absorb scheme chain hash verifier state (first :: rest) roots messages openings

end Reading

section Simulation
variable {n : Type → Type} [Monad n] [LawfulMonad n]

theorem simulateQ_collect' {ι : Type} {spec : OracleSpec ι} (impl : QueryImpl spec n) :
    ∀ (count : ℕ) (calls : Fin count → OracleComp spec S),
      simulateQ impl (collect count calls) = collect count fun index => simulateQ impl (calls index)
  | 0, _ => by simp [collect]
  | count + 1, calls => by
      have tail := simulateQ_collect' impl count fun index => calls index.succ
      simp only [collect, simulateQ_bind, simulateQ_pure, tail]

variable {ι : Type} {spec : OracleSpec ι} (impl : QueryImpl spec n)
  (absorb : Typed.Interface J E P (fun _ => Fin width → S)) (scheme : Extractable Shape Value Query S)
  (chain : Input (Absorbed E Shape S) S Bytes → OracleComp spec S)
  (hash : QueryImpl (Query →ₒ S) (OracleComp spec))

/-- Simulating the oracle of a chain reading answers its chain inputs and hash calls through the
simulation. -/
theorem simulateQ_chainRead :
    ∀ (process : PIR.Proc (committed J Shape Value) A) (state : S) (history : List (Absorbed E Shape S))
      (roots : List (Shape × S)) (messages : List (Message P S)) (openings : List (Opening Value S)),
      simulateQ impl (chainRead absorb scheme chain hash process state history roots messages openings) =
        chainRead absorb scheme (fun input => simulateQ impl (chain input))
          (fun query => simulateQ impl (hash query)) process state history roots messages openings := by
  intro process
  induction process with
  | done value => intro _ _ _ _ _; simp [chainRead]
  | halt stop => intro _ _ _ _ _; simp [chainRead]
  | call operation next ih =>
      intro state history roots messages openings
      cases operation with
      | base operation =>
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · rcases messages with _ | ⟨message | root, rest⟩
            · simp [chainRead, absorbed]
            · simp only [chainRead, absorbed]
              cases recover (event message) with
              | none => simp
              | some value =>
                  simp only [simulateQ_bind]
                  exact bind_congr fun advanced => ih value _ _ _ _ _
            · simp [chainRead, absorbed]
          · simp only [chainRead, absorbed, simulateQ_bind]
            exact bind_congr fun advanced => ih value _ _ _ _ _
          · simp only [chainRead, absorbed, simulateQ_bind, simulateQ_collect']
            refine bind_congr fun raw => bind_congr fun advanced => ?_
            cases decode raw with
            | none => simp
            | some value =>
                simp only [simulateQ_map]
                rw [ih value]
          · simp [chainRead, absorbed]
      | commit shape =>
          rcases messages with _ | ⟨message | root, rest⟩
          · simp [chainRead]
          · simp [chainRead]
          · simp only [chainRead, simulateQ_bind]
            exact bind_congr fun advanced => ih () _ _ _ _ _
      | read handle position =>
          unfold chainRead
          split
          · simp only [simulateQ_bind]
            rw [ZkcSecurity.Oracle.simulateQ_simulateQ]
            refine bind_congr fun authenticated => ?_
            cases authenticated.1 with
            | false => simp
            | true =>
                simp only [simulateQ_map]
                rw [ih]
          · simp

theorem simulateQ_absorbAll :
    ∀ (events : List (Absorbed E Shape S)) (state : S),
      simulateQ impl (absorbAll chain state events) =
        absorbAll (fun input => simulateQ impl (chain input)) state events
  | [], _ => by simp [absorbAll]
  | event :: rest, state => by
      simp only [absorbAll, simulateQ_bind]
      exact bind_congr fun next => simulateQ_absorbAll rest next

theorem simulateQ_chainVerify (verifier : PIR.Proc (committed J Shape Value) A)
    (initial : List (Absorbed E Shape S)) (roots : List (Shape × S)) (messages : List (Message P S))
    (openings : List (Opening Value S)) :
    simulateQ impl (chainVerify absorb scheme chain hash verifier initial roots messages openings) =
      chainVerify absorb scheme (fun input => simulateQ impl (chain input))
        (fun query => simulateQ impl (hash query)) verifier initial roots messages openings := by
  cases initial with
  | nil => simp [chainVerify]
  | cons first rest =>
      simp only [chainVerify, simulateQ_bind]
      refine bind_congr fun state => ?_
      rw [simulateQ_absorbAll]
      exact bind_congr fun state => simulateQ_chainRead impl absorb scheme chain hash verifier _ _ _ _ _

end Simulation

section Congruence
variable {m : Type → Type} [Monad m] (absorb : Typed.Interface J E P (fun _ => Fin width → S))
  (scheme : Extractable Shape Value Query S) (hash : QueryImpl (Query →ₒ S) m)

/-- A chain input of the reading: a binding, an absorption, or a counter block below the width of
a request whose occurrence is the event of a base operation. -/
def ReadInput (width : ℕ) : Input (Absorbed E Shape S) S Bytes → Prop
  | .bind _ => True
  | .absorb _ _ => True
  | .request _ occurrence block => (∃ event, occurrence = .event event) ∧ block < width
  | .other _ => False

/-- A chain input of the reading, as a chain call of the byte encodings. -/
def ReadInput.toCall {input : Input (Absorbed E Shape S) S Bytes} (small : width ≤ 2 ^ 64)
    (read : ReadInput width input) : ChainCall E Shape S :=
  ⟨input, by
    cases input with
    | bind => trivial
    | absorb => trivial
    | request _ _ _ => exact ⟨read.1, lt_of_lt_of_le read.2 small⟩
    | other => exact read.elim⟩

/-- The chain reading depends on its chain answers only at the inputs it makes. -/
theorem chainRead_congr {first second : Input (Absorbed E Shape S) S Bytes → m S}
    (same : ∀ input, ReadInput width input → first input = second input) :
    ∀ (process : PIR.Proc (committed J Shape Value) A) (state : S) (history : List (Absorbed E Shape S))
      (roots : List (Shape × S)) (messages : List (Message P S)) (openings : List (Opening Value S)),
      chainRead absorb scheme first hash process state history roots messages openings =
        chainRead absorb scheme second hash process state history roots messages openings := by
  intro process
  induction process with
  | done value => intro _ _ _ _ _; rfl
  | halt stop => intro _ _ _ _ _; rfl
  | call operation next ih =>
      intro state history roots messages openings
      cases operation with
      | base operation =>
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · rcases messages with _ | ⟨message | root, rest⟩
            · simp only [chainRead, absorbed]
            · simp only [chainRead, absorbed]
              cases recover (event message) with
              | none => rfl
              | some value =>
                  simp only
                  rw [same (.absorb state (.event (event message))) trivial]
                  exact bind_congr fun advanced => ih value _ _ _ _ _
            · simp only [chainRead, absorbed]
          · simp only [chainRead, absorbed]
            rw [same (.absorb state (.event event)) trivial]
            exact bind_congr fun advanced => ih value _ _ _ _ _
          · simp only [chainRead, absorbed]
            rw [collect_congr' fun block => same (.request state (.event event) block.val)
              ⟨⟨event, rfl⟩, block.isLt⟩, same (.absorb state (.event event)) trivial]
            refine bind_congr fun raw => bind_congr fun advanced => ?_
            cases decode raw with
            | none => rfl
            | some value => simp only; rw [ih value]
          · simp only [chainRead, absorbed]
      | commit shape =>
          rcases messages with _ | ⟨message | root, rest⟩
          · simp only [chainRead]
          · simp only [chainRead]
          · simp only [chainRead]
            rw [same (.absorb state (.root shape root)) trivial]
            exact bind_congr fun advanced => ih () _ _ _ _ _
      | read handle position =>
          unfold chainRead
          split
          · refine bind_congr fun authenticated => ?_
            cases authenticated.1 with
            | false => rfl
            | true => simp only; rw [ih]
          · rfl

theorem absorbAll_congr' {first second : Input (Absorbed E Shape S) S Bytes → m S}
    (same : ∀ input, ReadInput width input → first input = second input) :
    ∀ (events : List (Absorbed E Shape S)) (state : S), absorbAll first state events = absorbAll second state events
  | [], _ => rfl
  | event :: rest, state => by
      simp only [absorbAll]
      rw [same (.absorb state event) trivial]
      exact bind_congr fun next => absorbAll_congr' same rest next

theorem chainVerify_congr {first second : Input (Absorbed E Shape S) S Bytes → m S}
    (same : ∀ input, ReadInput width input → first input = second input)
    (verifier : PIR.Proc (committed J Shape Value) A) (initial : List (Absorbed E Shape S))
    (roots : List (Shape × S)) (messages : List (Message P S)) (openings : List (Opening Value S)) :
    chainVerify absorb scheme first hash verifier initial roots messages openings =
      chainVerify absorb scheme second hash verifier initial roots messages openings := by
  cases initial with
  | nil => rfl
  | cons event rest =>
      simp only [chainVerify]
      rw [same (.bind event) trivial]
      refine bind_congr fun state => ?_
      rw [absorbAll_congr' same rest state]
      exact bind_congr fun state => chainRead_congr absorb scheme hash same verifier _ _ _ _ _

end Congruence

section Bytes
variable (encoding : Encoding E Shape S Query)

/-- A chain input as a call of the byte hash at its bytes. -/
def byteChain (input : Input (Absorbed E Shape S) S Bytes) : OracleComp (ByteHash S) S :=
  byteCall (encoding.chainBytes input)

/-- A hash call as a call of the byte hash at its bytes. -/
def byteHash : QueryImpl (Query →ₒ S) (OracleComp (ByteHash S)) :=
  fun query => byteCall (encoding.callBytes query)

end Bytes

section Classification
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query]

/-- The state of the classification of a byte log: the answers of the calls read as private chain
calls, the history each generated state reaches, and the joint keys already read. -/
structure Classification (E Shape S Query : Type) where
  answers : Input (Absorbed E Shape S) S Bytes → Option S
  reached : S → Option (List (Absorbed E Shape S))
  emitted : JointKey E Shape S Query → Bool

/-- The classification before any call. -/
def Classification.empty : Classification E Shape S Query :=
  ⟨fun _ => none, fun _ => none, fun _ => false⟩

/-- The joint log entry of a call at a joint key with its answer; a transcript key's raw answer is
not read by the bridge's event and is filled with the call's answer. -/
def keyEntry (key : JointKey E Shape S Query) (answer : S) :
    (key : JointKey E Shape S Query) × Cells E Shape S Query width key :=
  match key with
  | .inl key => ⟨.inl key, fun _ => answer⟩
  | .inr call => ⟨.inr call, answer⟩

variable (encoding : Encoding E Shape S Query) (width : ℕ)

/-- One call of the byte log: the joint entry it adds, if it is the first call of its attempt,
and the classification after it. -/
noncomputable def Classification.step (classification : Classification E Shape S Query)
    (bytes : Bytes) (answer : S) :
    List ((key : JointKey E Shape S Query) × Cells E Shape S Query width key) ×
      Classification E Shape S Query :=
  match jointAttempt encoding width classification.reached bytes with
  | some key =>
      if classification.emitted key then ([], classification)
      else ([keyEntry key answer],
        { classification with emitted := Function.update classification.emitted key true })
  | none =>
      match classification.answers (encoding.chainInput bytes) with
      | some _ => ([], classification)
      | none => ([],
          { classification with
            answers := Function.update classification.answers (encoding.chainInput bytes) (some answer)
            reached := noteReached classification.reached (encoding.chainInput bytes) answer })

/-- The joint log of a byte log, read from a classification. -/
noncomputable def Classification.read (classification : Classification E Shape S Query) :
    QueryLog (ByteHash S) →
      List ((key : JointKey E Shape S Query) × Cells E Shape S Query width key)
  | [] => []
  | entry :: rest =>
      (classification.step encoding width entry.1 entry.2).1 ++
        (classification.step encoding width entry.1 entry.2).2.read rest

/-- The joint log of a byte log, read from the empty classification. -/
noncomputable def classifyLog (log : QueryLog (ByteHash S)) :
    QueryLog (OracleSpec.ofFn (Cells E Shape S Query width)) :=
  (Classification.empty : Classification E Shape S Query).read encoding width log

end Classification

section Experiment
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query]
  (encoding : Encoding E Shape S Query) (width : ℕ)
  (absorb : Typed.Interface J E P (fun _ => Fin width → S)) (scheme : Extractable Shape Value Query S)
  (verifier : Stmt → PIR.Proc (committed J Shape Value) A) (initial : Stmt → List (Absorbed E Shape S))
  (statementRoots : Stmt → List (Shape × S))

/-- The deployed verifier on the byte hash. -/
def deployed (statement : Stmt) (proof : Proof P Value S) :
    OracleComp (ByteHash S)
      (PIR.Outcome A × QueryLog (OracleSpec.ofFn (Cells E Shape S Query width))) :=
  chainVerify absorb scheme (byteChain encoding) (byteHash encoding) (verifier statement)
    (initial statement) (statementRoots statement) proof.messages proof.openings

/-- The run of the concrete experiment from the adversary's logged claim and the verifier's run:
the prover's log is the classification of the adversary's byte calls. -/
noncomputable def assemble (claim : (Stmt × Proof P Value S) × QueryLog (ByteHash S))
    (verifierRun : PIR.Outcome A × QueryLog (OracleSpec.ofFn (Cells E Shape S Query width))) :
    JointRun Stmt P Value S A (QueryLog (OracleSpec.ofFn (Cells E Shape S Query width))) :=
  { statement := claim.1.1, proof := claim.1.2, outcome := verifierRun.1,
    proverLog := classifyLog encoding width claim.2, verifierLog := verifierRun.2 }

/-- The concrete experiment: the adversary calls the byte hash, with its calls logged, and
outputs a statement and a proof; the deployed verifier then runs on the same byte hash. -/
noncomputable def concreteExperiment (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S)) :
    OracleComp (ByteHash S)
      (JointRun Stmt P Value S A (QueryLog (OracleSpec.ofFn (Cells E Shape S Query width)))) :=
  adversary.withQueryLog >>= fun claim =>
    assemble encoding width claim <$>
      deployed encoding width absorb scheme verifier initial statementRoots claim.1.1 claim.1.2

end Experiment

section Skeleton
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query]

/-- A joint log entry's key and, for a hash call, its answer. -/
def skeletonEntry (entry : (key : JointKey E Shape S Query) × Cells E Shape S Query width key) :
    JointKey E Shape S Query × Option S :=
  match entry with
  | ⟨.inl key, _⟩ => (.inl key, none)
  | ⟨.inr call, answer⟩ => (.inr call, some answer)

/-- The keys of a joint log with the answers of its hash calls. -/
def skeleton (log : List ((key : JointKey E Shape S Query) × Cells E Shape S Query width key)) :
    List (JointKey E Shape S Query × Option S) :=
  log.map skeletonEntry

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] in
theorem skeleton_append (first second : List ((key : JointKey E Shape S Query) ×
    Cells E Shape S Query width key)) :
    skeleton (first ++ second) = skeleton first ++ skeleton second :=
  List.map_append

/-- The hash calls before a transcript key's first query are read from the skeleton. -/
theorem hashEntries_beforeFirst_congr (key : TranscriptKey E Shape S) :
    ∀ (first second : List ((key : JointKey E Shape S Query) × Cells E Shape S Query width key)),
      skeleton first = skeleton second →
        hashEntries (beforeFirst (.inl key) first) = hashEntries (beforeFirst (.inl key) second)
  | [], [], _ => rfl
  | [], _ :: _, same => by cases same
  | _ :: _, [], same => by cases same
  | ⟨firstKey, firstAnswer⟩ :: firstRest, ⟨secondKey, secondAnswer⟩ :: secondRest, same => by
      simp only [skeleton, List.map_cons, List.cons.injEq] at same
      obtain ⟨heads, tails⟩ := same
      have rest := hashEntries_beforeFirst_congr key firstRest secondRest tails
      cases firstKey with
      | inl firstKey =>
          cases secondKey with
          | inl secondKey =>
              simp only [skeletonEntry, Prod.mk.injEq, Sum.inl.injEq, and_true] at heads
              subst heads
              rw [beforeFirst_cons, beforeFirst_cons]
              split
              · rfl
              · simp only [hashEntries, List.filterMap_cons]
                exact rest
          | inr secondCall => simp [skeletonEntry] at heads
      | inr firstCall =>
          cases secondKey with
          | inl secondKey => simp [skeletonEntry] at heads
          | inr secondCall =>
              simp only [skeletonEntry, Prod.mk.injEq, Sum.inr.injEq] at heads
              obtain ⟨rfl, answers⟩ := heads
              have equal : firstAnswer = secondAnswer := Option.some.inj answers
              subst equal
              rw [beforeFirst_cons, beforeFirst_cons]
              have different : (Sum.inr firstCall : JointKey E Shape S Query) ≠ .inl key := by simp
              simp only [different, ↓reduceIte, hashEntries, List.filterMap_cons]
              exact congrArg _ rest

variable (words : Words J Shape Value) (scheme : Extractable Shape Value Query S)
  (statementRoots : Stmt → List (Shape × S))

/-- The bridge's event reads the prover's log only through its skeleton. -/
theorem falseAcceptance_congr_skeleton (falseStatement : Stmt → List (Table Value) → Prop)
    (accepts : A → Prop)
    (result other : JointRun Stmt P Value S A (QueryLog (OracleSpec.ofFn (Cells E Shape S Query width))))
    (statement : result.statement = other.statement) (outcome : result.outcome = other.outcome)
    (verifierLog : result.verifierLog = other.verifierLog)
    (proverLog : skeleton result.proverLog = skeleton other.proverLog) :
    FalseAcceptance words scheme statementRoots falseStatement accepts result ↔
      FalseAcceptance words scheme statementRoots falseStatement accepts other := by
  have tables : ∀ key, checkpointTables words scheme statementRoots
      (result.proverLog ++ result.verifierLog) key result.statement =
        checkpointTables words scheme statementRoots (other.proverLog ++ other.verifierLog) key
          other.statement := by
    intro key
    unfold checkpointTables
    rw [statement, hashEntries_beforeFirst_congr key (result.proverLog ++ result.verifierLog)
      (other.proverLog ++ other.verifierLog) (by simp only [skeleton_append, proverLog, verifierLog])]
  unfold FalseAcceptance
  simp only [tables]
  simp only [statement, outcome, verifierLog]

end Skeleton

end ZkcSecurity.HashChain.Joint
