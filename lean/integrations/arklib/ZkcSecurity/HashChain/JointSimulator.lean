module

public import ZkcSecurity.HashChain.JointBytes
public import ZkcSecurity.HashChain.Bridge

@[expose] public section

/-! # The hash-chain simulator with row calls passed through

`jointSimulator` simulates the shared byte hash of a verifier with committed tables over a
hash-chain suite from the joint oracle of `ZkcSecurity.Commitment`, whose transcript cells are
keyed by pairs of an absorbed history and an occurrence and whose hash cells are the commitment's
hash calls (`Cells`). It extends `ZkcSecurity.HashChain.chainSimulator`:

- bytes classified as a hash call (`Encoding.classify`) belong to that call's own cell, and are
  answered by the cell's answer unchanged;
- every other input is the chain input it encodes, or another input, and is handled by the chain
  simulator: a counter block below the width of a request at a state with a recorded history `h`
  and occurrence `.event e` belongs to the transcript cell `(h, e)`, whose answer the simulator
  records under the chain history `h ++ [.event e]` (`chainKey`); every other call is answered
  privately from the tape.

The state (`JointState`) is the chain simulator's state and a record of hash-cell answers. The
chain simulator's state is the provider-state projection of the joint stage's frame: recording a
hash answer touches only the hash record (`record_hash_chain`), and every call that is not a hash
call reads and moves the state only through the chain part (`attempt_chain`, `recorded_chain`,
`record_transcript_chain`, `respond_chain`). Its attempts are the frame's namespaces: a hash call's
bytes belong to its own cell in every state (`attempt_callBytes`), only those bytes realize the
cell (`eq_callBytes_of_attempt`), and transcript cells are realized only by chain calls
(`chainCall_of_attempt`).

On a chain input, the flat simulation of the joint simulator against the lazily sampled joint
oracle is the flat simulation of the chain simulator against the lazily sampled history oracle,
with the transcript cells of the joint cache read at their chain histories and the hash cells kept
aside (`flatJoint_run_chain`, with the cache combination `combine`).
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain.Joint
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.Commitment
  ZkcSecurity.HashChain.Encoding ZkcSecurity.VCVio.Deferral

variable {E Shape S Query : Type}

/-- The joint oracle's answers for a chain whose requests answer `width` digests: a transcript
cell answers `width` digests and a hash cell one digest. -/
abbrev Cells (E Shape S Query : Type) (width : ℕ) : JointKey E Shape S Query → Type :=
  JointRange (fun _ : E => Fin width → S) Shape S Query

section Keys

/-- The chain history of a transcript key: the absorbed history followed by the occurrence. -/
def chainKey (key : TranscriptKey E Shape S) : List (Absorbed E Shape S) :=
  key.1 ++ [.event key.2]

theorem chainKey_injective : Function.Injective (chainKey (E := E) (Shape := Shape) (S := S)) := by
  intro first second same
  obtain ⟨prefixes, lasts⟩ := List.append_inj' same rfl
  simp only [List.singleton_inj, Absorbed.event.injEq] at lasts
  exact Prod.ext prefixes lasts

/-- The transcript key of a chain history ending with the event of a base operation. -/
def transcriptKey? (history : List (Absorbed E Shape S)) : Option (TranscriptKey E Shape S) :=
  (lastEvent history).map fun event => (history.dropLast, event)

theorem transcriptKey?_append (history : List (Absorbed E Shape S)) (event : E) :
    transcriptKey? (history ++ [.event event]) = some (history, event) := by
  simp [transcriptKey?, lastEvent_append_event]

theorem transcriptKey?_chainKey (key : TranscriptKey E Shape S) :
    transcriptKey? (chainKey key) = some key :=
  transcriptKey?_append key.1 key.2

end Keys

/-- The joint simulator's state: the chain simulator's state and the recorded hash-cell
answers. -/
structure JointState (E Shape S Query : Type) (width length : ℕ) where
  chain : ChainState (Absorbed E Shape S) S Bytes width length
  hashes : Query → Option S

section Attempts
variable (encoding : Encoding E Shape S Query) (width : ℕ)

/-- The attempt of bytes: a hash call's own cell, or the transcript cell of the chain attempt of
the chain input they encode. -/
noncomputable def jointAttempt (reached : S → Option (List (Absorbed E Shape S))) (bytes : Bytes) :
    Option (JointKey E Shape S Query) :=
  match encoding.classify bytes with
  | .inl call => some (.inr call)
  | .inr input => ((chainAttempt width reached input).bind transcriptKey?).map Sum.inl

theorem jointAttempt_callBytes (reached : S → Option (List (Absorbed E Shape S))) (call : Query) :
    jointAttempt encoding width reached (encoding.callBytes call) = some (.inr call) := by
  simp only [jointAttempt, encoding.classify_callBytes]

theorem jointAttempt_of_inr {reached : S → Option (List (Absorbed E Shape S))} {bytes : Bytes}
    {input : Input (Absorbed E Shape S) S Bytes} (classified : encoding.classify bytes = .inr input) :
    jointAttempt encoding width reached bytes =
      ((chainAttempt width reached input).bind transcriptKey?).map Sum.inl := by
  simp only [jointAttempt, classified]

/-- A classified chain input's attempt is the transcript cell of its chain attempt, which ends
with the event of a base operation. -/
theorem chainAttempt_of_jointAttempt {reached : S → Option (List (Absorbed E Shape S))}
    {bytes : Bytes} {input : Input (Absorbed E Shape S) S Bytes}
    (classified : encoding.classify bytes = .inr input) {key : TranscriptKey E Shape S}
    (assigned : jointAttempt encoding width reached bytes = some (.inl key)) :
    chainAttempt width reached input = some (chainKey key) := by
  rw [jointAttempt_of_inr encoding width classified] at assigned
  obtain ⟨found, bound, same⟩ := Option.map_eq_some_iff.mp assigned
  cases same
  obtain ⟨history, attempt, last⟩ := Option.bind_eq_some_iff.mp bound
  rw [attempt]
  cases input with
  | request state occurrence block =>
      obtain ⟨event, rfl⟩ := encoding.classify_request classified
      simp only [chainAttempt] at attempt
      split_ifs at attempt
      obtain ⟨before, -, rfl⟩ := Option.map_eq_some_iff.mp attempt
      rw [transcriptKey?_append] at last
      cases last
      rfl
  | bind => cases attempt
  | absorb => cases attempt
  | other => cases attempt

/-- A chain attempt of a classified chain input is the transcript cell of its history. -/
theorem jointAttempt_of_chainAttempt {reached : S → Option (List (Absorbed E Shape S))}
    {bytes : Bytes} {input : Input (Absorbed E Shape S) S Bytes}
    (classified : encoding.classify bytes = .inr input) {history : List (Absorbed E Shape S)}
    (attempt : chainAttempt width reached input = some history) :
    ∃ key, history = chainKey key ∧ jointAttempt encoding width reached bytes = some (.inl key) := by
  cases input with
  | request state occurrence block =>
      obtain ⟨event, rfl⟩ := encoding.classify_request classified
      have shaped := attempt
      simp only [chainAttempt] at shaped
      split_ifs at shaped
      obtain ⟨before, -, rfl⟩ := Option.map_eq_some_iff.mp shaped
      refine ⟨(before, event), rfl, ?_⟩
      rw [jointAttempt_of_inr encoding width classified, attempt]
      simp [transcriptKey?_append]
  | bind => cases attempt
  | absorb => cases attempt
  | other => cases attempt

/-- A classified chain input without a chain attempt has no attempt. -/
theorem jointAttempt_none {reached : S → Option (List (Absorbed E Shape S))} {bytes : Bytes}
    {input : Input (Absorbed E Shape S) S Bytes} (classified : encoding.classify bytes = .inr input)
    (outside : chainAttempt width reached input = none) :
    jointAttempt encoding width reached bytes = none := by
  rw [jointAttempt_of_inr encoding width classified, outside]
  rfl

/-- The attempt of bytes is kept when every chain attempt is. -/
theorem jointAttempt_mono {reached reached' : S → Option (List (Absorbed E Shape S))}
    (kept : ∀ (input : Input (Absorbed E Shape S) S Bytes) history,
      chainAttempt width reached input = some history →
        chainAttempt width reached' input = some history)
    {bytes : Bytes} {key : JointKey E Shape S Query}
    (assigned : jointAttempt encoding width reached bytes = some key) :
    jointAttempt encoding width reached' bytes = some key := by
  unfold jointAttempt at assigned ⊢
  cases classified : encoding.classify bytes with
  | inl call => simp only [classified] at assigned; exact assigned
  | inr input =>
      simp only [classified] at assigned
      obtain ⟨found, bound, rfl⟩ := Option.map_eq_some_iff.mp assigned
      obtain ⟨history, attempt, last⟩ := Option.bind_eq_some_iff.mp bound
      show Option.map Sum.inl ((chainAttempt width reached' input).bind transcriptKey?) = _
      rw [kept input history attempt, Option.bind_some, last, Option.map_some]

end Attempts

variable [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [Inhabited S]

section Simulator
variable (encoding : Encoding E Shape S Query) (width length : ℕ)

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [Inhabited S] in
/-- Bytes stand for a request at one state and occurrence only as that classified request. -/
theorem classify_of_chainInput_request {bytes : Bytes} {state : S} {occurrence : Absorbed E Shape S}
    {block : ℕ} (input : encoding.chainInput bytes = .request state occurrence block) :
    encoding.classify bytes = .inr (.request state occurrence block) := by
  unfold Encoding.chainInput at input
  cases classified : encoding.classify bytes with
  | inl call => simp only [classified] at input; cases input
  | inr other => simp only [classified] at input; rw [input]

/-- The hash-chain simulator with the commitment's hash calls passed through to their own cells. -/
@[reducible] noncomputable def jointSimulator :
    Provider.Simulator (ByteHash S) (Cells E Shape S Query width) (Fin length → S) where
  State := JointState E Shape S Query width length
  start tape := ⟨(chainSimulator width length).start tape, fun _ => none⟩
  attempt state bytes := jointAttempt encoding width state.chain.reached bytes
  recorded state key := match key with
    | .inl key => state.chain.recorded (chainKey key)
    | .inr call => state.hashes call
  record state key answer := match key, answer with
    | .inl key, answer =>
        { state with chain := { state.chain with
            recorded := Function.update state.chain.recorded (chainKey key) (some answer) } }
    | .inr call, answer => { state with hashes := Function.update state.hashes call (some answer) }
  shared bytes key answer := match key, answer with
    | .inl _, answer => chainShared width (encoding.chainInput bytes) answer
    | .inr _, answer => answer
  respond state bytes :=
    ((state.chain.respond (encoding.chainInput bytes)).1,
      { state with chain := (state.chain.respond (encoding.chainInput bytes)).2 })
  together first second := chainTogether width (encoding.chainInput first) (encoding.chainInput second)
  recorded_start _ key := by cases key <;> rfl
  recorded_record state key answer := by
    cases key with
    | inl key => exact Function.update_self _ _ _
    | inr call => exact Function.update_self _ _ _
  recorded_record_of_ne state key other answer different := by
    cases key with
    | inl key =>
        cases other with
        | inl other =>
            have distinct : chainKey other ≠ chainKey key := fun same =>
              different (congrArg Sum.inl (chainKey_injective same))
            exact Function.update_of_ne distinct _ _
        | inr call => rfl
    | inr call =>
        cases other with
        | inl other => rfl
        | inr other =>
            have distinct : other ≠ call := fun same => different (congrArg Sum.inr same)
            exact Function.update_of_ne distinct _ _
  recorded_respond state bytes key := by
    have kept : (state.chain.respond (encoding.chainInput bytes)).2.recorded = state.chain.recorded := by
      simp only [ChainState.respond]
      split <;> rfl
    cases key with
    | inl key => exact congrFun kept (chainKey key)
    | inr call => rfl
  attempt_record state key answer query attemptKey assigned := by
    cases key <;> exact assigned
  attempt_respond state call query attemptKey assigned :=
    jointAttempt_mono encoding width (fun input history attempt =>
      (chainSimulator width length).attempt_respond state.chain (encoding.chainInput call) input history
        attempt) assigned
  attempt_together state first second together := by
    have shaped : ∃ state' occurrence block block', encoding.chainInput first =
        .request state' occurrence block ∧ encoding.chainInput second = .request state' occurrence block' ∧
          block < width ∧ block' < width := by
      revert together
      cases encoding.chainInput first <;> cases encoding.chainInput second <;>
        simp only [chainTogether, IsEmpty.forall_iff]
      rintro ⟨rfl, rfl, below, below'⟩
      exact ⟨_, _, _, _, rfl, rfl, below, below'⟩
    obtain ⟨state', occurrence, block, block', firstInput, secondInput, below, below'⟩ := shaped
    change jointAttempt encoding width state.chain.reached first =
      jointAttempt encoding width state.chain.reached second
    rw [jointAttempt_of_inr encoding width (classify_of_chainInput_request encoding firstInput),
      jointAttempt_of_inr encoding width (classify_of_chainInput_request encoding secondInput)]
    simp only [chainAttempt, below, below', ↓reduceIte]

variable {encoding width length}

@[simp] theorem jointSimulator_attempt (state : (jointSimulator encoding width length).State)
    (bytes : Bytes) :
    (jointSimulator encoding width length).attempt state bytes =
      jointAttempt encoding width state.chain.reached bytes := rfl

/-! ### The frame's obligations -/

/-- A hash call's bytes belong to its own cell in every state. -/
theorem attempt_callBytes (state : (jointSimulator encoding width length).State) (call : Query) :
    (jointSimulator encoding width length).attempt state (encoding.callBytes call) = some (.inr call) :=
  jointAttempt_callBytes encoding width _ call

/-- Only a hash call's bytes realize its cell. -/
theorem eq_callBytes_of_attempt {state : (jointSimulator encoding width length).State} {bytes : Bytes}
    {call : Query} (assigned : (jointSimulator encoding width length).attempt state bytes = some (.inr call)) :
    bytes = encoding.callBytes call := by
  change jointAttempt encoding width state.chain.reached bytes = some (.inr call) at assigned
  unfold jointAttempt at assigned
  cases classified : encoding.classify bytes with
  | inl found =>
      rw [classified] at assigned
      cases assigned
      exact encoding.eq_of_classify_inl classified
  | inr input =>
      rw [classified] at assigned
      obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp assigned
      cases same

/-- Transcript cells are realized only by chain calls. -/
theorem chainCall_of_attempt {state : (jointSimulator encoding width length).State} {bytes : Bytes}
    {key : TranscriptKey E Shape S}
    (assigned : (jointSimulator encoding width length).attempt state bytes = some (.inl key)) :
    ∃ call : ChainCall E Shape S, bytes = encoding.chainBytes call.val := by
  change jointAttempt encoding width state.chain.reached bytes = some (.inl key) at assigned
  cases classified : encoding.classify bytes with
  | inl call =>
      rw [jointAttempt, classified] at assigned
      cases assigned
  | inr input =>
      have attempt := chainAttempt_of_jointAttempt encoding width classified assigned
      rcases encoding.classify_inr classified with chain | other
      · refine ⟨⟨input, chain⟩, ?_⟩
        have back := encoding.bytesOf_classify bytes
        rw [classified] at back
        exact back.symm
      · rw [other] at attempt
        cases attempt

/-- A hash call's reply is its cell's answer. -/
theorem shared_callBytes (call : Query) (answer : S) :
    (jointSimulator encoding width length).shared (encoding.callBytes call) (.inr call) answer = answer :=
  rfl

/-- Recording a hash answer leaves the chain simulator's state unchanged. -/
theorem record_hash_chain (state : (jointSimulator encoding width length).State) (call : Query)
    (answer : S) :
    ((jointSimulator encoding width length).record state (.inr call) answer).chain = state.chain :=
  rfl

/-- Attempts read the state only through the chain simulator's state. -/
theorem attempt_chain {state other : (jointSimulator encoding width length).State}
    (same : state.chain = other.chain) (bytes : Bytes) :
    (jointSimulator encoding width length).attempt state bytes =
      (jointSimulator encoding width length).attempt other bytes := by
  simp only [same]

/-- Recorded transcript answers are read from the chain simulator's state. -/
theorem recorded_chain {state other : (jointSimulator encoding width length).State}
    (same : state.chain = other.chain) (key : TranscriptKey E Shape S) :
    (jointSimulator encoding width length).recorded state (.inl key) =
      (jointSimulator encoding width length).recorded other (.inl key) := by
  change state.chain.recorded (chainKey key) = other.chain.recorded (chainKey key)
  rw [same]

/-- Recording a transcript answer moves the chain simulator's state as a function of it. -/
theorem record_transcript_chain {state other : (jointSimulator encoding width length).State}
    (same : state.chain = other.chain) (key : TranscriptKey E Shape S) (answer : Fin width → S) :
    ((jointSimulator encoding width length).record state (.inl key) answer).chain =
      ((jointSimulator encoding width length).record other (.inl key) answer).chain := by
  obtain ⟨chain, hashes⟩ := state
  obtain ⟨chain', hashes'⟩ := other
  change chain = chain' at same
  subst same
  rfl

/-- A private reply and its successor read the state only through the chain simulator's
state. -/
theorem respond_chain {state other : (jointSimulator encoding width length).State}
    (same : state.chain = other.chain) (bytes : Bytes) :
    ((jointSimulator encoding width length).respond state bytes).1 =
        ((jointSimulator encoding width length).respond other bytes).1 ∧
      ((jointSimulator encoding width length).respond state bytes).2.chain =
        ((jointSimulator encoding width length).respond other bytes).2.chain := by
  change (state.chain.respond _).1 = (other.chain.respond _).1 ∧
    (state.chain.respond _).2 = (other.chain.respond _).2
  rw [same]
  exact ⟨rfl, rfl⟩

end Simulator

section Flat
variable [SampleableType S] (encoding : Encoding E Shape S Query) (width length : ℕ)

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [Inhabited S]
  [SampleableType S] in
/-- The joint cache of a history cache and recorded hash answers: a transcript cell is read at its
chain history, a hash cell from the hash answers. -/
def combine (cache : (OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)).QueryCache)
    (hashes : Query → Option S) : (OracleSpec.ofFn (Cells E Shape S Query width)).QueryCache :=
  QueryCache.ofFn fun key => match key with
    | .inl key => cache (chainKey key)
    | .inr call => hashes call

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [Inhabited S]
  [SampleableType S] in
theorem combine_inl (cache : (OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)).QueryCache)
    (hashes : Query → Option S) (key : TranscriptKey E Shape S) :
    combine width cache hashes (.inl key) = cache (chainKey key) := rfl

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [Inhabited S]
  [SampleableType S] in
theorem combine_inr (cache : (OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)).QueryCache)
    (hashes : Query → Option S) (call : Query) :
    combine width cache hashes (.inr call) = hashes call := rfl

omit [Inhabited S] [SampleableType S] in
theorem combine_cacheQuery (cache : (OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)).QueryCache)
    (hashes : Query → Option S) (key : TranscriptKey E Shape S) (answer : Fin width → S) :
    combine width (cache.cacheQuery (chainKey key) answer) hashes =
      (combine width cache hashes).cacheQuery (.inl key) answer := by
  apply QueryCache.ext
  intro other
  cases other with
  | inl other =>
      by_cases same : other = key
      · subst same
        exact (QueryCache.cacheQuery_self cache (chainKey other) answer).trans
          (QueryCache.cacheQuery_self (combine width cache hashes) (.inl other) answer).symm
      · have distinct : chainKey other ≠ chainKey key := fun equal => same (chainKey_injective equal)
        have distinct' : (Sum.inl other : JointKey E Shape S Query) ≠ .inl key := by simpa using same
        exact (QueryCache.cacheQuery_of_ne cache answer distinct).trans
          (QueryCache.cacheQuery_of_ne (combine width cache hashes) (t := .inl key) answer
            distinct').symm
  | inr call =>
      have distinct : (Sum.inr call : JointKey E Shape S Query) ≠ .inl key := by simp
      exact (QueryCache.cacheQuery_of_ne (combine width cache hashes) (t := .inl key) answer
        distinct).symm

omit [Inhabited S] [SampleableType S] in
theorem combine_cacheQuery_hash (cache : (OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)).QueryCache)
    (hashes : Query → Option S) (call : Query) (answer : S) :
    combine width cache (Function.update hashes call (some answer)) =
      (combine width cache hashes).cacheQuery (.inr call) answer := by
  apply QueryCache.ext
  intro other
  cases other with
  | inl other =>
      have distinct : (Sum.inl other : JointKey E Shape S Query) ≠ .inr call := by simp
      exact (QueryCache.cacheQuery_of_ne (combine width cache hashes) (t := .inr call) answer
        distinct).symm
  | inr other =>
      by_cases same : other = call
      · subst same
        exact (Function.update_self other (some answer) hashes).trans
          (QueryCache.cacheQuery_self (combine width cache hashes) (.inr other) answer).symm
      · have distinct : (Sum.inr other : JointKey E Shape S Query) ≠ .inr call := by simpa using same
        exact (Function.update_of_ne same (some answer) hashes).trans
          (QueryCache.cacheQuery_of_ne (combine width cache hashes) (t := .inr call) answer
            distinct).symm

/-- The joint simulator against the lazily sampled joint oracle, as one simulation. -/
noncomputable def flatJoint :
    QueryImpl (ByteHash S)
      (StateT ((jointSimulator encoding width length).State ×
        (OracleSpec.ofFn (Cells E Shape S Query width)).QueryCache) ProbComp) :=
  flatten (jointSimulator encoding width length).handle randomOracle

omit [Inhabited S] in
/-- The transcript cell of a transcript key in a combined cache is the history cell at its chain
history. -/
theorem randomOracle_combine (cache : (OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)).QueryCache)
    (hashes : Query → Option S) (key : TranscriptKey E Shape S) :
    (randomOracle (spec := OracleSpec.ofFn (Cells E Shape S Query width)) (.inl key)).run
        (combine width cache hashes) =
      (fun step => (step.1, combine width step.2 hashes)) <$>
        (randomOracle (spec := OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)) (chainKey key)).run
          cache := by
  rw [randomOracle.run_eq, randomOracle.run_eq, combine_inl]
  cases cache (chainKey key) with
  | some answer => simp only [map_pure]; rfl
  | none =>
      simp only [map_bind, map_pure]
      refine bind_congr fun answer => ?_
      rw [combine_cacheQuery width cache hashes key answer]
      rfl

/-- On a chain input, the joint simulator's flat step is the chain simulator's, with the transcript
cells read at their chain histories and the hash answers kept aside. -/
theorem flatJoint_run_chain {bytes : Bytes} {input : Input (Absorbed E Shape S) S Bytes}
    (classified : encoding.classify bytes = .inr input)
    (chain : ChainState (Absorbed E Shape S) S Bytes width length) (hashes : Query → Option S)
    (cache : (OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)).QueryCache) :
    (flatJoint encoding width length bytes).run
        ((⟨chain, hashes⟩ : JointState E Shape S Query width length), combine width cache hashes) =
      (fun step => (step.1, (⟨step.2.1, hashes⟩, combine width step.2.2 hashes))) <$>
        (flatSimulator width length input).run (chain, cache) := by
  have chainInput := encoding.chainInput_of_inr classified
  cases attempt : chainAttempt width chain.reached input with
  | none =>
      have outside := jointAttempt_none encoding width classified attempt
      rw [flat_run_private attempt]
      simp only [flatJoint, flatten, StateT.run_mk]
      rw [(jointSimulator encoding width length).handle_private
        (state := (⟨chain, hashes⟩ : JointState E Shape S Query width length)) (query := bytes) outside]
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      change pure ((chain.respond (encoding.chainInput bytes)).1,
        ((⟨(chain.respond (encoding.chainInput bytes)).2, hashes⟩ : JointState E Shape S Query width length),
          combine width cache hashes)) = _
      rw [chainInput]
  | some history =>
      obtain ⟨key, rfl, assigned⟩ := jointAttempt_of_chainAttempt encoding width classified attempt
      cases recorded : chain.recorded (chainKey key) with
      | some answer =>
          rw [flat_run_recorded attempt recorded]
          simp only [flatJoint, flatten, StateT.run_mk]
          rw [(jointSimulator encoding width length).handle_recorded (state := (⟨chain, hashes⟩ : JointState E Shape S Query width length))
            (query := bytes) (key := .inl key) (ideal := answer) assigned recorded]
          simp only [simulateQ_pure, StateT.run_pure, map_pure]
          change pure (chainShared width (encoding.chainInput bytes) answer, _) = _
          rw [chainInput]
      | none =>
          rw [flat_run_fresh attempt recorded]
          simp only [flatJoint, flatten, StateT.run_mk]
          rw [(jointSimulator encoding width length).handle_fresh (state := (⟨chain, hashes⟩ : JointState E Shape S Query width length))
            (query := bytes) (key := .inl key) assigned recorded]
          simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
          rw [randomOracle_combine]
          obtain rfl : input = encoding.chainInput bytes := chainInput.symm
          simp only [bind_pure_comp]
          refine Eq.trans (comp_map _ _ _).symm (Eq.trans ?_ (comp_map _ _ _))
          rfl

/-- On a hash call, the joint simulator's flat step reads the recorded hash answer, or samples a
fresh one and records it in both the simulator's state and the cache. -/
theorem flatJoint_run_hash (call : Query) (chain : ChainState (Absorbed E Shape S) S Bytes width length)
    (hashes : Query → Option S)
    (cache : (OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)).QueryCache) :
    (flatJoint encoding width length (encoding.callBytes call)).run
        ((⟨chain, hashes⟩ : JointState E Shape S Query width length), combine width cache hashes) =
      match hashes call with
      | some answer => pure (answer, (⟨chain, hashes⟩, combine width cache hashes))
      | none => ($ᵗ S) >>= fun answer =>
          pure (answer, (⟨chain, Function.update hashes call (some answer)⟩,
            combine width cache (Function.update hashes call (some answer)))) := by
  have assigned := attempt_callBytes (encoding := encoding) (width := width) (length := length)
    (⟨chain, hashes⟩ : JointState E Shape S Query width length) call
  simp only [flatJoint, flatten, StateT.run_mk]
  cases recorded : hashes call with
  | some answer =>
      rw [(jointSimulator encoding width length).handle_recorded (state := (⟨chain, hashes⟩ : JointState E Shape S Query width length))
        (key := .inr call) (ideal := answer) assigned recorded]
      simp
  | none =>
      rw [(jointSimulator encoding width length).handle_fresh (state := (⟨chain, hashes⟩ : JointState E Shape S Query width length))
        (key := .inr call) assigned recorded]
      simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map,
        randomOracle.run_eq, combine_inr, recorded]
      simp only [map_bind, map_pure]
      refine bind_congr fun answer => ?_
      rw [combine_cacheQuery_hash width cache hashes call answer]

end Flat

end ZkcSecurity.HashChain.Joint
