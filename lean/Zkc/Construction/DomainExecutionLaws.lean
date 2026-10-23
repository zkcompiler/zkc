module

public import Zkc.Construction.DomainProducer
public import Zkc.Semantics.Yields

@[expose] public section

/-! All-reply structural laws and proof-handler controls. These laws concern
constructed instructions and their execution; they are not source compilation
or native codec correspondence theorems. -/
set_option autoImplicit false
namespace Zkc.Construction.Domain
open Zkc.Source

variable {carriers : Structured.Carriers}

namespace Value

theorem decode_encode {ty : Structured.Ty} {input : carriers.Value ty}
    {encoded : Value carriers} (ok : encode ty input = some encoded) :
    encoded.decode ty = some input := by
  unfold encode at ok
  cases h : Payload.ofValue ty input with
  | none => simp [h] at ok
  | some payload =>
      simp only [h, Option.map_some, Option.some.injEq] at ok
      subst encoded
      exact Payload.value_ofValue h

theorem encode_decode {ty : Structured.Ty} {encoded : Value carriers}
    {input : carriers.Value ty} (ok : encoded.decode ty = some input) :
    encode ty input = some encoded := by
  cases encoded with
  | data payload => simp only [decode] at ok; simp [encode, Payload.ofValue_value ok]
  | transcript => simp [decode] at ok
  | indices => simp [decode] at ok

/-- Nominal field identity is checked even when host carrier types coincide. -/
theorem field_wrong_domain {actual expected : String} (different : actual ≠ expected)
    (value : carriers.Field actual) :
    decode (.field expected) (.data (.field actual value)) = none := by
  simp [decode, Payload.value, different]

theorem service_refused (contract : String) (value : Value carriers) :
    decode (.service contract) value = none := by
  cases value with
  | data payload => cases payload <;> rfl
  | transcript => rfl
  | indices => rfl

end Value

theorem decodeValues_encodeValues {tys : List Structured.Ty}
    {input : Values carriers.Value tys} {encoded : Environment carriers}
    (ok : encodeValues input = some encoded) : decodeValues tys encoded = some input := by
  induction input generalizing encoded with
  | nil => simp only [encodeValues, Option.some.injEq] at ok; subst encoded; rfl
  | @cons ty tys head tail ih =>
      simp only [encodeValues] at ok
      cases hh : Value.encode ty head with
      | none => simp [hh] at ok
      | some value =>
          cases ht : encodeValues tail with
          | none => simp [hh, ht] at ok
          | some values =>
              simp [hh, ht] at ok
              subst encoded
              simp [decodeValues, Value.decode_encode hh, ih ht]

theorem encodeValues_decodeValues {tys : List Structured.Ty} {encoded : Environment carriers}
    {input : Values carriers.Value tys} (ok : decodeValues tys encoded = some input) :
    encodeValues input = some encoded := by
  induction tys generalizing encoded with
  | nil =>
      cases encoded <;> simp [decodeValues] at ok
      subst input
      rfl
  | cons ty tys ih =>
      cases encoded with
      | nil => simp [decodeValues] at ok
      | cons value values =>
          cases hh : value.decode ty with
          | none => simp [decodeValues, hh] at ok
          | some head =>
              cases ht : decodeValues tys values with
              | none => simp [decodeValues, hh, ht] at ok
              | some tail =>
                  simp [decodeValues, hh, ht] at ok
                  subst input
                  simp [encodeValues, Value.encode_decode hh, ih ht]

/-- Equality of open Processes quantifies every permitted typed reply. -/
theorem evaluate_append (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (first rest : List Instruction) (env : Environment model.toCarriers) :
    evaluate model program context (first ++ rest) env =
      (evaluate model program context first env).bind (evaluate model program context rest) := by
  induction first generalizing env with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, evaluate, PIR.Process.bind]
      congr 1
      funext reply
      rw [PIR.Process.bind_assoc]
      congr 1
      funext next
      simp only [PIR.Process.bind]
      congr 1
      funext reply
      exact ih next

/-- Relating loop bodies for every environment suffices for every adaptive
iteration, capture and yield. No honest-message restriction is introduced. -/
theorem iterate_congr
    (left right : Environment carriers → PIR.Process (effects carriers) (Environment carriers))
    (same : ∀ env, left env = right env) (outer : Environment carriers)
    (yielded : List Nat) (declared : List ValueSort) (indices : List Nat)
    (carried : Environment carriers) :
    iterate left outer yielded declared indices carried =
      iterate right outer yielded declared indices carried := by
  have h : left = right := funext same
  rw [h]

/-- The loop seam preserves captures, yielded references, and all body replies. -/
theorem iterate_cons
    (body : Environment carriers → PIR.Process (effects carriers) (Environment carriers))
    (outer : Environment carriers) (yielded : List Nat) (declared : List ValueSort)
    (index : Nat) (rest : List Nat) (carried : Environment carriers) :
    iterate body outer yielded declared (index :: rest) carried =
      (body (outer ++ .data (.index index) :: carried)).bind (fun final =>
        match read final yielded with
        | some next => if sortsMatch declared next then iterate body outer yielded declared rest next
            else .halt .refused
        | none => .halt .refused) := rfl

/-- A remaining-iteration invariant is preserved for every typed body reply.
Stops remain stops; this partial-return law makes no totality assertion. -/
theorem iterate_yields
    (body : Environment carriers → PIR.Process (effects carriers) (Environment carriers))
    (outer : Environment carriers) (yielded : List Nat) (declared : List ValueSort)
    (invariant : List Nat → Environment carriers → Prop)
    (preserved : ∀ index rest carried, invariant (index :: rest) carried →
      PIR.Yields (fun final => ∀ next, read final yielded = some next →
        sortsMatch declared next = true → invariant rest next)
        (body (outer ++ .data (.index index) :: carried))) :
    ∀ indices carried, invariant indices carried →
      PIR.Yields (invariant []) (iterate body outer yielded declared indices carried) := by
  intro indices
  induction indices with
  | nil => intro carried holds; exact holds
  | cons index rest ih =>
      intro carried holds
      simp only [iterate]
      apply (preserved index rest carried holds).bind
      intro final finalHolds
      cases found : read final yielded with
      | none => trivial
      | some next =>
          dsimp only
          split
          · exact ih next (finalHolds next found (by assumption))
          · trivial

/-- Every admitted query has the exact request-dependent field reply. -/
theorem queryOrigin_request (context : Context) (suite field : String) (template : Template)
    (coordinates : List Nat) (origin : Origin)
    (found : queryOrigin context suite field template coordinates = some origin) :
    origin.request = some (.draw field) := by
  unfold queryOrigin at found
  split at found
  · cases resolved : templateOrigin context template coordinates with
    | none => simp [resolved] at found
    | some candidate =>
        simp only [resolved] at found
        split at found
        · cases found; assumption
        · simp at found
  · simp at found

section Handlers
variable {m : Type → Type} [Monad m] [LawfulMonad m] {S A B : Type}
variable (oracle : Oracle m carriers S)

theorem run_bind (mode : Mode) (process : PIR.Process (effects carriers) A)
    (next : A → PIR.Process (effects carriers) B) (state : RuntimeState carriers S) :
    run mode oracle (process.bind next) state =
      (run mode oracle process state >>= fun result =>
        result.followM (fun value => run mode oracle (next value))) :=
  PIR.runM_bind _ _ _ _

/-- Direct proof-consuming execution of the open effect tree. This is a
handler reference shape; instruction/arithmetic/loop evaluation is shared. -/
def validateDirect : PIR.Process (effects carriers) A → RuntimeState carriers S →
    m (PIR.Execution (RuntimeState carriers S) (Event carriers) A)
  | .done value, state => pure ⟨.returned value, state, []⟩
  | .halt reason, state => pure ⟨.stopped reason, state, []⟩
  | .call (.receive ty _ _ _) next, state =>
      match state.proof with
      | [] => pure ⟨.stopped .refused, state, []⟩
      | payload :: unread =>
          match payload.value ty with
          | none => pure ⟨.stopped .refused, state, []⟩
          | some value => validateDirect (next value) { state with proof := unread }
  | .call (.send _ _ _ _) next, state => validateDirect (next ()) state
  | .call (.checkpoint env) next, state =>
      validateDirect (next ()) { state with environment := env }
  | .call (.observe event) next, state => do
      let result ← validateDirect (next ()) state
      pure { result with events := event :: result.events }
  | .call (.query history origin) next, state =>
      if drawRequest origin then do
        let (outcome, final) ← oracle history (.challenge origin) state.oracle
        let preceding : PIR.Execution (RuntimeState carriers S) (Event carriers)
            (Raw (.challenge origin)) :=
          ⟨outcome, { state with oracle := final }, [.challenge origin]⟩
        preceding.followM (fun answer state => validateDirect (next answer) state)
      else pure ⟨.stopped .refused, state, []⟩

theorem validator_eq_direct (process : PIR.Process (effects carriers) A)
    (state : RuntimeState carriers S) :
    run .validator oracle process state = validateDirect oracle process state := by
  induction process generalizing state with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
      cases operation with
      | receive ty site schema peer =>
          cases hp : state.proof with
          | nil => simp [run, PIR.Process.runM, handler, hp, PIR.Execution.followM, validateDirect]
          | cons payload unread =>
              cases hv : payload.value ty <;>
                simp [run, PIR.Process.runM, handler, hp, hv, PIR.Execution.followM,
                  validateDirect, ← ih]
      | send => simp [run, PIR.Process.runM, handler, PIR.Execution.followM, validateDirect, ← ih]
      | checkpoint =>
          simp [run, PIR.Process.runM, handler, PIR.Execution.followM, validateDirect, ← ih]
      | observe event =>
          simp [run, PIR.Process.runM, handler, PIR.Execution.followM, validateDirect, ← ih]
      | query history origin =>
          simp only [run, PIR.Process.runM, handler, validateDirect]
          split
          · simp only [bind_assoc, pure_bind]
            congr 1
            funext result
            rcases result with ⟨outcome, final⟩
            cases outcome <;> simp [PIR.Execution.followM, ← ih, run]
          · simp [PIR.Execution.followM]

/-- Prefixing an existing output buffer commutes with production. -/
def prependProof (preceding : Proof carriers) (state : RuntimeState carriers S) :
    RuntimeState carriers S := { state with proof := preceding ++ state.proof }

theorem producer_handler_prefix (preceding : Proof carriers) (operation : Effect carriers)
    (state : RuntimeState carriers S) :
    handler .producer oracle operation (prependProof preceding state) =
      (handler .producer oracle operation state >>= fun result =>
        pure { result with state := prependProof preceding result.state }) := by
  cases operation <;> simp [handler, prependProof, List.append_assoc]
  case query history origin =>
    split <;> simp

/-- Holds for every effect tree, including failures and adaptive continuations. -/
theorem producer_prefix (preceding : Proof carriers) (process : PIR.Process (effects carriers) A)
    (state : RuntimeState carriers S) :
    run .producer oracle process (prependProof preceding state) =
      (run .producer oracle process state >>= fun result =>
        pure { result with state := prependProof preceding result.state }) := by
  have law := fun operation state => producer_handler_prefix oracle preceding operation state
  have expanded := PIR.runM_expand (fun state => pure (prependProof preceding state))
    (handler .producer oracle) (handler .producer oracle)
    (by
      intro operation current
      simp only [pure_bind]
      unfold PIR.Execution.expand
      simpa using law operation current) process state
  unfold PIR.Execution.expand at expanded
  simpa [run] using expanded

/-- Sending before any kind of failure retains exactly that proof preceding. -/
theorem producer_send_halt (site schema peer : String) (payload : Payload carriers)
    (reason : PIR.Stop) (state : RuntimeState carriers S) :
    run .producer oracle (.call (.send site schema peer payload) (fun _ => .halt reason) :
      PIR.Process (effects carriers) A) state =
      pure ⟨.stopped reason, { state with proof := state.proof ++ [payload] }, []⟩ := by
  simp [run, PIR.Process.runM, handler, PIR.Execution.followM]

/-- A malformed proof head is refused without consuming it. -/
theorem validator_bad_head (ty : Structured.Ty) (site schema peer : String)
    (payload : Payload carriers) (unread : Proof carriers) (bad : payload.value ty = none)
    (next : carriers.Value ty → PIR.Process (effects carriers) A)
    (state : RuntimeState carriers S) :
    run .validator oracle (.call (.receive ty site schema peer) next)
        { state with proof := payload :: unread } =
      pure ⟨.stopped .refused, { state with proof := payload :: unread }, []⟩ := by
  simp [run, PIR.Process.runM, handler, bad, PIR.Execution.followM]

theorem bad_request_refuses (history : History carriers) (origin : Origin)
    (bad : drawRequest origin = false) (next : Raw (.challenge origin) →
      PIR.Process (effects carriers) A) (state : RuntimeState carriers S) (mode : Mode) :
    run mode oracle (.call (.query history origin) next) state =
      pure ⟨.stopped .refused, state, []⟩ := by
  simp [run, PIR.Process.runM, handler, bad, PIR.Execution.followM]

/-- Oracle failure preserves its state change and preceding proof, and does
not execute the reply continuation. The attempted query is still observed. -/
theorem query_failure (history : History carriers) (origin : Origin)
    (good : drawRequest origin = true) (reason : PIR.Stop) (final : S)
    (state : RuntimeState carriers S)
    (failed : oracle history (.challenge origin) state.oracle = pure (.stopped reason, final))
    (next : Raw (.challenge origin) → PIR.Process (effects carriers) A) (mode : Mode) :
    run mode oracle (.call (.query history origin) next) state =
      pure ⟨.stopped reason, { state with oracle := final }, [.challenge origin]⟩ := by
  simp [run, PIR.Process.runM, handler, good, failed, PIR.Execution.followM]

omit [LawfulMonad m] in
/-- Producing and validating query the same oracle cell, independent of mode. -/
theorem query_mode_agreement (history : History carriers) (origin : Origin)
    (state : RuntimeState carriers S) :
    handler .producer oracle (.query history origin) state =
      handler .validator oracle (.query history origin) state := rfl

/-- The constructed pair never replaces producer failure with verifier success. -/
theorem executePair_failure (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Environment model.toCarriers)
    (pairOracle : Oracle m model.toCarriers S) (initial : S)
    (produced : PIR.Execution (RuntimeState model.toCarriers S) (Event model.toCarriers)
      (Result model.toCarriers)) (reason : PIR.Stop)
    (execution : produce model program context producer producerInputs pairOracle initial = pure produced)
    (stopped : produced.outcome = .stopped reason) :
    executePair model program context producer validator producerInputs validatorInputs pairOracle initial =
      pure ⟨produced, none⟩ := by
  simp [executePair, execution, stopped]

end Handlers
/-- Every deterministic producer result, including a stopped one, extends the
initial proof buffer. No continuation can erase an earlier sent message. -/
theorem producer_proof_extends {S A : Type} (oracle : Oracle Id carriers S)
    (process : PIR.Process (effects carriers) A) (state : RuntimeState carriers S) :
    ∃ appended, (run .producer oracle process state).state.proof = state.proof ++ appended := by
  let initial := { state with proof := [] }
  have same := producer_prefix oracle state.proof process initial
  refine ⟨(run .producer oracle process initial).state.proof, ?_⟩
  change run .producer oracle process (prependProof state.proof initial) =
    { (run .producer oracle process initial) with
      state := prependProof state.proof (run .producer oracle process initial).state } at same
  have proofEq := congrArg (fun result => result.state.proof) same
  simpa [prependProof, initial] using proofEq

end Zkc.Construction.Domain
