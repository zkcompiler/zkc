module

public import ZkcSecurity.HashChain.Encoding
public import ZkcSecurity.HashChain.Instance

@[expose] public section

/-! The hash chain over a byte hash.

The deployed primitive is a byte hash `H : Bytes → S`. The chain verifier calls
it at the encodings of its classified inputs (`byteExperiment`), and the
adversary calls it at any bytes. Classifying the adversary's bytes (`parse`: the
classified chain input they encode, or an other input) gives the experiment of
`ZkcSecurity.HashChain.Model` over classified inputs, with the same law
(`byteExperiment_eq`): the classification is injective on the bytes and the
encoding is injective on chain inputs, so the two random oracles answer the same
calls with the same cached or fresh values.

`byte_soundness` is the resulting Fiat–Shamir soundness bound for the byte hash.
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.HashChain.Encoding
open OracleComp.ProgramLogic.Relational

variable {E S : Type}

/-- The byte hash. -/
abbrev ByteHash (S : Type) : OracleSpec Bytes := OracleSpec.ofFn fun _ : Bytes => S

section Classification
variable (stateBytes : S → Bytes) (eventBytes : E → Bytes)

/-- Bytes that encode a chain input with a counter below `2^64`. -/
def ChainBytes (bytes : Bytes) : Prop :=
  ∃ input : Input E S Bytes, Encodable input ∧ encodeInput stateBytes eventBytes input = bytes

open Classical in
/-- The classified input bytes encode: the chain input they encode, or else an
other input. -/
noncomputable def parse (bytes : Bytes) : Input E S Bytes :=
  if encoded : ChainBytes stateBytes eventBytes bytes then Classical.choose encoded
  else .other bytes

theorem encodeInput_parse (bytes : Bytes) :
    encodeInput stateBytes eventBytes (parse stateBytes eventBytes bytes) = bytes := by
  unfold parse
  split_ifs with encoded
  · exact (Classical.choose_spec encoded).2
  · rfl

theorem parse_injective : Function.Injective (parse (E := E) (S := S) stateBytes eventBytes) :=
  fun first second same => by
    rw [← encodeInput_parse stateBytes eventBytes first,
      ← encodeInput_parse stateBytes eventBytes second, same]

/-- An encodable chain input is the classification of its bytes. -/
theorem parse_encodeInput {width : ℕ} (stateLength : ∀ state, (stateBytes state).length = width)
    (stateInjective : Function.Injective stateBytes)
    (eventInjective : Function.Injective eventBytes) {input : Input E S Bytes}
    (encodable : Encodable input) :
    parse stateBytes eventBytes (encodeInput stateBytes eventBytes input) = input := by
  have encoded : ChainBytes stateBytes eventBytes (encodeInput stateBytes eventBytes input) :=
    ⟨input, encodable, rfl⟩
  unfold parse
  rw [dite_eq_left_of_eq_true (eq_true encoded)]
  obtain ⟨chosenEncodable, chosenBytes⟩ := Classical.choose_spec encoded
  exact encodeInput_injective stateLength stateInjective eventInjective chosenEncodable encodable
    chosenBytes

end Classification

section Congruence
variable {I : PIR.Signature} {P A : Type} {X : Type} {width : ℕ} {m : Type → Type} [Monad m]

/-- An input the chain verifier calls: a binding, an absorption, or a counter
block below the width. -/
def VerifierInput (width : ℕ) : Input E S X → Prop
  | .bind _ => True
  | .absorb _ _ => True
  | .request _ _ block => block < width
  | .other _ => False

omit [Monad m] in
theorem collect_congr {count : ℕ} [Monad m] {first second : Fin count → m S}
    (same : ∀ index, first index = second index) : collect count first = collect count second := by
  rw [funext same]

/-- The chain verifier depends on the hash only at the inputs it calls. -/
theorem chainTransform_congr (absorb : Typed.Interface I E P (Raw E S width))
    {first second : Input E S X → m S}
    (same : ∀ input, VerifierInput width input → first input = second input) :
    ∀ (process : PIR.Process I A) (state : S) (history : List E) (proof : List P),
      chainTransform absorb first process state history proof =
        chainTransform absorb second process state history proof := by
  intro process
  induction process with
  | done value => intro _ _ _; rfl
  | halt stop => intro _ _ _; rfl
  | call operation next ih =>
      intro state history proof
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · cases proof with
        | nil => simp only [chainTransform, absorbed]
        | cons message rest =>
            simp only [chainTransform, absorbed]
            cases recover (event message) with
            | none => rfl
            | some value =>
                simp only
                rw [same (.absorb state (event message)) trivial]
                exact bind_congr fun advanced => ih value _ _ _
      · simp only [chainTransform, absorbed]
        rw [same (.absorb state event) trivial]
        exact bind_congr fun advanced => ih value _ _ _
      · simp only [chainTransform, absorbed]
        rw [collect_congr fun block => same (.request state event block.val) block.isLt,
          same (.absorb state event) trivial]
        refine bind_congr fun raw => bind_congr fun advanced => ?_
        cases decode raw with
        | none => rfl
        | some value => exact ih value _ _ _
      · simp only [chainTransform, absorbed]

theorem absorbAll_congr {first second : Input E S X → m S}
    (same : ∀ input, VerifierInput width input → first input = second input) :
    ∀ (events : List E) (state : S), absorbAll first state events = absorbAll second state events
  | [], _ => rfl
  | event :: rest, state => by
      simp only [absorbAll]
      rw [same (.absorb state event) trivial]
      exact bind_congr fun next => absorbAll_congr same rest next

theorem chainRun_congr (absorb : Typed.Interface I E P (Raw E S width))
    {first second : Input E S X → m S}
    (same : ∀ input, VerifierInput width input → first input = second input)
    (validator : PIR.Process I A) (initial : List E) (proof : List P) :
    chainRun absorb first validator initial proof = chainRun absorb second validator initial proof := by
  cases initial with
  | nil => rfl
  | cons event rest =>
      simp only [chainRun]
      rw [same (.bind event) trivial]
      refine bind_congr fun state => ?_
      rw [absorbAll_congr same rest state]
      exact bind_congr fun started => chainTransform_congr absorb same validator _ _ proof

end Congruence

section Experiments
variable [DecidableEq E] [DecidableEq S] [SampleableType S] (stateBytes : S → Bytes)
  (eventBytes : E → Bytes) {I : PIR.Signature} {P A Stmt : Type} {width : ℕ}

/-- One call of the byte hash. -/
def byteCall (bytes : Bytes) : OracleComp (ByteHash S) S := liftM ((ByteHash S).query bytes)

/-- The concrete experiment over the byte hash: the adversary calls the byte hash
directly; the chain verifier calls it at the encodings of its inputs. -/
def byteExperiment (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Process I A) (initial : Stmt → List E)
    (adversary : OracleComp (ByteHash S) (Stmt × List P)) :
    OracleComp (ByteHash S) (Stmt × (PIR.Outcome A × List P)) :=
  adversary >>= fun claimed => (fun result => (claimed.1, result)) <$>
    chainRun absorb (fun input => byteCall (encodeInput stateBytes eventBytes input))
      (validator claimed.1) (initial claimed.1) claimed.2

/-- The adversary with its byte calls classified. -/
noncomputable def classify {α : Type} (adversary : OracleComp (ByteHash S) α) :
    OracleComp (Primitive E S Bytes) α :=
  simulateQ (fun bytes => call (parse stateBytes eventBytes bytes)) adversary

/-- Caches that answer the bytes of each classification alike. -/
def CachesAgree (bytesCache : (ByteHash S).QueryCache)
    (inputCache : (Primitive E S Bytes).QueryCache) : Prop :=
  ∀ bytes, bytesCache bytes = inputCache (parse stateBytes eventBytes bytes)

/-- One byte call against one classified call, from agreeing caches. -/
theorem byte_step (bytes : Bytes) (bytesCache : (ByteHash S).QueryCache)
    (inputCache : (Primitive E S Bytes).QueryCache)
    (agree : CachesAgree stateBytes eventBytes bytesCache inputCache) :
    RelTriple ((randomOracle (spec := ByteHash S) bytes).run bytesCache)
      ((randomOracle (spec := Primitive E S Bytes) (parse stateBytes eventBytes bytes)).run
        inputCache)
      (fun one two => one.1 = two.1 ∧ CachesAgree stateBytes eventBytes one.2 two.2) := by
  rw [randomOracle.run_eq, randomOracle.run_eq, ← agree bytes]
  cases bytesCache bytes with
  | some answer => exact relTriple_pure_pure ⟨rfl, agree⟩
  | none =>
      refine relTriple_fresh fun answer => ⟨rfl, fun other => ?_⟩
      by_cases same : other = bytes
      · subst same
        simp
      · rw [QueryCache.cacheQuery_of_ne _ _ same, QueryCache.cacheQuery_of_ne _ _
          fun equal => same (parse_injective stateBytes eventBytes equal)]
        exact agree other

/-- The byte-hash experiment and the experiment over classified inputs with the
classified adversary have equal results, coupled call by call. -/
theorem byteExperiment_coupling {width' : ℕ}
    (stateLength : ∀ state, (stateBytes state).length = width')
    (stateInjective : Function.Injective stateBytes) (eventInjective : Function.Injective eventBytes)
    (small : width ≤ 2 ^ 64) (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Process I A) (initial : Stmt → List E)
    (adversary : OracleComp (ByteHash S) (Stmt × List P)) :
    RelTriple
      ((simulateQ randomOracle (byteExperiment stateBytes eventBytes absorb validator initial
        adversary)).run' ∅)
      ((simulateQ randomOracle (experiment absorb validator initial
        (classify stateBytes eventBytes adversary))).run' ∅)
      (EqRel _) := by
  have normal : ∀ input : Input E S Bytes, VerifierInput width input →
      parse stateBytes eventBytes (encodeInput stateBytes eventBytes input) = input := by
    intro input verifierInput
    refine parse_encodeInput stateBytes eventBytes stateLength stateInjective eventInjective ?_
    cases input with
    | bind => trivial
    | absorb => trivial
    | request state event block => exact lt_of_lt_of_le verifierInput small
    | other => exact verifierInput.elim
  have classified : simulateQ randomOracle (classify stateBytes eventBytes adversary) =
      simulateQ (fun bytes => randomOracle (spec := Primitive E S Bytes)
        (parse stateBytes eventBytes bytes)) adversary := by
    rw [classify, ← QueryImpl.simulateQ_compose]
    congr 1
    funext bytes
    simp [call]
  have byteVerifier : ∀ (validatorProcess : PIR.Process I A) (history : List E) (proof : List P),
      simulateQ randomOracle (chainRun absorb
          (fun input => byteCall (encodeInput stateBytes eventBytes input)) validatorProcess
          history proof) =
        simulateQ (fun input : Input E S Bytes => randomOracle (spec := ByteHash S)
          (encodeInput stateBytes eventBytes input))
          (chainRun absorb call validatorProcess history proof) := by
    intro validatorProcess history proof
    let encoded : QueryImpl (Primitive E S Bytes) (OracleComp (ByteHash S)) :=
      fun input => byteCall (encodeInput stateBytes eventBytes input)
    have unfolded : chainRun absorb (fun input => byteCall (encodeInput stateBytes eventBytes input))
          validatorProcess history proof =
        simulateQ encoded (chainRun absorb call validatorProcess history proof) :=
      (simulateQ_chainRun encoded absorb validatorProcess history proof).symm
    rw [unfolded, ← QueryImpl.simulateQ_compose]
    congr 1
    funext input
    simp [encoded, byteCall]
  have inputVerifier : ∀ (validatorProcess : PIR.Process I A) (history : List E) (proof : List P),
      simulateQ randomOracle (chainRun absorb call validatorProcess history proof) =
        simulateQ (fun input : Input E S Bytes => randomOracle (spec := Primitive E S Bytes)
          (parse stateBytes eventBytes (encodeInput stateBytes eventBytes input)))
          (chainRun absorb call validatorProcess history proof) := by
    intro validatorProcess history proof
    rw [simulateQ_chainRun, simulateQ_chainRun]
    exact chainRun_congr absorb (fun input verifierInput => by rw [normal input verifierInput])
      validatorProcess history proof
  simp only [byteExperiment, experiment, simulateQ_bind, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, classified, byteVerifier, inputVerifier]
  refine relTriple_map (relTriple_bind
    (OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run randomOracle
      (fun bytes => randomOracle (spec := Primitive E S Bytes) (parse stateBytes eventBytes bytes))
      (CachesAgree stateBytes eventBytes) adversary
      (fun bytes bytesCache inputCache agree => byte_step stateBytes eventBytes bytes bytesCache
        inputCache agree) ∅ ∅ (fun _ => rfl)) fun one two coupled => ?_)
  obtain ⟨same, agree⟩ := coupled
  rw [same]
  refine relTriple_map (relTriple_post_mono
    (OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run
      (fun input : Input E S Bytes => randomOracle (spec := ByteHash S)
        (encodeInput stateBytes eventBytes input))
      (fun input : Input E S Bytes => randomOracle (spec := Primitive E S Bytes)
        (parse stateBytes eventBytes (encodeInput stateBytes eventBytes input)))
      (CachesAgree stateBytes eventBytes) _
      (fun input bytesCache inputCache agree' => byte_step stateBytes eventBytes
        (encodeInput stateBytes eventBytes input) bytesCache inputCache agree')
      one.2 two.2 agree) fun first second related => ?_)
  simp only [EqRel, related.1]

/-- The byte-hash experiment and the classified experiment give every event the
same probability. -/
theorem byteExperiment_eq {width' : ℕ}
    (stateLength : ∀ state, (stateBytes state).length = width')
    (stateInjective : Function.Injective stateBytes) (eventInjective : Function.Injective eventBytes)
    (small : width ≤ 2 ^ 64) (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Process I A) (initial : Stmt → List E)
    (adversary : OracleComp (ByteHash S) (Stmt × List P))
    (event : Stmt × (PIR.Outcome A × List P) → Prop) :
    Pr{let result ← (simulateQ randomOracle (byteExperiment stateBytes eventBytes absorb validator
        initial adversary)).run' ∅}[event result] =
      Pr{let result ← (simulateQ randomOracle (experiment absorb validator initial
        (classify stateBytes eventBytes adversary))).run' ∅}[event result] :=
  ZkcSecurity.VCVio.Deferral.prEvent_eq_of_evalSPMF_eq (evalDistEq_of_relTriple_eqRel
    (byteExperiment_coupling stateBytes eventBytes stateLength stateInjective eventInjective small
      absorb validator initial adversary)) event

omit [DecidableEq E] [DecidableEq S] [SampleableType S] in
/-- Classifying the calls keeps their number. -/
theorem classify_queryBound {α : Type} :
    ∀ (adversary : OracleComp (ByteHash S) α) (calls : ℕ), IsTotalQueryBound adversary calls →
      IsTotalQueryBound (classify (E := E) stateBytes eventBytes adversary) calls := by
  intro adversary
  induction adversary using OracleComp.inductionOn with
  | pure value => intro _ _; trivial
  | query_bind bytes next ih =>
      intro calls bounded
      obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bounded
      simp only [classify, simulateQ_bind, simulateQ_spec_query, call]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨positive, fun reply => ih reply _ (rest reply)⟩

end Experiments

section Soundness
variable [DecidableEq E] [DecidableEq S] [SampleableType S] [Inhabited S] [Fintype S]
  (stateBytes : S → Bytes) (eventBytes : E → Bytes) {I : PIR.Signature} {P A Stmt : Type}
  {width : ℕ}

/-- Fiat–Shamir soundness of the hash-chain construction over a byte hash read as
a random oracle: an adversary with at most `q` calls of the byte hash makes the
validator of a false statement accept with probability at most
`(q + queries) * bound + (q + V)² / |S|`. The states have one byte length and
the events an injective encoding, so the chain's inputs are distinct bytes. -/
theorem byte_soundness {stateLength : ℕ}
    (stateLengths : ∀ state, (stateBytes state).length = stateLength)
    (stateInjective : Function.Injective stateBytes) (eventInjective : Function.Injective eventBytes)
    (small : width ≤ 2 ^ 64) (positive : 0 < width)
    {absorb : Typed.Interface I E P (Raw E S width)} {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Typed.Certificate absorb accepts error) {bound : ENNReal}
    (bounded : ∀ event, error event ≤ bound) (validator : Stmt → PIR.Process I A)
    (initial : Stmt → List E) (determined : Typed.Determined initial)
    (nonempty : ∀ statement, initial statement ≠ []) (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    {queries : ℕ} (queryBounded : ∀ statement, Typed.QueryBound absorb (validator statement) queries)
    (verifierCalls : ℕ) (callBudget : Stmt → ℕ)
    (callBounded : ∀ statement, CallBound absorb (validator statement) (callBudget statement))
    (within : ∀ statement, (initial statement).length + callBudget statement ≤ verifierCalls)
    (adversary : OracleComp (ByteHash S) (Stmt × List P)) {calls : ℕ}
    (adversaryBound : IsTotalQueryBound adversary calls) :
    Pr{let result ← (simulateQ randomOracle (byteExperiment stateBytes eventBytes absorb validator
        initial adversary)).run' ∅}[falseStatement result.1 ∧ Accepted accepts result.2.1] ≤
      (calls + queries) * bound +
        (((calls + verifierCalls) * (calls + verifierCalls) : ℕ) : ENNReal) / Fintype.card S := by
  rw [byteExperiment_eq stateBytes eventBytes stateLengths stateInjective eventInjective small]
  exact concrete_soundness positive certificate bounded validator initial determined nonempty
    falseStatement doomedValidator queryBounded verifierCalls callBudget callBounded within
    (classify stateBytes eventBytes adversary)
    (classify_queryBound stateBytes eventBytes adversary calls adversaryBound)

end Soundness

end ZkcSecurity.HashChain
