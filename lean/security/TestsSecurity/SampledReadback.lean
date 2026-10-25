import ZkcSecurity.FiatShamir.HonestSampledReadback

/-! Narrow controls for private-prefix readback. These use actual Domain
effects and handlers; source admission and generated-client receipts belong
to their integration owners. -/

set_option autoImplicit false
namespace TestsSecurity.SampledReadback
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir OracleComp OracleSpec

abbrev carriers := Structured.uniformCarriers (Fin 2) Unit

def port : ServicePort := ⟨"coins", "producer", 3, 0, "random.coin/0"⟩
def origin : Origin := Origin.query "prefix-control" "draw" "input_3"
  "random.coin/0" "producer" (.draw "coin")
def publicOrigin : Origin := Origin.query "prefix-control" "challenge" "input_4"
  "random.coin/0" "verifier" (.draw "coin")

def Allowed (actualPort : ServicePort) (actualOrigin : Origin) : Prop :=
  actualPort = port ∧ actualOrigin = origin

/-- The same declared port and exact static origin are sampled twice. A
counter records both calls, including draws whose result a caller ignores. -/
def coins : Domain.LocalServices ProbComp carriers Nat := fun _ actualPort actualOrigin state =>
  if actualPort = port then
    if same : actualOrigin = origin then do
      let value ← $ᵗ (Fin 2)
      let reply : Domain.Raw (.challenge actualOrigin : Domain.Event carriers) := by
        simpa only [same, origin, Origin.query, Domain.Raw, Request.draw] using value
      pure (.returned reply, state + 1)
    else pure (.stopped .refused, state)
  else pure (.stopped .refused, state)

theorem coins_return : SampledReadback.Returns Allowed coins := by
  intro actualPort actualOrigin admitted state outcome final reached
  obtain ⟨rfl, rfl⟩ := admitted
  simp only [coins, ite_true] at reached
  obtain ⟨value, _, reached⟩ := mem_support_bind_peel _ _ reached
  have same := eq_of_mem_support_pure _ reached
  cases same
  exact ⟨value, rfl⟩

def drawPair : PIR.Process (Domain.effects carriers) (Fin 2 × Fin 2) :=
  .call (.checkpoint []) fun _ =>
  .call (.localService port origin) fun first =>
  .call (.checkpoint [.data (.field "coin" first)]) fun _ =>
  .call (.localService port origin) fun second => .done (first, second)

theorem two_draw_prefix : SamplingPrefix Allowed (fun _ => True) drawPair := by
  apply SamplingPrefix.checkpoint []
  apply SamplingPrefix.localService port origin ⟨rfl, rfl⟩
  intro first
  apply SamplingPrefix.checkpoint [.data (.field "coin" first)]
  apply SamplingPrefix.localService port origin ⟨rfl, rfl⟩
  intro second
  exact .done trivial

def history (first second : Fin 2) : Domain.History carriers :=
  [.message (Origin.message "prefix-control" "first" "producer" "validator")
    (.field "coin" first),
   .message (Origin.message "prefix-control" "second" "producer" "validator")
    (.field "coin" second)]

def producerTail (values : Fin 2 × Fin 2) :
    PIR.Process (Domain.effects carriers) (Fin 2 × Fin 2 × Fin 2) :=
  .call (.send "first" "first" "validator" (.field "coin" values.1)) fun _ =>
  .call (.send "second" "second" "validator" (.field "coin" values.2)) fun _ =>
  .call (.query (history values.1 values.2) publicOrigin) fun challenge =>
  .done (values.1, values.2, challenge)

def validatorTail : PIR.Process (Domain.effects carriers) (Fin 2 × Fin 2 × Fin 2) :=
  .call (.receive (.field "coin") "first" "first" "producer") fun first =>
  .call (.receive (.field "coin") "second" "second" "producer") fun second =>
  .call (.query (history first second) publicOrigin) fun challenge =>
  .done (first, second, challenge)

theorem deterministic_tail (values : Fin 2 × Fin 2) :
    Readback Eq (producerTail values) validatorTail := by
  unfold producerTail validatorTail
  apply Readback.sendReceive (carriers := carriers) (ty := .field "coin")
    "first" "first" "validator" "first" "first" "producer"
    (.field "coin" values.1) values.1 (by simp [Domain.Payload.value])
  apply Readback.sendReceive (carriers := carriers) (ty := .field "coin")
    "second" "second" "validator" "second" "second" "producer"
    (.field "coin" values.2) values.2 (by simp [Domain.Payload.value])
  apply Readback.query (history values.1 values.2) publicOrigin rfl
  intro reply
  exact .done rfl

theorem two_draw_readback : SampledReadback Allowed Eq (drawPair.bind producerTail) validatorTail :=
  two_draw_prefix.readback fun values _ => deterministic_tail values

/-- Completeness may be independent of both private replies. The actual
prefix still executes its two draws and checkpoints before this return. -/
theorem unused_samples_readback :
    SampledReadback Allowed Eq (drawPair.bind (fun _ => .done true)) (.done true) :=
  two_draw_prefix.readback fun _ _ => .done rfl

/-- Exact interpreter equation: repeated origins are fresh calls and the
service counter and checkpoint environment are preserved. -/
theorem two_draw_execution (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (initial : Nat) :
    Domain.run .producer (ReadbackTransport.tableOracle answers) drawPair
      ⟨[], [], initial⟩ coins = (do
        let first ← $ᵗ (Fin 2)
        let second ← $ᵗ (Fin 2)
        pure ⟨.returned (first, second),
          ⟨[.data (.field "coin" first)], [], initial + 2⟩, []⟩) := by
  simp [drawPair, Domain.run, PIR.Process.runM, Domain.handler, coins, PIR.Execution.followM,
    Nat.add_assoc, origin, Origin.query, Domain.Raw, Request.draw]

def independent : ProbComp (Fin 2 × Fin 2) := do
  let first ← $ᵗ (Fin 2)
  let second ← $ᵗ (Fin 2)
  pure (first, second)

theorem independent_agreement : Pr{let values ← independent}[values.1 = values.2] = 1 / 2 := by
  rw [independent, ← SampleableType.uniformSample_prod_eq_bind]
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun values : Fin 2 × Fin 2 => values.1 = values.2).card = 2 := by
    decide +kernel
  rw [count, Fintype.card_prod, Fintype.card_fin]
  norm_num only [Nat.cast_ofNat, Nat.cast_mul]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
  norm_num

theorem repeated_root_agreement
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id) :
    Pr{let result ← (Domain.run .producer (ReadbackTransport.tableOracle answers) drawPair
      ⟨[], [], 0⟩ coins)}[∃ first second, result.outcome = .returned (first, second) ∧ first = second] =
        1 / 2 := by
  rw [two_draw_execution]
  have mapped : (do
      let first ← $ᵗ (Fin 2)
      let second ← $ᵗ (Fin 2)
      pure (PIR.Execution.mk (.returned (first, second))
        (Domain.RuntimeState.mk (carriers := carriers) [.data (.field "coin" first)] [] (0 + 2))
        ([] : List (Domain.Event carriers)))) =
      (fun values : Fin 2 × Fin 2 => PIR.Execution.mk (.returned values)
        (Domain.RuntimeState.mk (carriers := carriers) [.data (.field "coin" values.1)] [] (0 + 2))
        ([] : List (Domain.Event carriers))) <$> independent := by
    simp [independent]
  rw [mapped, prEvent_map]
  have eventEq (values : Fin 2 × Fin 2) :
      (∃ first second, values = (first, second) ∧ first = second) ↔ values.1 = values.2 := by
    constructor
    · rintro ⟨first, second, rfl, equal⟩
      exact equal
    · intro equal
      exact ⟨values.1, values.2, rfl, equal⟩
  simpa only [PIR.Outcome.returned.injEq, eventEq] using independent_agreement

/-- Using one cached local reply would force equality and fails this control. -/
theorem repeated_root_not_cached
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id) :
    Pr{let result ← (Domain.run .producer (ReadbackTransport.tableOracle answers) drawPair
      ⟨[], [], 0⟩ coins)}[∃ first second, result.outcome = .returned (first, second) ∧ first = second] ≠ 1 := by
  rw [repeated_root_agreement]
  norm_num

def oneDraw : PIR.Process (Domain.effects carriers) (Fin 2) :=
  .call (.localService port origin) .done

def sampleSide (mode : Domain.Mode)
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id) (state : Nat) :
    ProbComp (Fin 2 × Nat) := do
  let observed ← Domain.run mode (ReadbackTransport.tableOracle answers) oneDraw ⟨[], [], state⟩ coins
  pure ((match observed.outcome with | .returned reply => reply | .stopped _ => 0), observed.state.oracle)

def sampleBothSides (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id) :
    ProbComp (Fin 2 × Fin 2) := do
  let produced ← sampleSide .producer answers 0
  let validated ← sampleSide .validator answers produced.2
  pure (produced.1, validated.1)

/-- Even the same nominal type, port and origin on two sides do not couple
fresh samples. This control uses the real handler twice with state handoff. -/
theorem two_sides_execution (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id) :
    sampleBothSides answers = independent := by
  simp [sampleBothSides, sampleSide, oneDraw, Domain.run, PIR.Process.runM, Domain.handler,
    coins, PIR.Execution.followM, independent, origin, Origin.query, Domain.Raw, Request.draw]

theorem private_sides_independent
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id) :
    Pr{let values ← sampleBothSides answers}[values.1 = values.2] = 1 / 2 := by
  rw [two_sides_execution]
  exact independent_agreement

theorem undeclared_port_refuses (actualPort : ServicePort) (different : actualPort ≠ port)
    (actualOrigin : Origin) (state : Nat) :
    coins .producer actualPort actualOrigin state = pure (.stopped .refused, state) := by
  simp [coins, different]

/-- The full producer proof is consumed and both actual returns agree. This
instantiates the prefix rule through communication and a public query. -/
theorem exact_readback (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (produced : PIR.Execution (Domain.RuntimeState carriers Nat) (Domain.Event carriers)
      (Fin 2 × Fin 2 × Fin 2))
    (reached : produced ∈ support (Domain.run .producer (ReadbackTransport.tableOracle answers)
      (drawPair.bind producerTail) ⟨[], [], 0⟩ coins)) :
    ∃ left right final events proof,
      produced.outcome = .returned left ∧ produced.state.proof = proof ∧
      Domain.run .validator (ReadbackTransport.tableOracle answers) validatorTail
        ⟨[], proof, produced.state.oracle⟩ coins =
          pure ⟨.returned right, ⟨final, [], produced.state.oracle⟩, events⟩ ∧ left = right := by
  simpa only [List.nil_append, List.append_nil] using
    two_draw_readback.run answers coins coins_return 0 [] [] [] [] produced reached

/-- Private computation, including repeated-root samples, leaves an existing
public cache untouched. The cache is not reset or replaced by the prefix. -/
theorem private_cache [DecidableEq (Domain.Event carriers)]
    [∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]
    (cache : (TranscriptOracle.DomainSpec carriers).QueryCache) :
    (simulateQ (TranscriptOracle.DomainSpec carriers).romImpl
      (liftM independent : OracleComp (HonestSampling.Spec (@Domain.Raw carriers)) _)).run cache =
      (fun values => (values, cache)) <$> independent :=
  HonestSampling.private_preserves_cache independent cache

-- A producer-private rule cannot silently admit a validator-private request.
theorem validator_sample_not_coupled :
    ¬ SampledReadback (carriers := carriers) Allowed (fun _ _ : Unit => True) (.done ())
      (.call (.localService port origin) (fun _ => .done ())) := by
  intro aligned
  cases aligned with
  | deterministic aligned => cases aligned

-- Sample-dependent failure has no perfect-prefix terminal rule.
theorem abort_not_prefix :
    ¬ SamplingPrefix (carriers := carriers) Allowed (fun _ : Unit => True) (.halt .abort) := by
  intro derivation
  cases derivation

theorem sampled_abort_not_prefix :
    ¬ SamplingPrefix (carriers := carriers) Allowed (fun _ : Unit => True)
      (.call (.localService port origin) (fun reply : Fin 2 =>
        if reply = 0 then .halt .abort else .done ())) := by
  intro derivation
  cases derivation with
  | localService _ _ _ next =>
      have stopped := next (0 : Fin 2)
      simp only [ite_true] at stopped
      cases stopped

#print axioms SamplingPrefix.readback
#print axioms Readback.runM_table
#print axioms SampledReadback.run
#print axioms SampledReadback.pair_success
#print axioms SampledReadback.failure_zero
#print axioms HonestSampling.simulate_executePair
#print axioms two_draw_readback
#print axioms two_draw_execution
#print axioms repeated_root_agreement
#print axioms private_sides_independent
#print axioms sampled_abort_not_prefix
#print axioms exact_readback

end TestsSecurity.SampledReadback
