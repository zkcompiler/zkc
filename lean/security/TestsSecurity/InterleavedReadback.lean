import ZkcSecurity.Examples.Components.SequentialSigma
import ZkcSecurity.Domains.PrimeField
import Mathlib.Algebra.Field.ZMod
import TestsSecurity.SampledReadback

/-! Kernel controls for interleaved honest composition. These exercise actual
Domain runners, stateful private services, and the shared public ROM. They are
not source-admission or native-code correspondence receipts. -/

set_option autoImplicit false
namespace TestsSecurity.InterleavedReadback
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir OracleComp OracleSpec
open ZkcSecurity.Examples.Components.SequentialSigma

instance : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩

abbrev F := ZMod 7
abbrev C := carriers F
abbrev Execution := PIR.Execution (Domain.RuntimeState C Nat) (Domain.Event C) (Frame F)

noncomputable instance : SampleableType F := SampleableType.ofFintype F
noncomputable instance : DecidableEq (Domain.Event C) := Classical.decEq _
noncomputable instance rawSamples : (event : Domain.Event C) → SampleableType (Domain.Raw event) := fun event => by
  cases event with
  | challenge origin =>
      rcases origin with ⟨entry, event, request⟩
      cases request with
      | none => exact inferInstanceAs (SampleableType Unit)
      | some request =>
          rcases request with ⟨method, parameters, sort⟩
          cases sort
          case field identity => exact SampleableType.ofFintype F
          all_goals exact inferInstanceAs (SampleableType Unit)
  | message | publicBinding => exact inferInstanceAs (SampleableType Unit)

noncomputable def coins : Domain.LocalServices ProbComp C Nat := fun mode actualPort origin state =>
  if mode = .producer ∧ actualPort = port ∧ origin = privateOrigin then
    letI : SampleableType (Domain.Raw (.challenge origin : Domain.Event C)) := rawSamples _
    do
      let reply ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event C))
      pure (.returned reply, state + 1)
  else pure (.stopped .refused, state)

theorem coins_return : SampledReadback.Returns Allowed coins := by
  intro actualPort origin admitted state outcome final reached
  obtain ⟨rfl, rfl⟩ := admitted
  simp only [coins, and_self, ite_true] at reached
  obtain ⟨reply, _, reached⟩ := mem_support_bind_peel _ _ reached
  have same := eq_of_mem_support_pure _ reached
  cases same
  exact ⟨reply, rfl⟩

/-- Full execution law for a component, including the private service counter,
heterogeneous proof, checkpoint frame and ordered public observations. -/
theorem stage_execution (answers : QueryImpl (TranscriptOracle.DomainSpec C) Id)
    (round : Nat) (prior : Domain.History C) (base witness : F)
    (initial : Nat) (preceding : Domain.Proof C) (env : Domain.Environment C) :
    Domain.run .producer (ReadbackTransport.tableOracle answers)
      (producerStage round prior base witness) ⟨env, preceding, initial⟩ coins = (do
        let nonce ← $ᵗ F
        let commitment := base * nonce
        let challenge : F := Typed.readTable (Raw := @Domain.Raw C) (R := Typed.ByLast (@Domain.Raw C)) answers
          (commitmentHistory prior round (flag round) commitment) (.challenge (publicOrigin round))
        let response := nonce + challenge * witness
        pure ⟨.returned (frame prior round (flag round) commitment challenge response),
          ⟨environment round (flag round) response,
            preceding ++ [.boolean (flag round), .index round,
              .field "scalar" commitment, .field "scalar" response], initial + 1⟩,
          [.challenge (publicOrigin round),
            .message (messageOrigin "response") (.field "scalar" response)]⟩) := by
  simp [producerStage, Domain.run, PIR.Process.runM, Domain.handler, coins,
    PIR.Execution.followM, ReadbackTransport.tableOracle, List.append_assoc,
    privateOrigin, Origin.query, Domain.Raw, Request.draw, publicOrigin, Domain.drawRequest]

/-- The second stage performs another draw after the first challenge. The
actual producer state records both calls, rather than resetting at bind. -/
theorem producer_counter (answers : QueryImpl (TranscriptOracle.DomainSpec C) Id)
    (base first second : F) (initial : Nat) (produced : Execution)
    (reached : produced ∈ support (Domain.run .producer (ReadbackTransport.tableOracle answers)
      (producer base first second) ⟨[], [], initial⟩ coins)) :
    produced.state.oracle = initial + 2 := by
  have bindLaw : Domain.run .producer (ReadbackTransport.tableOracle answers)
      (producer base first second) ⟨[], [], initial⟩ coins =
      (Domain.run .producer (ReadbackTransport.tableOracle answers)
        (producerStage 0 [] base first) ⟨[], [], initial⟩ coins >>= fun result =>
        result.followM (fun value state => Domain.run .producer
          (ReadbackTransport.tableOracle answers) (producerStage 1 value.history base second) state coins)) :=
    PIR.runM_bind _ _ _ _
  rw [bindLaw, stage_execution] at reached
  simp only [bind_assoc, pure_bind, PIR.Execution.followM] at reached
  obtain ⟨nonce, _, continued⟩ := mem_support_bind_peel _ _ reached
  rw [stage_execution] at continued
  simp only [bind_assoc, pure_bind] at continued
  obtain ⟨secondNonce, _, final⟩ := mem_support_bind_peel _ _ continued
  have same := eq_of_mem_support_pure _ final
  subst produced
  simp only [Nat.add_assoc]

/-- This is the exact suffix theorem for the two-stage client: both outcomes
return, the final private state is handed to the validator, and the arbitrary
suffix survives. No fresh private value is equated with a public reply. -/
theorem exact_readback (answers : QueryImpl (TranscriptOracle.DomainSpec C) Id)
    (base first second : F) (initial : Nat)
    (leftEnv rightEnv : Domain.Environment C) (preceding suffix : Domain.Proof C)
    (produced : Execution)
    (reached : produced ∈ support (Domain.run .producer (ReadbackTransport.tableOracle answers)
      (producer base first second) ⟨leftEnv, preceding, initial⟩ coins)) :
    ∃ result final events proof,
      produced.outcome = .returned result ∧ produced.state.proof = preceding ++ proof ∧
      Domain.run .validator (ReadbackTransport.tableOracle answers)
        (validator base (base * first) (base * second))
        ⟨rightEnv, proof ++ suffix, produced.state.oracle⟩ coins =
        pure ⟨.returned result, ⟨final, suffix, produced.state.oracle⟩, events⟩ := by
  obtain ⟨a, b, final, events, proof, returned, emitted, validated, same⟩ :=
    (readback base first second).run answers coins coins_return initial leftEnv rightEnv
      preceding suffix produced reached
  subst b
  exact ⟨a, final, events, proof, returned, emitted, validated⟩

abbrev Spec := HonestSampling.Spec (@Domain.Raw C)

noncomputable def publicOracle : Domain.Oracle (OracleComp Spec) C Nat := fun history event state => do
  let answer ← (liftM (Typed.ask (R := Typed.ByLast (@Domain.Raw C)) history event) : OracleComp Spec _)
  pure (.returned answer, state)

noncomputable def privateServices : Domain.LocalServices (OracleComp Spec) C Nat :=
  fun mode port origin state => liftM (coins mode port origin state)

theorem simulate_public (answers : QueryImpl (TranscriptOracle.DomainSpec C) Id) :
    (fun history event state => simulateQ (unifFwdAnswerImpl answers)
      (publicOracle history event state)) = ReadbackTransport.tableOracle answers := by
  funext history event state
  simp only [publicOracle, simulateQ_bind, simulateQ_pure, HonestSampling.simulate_transcript]
  simp [Typed.ask, Typed.answer, evalWithAnswerFn_map, evalWithAnswerFn_liftM_query,
    ReadbackTransport.tableOracle, Typed.readTable]

theorem simulate_private (answers : QueryImpl (TranscriptOracle.DomainSpec C) Id) :
    (fun mode port origin state => simulateQ (unifFwdAnswerImpl answers)
      (privateServices mode port origin state)) = coins := by
  funext mode port origin state
  simp only [privateServices, unifFwdAnswerImpl, QueryImpl.passthrough_add, QueryImpl.liftTarget_self]
  rw [QueryImpl.simulateQ_add_liftM_left, simulateQ_id']

/-- A test harness sequencing the actual Domain runners, with the same state
handoff and producer-stop branch as executePair. Both full records are retained. -/
noncomputable def joint (base first second : F) (initial : Nat) :
    OracleComp Spec (Execution × Option Execution) := do
  let produced ← Domain.run .producer publicOracle (producer base first second) ⟨[], [], initial⟩ privateServices
  match produced.outcome with
  | .stopped _ => pure (produced, none)
  | .returned _ =>
      let validated ← Domain.run .validator publicOracle
        (validator base (base * first) (base * second))
        ⟨[], produced.state.proof, produced.state.oracle⟩ privateServices
      pure (produced, some validated)

def Success (initial : Nat) (observed : Execution × Option Execution) : Prop :=
  ∃ result validated, observed.1.outcome = .returned result ∧
    observed.2 = some validated ∧ validated.outcome = .returned result ∧
    validated.state.proof = [] ∧ validated.state.oracle = observed.1.state.oracle ∧
    observed.1.state.oracle = initial + 2

theorem simulate_run (answers : QueryImpl (TranscriptOracle.DomainSpec C) Id)
    (mode : Domain.Mode) (process : PIR.Process (Domain.effects C) (Frame F))
    (state : Domain.RuntimeState C Nat) :
    simulateQ (unifFwdAnswerImpl answers) (Domain.run mode publicOracle process state privateServices) =
      Domain.run mode (ReadbackTransport.tableOracle answers) process state coins := by
  simp only [Domain.run, HonestSampling.simulate_runM]
  congr 1
  funext operation current
  rw [HonestSampling.simulate_handler, simulate_public, simulate_private]

/-- Perfect completeness in the shared ROM for the actual runners, including
both outcomes, complete proof consumption and the private service post-state. -/
theorem rom_perfect_completeness (base first second : F) (initial : Nat) :
    HonestSampling.failure (joint base first second initial) (Success initial) = 0 := by
  apply HonestSampling.failure_zero_of_all_tables
  intro answers
  apply (prEvent_eq_one_iff _ _).mpr
  intro observed reached
  simp only [joint, simulateQ_bind, simulate_run] at reached
  obtain ⟨produced, producedReached, continued⟩ := mem_support_bind_peel _ _ reached
  have counter := producer_counter answers base first second initial produced producedReached
  obtain ⟨result, final, events, proof, returned, emitted, validated⟩ :=
    exact_readback answers base first second initial [] [] [] [] produced producedReached
  simp only [List.nil_append, List.append_nil] at emitted validated
  simp only [returned, simulateQ_bind, simulateQ_pure, simulate_run, emitted, validated, pure_bind] at continued
  have same := eq_of_mem_support_pure _ continued
  subst observed
  exact ⟨result, _, returned, rfl, rfl, rfl, rfl, counter⟩

/-- Private draws inside a later round leave an arbitrary existing ROM cache
unchanged; no phase reset or extra public cache entry is introduced. -/
theorem interleaved_private_cache (state : Nat)
    (cache : (TranscriptOracle.DomainSpec C).QueryCache) :
    (simulateQ (TranscriptOracle.DomainSpec C).romImpl
      (privateServices .producer port privateOrigin state)).run cache =
      (fun value => (value, cache)) <$> coins .producer port privateOrigin state :=
  HonestSampling.private_preserves_cache _ cache

-- The review's previously refused send-then-draw example is now derivable.
theorem review_interleaving :
    SampledReadback TestsSecurity.SampledReadback.Allowed Eq
      (carriers := TestsSecurity.SampledReadback.carriers)
      (.call (.send "marker" "marker" "validator" (.field "coin" (0 : Fin 2))) fun _ =>
        .call (.localService TestsSecurity.SampledReadback.port TestsSecurity.SampledReadback.origin)
          fun _ => .done true)
      (.call (.receive (.field "coin") "marker" "marker" "producer") fun _ => .done true) := by
  apply SampledReadback.sendReceive (carriers := TestsSecurity.SampledReadback.carriers)
    (ty := .field "coin") "marker" "marker" "validator" "marker" "marker" "producer"
    (.field "coin" (0 : Fin 2)) (0 : Fin 2) (by simp [Domain.Payload.value])
  apply SampledReadback.localServiceLeft _ _ ⟨rfl, rfl⟩
  intro reply
  exact .deterministic (.done rfl)

/-- An existing deterministic component (two heterogeneous-origin sends and
its public challenge) remains usable before a new private draw at bind. -/
theorem deterministic_component_then_draw (values : Fin 2 × Fin 2) :
    SampledReadback TestsSecurity.SampledReadback.Allowed Eq
      ((TestsSecurity.SampledReadback.producerTail values).bind fun _ =>
        .call (.localService TestsSecurity.SampledReadback.port TestsSecurity.SampledReadback.origin)
          fun _ => .done true)
      (TestsSecurity.SampledReadback.validatorTail.bind fun _ => .done true) := by
  apply (TestsSecurity.SampledReadback.deterministic_tail values).bind_sampled
  intro left right same
  apply SampledReadback.localServiceLeft _ _ ⟨rfl, rfl⟩
  intro reply
  exact .deterministic (.done rfl)

-- A stopped producer still cannot be certified by the perfect-completeness method.
theorem stop_not_readback (reason : PIR.Stop) :
    ¬ SampledReadback (carriers := C) Allowed (fun _ _ : Unit => True) (.halt reason) (.done ()) := by
  intro aligned
  cases aligned with
  | deterministic aligned => cases aligned

theorem validator_private_not_coupled :
    ¬ SampledReadback (carriers := C) Allowed (fun _ _ : Unit => True) (.done ())
      (.call (.localService port privateOrigin) fun _ => .done ()) := by
  intro aligned
  cases aligned with
  | deterministic aligned => cases aligned

theorem wrong_nominal_head_refuses (answers : QueryImpl (TranscriptOracle.DomainSpec C) Id)
    (suffix : Domain.Proof C) (state : Nat) :
    Domain.run .validator (ReadbackTransport.tableOracle answers)
      (validatorStage 0 [] (1 : F) 2) ⟨[], .field "scalar" (0 : F) :: suffix, state⟩ coins =
      pure ⟨.stopped .refused, ⟨[], .field "scalar" (0 : F) :: suffix, state⟩, []⟩ := by
  simp [validatorStage, Domain.run, PIR.Process.runM, Domain.handler,
    Domain.Payload.value, PIR.Execution.followM]

noncomputable def stopping : Domain.LocalServices ProbComp C Nat :=
  fun _ _ _ state => pure (.stopped .exhausted, state + 9)

/-- A service stop retains its actual state update and the already sent
proof prefix. Its continuation, which would append another marker, is skipped. -/
theorem interleaved_stop (answers : QueryImpl (TranscriptOracle.DomainSpec C) Id)
    (initial : Nat) (preceding : Domain.Proof C) :
    Domain.run .producer (ReadbackTransport.tableOracle answers)
      (.call (.send "marker" "boolean" "validator" (.boolean true)) fun _ =>
        .call (.localService port privateOrigin) fun _ =>
          .call (.send "unreachable" "boolean" "validator" (.boolean false)) fun _ =>
          .done ()) (⟨[], preceding, initial⟩ : Domain.RuntimeState C Nat) stopping =
      pure (⟨.stopped .exhausted, ⟨[], preceding ++ [.boolean true], initial + 9⟩, []⟩ :
        PIR.Execution (Domain.RuntimeState C Nat) (Domain.Event C) Unit) := by
  simp [Domain.run, PIR.Process.runM, Domain.handler, stopping, PIR.Execution.followM]

theorem stopping_not_total : ¬ SampledReadback.Returns Allowed stopping := by
  intro total
  obtain ⟨reply, impossible⟩ := total port privateOrigin ⟨rfl, rfl⟩ 0 (.stopped .exhausted) 9 (by
    simp [stopping])
  cases impossible

theorem unauthorized_service_refuses (actualPort : ServicePort) (other : actualPort ≠ port)
    (origin : Origin) (state : Nat) :
    coins .producer actualPort origin state = pure (.stopped .refused, state) := by
  simp [coins, other]

theorem sampled_abort_not_readback :
    ¬ SampledReadback (carriers := C) Allowed (fun _ _ : Unit => True)
      (.call (.localService port privateOrigin) fun reply : F =>
        if reply = 0 then .halt .abort else .done ()) (.done ()) := by
  intro aligned
  cases aligned with
  | deterministic aligned => cases aligned
  | localServiceLeft _ _ _ next =>
      have stopped := next (0 : F)
      simp only [ite_true] at stopped
      exact stop_not_readback .abort stopped

theorem different_public_keys_not_aligned :
    ¬ SampledReadback (carriers := C) Allowed Eq
      (.call (.query [] (publicOrigin 0)) (fun reply : F => .done reply))
      (.call (.query [] (publicOrigin 1)) (fun reply : F => .done reply)) := by
  intro aligned
  unfold publicOrigin at aligned
  cases aligned with
  | deterministic aligned => cases aligned

theorem different_histories_not_aligned :
    ¬ SampledReadback (carriers := C) Allowed Eq
      (.call (.query [] (publicOrigin 0)) (fun reply : F => .done reply))
      (.call (.query [.message (messageOrigin "flag") (.boolean false)] (publicOrigin 0))
        (fun reply : F => .done reply)) := by
  intro aligned
  cases aligned with
  | deterministic aligned => cases aligned

#print axioms producer_counter
#print axioms interleaved_stop
#print axioms sampled_abort_not_readback
#print axioms different_public_keys_not_aligned
#print axioms different_histories_not_aligned

#print axioms deterministic_component_then_draw
#print axioms repeated_readback
#print axioms Readback.bind_sampled
#print axioms SampledReadback.bind
#print axioms SampledReadback.repeatN
#print axioms stage_readback
#print axioms readback
#print axioms stage_execution
#print axioms exact_readback
#print axioms rom_perfect_completeness
#print axioms review_interleaving

end TestsSecurity.InterleavedReadback
