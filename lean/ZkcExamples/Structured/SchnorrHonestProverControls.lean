module

public import ZkcExamples.Structured.SchnorrHonestProver
public import Mathlib.Algebra.Field.Rat

@[expose] public section

/-! Kernel controls. Rational additive arithmetic is a model instance,
not BLS arithmetic. Mutated constructor subjects have synthetic source markers
and are not claimed to be fresh native exports. -/
namespace ZkcExamples.Structured.SchnorrHonestProver.Controls
open Zkc.Source Zkc.Source.Structured

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option smartUnfolding false

/-- The verifier key violates the witness relation. Merely changing the unused
prover key is a different case, covered by `unused_prover_key_can_differ`. -/
theorem wrong_verifier_key_rejected :
    (Zkc.Protocols.Schnorr.Common.run (F := ℚ) SchnorrInteractive.verifier
      (1 : ℚ) 4 9 (strategy (F := ℚ) 1 2 2 3 8) 5).outcome ≠ .returned (some true) := by
  rw [ne_eq, SchnorrInteractive.contract.accepted_iff, strategy_eq]
  decide +kernel

theorem mismatched_base_rejected :
    (Zkc.Protocols.Schnorr.Common.run (F := ℚ) SchnorrInteractive.verifier
      (2 : ℚ) 2 9 (strategy (F := ℚ) 1 2 2 3 8) 5).outcome ≠ .returned (some true) := by
  rw [ne_eq, SchnorrInteractive.contract.accepted_iff, strategy_eq]
  decide +kernel

/-- The prover actually receives 6 while the verifier uses 5. Both source
messages still come from observations; honest challenge delivery is violated. -/
theorem bad_challenge_delivery_rejected :
    (Zkc.Protocols.Schnorr.Common.run (F := ℚ) SchnorrInteractive.verifier (1 : ℚ) 2 9
      ⟨(strategy (F := ℚ) (1 : ℚ) 2 2 3 8).commitment,
       fun c => (strategy (F := ℚ) (1 : ℚ) 2 2 3 8).response (c + 1)⟩ 5).outcome ≠
        .returned (some true) := by
  rw [ne_eq, SchnorrInteractive.contract.accepted_iff, strategy_eq]
  decide +kernel

/-- Honest source execution followed by response corruption in delivery. -/
theorem bad_response_delivery_rejected :
    (Zkc.Protocols.Schnorr.Common.run (F := ℚ) SchnorrInteractive.verifier (1 : ℚ) 2 9
      ⟨(strategy (F := ℚ) (1 : ℚ) 2 2 3 8).commitment,
       fun c => (strategy (F := ℚ) (1 : ℚ) 2 2 3 8).response c + 1⟩ 5).outcome ≠
        .returned (some true) := by
  rw [ne_eq, SchnorrInteractive.contract.accepted_iff, strategy_eq]
  decide +kernel

/-- The strengthened completeness theorem leaves the unused prover key
unconstrained; this mismatch does not violate its premises. -/
theorem unused_prover_key_can_differ :
    (Zkc.Protocols.Schnorr.Common.run (F := ℚ) SchnorrInteractive.verifier
      (1 : ℚ) 2 9 (strategy (F := ℚ) 1 99 2 3 8) 5).outcome = .returned (some true) := by
  exact accepts (F := ℚ) 1 99 1 2 2 3 5 8 9 rfl (by decide +kernel)

inductive Mutation where
  | response | site

def mutateInstruction (mutation : Mutation) : Instruction → Instruction
  | .instruction descriptor operands results regions site =>
      .instruction
        (match mutation, descriptor with
         | .response, .fieldAdd field => .fieldSubtract field
         | _, _ => descriptor)
        operands results regions
        (match mutation with
         | .response => site
         | .site => if site = SchnorrInteractive.wiring.responseSite then "changed_response" else site)

def mutateDefinition (mutation : Mutation) : Definition → Definition
  | .function f =>
      if f.name = SchnorrInteractiveData.snapshot.entry then
        .function { f with body := match f.body with
          | .block instructions terminator =>
              .block (instructions.map (mutateInstruction mutation)) terminator }
      else .function f
  | .finite f => .finite f
  | .realization f => .realization f
  | .map f => .map f

/-- Synthetic markers intentionally do not reuse the original source digest. -/
def mutatedSnapshot (mutation : Mutation) : Snapshot :=
  { SchnorrInteractiveData.snapshot with
    source := "sha256:" ++ String.ofList (List.replicate 64 '0')
    definitions := SchnorrInteractiveData.snapshot.definitions.map (mutateDefinition mutation) }

def responseProgram : Program :=
  (check (mutatedSnapshot .response)).toOption.get (by decide +kernel)

/-- The original dotted mutation is outside the native identifier profile and
is now refused by independent admission, before handler execution. -/
def malformedSiteSnapshot : Snapshot :=
  { mutatedSnapshot .site with definitions := (mutatedSnapshot .site).definitions.map fun
      | .function function => .function { function with body := match function.body with
          | .block instructions terminal => .block (instructions.map fun
              | .instruction descriptor operands results regions site =>
                  .instruction descriptor operands results regions
                    (if site = "changed_response" then "changed.response" else site)) terminal }
      | definition => definition }

theorem malformed_site_refused : (check malformedSiteSnapshot).isOk = false := by
  decide +kernel

def siteProgram : Program :=
  (check (mutatedSnapshot .site)).toOption.get (by decide +kernel)

theorem response_admitted : check (mutatedSnapshot .response) = .ok responseProgram := rfl
theorem site_admitted : check (mutatedSnapshot .site) = .ok siteProgram := rfl

section Generic
variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def responseProcess (base key : G) (secret : F) (service : Nat) :
    PIR.Proc (participantInterface F G) (Option Bool) :=
  (responseProgram.participant F G 0 (SchnorrInteractive.proverInputs base key secret service)).bind
    fun outputs => .done (outputs.get .here)

def siteProcess (base key : G) (secret : F) (service : Nat) :
    PIR.Proc (participantInterface F G) (Option Bool) :=
  (siteProgram.participant F G 0 (SchnorrInteractive.proverInputs base key secret service)).bind
    fun outputs => .done (outputs.get .here)

/-- Changed arithmetic is observed from another admitted constructor subject. -/
theorem response_equation (base key : G) (secret : F) (service : Nat) :
    responseProcess base key secret service =
      .call (.query SchnorrInteractive.nonceSite scalarDomain (.cons service .nil)) (fun (nonce : F) =>
      .call (.send (ty := .group groupDomain) SchnorrInteractive.wiring.commitmentSite 1 (nonce • base)) (fun _ =>
      .call (.receive (.field scalarDomain) SchnorrInteractive.wiring.deliverySite 1) (fun (challenge : F) =>
      .call (.send (ty := .field scalarDomain) SchnorrInteractive.wiring.responseSite 1 (nonce - challenge * secret))
        (fun _ => .done none)))) := rfl

theorem site_equation (base key : G) (secret : F) (service : Nat) :
    siteProcess base key secret service =
      .call (.query SchnorrInteractive.nonceSite scalarDomain (.cons service .nil)) (fun (nonce : F) =>
      .call (.send (ty := .group groupDomain) SchnorrInteractive.wiring.commitmentSite 1 (nonce • base)) (fun _ =>
      .call (.receive (.field scalarDomain) SchnorrInteractive.wiring.deliverySite 1) (fun (challenge : F) =>
      .call (.send (ty := .field scalarDomain) "changed_response" 1 (nonce + challenge * secret))
        (fun _ => .done none)))) := rfl

set_option smartUnfolding true

theorem response_execution (base key : G) (secret nonce challenge : F) (service : Nat) :
    (responseProcess base key secret service).run
      (replyHandler service (.returned nonce) (.returned challenge)) () =
      (⟨.returned none, (),
        [.query SchnorrInteractive.nonceSite scalarDomain (.cons service .nil),
         .send (ty := .group groupDomain) SchnorrInteractive.wiring.commitmentSite 1 (nonce • base),
         .receive (.field scalarDomain) SchnorrInteractive.wiring.deliverySite 1,
         .send (ty := .field scalarDomain) SchnorrInteractive.wiring.responseSite 1
           (nonce - challenge * secret)]⟩ : Execution F G) := by
  rw [response_equation]
  simp [PIR.Proc.run, PIR.Execution.follow, replyHandler, services, Values.get]
  rfl

theorem response_extracted (base key : G) (secret nonce challenge : F) (service : Nat) :
    extract service ((responseProcess base key secret service).run
      (replyHandler service (.returned nonce) (.returned challenge)) ()) =
        some (nonce • base, nonce - challenge * secret) := by
  rw [response_execution]
  simp [extract, services, Values.get]

/-- The same extraction-to-Strategy constructor as the original source, applied
to the actual admitted response mutation with its own success witness. -/
def responseStrategy (base key : G) (secret nonce : F) (service : Nat) :
    Zkc.Protocols.Schnorr.Common.Strategy F G :=
  strategyOf service (fun challenge => (responseProcess base key secret service).run
    (replyHandler service (.returned nonce) (.returned challenge)) ()) (by
      intro challenge
      rw [response_extracted]
      rfl)

theorem changed_site_refused (base key : G) (secret nonce challenge : F) (service : Nat) :
    ((siteProcess base key secret service).run
      (replyHandler service (.returned nonce) (.returned challenge)) ()).outcome =
        .stopped .refused := by
  rw [site_equation]
  simp [PIR.Proc.run, PIR.Execution.follow, replyHandler, services, Values.get,
    SchnorrInteractive.wiring, ZkcExamples.NativePrograms.Schnorr.wiring]

theorem changed_site_not_extracted (base key : G) (secret nonce challenge : F) (service : Nat) :
    extract service ((siteProcess base key secret service).run
      (replyHandler service (.returned nonce) (.returned challenge)) ()) = none := by
  unfold extract
  rw [changed_site_refused]

/-- Even an otherwise successful log with the source's action order
reversed cannot be silently converted into a causal Strategy. -/
theorem reordered_trace_not_extracted (base key : G) (secret nonce challenge : F) (service : Nat) :
    extract service { execution base key secret nonce challenge service with
      events := (execution base key secret nonce challenge service).events.reverse } = none := by
  rw [execution_eq]
  rfl

theorem extra_action_not_extracted (base key : G) (secret nonce challenge : F)
    (service : Nat) (extra : Action F G) :
    extract service { execution base key secret nonce challenge service with
      events := (execution base key secret nonce challenge service).events ++ [extra] } = none := by
  rw [execution_eq]
  rfl

end Generic

theorem changed_response_observed :
    extract 8 ((responseProcess (F := ℚ) (1 : ℚ) 2 2 8).run
      (replyHandler 8 (.returned 3) (.returned 5)) ()) = some (3, -7) := by
  rw [response_extracted]
  decide +kernel

theorem changed_response_not_original :
    extract 8 ((responseProcess (F := ℚ) (1 : ℚ) 2 2 8).run
      (replyHandler 8 (.returned 3) (.returned 5)) ()) ≠
      extract 8 (execution (F := ℚ) (1 : ℚ) 2 2 3 5 8) := by
  rw [response_extracted, extract_execution]
  decide +kernel

/-- Actual mutated source sends reach the unchanged checked verifier through
honest delivery. Rejection covers the full observation-to-verifier chain. -/
theorem changed_response_rejected :
    (Zkc.Protocols.Schnorr.Common.run (F := ℚ) SchnorrInteractive.verifier
      (1 : ℚ) 2 9 (responseStrategy (F := ℚ) 1 2 2 3 8) 5).outcome ≠
        .returned (some true) := by
  rw [ne_eq, SchnorrInteractive.contract.accepted_iff]
  simp [responseStrategy, strategyOf, response_extracted]
  decide +kernel

theorem wrong_service_refused :
    ((SchnorrInteractive.proverProcess (F := ℚ) (1 : ℚ) 2 2 8).run
      (replyHandler 7 (.returned 3) (.returned 5)) ()).outcome = .stopped .refused := by
  rw [SchnorrInteractive.prover_equation]
  rfl

end ZkcExamples.Structured.SchnorrHonestProver.Controls
