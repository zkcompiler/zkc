module

public import ZkcExamples.Structured.SchnorrInteractive

@[expose] public section

/-! Observation boundary for the checked original-stage prover.
Messages are extracted from `Proc.run`, never supplied by the algebraic formula.
The fixed replies describe one successful honest profile, not a provider law.
-/
namespace ZkcExamples.Structured.SchnorrHonestProver
open Zkc.Source Zkc.Source.Structured

set_option autoImplicit false

abbrev Action (F G : Type) := (participantInterface F G).Op
abbrev Execution (F G : Type) := PIR.Execution Unit (Action F G) (Option Bool)

/-- Deterministically log each actual request. Only the named nonce query,
challenge receive and two sends are allowed. Sampling, if any, happens outside
the run; the nonce arm does not inspect the challenge. Stopped replies preserve
the reached request prefix. Sends at the expected sites always succeed. -/
def replyHandler {F G : Type} (service : Nat) (nonce challenge : PIR.Outcome F) :
    PIR.Handler (participantInterface F G) Unit (Action F G)
  | action@(.query site domain args), state =>
      let field : String := domain
      let handle : Nat := args.get .here
      if site = SchnorrInteractive.nonceSite ∧ field = scalarDomain ∧ handle = service then
        ⟨nonce, state, [action]⟩
      else ⟨.stopped .refused, state, [action]⟩
  | action@(.receive (.field domain) site sender), state =>
      if domain = scalarDomain ∧ site = SchnorrInteractive.wiring.deliverySite ∧ sender = 1 then
        ⟨challenge, state, [action]⟩
      else ⟨.stopped .refused, state, [action]⟩
  | action@(.send (ty := .group domain) site receiver _), state =>
      if domain = groupDomain ∧ site = SchnorrInteractive.wiring.commitmentSite ∧ receiver = 1 then
        ⟨.returned (), state, [action]⟩
      else ⟨.stopped .refused, state, [action]⟩
  | action@(.send (ty := .field domain) site receiver _), state =>
      if domain = scalarDomain ∧ site = SchnorrInteractive.wiring.responseSite ∧ receiver = 1 then
        ⟨.returned (), state, [action]⟩
      else ⟨.stopped .refused, state, [action]⟩
  | action, state => ⟨.stopped .refused, state, [action]⟩

/-- Decode exactly the successful four-action profile, retaining domain, site,
endpoint, handle and order checks. No prefix, extra action or stop is totalized. -/
def extract {F G : Type} (service : Nat) (execution : Execution F G) : Option (G × F) :=
  match execution.outcome, execution.events with
  | .returned none,
      [.query querySite queryDomain args,
       .send (ty := .group commitmentDomain) commitmentSite commitmentPeer commitment,
       .receive (.field challengeDomain) challengeSite challengePeer,
       .send (ty := .field responseDomain) responseSite responsePeer response] =>
      let field : String := queryDomain
      let handle : Nat := args.get .here
      if querySite = SchnorrInteractive.nonceSite ∧ field = scalarDomain ∧ handle = service ∧
          commitmentDomain = groupDomain ∧ commitmentSite = SchnorrInteractive.wiring.commitmentSite ∧
          commitmentPeer = 1 ∧ challengeDomain = scalarDomain ∧
          challengeSite = SchnorrInteractive.wiring.deliverySite ∧ challengePeer = 1 ∧
          responseDomain = scalarDomain ∧ responseSite = SchnorrInteractive.wiring.responseSite ∧
          responsePeer = 1 then some (commitment, response) else none
  | _, _ => none

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def execution (base key : G) (secret nonce challenge : F) (service : Nat) : Execution F G :=
  (SchnorrInteractive.proverProcess base key secret service).run
    (replyHandler service (.returned nonce) (.returned challenge)) ()

/-- This equality is derived from the imported source equation. It records the
actual sent values and all four ordered external sites. Internal marks have
already been erased by `Program.participant`. -/
theorem execution_eq (base key : G) (secret nonce challenge : F) (service : Nat) :
    execution base key secret nonce challenge service =
      ⟨.returned none, (),
        [.query SchnorrInteractive.nonceSite scalarDomain (.cons service .nil),
         .send (ty := .group groupDomain) SchnorrInteractive.wiring.commitmentSite 1 (nonce • base),
         .receive (.field scalarDomain) SchnorrInteractive.wiring.deliverySite 1,
         .send (ty := .field scalarDomain) SchnorrInteractive.wiring.responseSite 1
           (nonce + challenge * secret)]⟩ := by
  rw [execution, SchnorrInteractive.prover_equation]
  simp [PIR.Proc.run, PIR.Execution.follow, replyHandler, services, Values.get]
  rfl

theorem extract_execution (base key : G) (secret nonce challenge : F) (service : Nat) :
    extract service (execution base key secret nonce challenge service) =
      some (nonce • base, nonce + challenge * secret) := by
  rw [execution_eq]
  simp [extract, services, Values.get]

/-- Total only because this particular source has a proved successful profile.
The value being unwrapped is the observation, not its algebraic specification. -/
def messages (base key : G) (secret nonce challenge : F) (service : Nat) : G × F :=
  (extract service (execution base key secret nonce challenge service)).get (by
    rw [extract_execution]; rfl)

theorem messages_eq (base key : G) (secret nonce challenge : F) (service : Nat) :
    messages base key secret nonce challenge service =
      (nonce • base, nonce + challenge * secret) := by
  simp [messages, extract_execution]

/-- The commitment observed before receive cannot depend on its reply. -/
theorem commitment_independent (base key : G) (secret nonce first second : F) (service : Nat) :
    (messages base key secret nonce first service).1 =
      (messages base key secret nonce second service).1 := by
  simp only [messages_eq]

/-- The complete request prefix through the challenge receive is independent
of that receive's reply; in particular the commitment send occurs before it. -/
theorem prefix_independent (base key : G) (secret nonce first second : F) (service : Nat) :
    (execution base key secret nonce first service).events.take 3 =
      (execution base key secret nonce second service).events.take 3 := by
  rw [execution_eq, execution_eq]
  rfl

/-- A zero challenge selects one representative commitment observation.
`execution_eq` and `prefix_independent` put that send before the challenge reply
for every challenge; `extract_execution` proves every such run completes under
this successful reply/send profile. Thus complete-trace extraction needs no
future-dependent choice or default. This is specific to the checked source,
not a causal adapter for arbitrary processes or handlers.
`strategy_supplied` proves that every independently supplied challenge sees it. -/
def strategy (base key : G) (secret nonce : F) (service : Nat) : Zkc.Protocols.Schnorr.Common.Strategy F G where
  commitment := (messages base key secret nonce 0 service).1
  response challenge := (messages base key secret nonce challenge service).2

theorem strategy_supplied (base key : G) (secret nonce challenge : F) (service : Nat) :
    extract service (execution base key secret nonce challenge service) =
      some ((strategy base key secret nonce service).commitment,
        (strategy base key secret nonce service).response challenge) := by
  simp [strategy, messages_eq, extract_execution]

theorem strategy_eq (base key : G) (secret nonce : F) (service : Nat) :
    strategy base key secret nonce service =
      ⟨nonce • base, fun challenge => nonce + challenge * secret⟩ := by
  simp [strategy, messages_eq]

/-- Copies are independent arguments. Equal bases/keys and the witness relation
are explicit sufficient conditions, and the existing handler delivers exactly
the extracted commitment/response and the fixed challenge. That delivery handler
selects replies by type; matching source sites are certified separately by the
process equations and extraction. This is not a joint routing theorem.
These conditions are
not necessary: this source prover ignores its local key, and some degenerate
inputs also accept. No mechanism enforces equality of participant copies. -/
theorem accepts (proverBase proverKey verifierBase verifierKey : G)
    (secret nonce challenge : F) (nonceService challengeService : Nat)
    (sameBase : proverBase = verifierBase) (sameKey : proverKey = verifierKey)
    (keyRelation : proverKey = secret • proverBase) :
    (Zkc.Protocols.Schnorr.Common.run SchnorrInteractive.verifier verifierBase verifierKey challengeService
      (strategy proverBase proverKey secret nonce nonceService) challenge).outcome =
        .returned (some true) := by
  subst verifierBase
  subst verifierKey
  rw [strategy_eq, keyRelation]
  exact SchnorrInteractive.contract.perfect_completeness proverBase secret nonce challenge challengeService

/-- A stopped service query retains its request and never sends a commitment. -/
theorem nonce_stopped (base key : G) (secret challenge : F) (service : Nat) (why : PIR.Stop) :
    (SchnorrInteractive.proverProcess base key secret service).run
        (replyHandler service (.stopped why) (.returned challenge)) () =
      ⟨.stopped why, (), [.query SchnorrInteractive.nonceSite scalarDomain (.cons service .nil)]⟩ := by
  rw [SchnorrInteractive.prover_equation]
  simp [PIR.Proc.run, PIR.Execution.follow, replyHandler, services, Values.get]

/-- A stopped receive retains the commitment and receive request, with no response. -/
theorem challenge_stopped (base key : G) (secret nonce : F) (service : Nat) (why : PIR.Stop) :
    (SchnorrInteractive.proverProcess base key secret service).run
        (replyHandler service (.returned nonce) (.stopped why)) () =
      ⟨.stopped why, (),
        [.query SchnorrInteractive.nonceSite scalarDomain (.cons service .nil),
         .send (ty := .group groupDomain) SchnorrInteractive.wiring.commitmentSite 1 (nonce • base),
         .receive (.field scalarDomain) SchnorrInteractive.wiring.deliverySite 1]⟩ := by
  rw [SchnorrInteractive.prover_equation]
  simp [PIR.Proc.run, PIR.Execution.follow, replyHandler, services, Values.get]
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem extract_stopped (service : Nat) (why : PIR.Stop) (events : List (Action F G)) :
    extract service (⟨.stopped why, (), events⟩ : Execution F G) = none := rfl

end ZkcExamples.Structured.SchnorrHonestProver
