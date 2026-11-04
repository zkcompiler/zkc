module

public import ZkcExamples.Construction.SchnorrAndArtifact
public import Zkc.Source.Structured.ReplyScript
public import Zkc.Semantics.ReturnView

@[expose] public section

/-! Complete executions of the admitted AND root. The two components consume
one challenge. Paired extraction keeps both commitments fixed and requires
distinct challenges; a single acceptance supplies no witness. -/

set_option autoImplicit false
set_option smartUnfolding false

namespace ZkcExamples.Construction.SchnorrAndExecution
open Zkc.Source Zkc.Source.Structured SchnorrAndProof

abbrev Action (F G : Type) := (participantInterface F G).Op

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Full actual verifier, before selecting its singleton output. -/
def execute {S E : Type} (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (handler : PIR.Handler (participantInterface F G) S E) (state : S) :=
  (program.participant F G 1
    (verifierInputs firstBase firstKey secondBase secondKey service)).run handler state

/-- The same return transport used by the single Schnorr root works for every
handler, state, event carrier, arbitrary reply and stopped prefix. -/
theorem execute_eq {S E : Type} (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (handler : PIR.Handler (participantInterface F G) S E) (state : S) :
    execute firstBase firstKey secondBase secondKey service handler state =
      ((process firstBase firstKey secondBase secondKey service).run handler state).follow
        (fun decision current ↦ ⟨.returned (.cons decision .nil), current, []⟩) := by
  exact PIR.Process.run_of_return_view
    (program.participant F G 1 (verifierInputs firstBase firstKey secondBase secondKey service))
    (fun outputs ↦ outputs.get .here) (fun decision ↦ .cons decision .nil)
    Values.singleton_get
    (process firstBase firstKey secondBase secondKey service) rfl handler state

theorem returned_iff {S E : Type} (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (handler : PIR.Handler (participantInterface F G) S E) (state : S) (decision : Option Bool) :
    (execute firstBase firstKey secondBase secondKey service handler state).outcome =
        .returned (.cons decision .nil) ↔
      ((process firstBase firstKey secondBase secondKey service).run handler state).outcome =
        .returned decision := by
  rw [execute_eq]
  exact PIR.Execution.follow_return_returned_iff _ _
    (fun _ _ same ↦ congrArg (fun values ↦ values.get .here) same) decision

theorem events_eq {S E : Type} (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (handler : PIR.Handler (participantInterface F G) S E) (state : S) :
    (execute firstBase firstKey secondBase secondKey service handler state).events =
      ((process firstBase firstKey secondBase secondKey service).run handler state).events := by
  rw [execute_eq]
  exact PIR.Execution.follow_return_events _ _

/-- A fixed commitment pair and challenge-indexed responses form the causal
replay input. The site script acknowledges sends and refuses unmatched reads. -/
def verifierReplies (commitments : G × G) (responses : F × F) (challenge : F) :
    ReplyScript F G where
  receive
    | .group _, site =>
      if site = wiring.firstCommitmentSite then some commitments.1
      else if site = wiring.secondCommitmentSite then some commitments.2 else none
    | .field _, site =>
      if site = wiring.firstResponseSite then some responses.1
      else if site = wiring.secondResponseSite then some responses.2 else none
    | _, _ => none
  draw site := if site = wiring.challengeSite then some challenge else none

/-- The actual tuple, state and six ordered requests, including the single
shared challenge query and its delivery before either response. -/
theorem verifier_execution (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (responses : F × F) (challenge : F) :
    execute firstBase firstKey secondBase secondKey service
        (verifierReplies commitments responses challenge).handler () =
      ⟨.returned (.cons (some
        (decide (responses.1 • firstBase = commitments.1 + challenge • firstKey) &&
         decide (responses.2 • secondBase = commitments.2 + challenge • secondKey))) .nil), (),
        [.receive (.group groupDomain) wiring.firstCommitmentSite 0,
         .receive (.group groupDomain) wiring.secondCommitmentSite 0,
         .query wiring.challengeSite scalarDomain (.cons service .nil),
         .send (ty := .field scalarDomain) wiring.deliverySite 0 challenge,
         .receive (.field scalarDomain) wiring.firstResponseSite 0,
         .receive (.field scalarDomain) wiring.secondResponseSite 0]⟩ := by
  rw [execute_eq, process_equation]
  rfl

theorem accepted_iff (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (responses : F × F) (challenge : F) :
    (execute firstBase firstKey secondBase secondKey service
      (verifierReplies commitments responses challenge).handler ()).outcome =
        .returned (.cons (some true) .nil) ↔
      responses.1 • firstBase = commitments.1 + challenge • firstKey ∧
      responses.2 • secondBase = commitments.2 + challenge • secondKey := by
  rw [returned_iff, process_equation]
  change (PIR.Outcome.returned (some
    (decide (responses.1 • firstBase = commitments.1 + challenge • firstKey) &&
     decide (responses.2 • secondBase = commitments.2 + challenge • secondKey))) =
      PIR.Outcome.returned (some true)) ↔ _
  simp

/-- Recovery is fixed componentwise. Both acceptances replay the same pair
of commitments, and the challenge difference must be nonzero. -/
theorem fixed_recovery (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (responses : F → F × F) (first second : F)
    (distinct : first ≠ second)
    (acceptFirst : (execute firstBase firstKey secondBase secondKey service
      (verifierReplies commitments (responses first) first).handler ()).outcome =
        .returned (.cons (some true) .nil))
    (acceptSecond : (execute firstBase firstKey secondBase secondKey service
      (verifierReplies commitments (responses second) second).handler ()).outcome =
        .returned (.cons (some true) .nil)) :
    firstKey = (((responses first).1 - (responses second).1) / (first - second)) • firstBase ∧
    secondKey = (((responses first).2 - (responses second).2) / (first - second)) • secondBase := by
  have firstAccepted := (accepted_iff ..).mp acceptFirst
  have secondAccepted := (accepted_iff ..).mp acceptSecond
  exact ⟨(Zkc.Protocols.Schnorr.extract_public_key _ _ _ _ _ _ _ distinct
    firstAccepted.1 secondAccepted.1).symm,
    (Zkc.Protocols.Schnorr.extract_public_key _ _ _ _ _ _ _ distinct
      firstAccepted.2 secondAccepted.2).symm⟩

/-- The producer owns both witnesses and its nonce service. The challenge
service belongs to the verifier and remains absent. -/
def proverInputs (firstBase firstKey secondBase secondKey : G) (secrets : F × F)
    (service : Nat) : Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some firstKey) (.cons (some secondBase)
    (.cons (some secondKey) (.cons (some secrets.1) (.cons (some secrets.2)
      (.cons (some service) (.cons none .nil)))))))

def proverProcess (firstBase firstKey secondBase secondKey : G) (secrets : F × F)
    (service : Nat) : PIR.Process (participantInterface F G) (Option Bool) :=
  (program.participant F G 0
    (proverInputs firstBase firstKey secondBase secondKey secrets service)).bind
      (fun outputs ↦ .done (outputs.get .here))

/-- Separate nonce binders retain the two draws before either commitment and
the one shared receive. Distributional independence is a separate sampling law. -/
theorem prover_equation (firstBase firstKey secondBase secondKey : G) (secrets : F × F)
    (service : Nat) :
    proverProcess firstBase firstKey secondBase secondKey secrets service =
      .call (.query "s0" scalarDomain (.cons service .nil)) (fun (firstNonce : F) ↦
      .call (.query "s2" scalarDomain (.cons service .nil)) (fun (secondNonce : F) ↦
      .call (.send (ty := .group groupDomain) wiring.firstCommitmentSite 1
        (firstNonce • firstBase)) (fun _ ↦
      .call (.send (ty := .group groupDomain) wiring.secondCommitmentSite 1
        (secondNonce • secondBase)) (fun _ ↦
      .call (.receive (.field scalarDomain) wiring.deliverySite 1) (fun (challenge : F) ↦
      .call (.send (ty := .field scalarDomain) wiring.firstResponseSite 1
        (firstNonce + challenge * secrets.1)) (fun _ ↦
      .call (.send (ty := .field scalarDomain) wiring.secondResponseSite 1
        (secondNonce + challenge * secrets.2)) (fun _ ↦ .done none))))))) := by
  rfl

theorem prover_full_execution {S E : Type} (firstBase firstKey secondBase secondKey : G)
    (secrets : F × F) (service : Nat) (handler : PIR.Handler (participantInterface F G) S E)
    (state : S) :
    (program.participant F G 0
      (proverInputs firstBase firstKey secondBase secondKey secrets service)).run handler state =
      ((proverProcess firstBase firstKey secondBase secondKey secrets service).run handler state).follow
        (fun decision current ↦ ⟨.returned (.cons decision .nil), current, []⟩) := by
  exact PIR.Process.run_of_return_view
    (program.participant F G 0
      (proverInputs firstBase firstKey secondBase secondKey secrets service))
    (fun outputs ↦ outputs.get .here) (fun decision ↦ .cons decision .nil)
    Values.singleton_get
    (proverProcess firstBase firstKey secondBase secondKey secrets service) rfl handler state

/-- The two nonce draws are selected by site; neither depends on the later
challenge. Unmatched reads stop rather than supplying default values. -/
def proverReplies (nonces : F × F) (challenge : F) : ReplyScript F G where
  receive
    | .field _, site => if site = wiring.deliverySite then some challenge else none
    | _, _ => none
  draw site := if site = "s0" then some nonces.1 else if site = "s2" then some nonces.2 else none

theorem prover_execution (firstBase firstKey secondBase secondKey : G)
    (secrets nonces : F × F) (service : Nat) (challenge : F) :
    (program.participant F G 0
      (proverInputs firstBase firstKey secondBase secondKey secrets service)).run
        (proverReplies nonces challenge).handler () =
      ⟨.returned (.cons none .nil), (),
        [.query "s0" scalarDomain (.cons service .nil),
         .query "s2" scalarDomain (.cons service .nil),
         .send (ty := .group groupDomain) wiring.firstCommitmentSite 1 (nonces.1 • firstBase),
         .send (ty := .group groupDomain) wiring.secondCommitmentSite 1 (nonces.2 • secondBase),
         .receive (.field scalarDomain) wiring.deliverySite 1,
         .send (ty := .field scalarDomain) wiring.firstResponseSite 1
           (nonces.1 + challenge * secrets.1),
         .send (ty := .field scalarDomain) wiring.secondResponseSite 1
           (nonces.2 + challenge * secrets.2)]⟩ := by
  rw [prover_full_execution, prover_equation]
  rfl

/-- The reached prefix includes both commitment sends before the challenge
reply. It is equal for independently supplied challenges. -/
theorem prover_prefix_independent (firstBase firstKey secondBase secondKey : G)
    (secrets nonces : F × F) (service : Nat) (first second : F) :
    ((program.participant F G 0
      (proverInputs firstBase firstKey secondBase secondKey secrets service)).run
        (proverReplies nonces first).handler ()).events.take 5 =
    ((program.participant F G 0
      (proverInputs firstBase firstKey secondBase secondKey secrets service)).run
        (proverReplies nonces second).handler ()).events.take 5 := by
  rw [prover_execution, prover_execution]
  rfl

/-- Independent role copies need the stated base agreement and witness
relations. No one-run knowledge conclusion is drawn from completeness. -/
theorem honest_accepts (firstBase secondBase : G) (secrets nonces : F × F)
    (service : Nat) (challenge : F) :
    (execute firstBase (secrets.1 • firstBase) secondBase (secrets.2 • secondBase) service
      (verifierReplies (nonces.1 • firstBase, nonces.2 • secondBase)
        (nonces.1 + challenge * secrets.1, nonces.2 + challenge * secrets.2) challenge).handler
      ()).outcome = .returned (.cons (some true) .nil) := by
  apply (accepted_iff ..).mpr
  exact ⟨Zkc.Protocols.Schnorr.response_equation nonces.1 challenge secrets.1 firstBase,
    Zkc.Protocols.Schnorr.response_equation nonces.2 challenge secrets.2 secondBase⟩

end ZkcExamples.Construction.SchnorrAndExecution
