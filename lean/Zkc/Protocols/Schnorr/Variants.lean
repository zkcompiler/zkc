module

public import Zkc.Protocols.Schnorr.Common

@[expose] public section

/-! Reusable common-source verifiers of three Schnorr-style proofs of knowledge.

Each verifier receives its commitments, asks one challenge of the challenge
service, delivers it to the prover, receives its responses and decides the
protocol's equations:

- `equality` (Chaum–Pedersen): two commitments and one response, accepted when
  the response opens each commitment at its base and key;
- `conjunction` (two Schnorr proofs under one challenge): two commitments and two
  responses, accepted when each response opens its commitment;
- `representation` (Okamoto): one commitment and two responses, accepted when
  the responses open the commitment at the two bases and the point.

The wiring names actual effect sites, the prover role and the domains, as for
the Schnorr verifier (`Zkc.Protocols.Schnorr.Common.experiment`). A compiled
Entry's original validator is one of these verifiers by computation; that
equation is the Entry's model, not an assumption of security.
-/
set_option autoImplicit false

namespace Zkc.Protocols.Schnorr.Variants
open Zkc.Source Zkc.Source.Common
open Zkc.Protocols.Schnorr.Common (actions)

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The sites of a verifier with two commitments and one response. -/
structure EqualityWiring where
  prover : Nat
  groupDomain : String
  fieldDomain : String
  firstCommitmentSite : String
  secondCommitmentSite : String
  challengeSite : String
  deliverySite : String
  responseSite : String

/-- The Chaum–Pedersen verifier: one response opens both commitments. -/
def equality (wiring : EqualityWiring) (firstBase firstKey secondBase secondKey : G) (service : Nat) :
    PIR.Proc (actions (F := F) (G := G)) (Option Bool) :=
  .call (.receive (.group wiring.groupDomain) wiring.firstCommitmentSite wiring.prover) fun firstCommitment =>
  .call (.receive (.group wiring.groupDomain) wiring.secondCommitmentSite wiring.prover) fun secondCommitment =>
  .call (.query wiring.challengeSite wiring.fieldDomain (.cons service .nil)) fun challenge =>
  .call (.send (ty := .field wiring.fieldDomain) wiring.deliverySite wiring.prover challenge) fun _ =>
  .call (.receive (.field wiring.fieldDomain) wiring.responseSite wiring.prover) fun response =>
  .done (some (decide (response • firstBase = firstCommitment + challenge • firstKey) &&
    decide (response • secondBase = secondCommitment + challenge • secondKey)))

/-- The sites of a verifier with two commitments and two responses. -/
structure ConjunctionWiring where
  prover : Nat
  groupDomain : String
  fieldDomain : String
  firstCommitmentSite : String
  secondCommitmentSite : String
  challengeSite : String
  deliverySite : String
  firstResponseSite : String
  secondResponseSite : String

/-- Two Schnorr verifiers under one challenge: each response opens its
commitment. -/
def conjunction (wiring : ConjunctionWiring) (firstBase firstKey secondBase secondKey : G) (service : Nat) :
    PIR.Proc (actions (F := F) (G := G)) (Option Bool) :=
  .call (.receive (.group wiring.groupDomain) wiring.firstCommitmentSite wiring.prover) fun firstCommitment =>
  .call (.receive (.group wiring.groupDomain) wiring.secondCommitmentSite wiring.prover) fun secondCommitment =>
  .call (.query wiring.challengeSite wiring.fieldDomain (.cons service .nil)) fun challenge =>
  .call (.send (ty := .field wiring.fieldDomain) wiring.deliverySite wiring.prover challenge) fun _ =>
  .call (.receive (.field wiring.fieldDomain) wiring.firstResponseSite wiring.prover) fun firstResponse =>
  .call (.receive (.field wiring.fieldDomain) wiring.secondResponseSite wiring.prover) fun secondResponse =>
  .done (some (decide (firstResponse • firstBase = firstCommitment + challenge • firstKey) &&
    decide (secondResponse • secondBase = secondCommitment + challenge • secondKey)))

/-- The sites of a verifier with one commitment and two responses. -/
structure RepresentationWiring where
  prover : Nat
  groupDomain : String
  fieldDomain : String
  commitmentSite : String
  challengeSite : String
  deliverySite : String
  firstResponseSite : String
  secondResponseSite : String

/-- Okamoto's verifier: the two responses open the commitment at the two bases
and the point. -/
def representation (wiring : RepresentationWiring) (firstBase secondBase point : G) (service : Nat) :
    PIR.Proc (actions (F := F) (G := G)) (Option Bool) :=
  .call (.receive (.group wiring.groupDomain) wiring.commitmentSite wiring.prover) fun commitment =>
  .call (.query wiring.challengeSite wiring.fieldDomain (.cons service .nil)) fun challenge =>
  .call (.send (ty := .field wiring.fieldDomain) wiring.deliverySite wiring.prover challenge) fun _ =>
  .call (.receive (.field wiring.fieldDomain) wiring.firstResponseSite wiring.prover) fun firstResponse =>
  .call (.receive (.field wiring.fieldDomain) wiring.secondResponseSite wiring.prover) fun secondResponse =>
  .done (some (decide (firstResponse • firstBase + secondResponse • secondBase = commitment + challenge • point)))

end Zkc.Protocols.Schnorr.Variants
