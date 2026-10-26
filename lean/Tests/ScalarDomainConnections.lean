import ZkcExamples.Construction.SchnorrDomainConnection
import ZkcExamples.Construction.SchnorrAndDomainConnection
import ZkcExamples.Construction.ChaumPedersenDomainConnection
import ZkcExamples.Construction.OkamotoDomainConnection
import ZkcExamples.Construction.GuessDomainConnection

/-! Focused controls of the new actual-artifact connections. Universal theorems
cover all replies; these controls pin malformed heads, stopped prefixes, unread
suffixes and the exact oracle history seen through the legacy boundary. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace Tests.ScalarDomainConnections
open Zkc Zkc.Source Zkc.Construction
open ZkcExamples.Construction
open Zkc.Construction.Uniform.SourceProcess
open Zkc.Construction.Uniform.DomainAdapter
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

-- Guess: an empty proof refuses without an oracle call or consumption.
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (offset : F) (initial : History F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (Structured.ringModel F G) GuessDomainConnection.program GuessDomainConnection.context
        GuessDomainConnection.artifact (GuessDomainConnection.inputs offset)) ([])
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        pure (.stopped .refused, []) := by
  rw [GuessDomainConnection.domain_transform challenge offset 37, GuessDomainConnection.source_equation]
  rfl

-- Guess: a malformed first head refuses without an oracle call or consumption.
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (offset : F) (initial : History F G) (unread : Proof F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (Structured.ringModel F G) GuessDomainConnection.program GuessDomainConnection.context
        GuessDomainConnection.artifact (GuessDomainConnection.inputs offset)) ((.boolean true) :: unread)
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        pure (.stopped .refused, (.boolean true) :: unread) := by
  rw [GuessDomainConnection.domain_transform challenge offset 37, GuessDomainConnection.source_equation]
  rfl

-- Schnorr: an empty proof refuses without an oracle call or consumption.
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (base point : G) (initial : History F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (Structured.ringModel F G) SchnorrDomainConnection.program SchnorrDomainConnection.context
        SchnorrDomainConnection.artifact (SchnorrDomainConnection.inputs base point)) ([])
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        pure (.stopped .refused, []) := by
  rw [SchnorrDomainConnection.domain_transform challenge base point 37, SchnorrDomainConnection.source_equation]
  rfl

-- Schnorr: a malformed first head refuses without an oracle call or consumption.
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (base point : G) (initial : History F G) (unread : Proof F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (Structured.ringModel F G) SchnorrDomainConnection.program SchnorrDomainConnection.context
        SchnorrDomainConnection.artifact (SchnorrDomainConnection.inputs base point)) ((.boolean true) :: unread)
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        pure (.stopped .refused, (.boolean true) :: unread) := by
  rw [SchnorrDomainConnection.domain_transform challenge base point 37, SchnorrDomainConnection.source_equation]
  rfl

-- SchnorrAnd: an empty proof refuses without an oracle call or consumption.
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase firstPoint secondBase secondPoint : G) (initial : History F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (Structured.ringModel F G) SchnorrAndDomainConnection.program SchnorrAndDomainConnection.context
        SchnorrAndDomainConnection.artifact (SchnorrAndDomainConnection.inputs firstBase firstPoint secondBase secondPoint)) ([])
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        pure (.stopped .refused, []) := by
  rw [SchnorrAndDomainConnection.domain_transform challenge firstBase firstPoint secondBase secondPoint 37, SchnorrAndDomainConnection.source_equation]
  rfl

-- SchnorrAnd: a malformed first head refuses without an oracle call or consumption.
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase firstPoint secondBase secondPoint : G) (initial : History F G) (unread : Proof F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (Structured.ringModel F G) SchnorrAndDomainConnection.program SchnorrAndDomainConnection.context
        SchnorrAndDomainConnection.artifact (SchnorrAndDomainConnection.inputs firstBase firstPoint secondBase secondPoint)) ((.boolean true) :: unread)
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        pure (.stopped .refused, (.boolean true) :: unread) := by
  rw [SchnorrAndDomainConnection.domain_transform challenge firstBase firstPoint secondBase secondPoint 37, SchnorrAndDomainConnection.source_equation]
  rfl

-- ChaumPedersen: an empty proof refuses without an oracle call or consumption.
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase firstPoint secondBase secondPoint : G) (initial : History F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (Structured.ringModel F G) ChaumPedersenDomainConnection.program ChaumPedersenDomainConnection.context
        ChaumPedersenDomainConnection.artifact (ChaumPedersenDomainConnection.inputs firstBase firstPoint secondBase secondPoint)) ([])
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        pure (.stopped .refused, []) := by
  rw [ChaumPedersenDomainConnection.domain_transform challenge firstBase firstPoint secondBase secondPoint 37, ChaumPedersenDomainConnection.source_equation]
  rfl

-- ChaumPedersen: a malformed first head refuses without an oracle call or consumption.
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase firstPoint secondBase secondPoint : G) (initial : History F G) (unread : Proof F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (Structured.ringModel F G) ChaumPedersenDomainConnection.program ChaumPedersenDomainConnection.context
        ChaumPedersenDomainConnection.artifact (ChaumPedersenDomainConnection.inputs firstBase firstPoint secondBase secondPoint)) ((.boolean true) :: unread)
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        pure (.stopped .refused, (.boolean true) :: unread) := by
  rw [ChaumPedersenDomainConnection.domain_transform challenge firstBase firstPoint secondBase secondPoint 37, ChaumPedersenDomainConnection.source_equation]
  rfl

-- Okamoto: an empty proof refuses without an oracle call or consumption.
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase secondBase point : G) (initial : History F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (Structured.ringModel F G) OkamotoDomainConnection.program OkamotoDomainConnection.context
        OkamotoDomainConnection.artifact (OkamotoDomainConnection.inputs firstBase secondBase point)) ([])
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        pure (.stopped .refused, []) := by
  rw [OkamotoDomainConnection.domain_transform challenge firstBase secondBase point 37, OkamotoDomainConnection.source_equation]
  rfl

-- Okamoto: a malformed first head refuses without an oracle call or consumption.
example {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (firstBase secondBase point : G) (initial : History F G) (unread : Proof F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (Structured.ringModel F G) OkamotoDomainConnection.program OkamotoDomainConnection.context
        OkamotoDomainConnection.artifact (OkamotoDomainConnection.inputs firstBase secondBase point)) ((.boolean true) :: unread)
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        pure (.stopped .refused, (.boolean true) :: unread) := by
  rw [OkamotoDomainConnection.domain_transform challenge firstBase secondBase point 37, OkamotoDomainConnection.source_equation]
  rfl

-- A stop is preserved before a receive, and the unread malformed head stays intact.
example (initial : History F G) (proof : Proof F G) :
    runK (m := Id) legacyOrigin initial (fun _ => (0 : F))
      (sourceView SchnorrDomainConnection.context
        (.halt .exhausted : PIR.Process (Actions F G) Bool) []) proof
      (fun result unread => (.returned result.1, unread)) = (.stopped .exhausted, proof) := rfl

-- A wrong nominal response after a valid Schnorr commitment remains unread.
example (base point commitment : G) (answer response : F) (initial : History F G) :
    runK (m := Id) legacyOrigin initial (fun _ => answer)
      (Domain.participant (Structured.ringModel F G) SchnorrDomainConnection.program
        SchnorrDomainConnection.context SchnorrDomainConnection.artifact
        (SchnorrDomainConnection.inputs base point))
      [.group "bls12-381.g1" commitment, .field "other" response]
      (fun result unread => pure (.returned (acceptance result.values), unread)) =
        (.stopped .refused, [.field "other" response]) := by
  rw [SchnorrDomainConnection.domain_transform (F := F) (G := G) (m := Id) (fun _ => answer) base point 37,
    SchnorrDomainConnection.source_equation]
  rfl

-- Guess's query history is observed by an effectful oracle. It ends with its
-- static challenge occurrence, following the guess and the opaque initial prefix.
example (offset guess answer : F) (initial : History F G) (unread : Proof F G) :
    (runK legacyOrigin initial
      (fun history => (modify (· ++ [history]) : StateM (List (History F G)) Unit) *> pure answer)
      (Domain.participant (Structured.ringModel F G) GuessDomainConnection.program
        GuessDomainConnection.context GuessDomainConnection.artifact (GuessDomainConnection.inputs offset))
      (.field "bls12-381.fr" guess :: unread)
      (fun result rest => pure (.returned (acceptance result.values), rest))).run [] =
    ((.returned (some (decide (guess + offset = answer))), unread),
      [initial ++ [.message (GuessDomainConnection.context.message GuessProof.guessSite 0 1)
        (.field "bls12-381.fr" guess),
        .challenge (GuessDomainConnection.context.query GuessProof.challengeSite (.draw "bls12-381.fr"))]]) := by
  rw [GuessDomainConnection.domain_transform _ offset 37, GuessDomainConnection.source_equation]
  simp only [GuessProof.experiment, transform_eq_receive, Payload.value, ite_true,
    transform_eq_query, transform_eq_send, Payload.ofValue, transform_eq_done]
  change ((PIR.Outcome.returned (some (decide (guess + offset = answer))), unread),
    [(initial ++ [.message (GuessDomainConnection.context.message GuessProof.guessSite 0 1)
      (.field "bls12-381.fr" guess)]) ++
      [.challenge (GuessDomainConnection.context.query GuessProof.challengeSite (.draw "bls12-381.fr"))]]) = _
  simp only [List.append_assoc, List.cons_append, List.nil_append]

-- Delivery precedes the response in the complete returned transcript suffix.
-- The source fold is not allowed to discard this observation after the oracle call.
example (base point commitment : G) (answer response : F) :
    (run (m := Id) legacyOrigin [] (fun _ => answer)
      (sourceView SchnorrDomainConnection.context
        (SchnorrDomainConnection.sourceDecision base point 37) [])
      [.group "bls12-381.g1" commitment, .field "bls12-381.fr" response]) =
    (.returned (decide (response • base = commitment + answer • point),
      [.message (SchnorrDomainConnection.context.message SchnorrProof.wiring.commitmentSite 0 1)
        (.group "bls12-381.g1" commitment),
       .challenge (SchnorrDomainConnection.context.query SchnorrProof.wiring.challengeSite (.draw "bls12-381.fr")),
       .message (SchnorrDomainConnection.context.message SchnorrProof.wiring.deliverySite 1 0)
        (.field "bls12-381.fr" answer),
       .message (SchnorrDomainConnection.context.message SchnorrProof.wiring.responseSite 0 1)
        (.field "bls12-381.fr" response)]), []) := by
  simp only [SchnorrDomainConnection.sourceDecision, SchnorrDomainConnection.source_equation]
  kernel_rfl

end Tests.ScalarDomainConnections
