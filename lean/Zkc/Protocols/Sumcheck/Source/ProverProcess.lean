module

public import Zkc.Protocols.Sumcheck.Source.VerifierProcess
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

/-! The prover's plain round process, shared by the complete-source prover
proofs and their consumers. The prover sends the two ordered half sums of its
current table, receives one challenge from the verifier and folds its table
at that challenge. Replies are unrestricted: the received challenge is any
interface-typed value. Literal source association is proved separately in
`SumcheckProverLaws`. -/
namespace ZkcExamples.Structured.SumcheckProverLaws
open Zkc.Source Zkc.Source.Structured
open SumcheckVerifierLaws (lowSite highSite deliverySite)
open Zkc.Polynomial.Multilinear (restrictValues)

variable {F G : Type} [CommRing F]

/-- The prover's four carried slots: table entries, remaining dimension, column
width and the point of received challenges. -/
abbrev ProverState (F : Type) := List F × Nat × Nat × List F

/-- Exact expansion target: LOW, HIGH, the delivered challenge, then the
actual fold and append. -/
def roundPresent (ctx : ProtocolContext) (state : ProverState F) :
    PIR.Process (participantInterface F G) (ProverState F) :=
  .call (.send (ty := .field "bls12-381.fr") (lowSite ctx) (ctx.roles 1)
    (state.1.take (state.1.length / 2)).sum) fun _ =>
  .call (.send (ty := .field "bls12-381.fr") (highSite ctx) (ctx.roles 1)
    (state.1.drop (state.1.length / 2)).sum) fun _ =>
  .call (.receive (.field "bls12-381.fr") (deliverySite ctx) (ctx.roles 1)) fun (cp : F) =>
  .done (restrictValues state.1 cp, state.2.1 - 1, state.2.2.1, state.2.2.2 ++ [cp])

end ZkcExamples.Structured.SumcheckProverLaws
