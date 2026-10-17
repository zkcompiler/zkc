module

public import Zkc.Semantics.ExactRefinement
public import Zkc.Source.Common.Scalar
public import Zkc.Protocols.Sumcheck.Transcript

@[expose] public section

/-! Common-source two-round Sumcheck contract with explicit effect wiring.
The contract preserves the open process; its security interpretation is separate.
-/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.Sumcheck.Common

open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Polynomial Zkc.Probability

structure Wiring where
  prover : Nat
  fieldDomain : String
  firstSites : String × String × String
  secondSites : String × String × String
  firstChallenge : String
  secondChallenge : String
  firstDelivery : String
  secondDelivery : String

structure Coefficients (F : Type) where
  constant : Message F
  linear : Message F
  quadratic : Message F

variable {F : Type} [Field F] [DecidableEq F]

abbrev actions := Participant.interface Nat Ty services (ScalarValue F F)

def rowPolynomial (row : Message F) : Quadratic F 1 :=
  .node (.constant row.constant) (.constant row.linear) (.constant row.quadratic)

def polynomial (coefficients : Coefficients F) : Quadratic F 2 :=
  .node (rowPolynomial coefficients.constant) (rowPolynomial coefficients.linear)
    (rowPolynomial coefficients.quadratic)

def wireEvaluate (message : Message F) (challenge : F) : F :=
  message.constant + challenge * message.linear + (challenge * challenge) * message.quadratic

def wireBoundary (message : Message F) : F :=
  message.constant + message.constant + message.linear + message.quadratic

omit [DecidableEq F] in
theorem wireEvaluate_eq (message : Message F) (challenge : F) :
    wireEvaluate message challenge = message.evaluate challenge := by
  simp only [wireEvaluate, Message.evaluate]
  ring

omit [DecidableEq F] in
theorem wireBoundary_eq (message : Message F) : wireBoundary message = message.boundary := by
  simp only [wireBoundary, Message.boundary, Message.evaluate]
  ring

def evaluate (coefficients : Coefficients F) (first second : F) : F :=
  wireEvaluate coefficients.constant second + first * wireEvaluate coefficients.linear second +
    (first * first) * wireEvaluate coefficients.quadratic second

omit [DecidableEq F] in
theorem evaluate_eq (coefficients : Coefficients F) (first second : F) :
    evaluate coefficients first second = (polynomial coefficients).eval
      (Zkc.Protocols.Sumcheck.tapePoint 2 (first, second, ())) := by rfl

/-- Pure computations can vary independently of the protocol's effect schedule. -/
structure VerifierArithmetic (F : Type) where
  boundary : Message F → F
  message : Message F → F → F
  statement : Coefficients F → F → F → F

def standardArithmetic : VerifierArithmetic F := ⟨wireBoundary, wireEvaluate, evaluate⟩

omit [DecidableEq F] in
theorem VerifierArithmetic.standard_eq (arithmetic : VerifierArithmetic F)
    (boundary : ∀ m, arithmetic.boundary m = wireBoundary m)
    (message : ∀ m x, arithmetic.message m x = wireEvaluate m x)
    (statement : ∀ p x y, arithmetic.statement p x y = evaluate p x y) :
    arithmetic = standardArithmetic := by
  cases arithmetic with
  | mk b m s =>
    have hb : b = wireBoundary := funext boundary
    have hm : m = wireEvaluate := funext (fun p => funext (message p))
    have hs : s = evaluate := funext (fun p => funext (fun x => funext (statement p x)))
    cases hb
    cases hm
    cases hs
    rfl

def experimentWith (wiring : Wiring) (arithmetic : VerifierArithmetic F) (coefficients : Coefficients F) (claim : F) (service : Nat) :
    PIR.Proc (actions (F := F)) (Option Bool) :=
  .call (.receive (.field wiring.fieldDomain) wiring.firstSites.1 wiring.prover) fun a =>
  .call (.receive (.field wiring.fieldDomain) wiring.firstSites.2.1 wiring.prover) fun b =>
  .call (.receive (.field wiring.fieldDomain) wiring.firstSites.2.2 wiring.prover) fun c =>
  if decide (arithmetic.boundary ⟨a,b,c⟩ = claim) then
    .call (.query wiring.firstChallenge wiring.fieldDomain (.cons service .nil)) fun first =>
    .call (.send (ty := .field wiring.fieldDomain) wiring.firstDelivery wiring.prover first) fun _ =>
    .call (.receive (.field wiring.fieldDomain) wiring.secondSites.1 wiring.prover) fun d =>
    .call (.receive (.field wiring.fieldDomain) wiring.secondSites.2.1 wiring.prover) fun e =>
    .call (.receive (.field wiring.fieldDomain) wiring.secondSites.2.2 wiring.prover) fun f =>
    if decide (arithmetic.boundary ⟨d,e,f⟩ = arithmetic.message ⟨a,b,c⟩ first) then
      .call (.query wiring.secondChallenge wiring.fieldDomain (.cons service .nil)) fun second =>
      .call (.send (ty := .field wiring.fieldDomain) wiring.secondDelivery wiring.prover second) fun _ =>
      .done (some (decide (arithmetic.message ⟨d,e,f⟩ second = arithmetic.statement coefficients first second)))
    else .halt .reject
  else .halt .reject

def experiment (wiring : Wiring) (coefficients : Coefficients F) (claim : F) (service : Nat) :
    PIR.Proc (actions (F := F)) (Option Bool) :=
  experimentWith wiring standardArithmetic coefficients claim service

/-- Pure arithmetic obligations suffice; all effects, guards and continuations
are preserved by substitution into the same open process. -/
theorem experimentWith_eq (wiring : Wiring) (arithmetic : VerifierArithmetic F)
    (boundary : ∀ m, arithmetic.boundary m = wireBoundary m)
    (message : ∀ m x, arithmetic.message m x = wireEvaluate m x)
    (statement : ∀ p x y, arithmetic.statement p x y = evaluate p x y)
    (coefficients : Coefficients F) (claim : F) (service : Nat) :
    experimentWith wiring arithmetic coefficients claim service = experiment wiring coefficients claim service := by
  rw [arithmetic.standard_eq boundary message statement]
  rfl

abbrev Verifier (F : Type) [Field F] :=
  Coefficients F → F → Nat → PIR.Proc (actions (F := F)) (Option Bool)

structure VerifierContract (wiring : Wiring) (program : Verifier F) : Prop where
  realizes : ∀ coefficients claim service,
    PIR.ExactRefinement (program coefficients claim service)
      (experiment wiring coefficients claim service)

end Zkc.Protocols.Sumcheck.Common
