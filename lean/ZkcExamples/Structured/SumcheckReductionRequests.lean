module

public import ZkcExamples.Structured.SumcheckContractRequests

@[expose] public section

/-! The residual-only wrapper and its actual checked Reduce invocation share
one fixed table interpretation. This module connects their selected outputs. -/
namespace ZkcExamples.Structured.SumcheckReductionRequests
open Zkc.Source Zkc.Source.Structured
open SumcheckRelationContract SumcheckContractBindings SumcheckContractRequests
open Zkc.Polynomial.Multilinear

set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def childProcess (claim : F) (count handle : Nat) :=
  (reductionCall.componentInput {} 1 (reductionCallEnvironment (G := G) claim count handle)).process.interpret
    forgetSites

set_option backward.isDefEq.respectTransparency false in
theorem child_present (claim : F) (count handle : Nat) (admitted : count ≤ 4) :
    childProcess (G := G) claim count handle =
      (PIR.repeatN count (SumcheckVerifierLaws.roundPresent (ProtocolContext.enter {} "s5" [0, 1]) handle)
        ([], claim)).bind (fun pc => .done (SumcheckVerifierPrelude.reduceResults (some pc.1, some pc.2))) := by
  change (invokeProtocol (SumcheckReduceViews.unit.protocolTable F G) SumcheckReduceBodies.reduceSignature
    (ProtocolContext.enter {} "s5" [0, 1]) 1
    (SumcheckVerifierPrelude.reduceArguments none none none (some []) (some claim) (some count) (some handle))).interpret
    forgetSites = _
  rw [SumcheckReduceViews.unit.protocolTable_forgetSites, SumcheckReduceVerifier.reduce_invoke_plain]
  rw [SumcheckVerifierPrelude.reduce_optional SumcheckReduceViews.unit SumcheckReduceVerifier.helperBodies SumcheckReduceVerifier.claimBodies
    (ProtocolContext.enter {} "s5" [0, 1]) 1 rfl (by decide)]
  simp only [SumcheckVerifierPrelude.pendingRounds, admitted, ↓reduceIte]
  rw [SumcheckVerifierLaws.repeat_present (ProtocolContext.enter {} "s5" [0, 1]) handle count ([], claim)]
  exact PIR.Process.bind_assoc _ _ _

def assignments (raw : List F) (dimension : Nat) :=
  fixedReduction (G := G)
    (invocation := reductionCall.childInvocation rootInvocation (fun index => Fin.elim0 index)) raw dimension

def terminal (remaining count : Nat) : ExternalTerminal reductionOwner F G :=
  residualTerminal reductionOwner (.parameter reductionTable) remaining count reductionPoint reductionValue rfl rfl

def request (raw : List F) (remaining count : Nat) (claim : F) (handle : Nat)
    (outputs : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs) : Prop :=
  (terminal (G := G) remaining count).Holds (ProtocolContext.enter {} "s5" [0, 1])
    (reductionBoundary claim count handle (.returned outputs)) (assignments raw (remaining + count))

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
set_option backward.isDefEq.respectTransparency false in
theorem request_iff (raw : List F) (remaining count : Nat) (claim : F) (handle : Nat)
    (table : Table F (remaining + count)) (decoded : ofList? (remaining + count) raw = some table)
    (outputs : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs) :
    request raw remaining count claim handle outputs ↔
      match outputs.get (.there (.there (.there (.there .here)))),
          outputs.get (.there (.there (.there (.there (.there .here))))) with
      | some point, some value => Residual remaining count table point value
      | _, _ => False := by
  refine (residual_terminal_iff (.parameter reductionTable) remaining count reductionPoint reductionValue rfl rfl
    (ProtocolContext.enter {} "s5" [0, 1]) (reductionBoundary claim count handle (.returned outputs))
    (assignments raw (remaining + count)) raw rfl table decoded).trans ?_
  have pointRead := reductionCall.boundaryOfOutcome_returned_output {} 1
    (reductionCallEnvironment (G := G) claim count handle) outputs reductionPoint
    (.there (.there (.there (.there .here)))) rfl rfl
  have valueRead := reductionCall.boundaryOfOutcome_returned_output {} 1
    (reductionCallEnvironment (G := G) claim count handle) outputs reductionValue
    (.there (.there (.there (.there (.there .here))))) rfl rfl
  change (∃ p v, _ = some p ∧ _ = some v ∧ Residual remaining count table p v) ↔ _
  erw [pointRead, valueRead]
  generalize outputs.get (.there (.there (.there (.there .here)))) = op
  generalize outputs.get (.there (.there (.there (.there (.there .here))))) = ov
  cases op <;> cases ov <;> simp

/-- This is the actual wrapper return projection of the two child V outputs;
P's returned table and metadata are not used by the mathematical request. -/
def wrapperOutputs (outputs : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs) :=
  SumcheckReduceVerifier.reduceRootResults (G := G)
    (outputs.get (.there (.there (.there (.there .here)))),
     outputs.get (.there (.there (.there (.there (.there .here))))))

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem wrapper_request_iff (raw : List F) (remaining count : Nat) (claim : F) (handle : Nat)
    (table : Table F (remaining + count)) (decoded : ofList? (remaining + count) raw = some table)
    (proverValues : Option (List F)) (proverDimension : Option Nat)
    (outputs : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs) :
    (wrapperTerminal raw remaining count).Holds {}
      ((reductionRootInput proverValues proverDimension claim count handle).boundary
        (.returned (wrapperOutputs outputs))) (wrapperAssignments (G := G)) ↔
      request raw remaining count claim handle outputs :=
  (wrapper_terminal_iff raw remaining count table decoded proverValues proverDimension claim handle
    (wrapperOutputs outputs)).trans (request_iff raw remaining count claim handle table decoded outputs).symm

end ZkcExamples.Structured.SumcheckReductionRequests
