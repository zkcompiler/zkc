import Zkc.Source.Structured.ContractComposition
import ZkcExamples.Structured.SumcheckSourceViews
import ZkcExamples.Structured.SumcheckReduceViews
import ZkcExamples.Structured.ApplicationWrapperViews
import ZkcExamples.Structured.SumcheckContractInstantiation
import Zkc.Source.DeriveRegion

/-! Actual maintained source subjects: lexical inventories and one concrete
nested caller composition. These controls do not prove security or reachability. -/
set_option autoImplicit false
set_option smartUnfolding false
namespace Tests.ContractSourceCalls
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

example : (callSites SumcheckSourceViews.runDefinition.body).map (·.signature) =
    [SumcheckSourceBodies.reduceSignature] := rfl
example : (callSites SumcheckSourceViews.runDefinition.body).map (·.site) =
    ["label_726564756365"] := rfl
example : (callSites SumcheckSourceViews.runDefinition.body).map (fun c => c.operands.indices) =
    [[0, 1, 2, 5, 6, 7]] := rfl
example : (callSites SumcheckReduceViews.runDefinition.body).map (·.signature) =
    [SumcheckReduceBodies.reduceSignature] := rfl
example : (callSites SumcheckReduceViews.runDefinition.body).map (fun c => c.operands.indices) =
    [[0, 1, 2, 6, 7, 8]] := rfl
set_option maxRecDepth 20000 in
example : (callInventory SumcheckSourceViews.reduceDefinition.body).length = 0 := rfl
set_option maxRecDepth 20000 in
example : (callInventory SumcheckReduceViews.reduceDefinition.body).length = 0 := rfl

example : (callSites ApplicationWrapperViews.outerDefinition.body).map (·.signature) =
    [ServiceOrderBodies.runSignature] := rfl
example : (callSites ServiceOrderViews.runDefinition.body).map (·.signature) =
    [ServiceOrderBodies.drawSignature] := rfl
example : (callInventory ServiceOrderViews.drawDefinition.body).length = 0 := rfl

open ServiceOrderBodies ApplicationWrapperViews

/-- The continuation is extracted from the actual maintained wrapper. -/
def outerCall : CallOccurrence outerBody :=
  ⟨⟨inputTypes, runSignature, [0, 1], "s0",
    .cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))⟩,
    .next _ _ _ _ (.here _)⟩

example : outerCall ∈ callInventory outerDefinition.body := callInventory_complete _
example : outerCall.position = [1] := rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- A local Run law (which can itself use a Draw law) composes into the actual
Outer source call. Its identity and complete ABI come from the checked table. -/
theorem outer_call_substitution (self : Nat) (context : ProtocolContext)
    (environment : Environment (Component (assignment F G)) inputTypes)
    (inside : (context.enter "s0" [0, 1]).contains runSignature self = true)
    (replacement : PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) resultTypes))
    (localLaw : CalleeResolution
      (participantMeaning (unit.tables F G) self (unit.protocolTable F G) (context.enter "s0" [0, 1]))
      runBody (maskValues self ((context.enter "s0" [0, 1]).mapScopes runSignature.inputScopes)
        (outerCall.callSite.operands.eval environment)).get replacement) :
    outerCall.application.denote
      (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context) environment =
      replacement.bind (fun returned => outerCall.continuation.2.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (environment.prepend (maskValues self
          ((context.enter "s0" [0, 1]).mapScopes runSignature.outputScopes) returned))) :=
  unit.protocolApply_substitute ServiceOrderViews.runDefinition run_member runSignature
    ServiceOrderViews.run_signature runBody ServiceOrderViews.run_raw [0, 1] "s0" context self
    outerCall.callSite.operands outerCall.continuation.2 environment inside replacement localLaw

/-- This is the whole actual caller, including its prefix mark. Only the local
callee body law is a premise; no whole-Outer equivalence is assumed. -/
theorem outer_body_composition (self : Nat) (context : ProtocolContext)
    (environment : Environment (Component (assignment F G)) inputTypes)
    (inside : (context.enter "s0" [0, 1]).contains runSignature self = true)
    (replacement : PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) resultTypes))
    (localLaw : CalleeResolution
      (participantMeaning (unit.tables F G) self (unit.protocolTable F G) (context.enter "s0" [0, 1]))
      runBody (maskValues self ((context.enter "s0" [0, 1]).mapScopes runSignature.inputScopes)
        (outerCall.callSite.operands.eval environment)).get replacement) :
    outerBody.denote
      (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context) environment =
      .call (.mark (qualifyProtocolSite context.applicationPrefix "s0")) (fun _ =>
        replacement.bind (fun returned => outerCall.continuation.2.denote
          (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
          (environment.prepend (maskValues self
            ((context.enter "s0" [0, 1]).mapScopes runSignature.outputScopes) returned)))) := by
  have callRule : (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context).OperationLaw
      (fun op => .call op .done) (.protocolApply runSignature [0, 1] "s0")
      (outerCall.callSite.operands.eval environment) .nil
      (replacement.bind (fun returned => .done (maskValues self
        ((context.enter "s0" [0, 1]).mapScopes runSignature.outputScopes) returned))) := by
    convert
      (unit.protocolApply_operationLaw (observedSites F G) observeAction (unit.tables F G)
        (fun op => .call op .done) ServiceOrderViews.runDefinition run_member runSignature
        ServiceOrderViews.run_signature runBody ServiceOrderViews.run_raw [0, 1] "s0" context self
        (outerCall.callSite.operands.eval environment) replacement
        (fun _ => by rw [PIR.Proc.interpret_identity]; exact localLaw.sound)) using 1
    simp only [inside, ↓reduceIte]
    rfl
  apply Eq.trans
  · apply Region.Derivation.sound_identity
    derive_region using (
      first
      | exact callRule
      | apply RegionMeaning.OperationLaw.identity
        rfl)
  · change (.call (.mark (qualifyProtocolSite context.applicationPrefix "s0")) _ :
      PIR.Proc (observedInterface F G) _) = _
    congr 1
    funext reply
    simp only [PIR.Proc.bind_assoc, Values.reify_get]
    rfl

/-- Actual Sumcheck-to-Reduce occurrence, extracted from the complete inventory. -/
def sumcheckCall : CallOccurrence SumcheckSourceViews.runDefinition.body :=
  SumcheckContractInstantiation.publicReductionCall.toCallOccurrence

example : sumcheckCall ∈ callInventory SumcheckSourceViews.runDefinition.body :=
  SumcheckContractInstantiation.publicReductionCall.toCallOccurrence_mem

example : sumcheckCall.occurrence = SumcheckContractInstantiation.publicReductionCall.occurrence := rfl

/-- The retained same-snapshot callee binding supplies the operation rule's
identity, complete ABI and body association; no second link record is supplied. -/
theorem sumcheck_bound_operationLaw (self : Nat) (context : ProtocolContext)
    (environment : Environment (Component (assignment F G)) sumcheckCall.callSite.context)
    (replacement : PIR.Proc (participantInterface F G)
      (Values (Component (assignment F G)) sumcheckCall.callSite.signature.outputs))
    (localLaw : (context.enter sumcheckCall.callSite.site sumcheckCall.callSite.roles).contains
      sumcheckCall.callSite.signature self = true →
      (SumcheckContractInstantiation.childOwner.protocol.body.denote
        (participantMeaning (SumcheckSourceViews.unit.tables F G) self
          (SumcheckSourceViews.unit.protocolTable F G)
          (context.enter sumcheckCall.callSite.site sumcheckCall.callSite.roles))
        (maskValues self
          ((context.enter sumcheckCall.callSite.site sumcheckCall.callSite.roles).mapScopes
            sumcheckCall.callSite.signature.inputScopes)
          (sumcheckCall.callSite.operands.eval environment)).get).interpret forgetSites = replacement) :
    (participantMeaning (SumcheckSourceViews.unit.tables F G) self
      (SumcheckSourceViews.unit.protocolTable F G) context).OperationLaw forgetSites
      (.protocolApply sumcheckCall.callSite.signature sumcheckCall.callSite.roles sumcheckCall.callSite.site)
      (sumcheckCall.callSite.operands.eval environment) .nil
      (if (context.enter sumcheckCall.callSite.site sumcheckCall.callSite.roles).contains
          sumcheckCall.callSite.signature self then
        replacement.bind (fun returned => .done (maskValues self
          ((context.enter sumcheckCall.callSite.site sumcheckCall.callSite.roles).mapScopes
            sumcheckCall.callSite.signature.outputScopes) returned))
       else .done (Values.absent (assignment F G) sumcheckCall.callSite.signature.outputs)) :=
  SumcheckContractInstantiation.childOwner.protocolApply_operationLaw (observedSites F G)
    observeAction (SumcheckSourceViews.unit.tables F G) forgetSites sumcheckCall.callSite.roles
    sumcheckCall.callSite.site context self (sumcheckCall.callSite.operands.eval environment) replacement localLaw

/-- The maintained Sumcheck call accepts a LOCAL participant-level Reduce law.
The actual terminal-check suffix sees exactly Reduce's masked returned tuple. -/
theorem sumcheck_reduce_substitution (self : Nat) (context : ProtocolContext)
    (environment : Environment (Component (assignment F G)) sumcheckCall.callSite.context)
    (inside : (context.enter sumcheckCall.callSite.site sumcheckCall.callSite.roles).contains
      sumcheckCall.callSite.signature self = true)
    (replacement : PIR.Proc (participantInterface F G)
      (Values (Component (assignment F G)) sumcheckCall.callSite.signature.outputs))
    (localLaw : (SumcheckSourceBodies.reduceBody.denote
      (participantMeaning (SumcheckSourceViews.unit.tables F G) self
        (SumcheckSourceViews.unit.protocolTable F G)
        (context.enter sumcheckCall.callSite.site sumcheckCall.callSite.roles))
      (maskValues self
        ((context.enter sumcheckCall.callSite.site sumcheckCall.callSite.roles).mapScopes
          sumcheckCall.callSite.signature.inputScopes)
        (sumcheckCall.callSite.operands.eval environment)).get).interpret forgetSites = replacement) :
    (sumcheckCall.application.denote
      (participantMeaning (SumcheckSourceViews.unit.tables F G) self
        (SumcheckSourceViews.unit.protocolTable F G) context) environment).interpret forgetSites =
      replacement.bind (fun returned => (sumcheckCall.continuation.2.denote
        (participantMeaning (SumcheckSourceViews.unit.tables F G) self
          (SumcheckSourceViews.unit.protocolTable F G) context)
        (environment.prepend (maskValues self
          ((context.enter sumcheckCall.callSite.site sumcheckCall.callSite.roles).mapScopes
            sumcheckCall.callSite.signature.outputScopes) returned))).interpret forgetSites) :=
  SumcheckSourceViews.unit.protocolApply_interpret_substitute SumcheckSourceViews.reduceDefinition
    SumcheckSourceViews.reduce_member sumcheckCall.callSite.signature rfl
    SumcheckSourceBodies.reduceBody SumcheckSourceViews.reduce_raw
    sumcheckCall.callSite.roles sumcheckCall.callSite.site context self sumcheckCall.callSite.operands
    sumcheckCall.continuation.2 environment inside forgetSites replacement localLaw

end Tests.ContractSourceCalls
