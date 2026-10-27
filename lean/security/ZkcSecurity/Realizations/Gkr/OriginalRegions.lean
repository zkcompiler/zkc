module

public import ZkcSecurity.Realizations.Gkr.OriginalRounds
public import ZkcSecurity.Realizations.Gkr.OriginalCoefficient
public import ZkcExamples.Construction.GkrOriginalRoutes
public import Zkc.Source.DeriveRegion

@[expose] public section
/-! Source presentations used at component boundaries. The existing source
traversal checks each operation; nested callbacks remain their original regions. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OriginalRegions
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks GkrRoundsNormalForms
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

attribute [local irreducible] roundBody coefficientBody

/-- These callbacks have no protocol application. The immutable protocol table
therefore does not change their denotation; the actual body is retained. -/
theorem coefficient_table (self : Nat) (ctx : ProtocolContext)
    (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
    (args : Values (Component (assignment F G)) (.index :: (coefficientState ++ coefficientCaptures))) :
    coefficientBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self protocols ctx Occurrence.iterations) args.get =
    coefficientBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self [] ctx Occurrence.iterations) args.get := by
  simp only [coefficientBody, Region.denote, participantMeaningWithOn,
    protocolOperationWithOn, Regions.denote, Operands.eval, Values.get,
    Environment.prepend, Environment.push]

theorem output_table (self : Nat) (ctx : ProtocolContext)
    (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
    (args : Values (Component (assignment F G)) (.index :: (outputState ++ outputCaptures))) :
    outputBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self protocols ctx Occurrence.iterations) args.get =
    outputBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self [] ctx Occurrence.iterations) args.get := by
  simp only [outputBody, Region.denote, participantMeaningWithOn,
    protocolOperationWithOn, Regions.denote, Operands.eval, Values.get,
    Environment.prepend, Environment.push]

theorem producer_rounds (side : Side) (add mul left right : Option (List F))
    (count : Option Nat) (point : Option (List F)) (claim : Option F) (service : Option Nat) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.roundsSignature (roundContext side) 0
      (.cons add (.cons mul (.cons left (.cons right (.cons point (.cons claim
        (.cons count (.cons service .nil)))))))) =
      roundsPresentation (roundContext side) add mul left right count :=
  rounds_invocation (roundContext side) (by cases side <;> rfl) (by cases side <;> rfl)
    add mul left right count point claim service

def validatorRounds (side : Side) (point : List F) (claim : F) (count handle : Nat) :
    PIR.Process (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) roundsOutputs) :=
  (invoke observedHelpers.closed GkrSourceBodies.sourceHelper40Helper
    (.cons point (.cons claim .nil))).bind fun initial =>
  (denoteRepeatOn (carriers := uniformCarriers F G) roundSpec (roundContext side) 1 (some count)
    (verifierState (some (initial.get .here)) (some (initial.get (.there .here))))
    (.cons (some handle) .nil)
    (fun args => roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers 1 [] (roundContext side) Occurrence.iterations) args.get)
    Occurrence.iterations "s9").bind fun final =>
  match final.get (.there (.there (.there (.there (.there .here))))) with
  | none => .halt .incomplete
  | some point =>
    match final.get (.there (.there (.there (.there (.there (.there .here)))))) with
    | none => .halt .incomplete
    | some claim =>
      (invoke observedHelpers.closed GkrSourceBodies.sourceHelper49Helper
        (.cons point (.cons claim .nil))).bind fun result =>
      .done (.cons none (.cons none (.cons none (.cons none (.cons none
        (.cons (some (result.get .here)) (.cons (some (result.get (.there .here))) .nil)))))))

theorem validator_rounds (side : Side) (point : List F) (claim : F) (count handle : Nat)
    (add mul left right : Option (List F)) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.roundsSignature (roundContext side) 1
      ((.cons add (.cons mul (.cons left (.cons right (.cons (some point) (.cons (some claim)
        (.cons (some count) (.cons (some handle) .nil)))))))) :
          Values (Component (assignment F G)) roundsInputs) =
      validatorRounds side point claim count handle := by
  rw [rounds_body]
  have masked : maskValues (Value := assignment F G) 1
      ((roundContext side).mapScopes GkrSourceBodies.roundsSignature.inputScopes)
      ((.cons add (.cons mul (.cons left (.cons right (.cons (some point) (.cons (some claim)
        (.cons (some count) (.cons (some handle) .nil)))))))) :
          Values (Component (assignment F G)) roundsInputs) =
      (.cons none (.cons none (.cons none (.cons none (.cons (some point) (.cons (some claim)
        (.cons (some count) (.cons (some handle) .nil)))))))) := by
    cases side <;> rfl
  rw [masked]
  have zero : (roundContext side).roles 0 = 0 := by cases side <;> rfl
  have one : (roundContext side).roles 1 = 1 := by cases side <;> rfl
  simp [roundsBody, Region.denote, participantMeaningWithOn, protocolOperationWithOn,
    Operands.eval, Regions.denote, Values.get, Environment.prepend, Environment.push,
    SiteObservations.silent, PIR.Process.bind, Participant.owned, RoleFamily.sequence,
    zero, one, ↓reduceIte, Values.absent, Values.present, Values.split, ProtocolOp.results,
    GkrSourceBodies.sourceHelper40Helper, GkrSourceBodies.sourceHelper49Helper,
    PIR.Process.bind_assoc, validatorRounds]
  apply congrArg (PIR.Process.bind _)
  funext initial
  cases initial with | cons point rest =>
    cases rest with | cons claim rest =>
      cases rest
      simp only [Values.get, Environment.prepend, Environment.push, Values.present,
        PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext final
      cases final with | cons a rest =>
        cases rest with | cons b rest =>
          cases rest with | cons c rest =>
            cases rest with | cons d rest =>
              cases rest with | cons e rest =>
                cases rest with | cons p rest =>
                  cases rest with | cons q rest =>
                    cases rest
                    cases p <;> cases q <;> cases side <;>
                      simp [Environment.prepend, Environment.push, Values.get,
                        Values.present, maskValues, ProtocolContext.mapScopes, Participant.restrict, ProtocolContext.roles, ProtocolContext.enter,
                        GkrSourceBodies.roundsSignature, roundContext, GkrVerifier.leftContext,
                        GkrVerifier.rightContext, roleSubstitution, PIR.Process.bind_assoc, PIR.Process.bind] <;>
                        (apply congrArg (PIR.Process.bind _)
                         funext result
                         cases result with | cons p rest =>
                           cases rest with | cons q rest =>
                             cases rest
                             rfl)

end ZkcSecurity.Realizations.Gkr.OriginalRegions
