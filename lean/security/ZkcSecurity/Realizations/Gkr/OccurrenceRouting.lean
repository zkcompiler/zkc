module

public import ZkcExamples.Construction.GkrSourceRouting
public import ZkcSecurity.Realizations.Gkr.HonestProducerSource
public import ZkcExamples.Structured.GkrInputNormalForms

@[expose] public section

/-! Routing certificates for the actual current GKR occurrence source. Closed
helpers retain all outcomes; only reached field effects consult source routes. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OccurrenceRouting
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcExamples.Construction.GkrSourceRouting
open Zkc.Construction.Uniform.OccurrenceSourceProcess
open HonestProducerSource
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def closedTables : Evaluation.ComponentTablesOn (uniformCarriers F G) closedInterface :=
  GkrSourceViews.unit.definitions.foldl
    (Evaluation.ComponentTablesOn.extend (ringModel F G) (.silent _)) ⟨[], []⟩

theorem closed_tables :
    Evaluation.ComponentTablesOn.Interprets (model := ringModel F G)
      (closedLift (I := Occurrence.signature (uniformCarriers F G)))
      closedTables observedHelpers :=
  Evaluation.ComponentTablesOn.fold_interpret _ (SiteObservations.silent_interpret _)
    (.empty _) _

def helper_routed (handle : Nat) (frames : Original.Frames) (entry : Helper)
    (arguments : Values (assignment F G) entry.inputs) :
    Routed (routing handle) frames frames
      (invoke (observedHelpers (F := F) (G := G)).closed entry arguments) := by
  rw [← closed_tables.closed]
  exact Routed.closed frames _

def components_routed (handle : Nat) (frames : Original.Frames) (entry : Helper)
    (arguments : Values (Component (assignment F G)) entry.inputs) :
    Routed (routing handle) frames frames
      (invoke (observedHelpers (F := F) (G := G)).components entry arguments) := by
  rw [← closed_tables.components]
  exact Routed.closed frames _

def calculation_routed (handle : Nat) (frames : Original.Frames) (operation : Op)
    (allowed : operation.isCalculation = true)
    (arguments : Values (Component (assignment F G)) operation.arguments) :
    Routed (routing handle) frames frames
      (Evaluation.componentOperationOn (ringModel F G) (.silent _) observedHelpers
        operation arguments (operation.calculationRegions allowed)) := by
  have equation := Evaluation.componentOperationOn_interpret
    (closedLift (I := Occurrence.signature (uniformCarriers F G)))
    (SiteObservations.silent_interpret _) closed_tables operation arguments
    (operation.calculationRegions (I := closedInterface) allowed)
  rw [Op.calculationRegions_translate] at equation
  rw [← equation]
  exact Routed.closed frames _

def plain_helper_routed (handle : Nat) (frames : Original.Frames) (entry : Helper)
    (arguments : Values (assignment F G) entry.inputs) :
    Routed (routing handle) frames frames
      ((invoke (Zkc.Source.Structured.plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
        entry arguments).interpret Occurrence.actions) := by
  rw [← observed_helper]
  exact helper_routed handle frames entry arguments

def output_process_routed (handle index : Nat) (point : Option (List F)) :
    Routed (routing handle) [⟨"s37", index⟩] [⟨"s37", index⟩]
      ((GkrSourceCallbacks.verifierOutputProcess (F := F) (G := G) {} (some handle) point).interpret
        Occurrence.actions) := by
  simp only [GkrSourceCallbacks.verifierOutputProcess, PIR.Process.interpret,
    Occurrence.actions, PIR.Process.bind, GkrSourceCallbacks.outputSite,
    GkrSourceCallbacks.outputDeliverySite]
  refine .query _ _ _ _ _ _ (output_draw handle index .validator)
    (query_coordinates context _ _ _) ?_ (fun value => ?_)
  · exact OccurrenceResolution.atCoordinates_request _ _
  · refine .send _ _ _ _ _ _ _ (output_message handle index .validator)
      (message_coordinates context _ _ _ _) ?_
    cases point with
    | none => exact .halt _ _ _
    | some point =>
      simp only [PIR.Process.interpret_bind, PIR.Process.interpret]
      exact (plain_helper_routed (F := F) (G := G) handle _ _ _).bind fun _ => .done _ _

def output_callback_routed (handle index : Nat) (point : Option (List F)) :
    Routed (routing handle) [⟨"s37", index⟩] [⟨"s37", index⟩]
      (GkrSourceCallbacks.outputBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers 1 beforeRoot {} Occurrence.iterations)
        (Values.cons (some index) ((GkrSourceCallbacks.verifierOutputState (F := F) (G := G) point).append
          (.cons (some handle) .nil))).get) := by
  have tables (args : Values (Component (assignment F G))
      (.index :: (GkrSourceCallbacks.outputSpec.state ++ GkrSourceCallbacks.outputSpec.captures))) :
      GkrSourceCallbacks.outputBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers 1 beforeRoot {} Occurrence.iterations) args.get =
      GkrSourceCallbacks.outputBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers 1 [] {} Occurrence.iterations) args.get := by
    kernel_rfl
  rw [tables]
  rw [output_callback, GkrSourceCallbacks.verifierOutput_process {} 1 rfl (by decide)]
  simp only [PIR.Process.interpret_bind, PIR.Process.interpret]
  exact (output_process_routed handle index point).bind fun _ => .done _ _

def round_process_routed (side : Side) (handle layer index : Nat)
    (point : Option (List F)) (claim : Option F) :
    Routed (routing handle) (roundFrames side layer index) (roundFrames side layer index)
      ((GkrRoundsNormalForms.verifierProcess (F := F) (G := G) (roundContext side)
        (some handle) point claim).interpret Occurrence.actions) := by
  have zero : toString (0 : Nat) = "0" := by
    rw [← protocolSiteDecimal_eq_toString]
    cbv
  have one : toString (1 : Nat) = "1" := by
    rw [← protocolSiteDecimal_eq_toString]
    cbv
  have two : toString (2 : Nat) = "2" := by
    rw [← protocolSiteDecimal_eq_toString]
    cbv
  have first := round_message side ⟨0, by decide⟩ handle layer index .validator
  have second := round_message side ⟨1, by decide⟩ handle layer index .validator
  have third := round_message side ⟨2, by decide⟩ handle layer index .validator
  simp only [zero, one, two] at first second third
  have producer : (roundContext side).roles 0 = 0 := by cases side <;> rfl
  simp only [GkrRoundsNormalForms.verifierProcess, PIR.Process.interpret,
    Occurrence.actions, PIR.Process.bind]
  simp only [producer, GkrRoundsNormalForms.round0Site, GkrRoundsNormalForms.round1Site,
    GkrRoundsNormalForms.round2Site]
  refine .receive _ _ _ _ _
    (Domain.atCoordinates (context.message (GkrVerifier.roundSite (roundContext side) "0") 0 1) [layer, index])
    (by cases side <;> exact first) (by cases side <;> exact message_coordinates context _ _ _ _) (fun m0 => ?_)
  refine .receive _ _ _ _ _
    (Domain.atCoordinates (context.message (GkrVerifier.roundSite (roundContext side) "1") 0 1) [layer, index])
    (by cases side <;> exact second) (by cases side <;> exact message_coordinates context _ _ _ _) (fun m1 => ?_)
  refine .receive _ _ _ _ _
    (Domain.atCoordinates (context.message (GkrVerifier.roundSite (roundContext side) "2") 0 1) [layer, index])
    (by cases side <;> exact third) (by cases side <;> exact message_coordinates context _ _ _ _) (fun m2 => ?_)
  cases claim with
  | none => exact .halt _ _ _
  | some claim =>
    dsimp only
    split
    · simp only [PIR.Process.interpret, Occurrence.actions, PIR.Process.bind]
      refine .query _ _ _ _ _ _ (round_draw side handle layer index .validator)
        (query_coordinates context _ _ _) (OccurrenceResolution.atCoordinates_request _ _) (fun value => ?_)
      refine .send _ _ _ _ _ _
        (Domain.atCoordinates (context.message (GkrVerifier.deliverySite (roundContext side)) 1 0) [layer, index])
        (by cases side <;> exact round_delivery_message _ handle layer index .validator)
        (by cases side <;> exact message_coordinates context _ _ _ _) ?_
      cases point with
      | none => exact .halt _ _ _
      | some point =>
        simp only [PIR.Process.interpret_bind, PIR.Process.interpret]
        exact (plain_helper_routed (F := F) (G := G) handle _ _ _).bind fun _ => .done _ _
    · exact .halt _ _ _

def coefficient_process_routed (handle layer index : Nat) (coefficients : Option (List F)) :
    Routed (routing handle) [⟨"s57", layer⟩, ⟨"s91", index⟩] [⟨"s57", layer⟩, ⟨"s91", index⟩]
      ((GkrSourceCallbacks.verifierCoefficientProcess (F := F) (G := G) {} coefficients).interpret
        Occurrence.actions) := by
  simp only [GkrSourceCallbacks.verifierCoefficientProcess, PIR.Process.interpret,
    Occurrence.actions, PIR.Process.bind, GkrSourceCallbacks.lineCoefficientSite]
  refine .receive _ _ _ _ _ _ (coefficient_message handle layer index .validator)
    (message_coordinates context _ _ _ _) (fun value => ?_)
  cases coefficients with
  | none => exact .halt _ _ _
  | some coefficients =>
    simp only [PIR.Process.interpret_bind, PIR.Process.interpret]
    exact (plain_helper_routed (F := F) (G := G) handle _ _ _).bind fun _ => .done _ _

def round_callback_routed (side : Side) (handle layer index : Nat)
    (point : Option (List F)) (claim : Option F) :
    Routed (routing handle) (roundFrames side layer index) (roundFrames side layer index)
      (GkrRoundsNormalForms.roundBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers 1 [] (roundContext side) Occurrence.iterations)
        (Values.cons (some index) ((GkrRoundsNormalForms.verifierState (F := F) (G := G) point claim).append
          (.cons (some handle) .nil))).get) := by
  rw [round_callback, GkrRoundsNormalForms.verifier_process (roundContext side) 1
    (by cases side <;> rfl) (by cases side <;> decide)]
  simp only [PIR.Process.interpret_bind, PIR.Process.interpret]
  exact (round_process_routed side handle layer index point claim).bind fun _ => .done _ _

def coefficient_callback_routed (handle layer index : Nat)
    (coefficients line : Option (List F)) :
    Routed (routing handle) [⟨"s57", layer⟩, ⟨"s91", index⟩] [⟨"s57", layer⟩, ⟨"s91", index⟩]
      (GkrSourceCallbacks.coefficientBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers 1 beforeRoot {} Occurrence.iterations)
        (Values.cons (some index) ((GkrSourceCallbacks.verifierCoefficientState (F := F) (G := G) coefficients).append
          (.cons line .nil))).get) := by
  have tables (args : Values (Component (assignment F G))
      (.index :: (GkrSourceCallbacks.coefficientSpec.state ++ GkrSourceCallbacks.coefficientSpec.captures))) :
      GkrSourceCallbacks.coefficientBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers 1 beforeRoot {} Occurrence.iterations) args.get =
      GkrSourceCallbacks.coefficientBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers 1 [] {} Occurrence.iterations) args.get := by
    kernel_rfl
  rw [tables]
  rw [coefficient_callback, GkrSourceCallbacks.verifierCoefficient_process {} 1 rfl (by decide)]
  simp only [PIR.Process.interpret_bind, PIR.Process.interpret]
  exact (coefficient_process_routed handle layer index coefficients).bind fun _ => .done _ _

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem round_masked (side : Side)
    (state : Values (Component (assignment F G)) GkrRoundsNormalForms.roundSpec.state) :
    maskValues 1 ((roundContext side).mapScopes GkrRoundsNormalForms.roundSpec.stateScopes) state =
      GkrRoundsNormalForms.verifierState (state.get (.there (.there (.there (.there (.there .here)))))) (state.get (.there (.there (.there (.there (.there (.there .here))))))) := by
  cases state with | cons value0 state =>
    cases state with | cons value1 state =>
      cases state with | cons value2 state =>
        cases state with | cons value3 state =>
          cases state with | cons value4 state =>
            cases state with | cons value5 state =>
              cases state with | cons value6 state =>
                cases state
                cases side <;> rfl

def round_masked_routed (side : Side) (handle layer index : Nat)
    (state : Values (Component (assignment F G)) GkrRoundsNormalForms.roundSpec.state) :
    Routed (routing handle) (roundFrames side layer index) (roundFrames side layer index)
      (GkrRoundsNormalForms.roundBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers 1 [] (roundContext side) Occurrence.iterations)
        (Values.cons (some index) ((maskValues 1
          ((roundContext side).mapScopes GkrRoundsNormalForms.roundSpec.stateScopes) state).append
          (.cons (some handle) .nil))).get) := by
  rw [round_masked]
  exact round_callback_routed side handle layer index _ _

def rounds_routed (side : Side) (handle layer : Nat)
    (add mul left right point : Option (List F)) (claim : Option F) (count : Option Nat) :
    Routed (routing handle) [⟨"s57", layer⟩] [⟨"s57", layer⟩]
      (invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.roundsSignature (roundContext side) 1
        (.cons add (.cons mul (.cons left (.cons right (.cons point (.cons claim
          (.cons count (.cons (some handle) .nil))))))))) := by
  rw [rounds_body]
  have masked : maskValues (Value := assignment F G) 1 ((roundContext side).mapScopes GkrSourceBodies.roundsSignature.inputScopes)
      ((.cons add (.cons mul (.cons left (.cons right (.cons point (.cons claim
        (.cons count (.cons (some handle) .nil)))))))) : Values (Component (assignment F G)) GkrSourceBodies.roundsSignature.inputs) =
    (.cons none (.cons none (.cons none (.cons none (.cons point (.cons claim
        (.cons count (.cons (some handle) .nil)))))))) := by
    cases side <;> rfl
  rw [masked]
  apply Routed.bind (middle := [⟨"s57", layer⟩])
  · unfold GkrRoundsNormalForms.roundsBody
    apply Routed.letOp (middle := [⟨"s57", layer⟩])
    · exact .done _ _
    · intro mark; cases mark
      apply Routed.letOp (middle := [⟨"s57", layer⟩])
      · simp only [participantMeaningWithOn, protocolOperationWithOn]
        exact Routed.owned (F := F) (G := G) _ _ _ _
          (fun values => helper_routed handle _ _ values) _
      · intro empty
        rcases empty with ⟨empty, ⟨⟩⟩
        apply Routed.letOp (middle := [⟨"s57", layer⟩])
        · exact .done _ _
        · intro mark; cases mark
          apply Routed.letOp (middle := [⟨"s57", layer⟩])
          · simp only [participantMeaningWithOn, protocolOperationWithOn]
            exact Routed.owned (F := F) (G := G) _ _ _ _
              (fun values => helper_routed handle _ _ values) _
          · intro initial
            rcases initial with ⟨first, second, ⟨⟩⟩
            apply Routed.letOp (middle := [⟨"s57", layer⟩])
            · exact .done _ _
            · intro mark; cases mark
              apply Routed.letOp (middle := [⟨"s57", layer⟩])
              · apply Routed.repeatCaptured
                intro index carried
                have certificate := round_masked_routed (F := F) (G := G) side handle layer index carried
                cases_type* Values
                exact certificate

              · intro final
                apply Routed.letOp (middle := [⟨"s57", layer⟩])
                · exact .done _ _
                · intro mark; cases mark
                  apply Routed.letOp (middle := [⟨"s57", layer⟩])
                  · simp only [participantMeaningWithOn, protocolOperationWithOn]
                    exact Routed.owned (F := F) (G := G) _ _ _ _
                      (fun values => helper_routed handle _ _ values) _
                  · intro result
                    exact .done _ _
  · intro _; exact .done _ _

def input_routed (handle : Nat) (frames : Original.Frames) (ctx : ProtocolContext)
    (self : Nat) (arguments : Values (Component (assignment F G)) GkrSourceBodies.sourceProtocol80Signature.inputs) :
    Routed (routing handle) frames frames
      (invokeProtocol beforeRoot GkrSourceBodies.sourceProtocol80Signature ctx self arguments) := by
  change Routed _ _ _ (invokeProtocol
    (⟨GkrSourceViews.sourceProtocol80Definition.signature, _⟩ :: beforeInput)
    GkrSourceViews.sourceProtocol80Definition.signature ctx self arguments)
  rw [invokeProtocol_cons_same]
  unfold CheckedProtocol.denoteWithOn
  erw [GkrSourceViews.sourceProtocol80Definition.body_eq_of_raw _ GkrInputNormalForms.inputBody_raw]
  apply Routed.bind
  · unfold GkrInputNormalForms.inputBody
    simp only [Region.denote, participantMeaningWithOn, protocolOperationWithOn,
      Operands.eval, Regions.denote, Values.get_cons, Environment.prepend, Environment.push,
      SiteObservations.silent, PIR.Process.bind, PIR.Process.bind_done]
    exact (Routed.owned frames self (ctx.roles 0) _
      (fun values => helper_routed (F := F) (G := G) handle frames _ values) _).bind fun _ => .done _ _
  · intro _; exact .done _ _

end ZkcSecurity.Realizations.Gkr.OccurrenceRouting
