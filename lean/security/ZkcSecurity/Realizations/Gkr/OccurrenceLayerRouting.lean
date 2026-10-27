module

public import ZkcSecurity.Realizations.Gkr.OccurrenceRouting

@[expose] public section

/-! All-outcome routing of the current layer callback. Local helpers retain
all stops; each reached field effect uses its complete source occurrence. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OccurrenceRouting
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcExamples.Construction.GkrSourceRouting
open Zkc.Construction.Uniform.OccurrenceSourceProcess
open HonestProducerSource
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

macro "route_mark" : tactic =>
  `(tactic| refine Routed.pureLet _ _ _ _ _ _ .nil rfl ?_)

macro "route_helper " handle:term " at " frames:term " over " scalar:term "," group:term : tactic =>
  `(tactic|
    refine Routed.letOp (middle := $frames) _ _ _ _ _ _
      (by
        simp only [participantMeaningWithOn, protocolOperationWithOn]
        exact Routed.owned (F := $scalar) (G := $group) _ _ _ _
          (fun values => helper_routed (F := $scalar) (G := $group) $handle _ _ values) _)
      ?_)


macro "route_calculation " handle:term " at " frames:term " over " scalar:term "," group:term : tactic =>
  `(tactic|
    refine Routed.letOp (middle := $frames) _ _ _ _ _ _
      (by
        simp only [participantMeaningWithOn, protocolOperationWithOn]
        exact calculation_routed (F := $scalar) (G := $group) $handle $frames _ rfl _)
      ?_)

macro "route_restrict" : tactic =>
  `(tactic| refine Routed.pureLet _ _ _ _ _ _ (.cons _ .nil) rfl ?_)

/-- Missing components and stopped helper executions remain part of the
certificate. Only the selected immutable service capture is fixed. -/
def layer_routed (handle layer : Nat)
    (producerPoint point : Option (List F)) (claim : Option F)
    (initial add mul : Option (List F)) (layers selector width : Option Nat) :
    Routed (routing handle) [⟨"s57", layer⟩] [⟨"s57", layer⟩]
      (GkrSourceCallbacks.layerBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers 1 beforeRoot {} Occurrence.iterations)
        (Values.cons (some layer) (.cons producerPoint (.cons point (.cons claim
          (.cons initial (.cons add (.cons mul (.cons layers (.cons selector
            (.cons width (.cons (some handle) .nil))))))))))).get) := by
  unfold GkrSourceCallbacks.layerBody
  route_mark
  route_helper handle at [⟨"s57", layer⟩] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [⟨"s57", layer⟩] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [⟨"s57", layer⟩] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [⟨"s57", layer⟩] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [⟨"s57", layer⟩] over F, G
  intro values
  cases_type* Values
  route_mark
  route_helper handle at [⟨"s57", layer⟩] over F, G
  intro values
  cases_type* Values
  route_mark
  apply Routed.letOp (middle := [⟨"s57", layer⟩])
  · simp only [participantMeaningWithOn, protocolOperationWithOn]
    have inside : (({} : ProtocolContext).enter "label_6c656674" [0, 1]).contains
        GkrSourceBodies.roundsSignature 1 = true := by decide +kernel
    rw [inside]
    exact rounds_routed .left handle layer _ _ _ _ _ _ _
  · intro values
    cases_type* Values
    route_mark
    apply Routed.letOp (middle := [⟨"s57", layer⟩])
    · simp only [participantMeaningWithOn, protocolOperationWithOn]
      have inside : (({} : ProtocolContext).enter "label_7269676874" [0, 1]).contains
          GkrSourceBodies.roundsSignature 1 = true := by decide +kernel
      rw [inside]
      exact rounds_routed .right handle layer _ _ _ _ _ _ _
    · intro values
      cases_type* Values
      route_mark
      route_helper handle at [⟨"s57", layer⟩] over F, G
      intro values
      cases_type* Values
      route_mark
      route_helper handle at [⟨"s57", layer⟩] over F, G
      intro values
      cases_type* Values
      route_mark
      route_helper handle at [⟨"s57", layer⟩] over F, G
      intro values
      cases_type* Values
      route_mark
      route_calculation handle at [⟨"s57", layer⟩] over F, G
      intro values
      cases_type* Values
      route_mark
      route_helper handle at [⟨"s57", layer⟩] over F, G
      intro values
      cases_type* Values
      route_mark
      apply Routed.letOp (middle := [⟨"s57", layer⟩])
      · simp only [participantMeaningWithOn, protocolOperationWithOn,
          Participant.exchange, ProtocolContext.roles, PIR.Process.interpret,
          Occurrence.actions, PIR.Process.bind]
        refine .receive _ _ _ _ _ _ (constant_message handle layer .validator)
          (message_coordinates context _ _ _ _) (fun value => ?_)
        exact .done _ _
      · intro values
        cases_type* Values
        route_mark
        route_restrict
        route_mark
        route_helper handle at [⟨"s57", layer⟩] over F, G
        intro values
        cases_type* Values
        route_mark
        route_helper handle at [⟨"s57", layer⟩] over F, G
        intro values
        cases_type* Values
        route_mark
        apply Routed.letOp (middle := [⟨"s57", layer⟩])
        · simp only [participantMeaningWithOn, protocolOperationWithOn, Operands.eval,
            Values.get, Environment.prepend, Environment.push, Regions.denote]
          apply Routed.repeatCaptured
          intro index carried
          cases_type* Values
          exact coefficient_callback_routed (F := F) (G := G) handle layer index _ _
        · intro values
          cases_type* Values
          route_mark
          route_helper handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          route_helper handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          route_helper handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          route_helper handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          route_helper handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          route_calculation handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          route_calculation handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          route_calculation handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          route_calculation handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          route_calculation handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          route_calculation handle at [⟨"s57", layer⟩] over F, G
          intro values
          cases_type* Values
          route_mark
          apply Routed.letOp (middle := [⟨"s57", layer⟩])
          · simp only [participantMeaningWithOn, protocolOperationWithOn]
            exact (Routed.guard (F := F) (G := G) _ _ _ _).bind fun _ => .done _ _
          · intro values
            cases_type* Values
            route_mark
            apply Routed.letOp (middle := [⟨"s57", layer⟩])
            · simp only [participantMeaningWithOn, protocolOperationWithOn,
                Participant.query, ProtocolContext.roles, RoleFamily.sequence,
                PIR.Process.interpret, Occurrence.actions, PIR.Process.bind]
              refine .query _ _ _ _ _ _ (line_draw handle layer .validator)
                (query_coordinates context _ _ _) (OccurrenceResolution.atCoordinates_request _ _)
                (fun value => ?_)
              exact .done _ _
            · intro values
              cases values with | cons challenge rest =>
                cases rest
                change Option F at challenge
                route_mark
                apply Routed.letOp (middle := [⟨"s57", layer⟩])
                · simp only [participantMeaningWithOn, protocolOperationWithOn,
                    Participant.exchange, ProtocolContext.roles, PIR.Process.interpret,
                    Occurrence.actions, PIR.Process.bind]
                  cases challenge with
                  | none => exact .halt _ _ _
                  | some challenge =>
                    refine .send _ _ _ _ _ _ _ (line_message handle layer .validator)
                      (message_coordinates context _ _ _ _) ?_
                    exact .done _ _
                · intro values
                  cases_type* Values
                  route_mark
                  route_restrict
                  route_mark
                  route_helper handle at [⟨"s57", layer⟩] over F, G
                  intro values
                  cases_type* Values
                  route_mark
                  route_helper handle at [⟨"s57", layer⟩] over F, G
                  intro values
                  cases_type* Values
                  route_mark
                  route_helper handle at [⟨"s57", layer⟩] over F, G
                  intro values
                  cases_type* Values
                  route_mark
                  route_helper handle at [⟨"s57", layer⟩] over F, G
                  intro values
                  exact .done _ _

end ZkcSecurity.Realizations.Gkr.OccurrenceRouting
