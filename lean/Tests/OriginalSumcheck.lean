import Zkc.Construction.OriginalCorrespondence
import Zkc.Protocols.Sumcheck.Source.Library
import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckSumcheck
import ZkcExamples.Structured.Generated.Bindings.TwoSumsSumcheck

/-! All-response laws for the actual admitted Sumcheck round and repeat.
This module does not claim a SmallSumcheck/TwoSums artifact certificate. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 400000
noncomputable section
namespace Tests.OriginalSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction.Original
open ZkcExamples.Structured

private abbrev round (model : DomainModel) (payload : UnitPayload)
    (context : ProtocolContext) (self : Nat) :
    RegionFunction (Component model.Value) (Occurrence.signature model.toCarriers)
      (.index :: (SumcheckVerifierBodies.repeatState ++ [.service "random.bls12-381.fr/0"]),
        SumcheckVerifierBodies.repeatState) :=
  fun args => SumcheckVerifierBodies.roundBody.denote
    (participantMeaningWithOn model (.silent _) Occurrence.actions
      (payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩)
      self (Occurrence.table model payload) context Occurrence.iterations) args.get

-- The shared original-library proof supplies the real round equation. Its
-- source identity comes from the admitted body; no compiled round is decoded.


-- Both retained roots select exactly this original library round. TwoSums has
-- a different repeat maximum and two call occurrences, not a new family body.
example :
    ZkcExamples.Structured.Generated.Bindings.SmallSumcheckCallbacks.protocol0Role1Callback0Body =
      SumcheckVerifierBodies.roundBody :=
  ZkcExamples.Structured.Generated.Bindings.SmallSumcheckSumcheck.protocol0Role1Callback0_body_template
example :
    ZkcExamples.Structured.Generated.Bindings.TwoSumsCallbacks.protocol0Role1Callback0Body =
      SumcheckVerifierBodies.roundBody :=
  ZkcExamples.Structured.Generated.Bindings.TwoSumsSumcheck.protocol0Role1Callback0_body_template

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private theorem round_original (payload : UnitPayload) (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G))
      (.index :: (SumcheckVerifierBodies.repeatState ++ [.service "random.bls12-381.fr/0"]))) :
    round (ringModel F G) payload context self args =
      OriginalSumcheckLibrary.round payload context self args := by
  have tables : (OriginalSumcheckLibrary.helpers (F := F) (G := G) payload).toOn =
      payload.definitions.foldl
        (Evaluation.ComponentTablesOn.extend (ringModel F G)
          (.silent (Occurrence.signature (uniformCarriers F G)))) ⟨[], []⟩ :=
    Evaluation.ComponentTables.fold_toOn (.silent _) payload.definitions ⟨[], []⟩
  unfold round
  rw [← tables]
  exact OriginalSumcheckLibrary.round_on payload context self _ _ args

/-- The literal source round constructs its real calculated guard, query,
delivery, append and interpolation, with every optional state and typed reply.
The history and frame state belongs to the nominal construction, not the
uniform source arithmetic presentation. -/
theorem verifier_round_constructed (payload : UnitPayload)
    (bodies : SumcheckVerifierHelpers.Bodies payload.definitions)
    (routing : Routing) (context : ProtocolContext) (self : Nat)
    (role : self = context.roles 1) (separate : context.roles 0 ≠ self)
    (index : Nat) (service : Option Nat) (point : Option (List F)) (claim : Option F)
    (state : State (uniformCarriers F G)) :
    fold routing (round (ringModel F G) payload context self (.cons (some index)
      ((SumcheckVerifierLaws.embedV (G := G) (point, claim)).append (.cons service .nil)))) state =
      ((SumcheckVerifierLaws.roundPlain (G := G) context service (point, claim)).interpretState
        (fun operation current => operations routing (.action operation) current) state).bind
        (fun (result, final) => .done (SumcheckVerifierLaws.embedV result, final)) := by
  have source := (round_original (F := F) (G := G) payload context self _).trans
    (OriginalSumcheckLibrary.round_verifier payload bodies context self role separate
      index service point claim)
  have equation := congrArg (fun process => fold routing process state) source
  refine equation.trans ?_
  change fold routing (((SumcheckVerifierLaws.roundPlain (G := G) context service (point, claim)).interpret
    Occurrence.actions).bind fun result => .done (SumcheckVerifierLaws.embedV result)) state = _
  rw [fold_bind, fold_actions]
  rfl

/-- A separate producer law retains the original sums/restriction calculations.
Its explicit source shape preconditions are not assumed for the validator. -/
theorem producer_round_constructed (payload : UnitPayload)
    (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (routing : Routing) (context : ProtocolContext) (self : Nat)
    (role : self = context.roles 0) (separate : context.roles 1 ≠ self)
    (index : Nat) (service : Option Nat) (value : SumcheckProverLaws.ProverState F)
    (shape : PrimitiveLibrary.HasShape value.1 value.2.1 value.2.2.1)
    (bound : value.1.length < indexLimit) (positive : 0 < value.2.1)
    (state : State (uniformCarriers F G)) :
    fold routing (round (ringModel F G) payload context self (.cons (some index)
      ((SumcheckProverLaws.embedP (G := G) value).append (.cons service .nil)))) state =
      ((SumcheckProverLaws.roundPresent (G := G) context value).interpretState
        (fun operation current => operations routing (.action operation) current) state).bind
        (fun (result, final) => .done (SumcheckProverLaws.embedP result, final)) := by
  have source := (round_original (F := F) (G := G) payload context self _).trans
    (OriginalSumcheckLibrary.round_producer payload bodies context self role separate
      index service value shape bound positive)
  have equation := congrArg (fun process => fold routing process state) source
  refine equation.trans ?_
  change fold routing (((SumcheckProverLaws.roundPresent (G := G) context value).interpret
    Occurrence.actions).bind fun result => .done (SumcheckProverLaws.embedP result)) state = _
  rw [fold_bind, fold_actions]
  rfl

/-- One reached real source iteration, with its actual qualified loop site
and index. A rejected guard or failed request never executes the closing frame
or any loop suffix. All optional carried state is retained in the six-slot ABI. -/
theorem verifier_step_constructed (payload : UnitPayload)
    (bodies : SumcheckVerifierHelpers.Bodies payload.definitions)
    (routing : Routing) (context : ProtocolContext) (self : Nat)
    (role : self = context.roles 1) (separate : context.roles 0 ≠ self)
    (maximum index : Nat) (service : Option Nat) (point : Option (List F)) (claim : Option F)
    (state : State (uniformCarriers F G)) :
    fold routing (Repeat.stepOn (SumcheckVerifierBodies.repeatSpec maximum) context self
      (SumcheckVerifierLaws.cap service) (round (ringModel F G) payload context self)
      (SumcheckVerifierLaws.embedV (G := G) (point, claim)) index Occurrence.iterations "s18") state =
      ((SumcheckVerifierLaws.roundPlain (G := G) context service (point, claim)).interpretState
        (fun operation current => operations routing (.action operation) current)
        { state with frames := state.frames ++ [({ site := qualifyProtocolSite context.applicationPrefix "s18", index := index } : Occurrence.Frame)] }).bind
        (fun (result, final) =>
          if final.frames.getLast? = some ({ site := qualifyProtocolSite context.applicationPrefix "s18", index := index } : Occurrence.Frame) then
            .done (SumcheckVerifierLaws.embedV result, { final with frames := final.frames.dropLast })
          else .halt .refused) := by
  simp only [Repeat.stepOn, SumcheckVerifierLaws.mask_embedV context self role maximum]
  rw [fold_bind, fold_within]
  simp only [SumcheckVerifierLaws.cap]
  rw [verifier_round_constructed (F := F) (G := G) payload bodies routing context self role separate
    index service point claim]
  change ((((SumcheckVerifierLaws.roundPlain (G := G) context service (point, claim)).interpretState
    (fun operation current => operations routing (.action operation) current)
    { state with frames := state.frames ++ [({ site := qualifyProtocolSite context.applicationPrefix "s18", index := index } : Occurrence.Frame)] }).bind
    (fun (result, final) => .done (SumcheckVerifierLaws.embedV (G := G) result, final))).bind
    (fun ((value, final) : Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState ×
        State (uniformCarriers F G)) =>
      if final.frames.getLast? = some ({ site := qualifyProtocolSite context.applicationPrefix "s18", index := index } : Occurrence.Frame) then
        .done (value, { final with frames := final.frames.dropLast })
      else .halt .refused)).bind
    (fun ((value, final) : Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState ×
        State (uniformCarriers F G)) => fold routing (.done (maskValues self
      (context.mapScopes (SumcheckVerifierBodies.repeatSpec maximum).stateScopes) value)) final) = _
  rw [PIR.Process.bind_assoc, PIR.Process.bind_assoc]
  congr 1
  funext result
  change ((if result.2.frames.getLast? = some
      ({ site := qualifyProtocolSite context.applicationPrefix "s18", index := index } : Occurrence.Frame) then
      PIR.Process.done (I := Zkc.Construction.Domain.effects (uniformCarriers F G))
        (SumcheckVerifierLaws.embedV (G := G) result.1,
          { result.2 with frames := result.2.frames.dropLast })
    else PIR.Process.halt .refused).bind
      (fun ((value, final) : Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState ×
          State (uniformCarriers F G)) =>
        .done (maskValues self (context.mapScopes (SumcheckVerifierBodies.repeatSpec maximum).stateScopes) value,
          final))) = _
  split
  · change PIR.Process.done (I := Zkc.Construction.Domain.effects (uniformCarriers F G))
      (maskValues self (context.mapScopes (SumcheckVerifierBodies.repeatSpec maximum).stateScopes)
        (SumcheckVerifierLaws.embedV (G := G) result.1),
        { result.2 with frames := result.2.frames.dropLast }) = _
    rw [SumcheckVerifierLaws.mask_embedV context self role maximum]
  · rfl

private def verifierStep (routing : Routing) (context : ProtocolContext) (service : Option Nat)
    (value : (Option (List F) × Option F) × State (uniformCarriers F G)) (index : Nat) :
    PIR.Process (Zkc.Construction.Domain.effects (uniformCarriers F G))
      ((Option (List F) × Option F) × State (uniformCarriers F G)) :=
  ((SumcheckVerifierLaws.roundPlain (G := G) context service value.1).interpretState
    (fun operation current => operations routing (.action operation) current)
    { value.2 with frames := value.2.frames ++ [⟨qualifyProtocolSite context.applicationPrefix "s18", index⟩] }).bind
      (fun (result, final) => .done (result, { final with frames := value.2.frames }))

private theorem verifier_step_embed (payload : UnitPayload)
    (bodies : SumcheckVerifierHelpers.Bodies payload.definitions)
    (routing : Routing) (context : ProtocolContext) (self : Nat)
    (role : self = context.roles 1) (separate : context.roles 0 ≠ self)
    (maximum index : Nat) (service : Option Nat)
    (value : (Option (List F) × Option F) × State (uniformCarriers F G)) :
    fold routing (Repeat.stepOn (SumcheckVerifierBodies.repeatSpec maximum) context self
      (SumcheckVerifierLaws.cap service) (round (ringModel F G) payload context self)
      (SumcheckVerifierLaws.embedV (G := G) value.1) index Occurrence.iterations "s18") value.2 =
      (verifierStep routing context service value index).bind
        (fun result => .done (SumcheckVerifierLaws.embedV result.1, result.2)) := by
  rw [verifier_step_constructed (F := F) (G := G) payload bodies routing context self role separate
    maximum index service value.1.1 value.1.2 value.2]
  unfold verifierStep
  rw [PIR.Process.bind_assoc]
  apply (actions_frames routing (SumcheckVerifierLaws.roundPlain (G := G) context service value.1)
    { value.2 with frames := value.2.frames ++ [⟨qualifyProtocolSite context.applicationPrefix "s18", index⟩] }).bind_congr
  intro result frames
  simp only [frames, List.getLast?_concat, ↓reduceIte, List.dropLast_concat, PIR.Process.bind]

/-- The actual original Sumcheck loop factors through its mathematical carried
state and reached construction state. Every qualified index and every arbitrary
reply is retained. Count admission is covered separately by repeat_original. -/
theorem verifier_loop_constructed (payload : UnitPayload)
    (bodies : SumcheckVerifierHelpers.Bodies payload.definitions)
    (routing : Routing) (context : ProtocolContext) (self : Nat)
    (role : self = context.roles 1) (separate : context.roles 0 ≠ self)
    (maximum : Nat) (service : Option Nat) (indices : List Nat)
    (value : (Option (List F) × Option F) × State (uniformCarriers F G)) :
    fold routing (Finite.fold (fun current index =>
      Repeat.stepOn (SumcheckVerifierBodies.repeatSpec maximum) context self
        (SumcheckVerifierLaws.cap service) (round (ringModel F G) payload context self)
        current index Occurrence.iterations "s18") indices (SumcheckVerifierLaws.embedV (G := G) value.1)) value.2 =
      (Finite.fold (verifierStep routing context service) indices value).bind
        (fun result => .done (SumcheckVerifierLaws.embedV result.1, result.2)) := by
  rw [fold_finite]
  exact finite_embed
    (fun (value : (Option (List F) × Option F) × State (uniformCarriers F G)) =>
      (SumcheckVerifierLaws.embedV (G := G) value.1, value.2))
    (verifierStep routing context service)
    (fun (current, state) index =>
      fold routing (Repeat.stepOn (SumcheckVerifierBodies.repeatSpec maximum) context self
        (SumcheckVerifierLaws.cap service) (round (ringModel F G) payload context self)
        current index Occurrence.iterations "s18") state)
    (fun value index => verifier_step_embed (F := F) (G := G) payload bodies routing context self role
      separate maximum index service value) indices value

/-- The real source loop, over arbitrary nominal models and all count/mask
branches. This instantiates the generic construction law at the actual round. -/
theorem repeat_original (model : DomainModel) (payload : UnitPayload)
    (routing : Routing) (context : ProtocolContext) (self maximum : Nat) (count : Option Nat)
    (initial : Values (Component model.Value) SumcheckVerifierBodies.repeatState)
    (captures : Values (Component model.Value) [.service "random.bls12-381.fr/0"])
    (state : State model.toCarriers) :
    fold routing (denoteRepeatOn (SumcheckVerifierBodies.repeatSpec maximum) context self count
      initial captures (round model payload context self) Occurrence.iterations "s18") state =
      (if ([0, 1].map context.roles).contains self then
        match count with
        | none => .halt .incomplete
        | some count =>
          if count ≤ maximum then
            Finite.fold (fun (value, current) index =>
              fold routing (Repeat.stepOn (SumcheckVerifierBodies.repeatSpec maximum) context self
                captures (round model payload context self) value index Occurrence.iterations "s18") current)
              (List.range count)
              (maskValues self (context.mapScopes (SumcheckVerifierBodies.repeatSpec maximum).stateScopes) initial, state)
          else .halt .refused
      else .done (Values.absent model.Value SumcheckVerifierBodies.repeatState, state)) :=
  fold_repeat (carriers := model.toCarriers) routing
    (SumcheckVerifierBodies.repeatSpec maximum) context self count initial captures
    (round model payload context self) "s18" state

/-- Complete entry to the real verifier repeat, including unavailable and
excessive counts. The six-slot optional source state is related to the carried
mathematical state before any iteration is reached. -/
theorem verifier_repeat_constructed (payload : UnitPayload)
    (bodies : SumcheckVerifierHelpers.Bodies payload.definitions)
    (routing : Routing) (context : ProtocolContext) (self : Nat)
    (role : self = context.roles 1) (separate : context.roles 0 ≠ self)
    (maximum : Nat) (count : Option Nat) (service : Option Nat)
    (value : (Option (List F) × Option F) × State (uniformCarriers F G)) :
    fold routing (denoteRepeatOn (SumcheckVerifierBodies.repeatSpec maximum) context self count
      (SumcheckVerifierLaws.embedV (G := G) value.1) (SumcheckVerifierLaws.cap service)
      (round (ringModel F G) payload context self) Occurrence.iterations "s18") value.2 =
      (match count with
      | none => .halt .incomplete
      | some count =>
          if count ≤ maximum then
            (Finite.fold (verifierStep routing context service) (List.range count) value).bind
              (fun result => .done (SumcheckVerifierLaws.embedV result.1, result.2))
          else .halt .refused) := by
  rw [repeat_original (ringModel F G) payload routing context self maximum count
    (SumcheckVerifierLaws.embedV (G := G) value.1) (SumcheckVerifierLaws.cap service) value.2]
  have active : ([0, 1].map context.roles).contains self = true := by simp [role]
  simp only [active, ↓reduceIte]
  cases count with
  | none => rfl
  | some count =>
      by_cases bound : count ≤ maximum
      · simp only [bound, ↓reduceIte, SumcheckVerifierLaws.mask_embedV context self role maximum]
        have loop := verifier_loop_constructed (F := F) (G := G) payload bodies routing context self
          role separate maximum service (List.range count) value
        rw [fold_finite] at loop
        exact loop
      · simp only [bound, ↓reduceIte]

#print axioms Tests.OriginalSumcheck.verifier_loop_constructed
#print axioms Tests.OriginalSumcheck.verifier_repeat_constructed
#print axioms Tests.OriginalSumcheck.producer_round_constructed
#print axioms Tests.OriginalSumcheck.repeat_original
end Tests.OriginalSumcheck
