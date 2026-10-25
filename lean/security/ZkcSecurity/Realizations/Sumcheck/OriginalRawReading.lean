module

public import ZkcSecurity.Realizations.Sumcheck.OriginalRawSource
public import ZkcSecurity.Realizations.Sumcheck.OriginalSecurity
public import ZkcSecurity.Families.Sumcheck.TableComponentExecutionLaws

@[expose] public section

/-! Exact original callback routing to a shape-free nominal process. Only the
pure nominal run, length, residual, and cost laws are owned by
TableComponent.Execution. No compiled round matcher, plan, offset binding,
or source connection structure supplies this presentation.
The source equations are OriginalRaw.source_step/source_reduce instead. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent

variable {F G : Type} [Field F] [DecidableEq F]

abbrev ConstructionState := Zkc.Construction.Original.State (uniformCarriers F G)

def nominal (state : State F) (construction : ConstructionState (F := F) (G := G)) :
    TableComponent.Execution.State F G := ⟨state.point, state.scalar, construction.history⟩

def unpack (state : TableComponent.Execution.State F G)
    (construction : ConstructionState (F := F) (G := G)) : State F × ConstructionState (F := F) (G := G) :=
  (⟨state.point, state.scalar⟩, { construction with history := state.history })

noncomputable def presentedRun (schedule : Nominal.Schedule "bls12-381.fr")
    (indices : List Nat) (state : State F) (construction : ConstructionState (F := F) (G := G)) :=
  (TableComponent.Execution.run "bls12-381.fr" schedule indices (nominal state construction)).bind
    (fun final => .done (unpack final construction))

set_option backward.isDefEq.respectTransparency false in
/-- Exact one-round reading at the actual source index. The full source state
and outer occurrence stack survive every successful continuation. -/
theorem step_bridge (routing : Zkc.Construction.Original.Routing)
    (context : Realizations.Sumcheck.Original.Context) (schedule : Nominal.Schedule "bls12-381.fr")
    (index : Nat) (state : State F) (construction : ConstructionState (F := F) (G := G))
    (routes : OriginalSecurity.Routes routing context schedule construction.frames) :
    DomainReduction.Bridge (Nominal.interface (G := G) "bls12-381.fr")
      (fun reached result => result.2.history = reached ∧ result.2.frames = construction.frames)
      construction.history
      (Zkc.Construction.Original.fold routing (step context index state) construction)
      ((TableComponent.Execution.run "bls12-381.fr" schedule [index] (nominal state construction)).bind
        (fun final => .done (unpack final construction))) := by
  have request := schedule.request index
  simp only [step, TableComponent.Execution.run, nominal,
    Zkc.Construction.Original.fold, PIR.Process.interpretState,
    Zkc.Construction.Original.operations, Zkc.Construction.Original.receive,
    Zkc.Construction.Original.query, Zkc.Construction.Original.send,
    Zkc.Construction.Original.record, routes.mode, routes.low, routes.high,
    routes.draw, routes.delivery, Domain.Payload.ofValue,
    PIR.Process.bind, PIR.Process.bind_assoc]
  constructor
  · apply DomainReduction.ReadingTo.receive (I := Nominal.signature F "bls12-381.fr")
      (.field "bls12-381.fr") _ _ _ _
      (.receive (schedule.low index)) _
      (.message (schedule.low index)) (Nominal.received "bls12-381.fr" _)
      (fun value => value) rfl (by intro payload; simpa using Nominal.received_message _ _ payload)
    intro payload low decoded
    have payloadEq : payload = .field "bls12-381.fr" low := by
      simpa only [Domain.Payload.ofValue, Option.some.injEq] using
        (Domain.Payload.ofValue_value decoded).symm
    subst payload
    apply DomainReduction.ReadingTo.observe
    apply DomainReduction.ReadingTo.receive (I := Nominal.signature F "bls12-381.fr")
      (.field "bls12-381.fr") _ _ _ _
      (.receive (schedule.high index)) _
      (.message (schedule.high index)) (Nominal.received "bls12-381.fr" _)
      (fun value => value) rfl (by intro payload; simpa using Nominal.received_message _ _ payload)
    intro payload high decoded
    have payloadEq : payload = .field "bls12-381.fr" high := by
      simpa only [Domain.Payload.ofValue, Option.some.injEq] using
        (Domain.Payload.ofValue_value decoded).symm
    subst payload
    apply DomainReduction.ReadingTo.observe
    by_cases passed : state.scalar = low + high
    · simp only [passed, ite_true, PIR.Process.interpretState, Zkc.Construction.Original.operations,
        Zkc.Construction.Original.query, Zkc.Construction.Original.send, routes.mode, routes.draw,
        routes.delivery, Zkc.Construction.Original.record, Domain.Payload.ofValue,
        Zkc.Construction.Original.queryField, request, ↓reduceDIte, PIR.Process.bind]
      apply DomainReduction.ReadingTo.query (I := Nominal.signature F "bls12-381.fr")
        _ _ _ (.query _ request) _ (DomainReduction.fieldReply request)
      · exact DomainReduction.drawRequest_of_request request
      · rfl
      · intro challenge
        apply DomainReduction.ReadingTo.observe
        apply DomainReduction.ReadingTo.absorbSend (I := Nominal.signature F "bls12-381.fr")
          (.deliver _ _) _ _ () rfl
        simp only [TableComponent.Execution.run, PIR.Process.bind, PIR.Process.interpretState, Zkc.Construction.Original.operations,
          List.getLast?_append, List.getLast?_cons, List.getLast?_nil, ↓reduceIte,
          List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]
        simpa [unpack, nominal, TableComponent.Execution.advance, TableComponent.Execution.finalHistory,
          TableComponent.Execution.receivedHistory, advance, List.append_assoc,
          DomainReduction.fieldReply, PIR.Process.bind] using
          (DomainReduction.ReadingTo.done (absorb := Nominal.interface (F := F) (G := G) "bls12-381.fr")
            _ _ (show _ ∧ _ from ⟨rfl, rfl⟩))
    · simp only [passed, ite_false, PIR.Process.interpretState, PIR.Process.bind]
      exact .halt _ .reject
  · apply DomainReduction.CoherentTo.receive
    intro low
    apply DomainReduction.CoherentTo.observe
    apply DomainReduction.CoherentTo.receive
    intro high
    apply DomainReduction.CoherentTo.observe
    by_cases passed : state.scalar = low + high
    · simp only [passed, ite_true, PIR.Process.interpretState, Zkc.Construction.Original.operations,
        Zkc.Construction.Original.query, Zkc.Construction.Original.send, routes.mode, routes.draw,
        routes.delivery, Zkc.Construction.Original.record, Domain.Payload.ofValue,
        Zkc.Construction.Original.queryField, request, ↓reduceDIte, PIR.Process.bind, List.append_assoc]
      apply DomainReduction.CoherentTo.query _ _ _
      · exact DomainReduction.drawRequest_of_request request
      · intro challenge
        apply DomainReduction.CoherentTo.observe
        simp only [TableComponent.Execution.run, PIR.Process.bind, PIR.Process.interpretState, Zkc.Construction.Original.operations,
          List.getLast?_append, List.getLast?_cons, List.getLast?_nil, ↓reduceIte,
          List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]
        simp [PIR.Process.bind, List.append_assoc]
        apply DomainReduction.CoherentTo.done
        exact ⟨rfl, rfl⟩
    · simp only [passed, ite_false, PIR.Process.interpretState, PIR.Process.bind]
      exact .halt _ .reject


/-- Compose the checked source callback at arbitrary indices and raw state.
The immutable occurrence stack and actual reached history remain explicit. -/
theorem run_bridge (routing : Zkc.Construction.Original.Routing)
    (context : Realizations.Sumcheck.Original.Context) (schedule : Nominal.Schedule "bls12-381.fr")
    (indices : List Nat) (state : State F) (construction : ConstructionState (F := F) (G := G))
    (routes : OriginalSecurity.Routes routing context schedule construction.frames) :
    DomainReduction.Bridge (Nominal.interface (G := G) "bls12-381.fr")
      (fun reached result => result.2.history = reached ∧ result.2.frames = construction.frames)
      construction.history (Zkc.Construction.Original.fold routing (run context indices state) construction)
      (presentedRun schedule indices state construction) := by
  induction indices generalizing state construction with
  | nil =>
    simp only [run, Zkc.Construction.Original.fold, PIR.Process.interpretState,
      presentedRun, TableComponent.Execution.run, PIR.Process.bind, unpack, nominal]
    exact .done _ _ ⟨rfl, rfl⟩
  | cons index rest ih =>
    rw [run, Zkc.Construction.Original.fold_bind]
    have continued := (step_bridge routing context schedule index state construction routes).bind
      (fun result => Zkc.Construction.Original.fold routing (run context rest result.1) result.2)
      (fun result => presentedRun schedule rest result.1 result.2)
      (PostNext := fun reached result =>
        result.2.history = reached ∧ result.2.frames = construction.frames) (by
        intro reached result preserved
        have nextRoutes : OriginalSecurity.Routes routing context schedule result.2.frames :=
          preserved.2 ▸ routes
        have tail := ih result.1 result.2 nextRoutes
        rw [preserved.1] at tail
        exact tail.weaken (fun reached result holds => ⟨holds.1, holds.2.trans preserved.2⟩))
    convert continued using 1
    simp only [presentedRun, TableComponent.Execution.run, PIR.Process.bind_assoc, PIR.Process.bind]
    congr 1
    funext low
    congr 1
    funext high
    split
    · simp only [PIR.Process.bind]
      congr 1
    · rfl

end ZkcSecurity.Realizations.Sumcheck.OriginalRaw
