module

public import ZkcSecurityExamples.Sumcheck.SourceRootCost
public import ZkcSecurity.Bindings.Transcript.DomainSourceReading

@[expose] public section

/-! The mathematical source installation supplies support for the existing
nominal lossless presentation, through all typed attacker replies. This is
local source support; structural artifact alignment and root receipts are external. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceLossless
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration SourceRootProperties
open SumcheckSourceSelections hiding field
open ZkcSecurity.FiatShamir
open Zkc.Construction
attribute [local implicit_reducible] NormalForm.InputPattern.scope SourceRootReference.pattern

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame : Type}

omit fieldLaw in
theorem reference_data (ctx : ProtocolContext) (point : List (model.Field field))
    (scalar : model.Field field) (handle : Nat) :
    PIR.OperationSupport DomainSourceReading.DataOperation
      (SumcheckReferenceInstallation.reference model ctx (some handle) (some point) (some scalar)) := by
  refine ⟨rfl,fun lo => ⟨rfl,fun hi => ?_⟩⟩
  by_cases checked : scalar = lo+hi
  · simp only [checked,↓reduceIte]
    exact ⟨trivial,fun _ => ⟨trivial,fun _ => trivial⟩⟩
  · simp only [checked,↓reduceIte,PIR.OperationSupport]

variable (selection : Selection) (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2)
  (handle : Nat)
include distinct

theorem step_data {n : Nat} (index : Nat) (reference : PrefixState (model.Field field) Frame (n+1)) :
    PIR.OperationSupport DomainSourceReading.DataOperation
      (step model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
        ctx handle (encode model index reference)) := by
  have roundData : PIR.OperationSupport DomainSourceReading.DataOperation
      (roundStep model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
        ctx handle (encode model index reference)) := by
    rw [round_reference model _ (source selection).payload.linked (roundBodies selection) _ ctx distinct handle]
    exact (reference_data model ctx reference.point reference.scalar handle).bind _ (fun _ => trivial)
  change PIR.OperationSupport DomainSourceReading.DataOperation ((.call
    (Occurrence.Action.enter ⟨repeatSite ctx, index⟩) (fun _ =>
    (roundStep model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
      ctx handle (encode model index reference)).bind _)) : PIR.Process (Occurrence.signature model.toCarriers) _)
  exact ⟨trivial,fun _ => roundData.bind _ (fun _ => ⟨trivial,fun _ => trivial⟩)⟩

theorem repeat_data (original : List (model.Field field)) (callerFrame : Frame) :
    ∀ count (runtime : Runtime model Frame), represented model original callerFrame count runtime →
      PIR.OperationSupport DomainSourceReading.DataOperation
        (PIR.repeatN count (step model (source selection).payload.definitions
          (Occurrence.table model (source selection).payload) ctx handle) runtime) := by
  intro count
  induction count with
  | zero => intros; trivial
  | succ count ih =>
    intro runtime valid
    have supported : PIR.OperationSupport DomainSourceReading.DataOperation
        (step model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
          ctx handle runtime) := by
      obtain ⟨reference,_,_,encoded⟩ := valid
      rw [encoded]
      exact step_data model selection ctx distinct handle runtime.index reference
    exact supported.bind_framed
      (frame_contract (E := Unit) model _ (source selection).payload.linked (roundBodies selection)
        _ ctx distinct handle original callerFrame count runtime valid) _ ih

omit distinct fieldLaw in
theorem terminal_data (original : List (model.Field field))
    (returned : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs) :
    PIR.OperationSupport DomainSourceReading.DataOperation (terminalCheck model selection original returned) := by
  change PIR.OperationSupport _ ((Participant.owned _ _ _ _).bind _)
  refine PIR.OperationSupport.bind ?_ _ ?_
  · exact ZkcSecurity.Obligations.SourcePure.owned_support model _ _ 1 1 _ _
  · intro; trivial

omit ctx distinct in
theorem one_data (site : String) (original : List (model.Field field))
    (count : Nat) (scalar : model.Field field) (callerFrame : Frame)
    (shape : original.length = 2^count) (bounded : count ≤ maximum selection) :
    PIR.OperationSupport DomainSourceReading.DataOperation
      (SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle)) := by
  rw [one_reduction model selection site original count handle scalar callerFrame shape]
  apply PIR.OperationSupport.bind (source := reduction model _ _ _ _ _ _ _) _ _
    (fun returned => terminal_data model selection original returned.1)
  change PIR.OperationSupport _ (reduction model _ _ (context site) _ _ _ _)
  rw [reduction_equation model _ (source selection).payload.linked (roundBodies selection)
    _ (context site) (context_distinct site) handle (SumcheckReductionReference.actual_bodies model selection)
    (maximum selection) count bounded]
  exact (repeat_data model selection (context site) (context_distinct site) handle original callerFrame count
    (encode model 0 (PrefixState.initial original count scalar callerFrame shape)) ⟨_,rfl,rfl,rfl⟩).bind _ (fun _ => trivial)

omit ctx distinct in
theorem small_data (original : List (model.Field field)) (count : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count) (bounded : count ≤ maximum .small) :
    PIR.OperationSupport DomainSourceReading.DataOperation
      (Occurrence.participant model (source .small) 1 (SourceRootReference.rootInputs model .small
        (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil)))))) := by
  let args : NormalForm.Binders model (SourceRootReference.pattern .small).scope :=
    .cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil)))
  change PIR.OperationSupport _ (Occurrence.participant model (source .small) 1
    (SourceRootReference.rootInputs model .small args))
  rw [SourceRootReference.actual_reference model .small args]
  dsimp only [args]
  exact (one_data model .small handle "label_726564756365" original count scalar callerFrame shape bounded).bind _
    (fun _ => trivial)

omit ctx distinct in
theorem two_data (left right : List (model.Field field)) (count : Nat) (a b : model.Field field)
    (callerFrame : Frame) (leftShape : left.length = 2^count) (rightShape : right.length = 2^count)
    (bounded : count ≤ maximum .twoSums) :
    PIR.OperationSupport DomainSourceReading.DataOperation
      (Occurrence.participant model (source .twoSums) 1 (SourceRootReference.rootInputs model .twoSums
        (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
          (.cons (some count) (.cons (some handle) .nil)))))))) := by
  let args : NormalForm.Binders model (SourceRootReference.pattern .twoSums).scope :=
    .cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
      (.cons (some count) (.cons (some handle) .nil)))))
  change PIR.OperationSupport _ (Occurrence.participant model (source .twoSums) 1
    (SourceRootReference.rootInputs model .twoSums args))
  rw [SourceRootReference.actual_reference model .twoSums args]
  dsimp only [args]
  apply (one_data model .twoSums handle "label_6c656674" left count a callerFrame leftShape bounded).bind
  intro _
  apply (one_data model .twoSums handle "label_7269676874" right count b callerFrame rightShape bounded).bind
  intro _
  refine PIR.OperationSupport.bind ?_ _ ?_
  · exact ZkcSecurity.Obligations.SourcePure.components_support model _ _ _ _
  · intro; trivial

omit ctx distinct handle fieldLaw in
/-- The same existing lossless adapter consumes either actual-source support
certificate. Inputs stay abstract here to avoid reducing a generated source
when applying its dependent support certificate. Routing coverage and root
receipts remain separate obligations. -/
theorem root_lossless (selection : Selection)
    (inputs : Values (Component model.Value) (source selection).payload.entry.inputs)
    (data : PIR.OperationSupport DomainSourceReading.DataOperation
      (Occurrence.participant model (source selection) 1 inputs))
    (routing : Zkc.Construction.Original.Routing)
    (initial : Zkc.Construction.Original.State model.toCarriers) :
    ZkcSecurity.FiatShamir.Original.LosslessOn (NominalDomain.interface (carriers := model.toCarriers))
      (DomainSourceReading.presentation routing
        (Occurrence.participant model (source selection) 1 inputs) initial) :=
  DomainSourceReading.presentation_lossless model routing _ data initial

#print axioms small_data
#print axioms two_data
#print axioms root_lossless
end ZkcSecurity.Realizations.Sumcheck.SourceLossless
