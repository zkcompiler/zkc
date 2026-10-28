module

public import ZkcExamples.Structured.SumcheckSourceSelections
public import Zkc.Source.Structured.DomainProtocolLinking
public import Zkc.Construction.ConnectionLibrary

@[expose] public section

/-! Actual root syntax selections for the nominal mathematical consumers.
Local helpers remain shared calls and the reduction remains a shared callee.
This is a source occurrence normal form, with no artifact or receipt claims. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Families.Sumcheck.SourceRootReference
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcExamples.Structured SumcheckSourceSelections

def reductionName : Selection → String
  | .small => Generated.Bindings.SmallSumcheckInputs.protocol0Signature.name
  | .twoSums => Generated.Bindings.TwoSumsInputs.protocol0Signature.name

def reductionSignature (selection : Selection) : ProtocolSignature :=
  ⟨reductionName selection, ["role00000000", "role00000001"], SumcheckVerifierBodies.reduceInputs,
    SumcheckVerifierBodies.reduceOutputs, [[0],[0],[0],[1],[1],[0,1],[1]], [[0],[0],[0],[0],[1],[1]]⟩

attribute [local implicit_reducible] reductionSignature

def reductionPattern : InputPattern SumcheckVerifierBodies.reduceInputs :=
  .cons .absent (.cons .absent (.cons .absent (.cons .optional
    (.cons .optional (.cons .optional (.cons .optional .nil))))))

def signature (selection : Selection) : Signature :=
  ⟨[], false, true, [Generated.Bindings.SmallSumcheckInputs.helper9Helper,
    Generated.Bindings.SmallSumcheckInputs.helper33Helper, Generated.Bindings.TwoSumsInputs.helper25Helper],
    [⟨reductionSignature selection, 1, reductionPattern, [none,none,none,none]⟩]⟩

def pattern (selection : Selection) : InputPattern (source selection).payload.entry.inputs :=
  match selection with
  | .small => .cons .optional (.cons .optional (.cons .optional (.cons .optional .nil)))
  | .twoSums => .cons .optional (.cons .optional (.cons .optional (.cons .optional
      (.cons .optional (.cons .optional .nil)))))

noncomputable def form (selection : Selection) :
    Form (signature selection).laws (signature selection).callees (pattern selection).scope
      (source selection).payload.entry.outputs :=
  match normalize (signature selection) (source selection).payload.entry.body 1 2 (pattern selection) with
  | .ok value => value
  | .error _ => .halt .refused

theorem normalized (selection : Selection) :
    normalize (signature selection) (source selection).payload.entry.body 1 2 (pattern selection) =
      .ok (form selection) := by
  cases selection <;> kernel_rfl

theorem matched (selection : Selection) : (form selection).CallsMatch := by
  cases selection <;> kernel_rfl

variable (model : DomainModel)

noncomputable def reductionDefinition (selection : Selection) : CheckedProtocol :=
  (source selection).payload.protocols[0]'(by cases selection <;> decide +kernel)

theorem reduction_member (selection : Selection) :
    reductionDefinition selection ∈ (source selection).payload.protocols :=
  List.getElem_mem _

/-- The semantic body is shared; this proof only selects an admitted declaration. -/
theorem reduction_declared (selection : Selection) :
    (reductionDefinition selection).signature = reductionSignature selection ∧
    (reductionDefinition selection).body.erase =
      (SumcheckVerifierBodies.reduceBody (maximum selection)).erase := by
  cases selection <;> constructor <;> kernel_rfl

def reductionBinders (point : Option (List (model.Field SumcheckReferenceInstallation.field)))
    (scalar : Option (model.Field SumcheckReferenceInstallation.field)) (count service : Option Nat) :
    Binders model reductionPattern.scope := .cons point (.cons scalar (.cons count (.cons service .nil)))

noncomputable def callees (selection : Selection) :
    CalleeProcesses model (signature selection).callees (Occurrence.signature model.toCarriers) :=
  fun entry => match entry with
  | ⟨0,_⟩ => fun ctx args =>
    SumcheckReductionReference.reference model (source selection).payload.definitions
      (Occurrence.table model (source selection).payload) (maximum selection) ctx
      (entryAt args .here) (entryAt args (.there .here))
      (entryAt args (.there (.there .here))) (entryAt args (.there (.there (.there .here))))
  | ⟨_+1, outside⟩ => absurd outside (by simp [signature])

theorem masked_fill (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (args : Binders model reductionPattern.scope)
    (others : Values (Component model.Value) reductionPattern.absentTypes) :
    maskValues (ctx.roles 1) (ctx.mapScopes [[0],[0],[0],[1],[1],[0,1],[1]])
      (reductionPattern.fill model args others) =
      SumcheckReductionReference.pattern.environment model args := by
  exact (Zkc.Construction.ConnectionLibrary.mask_context distinct _ (by decide +kernel) _).trans
    (Zkc.Construction.ConnectionLibrary.mask_fill model 1 reductionPattern _
      (by decide +kernel) args others)

theorem callee_body (selection : Selection) (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) (args : Binders model reductionPattern.scope)
    (others : Values (Component model.Value) reductionPattern.absentTypes) :
    (SumcheckVerifierBodies.reduceBody (maximum selection)).denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions
        (SumcheckReferenceInstallation.tables model (source selection).payload.definitions)
        (ctx.roles 1) (Occurrence.table model (source selection).payload) ctx Occurrence.iterations)
      (maskValues (ctx.roles 1) (ctx.mapScopes [[0],[0],[0],[1],[1],[0,1],[1]])
        (reductionPattern.fill model args others)).get =
      (callees model selection) ⟨0,by simp [signature]⟩ ctx args := by
  rw [masked_fill model ctx distinct]
  match args with
  | .cons point (.cons scalar (.cons count (.cons service .nil))) =>
    exact SumcheckReductionReference.body_reference model _ (source selection).payload.linked
      (SumcheckReductionReference.actual_bodies model selection) _ _
      ctx distinct point scalar count service

theorem reduction_invoke (selection : Selection) (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) (args : Binders model reductionPattern.scope)
    (others : Values (Component model.Value) reductionPattern.absentTypes) :
    invokeProtocol (Occurrence.table model (source selection).payload) (reductionSignature selection)
      ctx (ctx.roles 1) (reductionPattern.fill model args others) =
      ((callees model selection) ⟨0,by simp [signature]⟩ ctx args).bind fun out =>
        .done (staticMask 1 out (reductionSignature selection).outputScopes
          (Operands.identity (reductionSignature selection).outputs)) := by
  have declared := Occurrence.invoke_body model (source selection).payload (reductionDefinition selection)
    (reduction_member selection) ctx (ctx.roles 1)
  have body := congrArg (fun process => process.bind (fun returned => PIR.Process.done
    (maskValues (ctx.roles 1) (ctx.mapScopes (reductionSignature selection).outputScopes) returned)))
      (callee_body model selection ctx distinct args others)
  have masked : ((callees model selection) ⟨0,by simp [signature]⟩ ctx args).bind
      (fun out => PIR.Process.done
        (maskValues (ctx.roles 1) (ctx.mapScopes (reductionSignature selection).outputScopes) out)) =
      ((callees model selection) ⟨0,by simp [signature]⟩ ctx args).bind (fun out =>
        .done (staticMask 1 out (reductionSignature selection).outputScopes
          (Operands.identity (reductionSignature selection).outputs))) := by
    apply congrArg (PIR.Process.bind _)
    funext returned
    apply congrArg PIR.Process.done
    exact (Zkc.Construction.ConnectionLibrary.mask_context distinct
      (reductionSignature selection).outputScopes (by cases selection <;> decide +kernel) returned).trans
      (Zkc.Construction.ConnectionLibrary.staticMask_identity 1
        (reductionSignature selection).outputScopes returned).symm
  have installed := body.trans masked
  cases selection <;> exact (declared _).trans installed

theorem callees_hold (selection : Selection) {types : List Ty}
    (input : Values (Component model.Value) types) :
    CalleesHold (Occurrence.table model (source selection).payload) (callees model selection) input := by
  intro entry ctx args others _ distinct
  match entry with
  | ⟨0,_⟩ => exact reduction_invoke model selection ctx distinct args others
  | ⟨_+1,outside⟩ => exact absurd outside (by simp [signature])


def results (selection : Selection) : LawResults model (signature selection).laws :=
  ⟨fun entry => Fin.elim0 entry⟩

noncomputable def rootInputs (selection : Selection) (args : Binders model (pattern selection).scope) :=
  (pattern selection).environment model args

theorem root_mask (selection : Selection) (args : Binders model (pattern selection).scope) :
    maskValues 1 (source selection).payload.entry.inputScopes (rootInputs model selection args) =
      (pattern selection).environment model args := by
  cases selection <;>
    exact Zkc.Construction.ConnectionLibrary.mask_fill model 1 _ _ (by decide +kernel) args .nil


/-- Actual admitted roots, with their masks, shared nominal library and shared
reduction callee. This equality is derived from the local source installation. -/
theorem root_equation (selection : Selection) (args : Binders model (pattern selection).scope) :
    Occurrence.participant model (source selection) 1 (rootInputs model selection args) =
      ((form selection).denoteOn model Occurrence.actions
        (Occurrence.helpers model (source selection).payload) (results model selection) {}
        (runsAtOn model Occurrence.actions Occurrence.iterations
          (Occurrence.helpers model (source selection).payload)
          (Occurrence.table model (source selection).payload) {} 1)
        (callees model selection) args).bind fun returned =>
          .done (maskValues 1 (source selection).payload.entry.outputScopes returned) := by
  apply normalize_program_occurrence (source selection) (signature selection) 1
    (pattern selection) (form selection)
  · cases selection <;> kernel_rfl
  · exact matched selection
  · intro index _ different
    exact different
  · exact root_mask model selection args
  · intro entry
    exact Fin.elim0 entry
  · exact callees_hold model selection _


/-- A single source-level use of the shared reduction, between its nominal
initial and terminal helper calls. Optional inputs and all stops are preserved. -/
def one (selection : Selection) (ctx : ProtocolContext) (site : String)
    (raw : Option (List (model.Field SumcheckReferenceInstallation.field)))
    (scalar : Option (model.Field SumcheckReferenceInstallation.field)) (count service : Option Nat) :=
  (Participant.owned (ctx.roles 1) (ctx.roles 1)
    (invoke (SumcheckReferenceInstallation.tables model (source selection).payload.definitions).closed
      Generated.Bindings.SmallSumcheckInputs.helper9Helper) (.cons scalar .nil)).bind fun initial =>
  (SumcheckReductionReference.reference model (source selection).payload.definitions
    (Occurrence.table model (source selection).payload) (maximum selection) (ctx.enter site [0,1])
    (initial.get .here) (initial.get (.there .here)) count service).bind fun reduced =>
  (Participant.owned (ctx.roles 1) (ctx.roles 1)
    (invoke (SumcheckReferenceInstallation.tables model (source selection).payload.definitions).closed
      Generated.Bindings.SmallSumcheckInputs.helper33Helper)
    (.cons raw (.cons (reduced.get (.there (.there (.there (.there .here)))))
      (.cons (reduced.get (.there (.there (.there (.there (.there .here)))))) .nil)))).bind fun checked =>
  PIR.Process.done (checked.get .here)

def reference (selection : Selection) (args : Binders model (pattern selection).scope) :
    PIR.Process (Occurrence.signature model.toCarriers)
      (Values (Component model.Value) (source selection).payload.entry.outputs) :=
  match selection, args with
  | .small, .cons raw (.cons scalar (.cons count (.cons service .nil))) =>
    (one model .small {} "label_726564756365" raw scalar count service).bind fun accepted =>
      .done (.cons accepted .nil : Values (Component model.Value) [.boolean])
  | .twoSums, .cons left (.cons right (.cons a (.cons b (.cons count (.cons service .nil))))) =>
    (one model .twoSums {} "label_6c656674" left a count service).bind fun leftAccepted =>
    (one model .twoSums {} "label_7269676874" right b count service).bind fun rightAccepted =>
    (invoke (SumcheckReferenceInstallation.tables model (source .twoSums).payload.definitions).components
        Generated.Bindings.TwoSumsInputs.helper25Helper
      (.cons leftAccepted (.cons rightAccepted .nil))).bind fun accepted =>
        .done (.cons (accepted.get .here) .nil : Values (Component model.Value) [.boolean])

theorem presentation (selection : Selection) (args : Binders model (pattern selection).scope) :
    ((form selection).denoteOn model Occurrence.actions
        (Occurrence.helpers model (source selection).payload) (results model selection) {}
        (runsAtOn model Occurrence.actions Occurrence.iterations
          (Occurrence.helpers model (source selection).payload)
          (Occurrence.table model (source selection).payload) {} 1)
        (callees model selection) args).bind (fun returned =>
          .done (maskValues 1 (source selection).payload.entry.outputScopes returned)) =
      reference model selection args := by
  cases selection
  · match args with
    | .cons raw (.cons scalar (.cons count (.cons service .nil))) =>
      dsimp only [reference, one]
      simp only [PIR.Process.bind_assoc, PIR.Process.bind]
      change ((_ : PIR.Process _ _).bind _).bind _ = _
      rw [PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext initial
      change ((_ : PIR.Process _ _).bind _).bind _ = _
      rw [PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext reduced
      change ((_ : PIR.Process _ _).bind _).bind _ = _
      rw [PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext checked
      rfl
  · match args with
    | .cons left (.cons right (.cons a (.cons b (.cons count (.cons service .nil))))) =>
      dsimp only [reference, one]
      simp only [PIR.Process.bind_assoc, PIR.Process.bind]
      change ((_ : PIR.Process _ _).bind _).bind _ = _
      rw [PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext leftInitial
      change ((_ : PIR.Process _ _).bind _).bind _ = _
      rw [PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext leftReduced
      change ((_ : PIR.Process _ _).bind _).bind _ = _
      rw [PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext leftChecked
      change ((_ : PIR.Process _ _).bind _).bind _ = _
      rw [PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext rightInitial
      change ((_ : PIR.Process _ _).bind _).bind _ = _
      rw [PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext rightReduced
      change ((_ : PIR.Process _ _).bind _).bind _ = _
      rw [PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext rightChecked
      change ((_ : PIR.Process _ _).bind _).bind _ = _
      rw [PIR.Process.bind_assoc]
      apply congrArg (PIR.Process.bind _)
      funext accepted
      rfl

theorem actual_reference (selection : Selection) (args : Binders model (pattern selection).scope) :
    Occurrence.participant model (source selection) 1 (rootInputs model selection args) =
      reference model selection args :=
  (root_equation model selection args).trans (presentation model selection args)

end ZkcSecurity.Families.Sumcheck.SourceRootReference
