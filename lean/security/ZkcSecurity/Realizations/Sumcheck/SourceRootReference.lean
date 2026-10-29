module

public import ZkcSecurity.Realizations.Sumcheck.SourceFamilySelections
public import ZkcSecurity.Realizations.Sumcheck.SourceFamilyComposition
public meta import ZkcTools.StructuredSource.NormalizedRoot

@[expose] public section

/-! Retained source selections contain checked data only. Normalizer transport,
component factoring and its proof production are shared with fresh clients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceRootReference
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcExamples.Structured SumcheckSourceSelections
open ZkcSecurity.Source

def pattern (selection : Selection) : InputPattern (source selection).payload.entry.inputs :=
  NormalizedRoot.pattern (source selection) 1

def signature (selection : Selection) :=
  SourceFamily.validatorSignature (SourceFamilySelections.installed selection)

def reductionPattern := SourceFamily.validatorPattern

def reductionSignature (selection : Selection) :=
  SourceFamily.reductionSignature (SourceFamilySelections.installed selection).reductionName

structure Client (selection : Selection) where
  root : NormalizedRoot.CheckedOn (source selection) 1 (signature selection) (pattern selection)
  composition : ∀ (model : DomainModel) (args : Binders model (pattern selection).scope),
    NormalizedRoot.Composed root model args
      (SourceFamily.validatorResults (SourceFamilySelections.installed selection) model)
      (SourceFamily.validatorCallees (SourceFamilySelections.installed selection) model)

noncomputable def smallRoot : NormalizedRoot.CheckedOn
    (source .small) 1 (signature .small) (pattern .small) := by
  derive_normalized_source_root

noncomputable def smallReference (model : DomainModel) (args : Binders model (pattern .small).scope) :=
  source_composition (NormalizedRoot.process smallRoot model args
    (SourceFamily.validatorResults (SourceFamilySelections.installed .small) model)
    (SourceFamily.validatorCallees (SourceFamilySelections.installed .small) model))
  components [fun site raw scalar count service => SourceFamily.one (SourceFamilySelections.installed .small) model {} site raw scalar count service]
  atoms [Participant.owned, invoke, SumcheckReductionReference.reference]

theorem smallPresentation (model : DomainModel) (args : Binders model (pattern .small).scope) :
    NormalizedRoot.process smallRoot model args
      (SourceFamily.validatorResults (SourceFamilySelections.installed .small) model)
      (SourceFamily.validatorCallees (SourceFamilySelections.installed .small) model) =
      smallReference model args := by
  source_composition_equation atoms [Participant.owned, invoke, SumcheckReductionReference.reference]

noncomputable def small : Client .small where
  root := smallRoot
  composition model args := ⟨smallReference model args, smallPresentation model args⟩

noncomputable def twoSumsRoot : NormalizedRoot.CheckedOn
    (source .twoSums) 1 (signature .twoSums) (pattern .twoSums) := by
  derive_normalized_source_root

noncomputable def twoSumsReference (model : DomainModel) (args : Binders model (pattern .twoSums).scope) :=
  source_composition (NormalizedRoot.process twoSumsRoot model args
    (SourceFamily.validatorResults (SourceFamilySelections.installed .twoSums) model)
    (SourceFamily.validatorCallees (SourceFamilySelections.installed .twoSums) model))
  components [fun site raw scalar count service => SourceFamily.one (SourceFamilySelections.installed .twoSums) model {} site raw scalar count service]
  atoms [Participant.owned, invoke, SumcheckReductionReference.reference]

theorem twoSumsPresentation (model : DomainModel) (args : Binders model (pattern .twoSums).scope) :
    NormalizedRoot.process twoSumsRoot model args
      (SourceFamily.validatorResults (SourceFamilySelections.installed .twoSums) model)
      (SourceFamily.validatorCallees (SourceFamilySelections.installed .twoSums) model) =
      twoSumsReference model args := by
  source_composition_equation atoms [Participant.owned, invoke, SumcheckReductionReference.reference]

noncomputable def twoSums : Client .twoSums where
  root := twoSumsRoot
  composition model args := ⟨twoSumsReference model args, twoSumsPresentation model args⟩

/-- Selection chooses already checked source data; no correctness theorem
branches on the selection or on a protocol name. -/
def client : (selection : Selection) → Client selection
  | .small => small
  | .twoSums => twoSums

variable (model : DomainModel)

def rootInputs (selection : Selection) (args : Binders model (pattern selection).scope) :=
  NormalizedRoot.inputsOn model (pattern selection) args

def reference (selection : Selection) (args : Binders model (pattern selection).scope) :=
  ((client selection).composition model args).presented

theorem actual_reference (selection : Selection) (args : Binders model (pattern selection).scope) :
    Occurrence.participant model (source selection) 1 (rootInputs model selection args) =
      reference model selection args :=
  (NormalizedRoot.equation (client selection).root model args
    (SourceFamily.validatorResults (SourceFamilySelections.installed selection) model)
    (SourceFamily.validatorCallees (SourceFamilySelections.installed selection) model)
    (fun entry => Fin.elim0 entry)
    (SourceFamily.validatorCallees_hold (SourceFamilySelections.installed selection) model _)).trans
      ((client selection).composition model args).equation

def reductionAssociation (selection : Selection) :=
  (SourceFamilySelections.installed selection).reduction

def one (selection : Selection) (ctx : ProtocolContext) (site : String)
    (raw : Option (List (model.Field SumcheckReferenceInstallation.field)))
    (scalar : Option (model.Field SumcheckReferenceInstallation.field)) (count service : Option Nat) :=
  SourceFamily.one (SourceFamilySelections.installed selection) model ctx site raw scalar count service

end ZkcSecurity.Realizations.Sumcheck.SourceRootReference
