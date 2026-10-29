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
namespace ZkcSecurity.Realizations.Sumcheck.SourceProducerRoot
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcExamples.Structured SumcheckSourceSelections
open ZkcSecurity.Source

def pattern (selection : Selection) : InputPattern (source selection).payload.entry.inputs :=
  match selection with
  | .small => .cons .present (.cons .absent (.cons .present (.cons .absent .nil)))
  | .twoSums => .cons .present (.cons .present (.cons .absent (.cons .absent
      (.cons .present (.cons .absent .nil)))))

def signature (selection : Selection) :=
  SourceFamily.producerSignature (SourceFamilySelections.installed selection)

def reductionPattern := SourceFamily.producerPattern

def reductionSignature (selection : Selection) :=
  SourceFamily.reductionSignature (SourceFamilySelections.installed selection).reductionName

structure Client (selection : Selection) where
  root : NormalizedRoot.CheckedOn (source selection) 0 (signature selection) (pattern selection)
  composition : ∀ (model : DomainModel) (args : Binders model (pattern selection).scope),
    NormalizedRoot.Composed root model args
      (SourceFamily.producerResults (SourceFamilySelections.installed selection) model)
      (SourceFamily.producerCallees (SourceFamilySelections.installed selection) model)

noncomputable def smallRoot : NormalizedRoot.CheckedOn
    (source .small) 0 (signature .small) (pattern .small) := by
  derive_normalized_source_root

noncomputable def smallReference (model : DomainModel) (args : Binders model (pattern .small).scope) :=
  source_composition (NormalizedRoot.process smallRoot model args
    (SourceFamily.producerResults (SourceFamilySelections.installed .small) model)
    (SourceFamily.producerCallees (SourceFamilySelections.installed .small) model))
  components [fun site raw count => SourceFamily.producerOne (SourceFamilySelections.installed .small) model site raw count]
  atoms [Participant.owned, invoke, SourceFamily.producerReduction]

theorem smallPresentation (model : DomainModel) (args : Binders model (pattern .small).scope) :
    NormalizedRoot.process smallRoot model args
      (SourceFamily.producerResults (SourceFamilySelections.installed .small) model)
      (SourceFamily.producerCallees (SourceFamilySelections.installed .small) model) =
      smallReference model args := by
  source_composition_equation atoms [Participant.owned, invoke, SourceFamily.producerReduction]

noncomputable def small : Client .small where
  root := smallRoot
  composition model args := ⟨smallReference model args, smallPresentation model args⟩

noncomputable def twoSumsRoot : NormalizedRoot.CheckedOn
    (source .twoSums) 0 (signature .twoSums) (pattern .twoSums) := by
  derive_normalized_source_root

noncomputable def twoSumsReference (model : DomainModel) (args : Binders model (pattern .twoSums).scope) :=
  source_composition (NormalizedRoot.process twoSumsRoot model args
    (SourceFamily.producerResults (SourceFamilySelections.installed .twoSums) model)
    (SourceFamily.producerCallees (SourceFamilySelections.installed .twoSums) model))
  components [fun site raw count => SourceFamily.producerOne (SourceFamilySelections.installed .twoSums) model site raw count]
  atoms [Participant.owned, invoke, SourceFamily.producerReduction]

theorem twoSumsPresentation (model : DomainModel) (args : Binders model (pattern .twoSums).scope) :
    NormalizedRoot.process twoSumsRoot model args
      (SourceFamily.producerResults (SourceFamilySelections.installed .twoSums) model)
      (SourceFamily.producerCallees (SourceFamilySelections.installed .twoSums) model) =
      twoSumsReference model args := by
  source_composition_equation atoms [Participant.owned, invoke, SourceFamily.producerReduction]

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
    Occurrence.participant model (source selection) 0 (rootInputs model selection args) =
      reference model selection args :=
  (NormalizedRoot.equation (client selection).root model args
    (SourceFamily.producerResults (SourceFamilySelections.installed selection) model)
    (SourceFamily.producerCallees (SourceFamilySelections.installed selection) model)
    (fun entry => Fin.elim0 entry)
    (SourceFamily.producerCallees_hold (SourceFamilySelections.installed selection) model _)).trans
      ((client selection).composition model args).equation

def one (selection : Selection) (site : String)
    (original : List (model.Field SumcheckReferenceInstallation.field)) (count : Nat) :=
  SourceFamily.producerOne (SourceFamilySelections.installed selection) model site original count

end ZkcSecurity.Realizations.Sumcheck.SourceProducerRoot
