module

public import Zkc.Applications.Security.Gkr.HonestHelpersReadbackGoals
public import Zkc.Program.Algorithms.ListReadback

public meta import Zkc.Tools.IR.StructuredSource.ReferenceInstallation

@[expose] public section

/-! The chosen representation scans a list with a default and a cursor. These
ordinary companions prove the complete generated goals, retaining failures and
all results. Structural expectations and ABI records come from the source. -/
namespace ZkcSecurity.Realizations.Gkr.HonestHelpers.ReadbackCompanion
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ReadbackGoals
open Zkc.Algorithms

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local implicit_reducible] Collection.type Collection.element

variable (model : DomainModel)

def zeroReference : PIR.Outcome (Zero.Output model) := .returned ⟨0⟩

theorem zero : Zero.Goal model (zeroReference model) (fun _ => True) := by
  intro table _
  simp [Zero.run, zeroReference, primitiveOutcome, PIR.Process.bind, Environment.prepend, Environment.push, Values.get]

noncomputable def zeroLaw := Zero.law model (zeroReference model) (fun _ => True) (zero model)

noncomputable def zeroWrapperLaw :=
  forward_reference% ZeroWrapper.body using (zeroLaw model)

def stepReference (current : model.Field scalarDomain) (index : Nat)
    (value : model.Field scalarDomain) (position : Nat) : PIR.Outcome (Step.Output model) :=
  match ListReadback.step indexLimit position (current, index) value with
  | .returned state => .returned ⟨state.1, state.2⟩
  | .stopped reason => .stopped reason

theorem step : Step.Goal model (stepReference model) (fun _ _ _ _ _ => True) := by
  intro table current index value position _
  by_cases equal : index = position
  · subst position
    by_cases small : index < indexLimit <;> by_cases next : index + 1 < indexLimit <;>
      simp [Step.run, stepReference, ListReadback.step, ListReadback.transition,
        Primitive.evaluateOn, checkedIndices, small, next,
        show 1 < indexLimit by decide +kernel, primitiveOutcome, PIR.Process.bind,
        Evaluation.invokeCallbackOn, Environment.prepend, Environment.push, Values.get]
  · by_cases small : index < indexLimit ∧ position < indexLimit
    · by_cases next : index + 1 < indexLimit <;>
        simp [Step.run, stepReference, ListReadback.step, ListReadback.transition,
          Primitive.evaluateOn, checkedIndices, small, small.1, small.2, next, equal,
          show 1 < indexLimit by decide +kernel, primitiveOutcome, PIR.Process.bind,
          Evaluation.invokeCallbackOn, Environment.prepend, Environment.push, Values.get]
    · simp [Step.run, stepReference, ListReadback.step, Primitive.evaluateOn, checkedIndices,
        small, show ¬ (index < indexLimit ∧ position < indexLimit ∧ index + 1 < indexLimit) from
          fun h => small ⟨h.1, h.2.1⟩, primitiveOutcome, PIR.Process.bind,
        Environment.prepend, Environment.push, Values.get]

noncomputable def stepLaw :=
  Step.law model (stepReference model) (fun _ _ _ _ _ => True) (step model)

noncomputable def callbackLaw :=
  forward_reference% Callback.body using (stepLaw model)

def scanReference (source : List (model.Field scalarDomain)) (current : model.Field scalarDomain)
    (index position : Nat) : PIR.Outcome (Scan.Output model) :=
  if source.length < indexLimit then
    match ListReadback.scan indexLimit position source current index with
    | .returned state => .returned ⟨state.1, state.2⟩
    | .stopped reason => .stopped reason
  else .stopped .exhausted

def scanCondition := fun table (_ : List (model.Field scalarDomain))
    (_ : model.Field scalarDomain) (_ _ : Nat) =>
  (callbackLaw model).Realizes (helper := GkrSourceBodies.helper30Helper) table

/-- Admission is checked before the scan; the shared fold law handles every
step outcome. The named state encoding is a source representation choice. -/
theorem scan : Scan.Goal model (scanReference model) (scanCondition model) := by
  intro table source current index position dependency
  simp only [Scan.run, Environment.prepend, Environment.push, Values.get, PIR.Process.bind_done]
  let encode : model.Field scalarDomain × Nat → Values model.Value foldSpec.state := fun state =>
    State.pack (Value := model.Value) { current := state.1, index := state.2 }
  by_cases bounded : source.length < indexLimit
  · have admitted : foldSpec.domain.admit (DomainArguments.pack (Value := model.Value) ⟨source⟩) =
        .returned (source.map fun value => Item.pack (Value := model.Value) ⟨value⟩) := by
      simp [foldSpec, GkrSourceLaws.fold?, GkrSourceBodies.helper95Body,
        DomainSpec.admit, DomainBody.admit, DomainNode.admit, Collection.values,
        DomainArguments.pack, Item.pack, Values.get, bounded, Finite.continueWith]
    have folded := Evaluation.denoteFoldOn_checked table foldSpec
      (DomainArguments.pack ⟨source⟩) (Captures.pack ⟨position⟩) source
      (fun value => Item.pack ⟨value⟩) encode (current, index) admitted
      (ListReadback.step indexLimit position) (by
        intro state value
        have call := dependency (Callback.Inputs.pack
          { current := state.1, index := state.2, value, source, position })
        change _ = primitiveOutcome ((callbackLaw model).reference _) at call
        change invoke table GkrSourceBodies.helper30Helper (Callback.Inputs.pack
          { current := state.1, index := state.2, value, source, position }) = _
        rw [call]
        change primitiveOutcome (Step.encodeOutcome model
          (stepReference model state.1 state.2 value position)) = _
        cases state with | mk current index =>
          cases outcome : ListReadback.step indexLimit position (current, index) value <;>
            simp [stepReference, outcome, Step.encodeOutcome, Step.encode,
              Finite.toProcess, primitiveOutcome, PIR.Process.bind, encode, State.pack])
    dsimp only [DomainArguments.pack, Captures.pack, Item.pack, encode, State.pack] at folded
    erw [folded]
    simp only [scanReference, bounded, ↓reduceIte]
    cases outcome : ListReadback.scan indexLimit position source current index <;>
      simp [ListReadback.scan] at outcome <;>
      simp [ListReadback.scan, outcome, Finite.toProcess, PIR.Process.bind,
        Environment.prepend, Environment.push, Values.get,
        encode, State.pack, Scan.decode, primitiveOutcome]
  · have exhausted : foldSpec.domain.admit (DomainArguments.pack (Value := model.Value) ⟨source⟩) =
        .stopped .exhausted := by
      simp [foldSpec, GkrSourceLaws.fold?, GkrSourceBodies.helper95Body,
        DomainSpec.admit, DomainBody.admit, DomainNode.admit, Collection.values,
        DomainArguments.pack, Item.pack, Values.get, bounded, Finite.continueWith]
    dsimp only [DomainArguments.pack] at exhausted
    simp only [Evaluation.denoteFoldOn, Values.split]
    erw [exhausted]
    simp [scanReference, bounded, Finite.admitThen, PIR.Process.bind, primitiveOutcome]

noncomputable def scanLaw := Scan.law model (scanReference model) (scanCondition model) (scan model)

noncomputable def wrapperLaw :=
  forward_reference% ScanWrapper.body using (scanLaw model)

def elementReference (source : List (model.Field scalarDomain)) (position : Nat) :
    PIR.Outcome (Element.Output model) :=
  match scanReference model source 0 0 position with
  | .returned result => .returned ⟨result.selected⟩
  | .stopped reason => .stopped reason

def elementCondition := fun table (_ : List (model.Field scalarDomain)) (_ : Nat) =>
  (zeroWrapperLaw model).Realizes (helper := GkrSourceBodies.helper87Helper) table ∧
  (wrapperLaw model).Realizes (helper := GkrSourceBodies.helper96Helper) table

theorem element : Element.Goal model (elementReference model) (elementCondition model) := by
  intro table source position dependencies
  have zeroCall := dependencies.1 (Zero.Inputs.pack (Value := model.Value) {})
  have scanCall := dependencies.2 (ScanWrapper.Inputs.pack
    { current := 0, index := 0, position, source })
  simp only [Element.run, Environment.prepend, Environment.push, Values.get, PIR.Process.bind_done]
  change invoke table GkrSourceBodies.helper87Helper .nil = .done (.cons 0 .nil) at zeroCall
  rw [zeroCall]
  simp only [zeroWrapperLaw, zeroLaw, Zero.law, zeroReference, Zero.encodeOutcome, Zero.encode,
    primitiveOutcome, PIR.Process.bind, Environment.prepend, Environment.push, Values.get,
    Primitive.evaluateOn, show 0 < indexLimit by decide +kernel, ↓reduceIte]
  change invoke table GkrSourceBodies.helper96Helper _ =
    primitiveOutcome (Scan.encodeOutcome model (scanReference model source 0 0 position)) at scanCall
  dsimp only [ScanWrapper.Inputs.pack] at scanCall
  rw [scanCall]
  simp only [elementReference]
  cases outcome : scanReference model source 0 0 position <;>
    simp [outcome, Scan.encodeOutcome, Scan.encode,
      primitiveOutcome, PIR.Process.bind, Element.decode,
      Environment.prepend, Environment.push, Values.get]

noncomputable def elementLaw :=
  Element.law model (elementReference model) (elementCondition model) (element model)

def afterReference (source : List (model.Field scalarDomain)) (position : Nat) :
    PIR.Outcome (After.Output model) :=
  if position + 1 < indexLimit then
    match elementReference model source (position + 1) with
    | .returned result => .returned ⟨result.value⟩
    | .stopped reason => .stopped reason
  else .stopped .refused

def afterCondition := fun table (_ : List (model.Field scalarDomain)) (_ : Nat) =>
  (elementLaw model).Realizes (helper := GkrSourceBodies.helper97Helper) table

theorem after : After.Goal model (afterReference model) (afterCondition model) := by
  intro table source position dependency
  by_cases bounded : position + 1 < indexLimit
  · have small : position < indexLimit := Nat.lt_trans (Nat.lt_succ_self position) bounded
    have call := dependency (Element.Inputs.pack { source, position := position + 1 })
    simp only [After.run, Primitive.evaluateOn, checkedIndices,
      show 1 < indexLimit by decide +kernel, small, bounded, and_self, ↓reduceIte,
      primitiveOutcome, PIR.Process.bind, Environment.prepend, Environment.push, Values.get]
    dsimp only [Element.Inputs.pack] at call
    change _ = primitiveOutcome (Element.encodeOutcome model (elementReference model source (position + 1))) at call
    rw [call]
    simp only [afterReference, bounded, ↓reduceIte]
    cases outcome : elementReference model source (position + 1) <;>
      simp [elementLaw, afterReference, bounded, outcome, Element.encodeOutcome,
        primitiveOutcome, PIR.Process.bind, After.decode, Element.encode,
        Environment.prepend, Environment.push, Values.get]
  · by_cases small : position < indexLimit <;>
      simp [After.run, afterReference, Primitive.evaluateOn, checkedIndices, small, bounded,
        show 1 < indexLimit by decide +kernel, primitiveOutcome, PIR.Process.bind,
        Environment.prepend, Environment.push, Values.get]

noncomputable def afterLaw :=
  After.law model (afterReference model) (afterCondition model) (after model)

/-- A shared installation into the actual complete linked helper table. -/
structure Laws (table : Evaluation.MeaningsOn model.toCarriers closedInterface) : Prop where
  zero : (zeroLaw model).Realizes (helper := GkrSourceBodies.helper28Helper) table
  zeroWrapper : (zeroWrapperLaw model).Realizes (helper := GkrSourceBodies.helper87Helper) table
  step : (stepLaw model).Realizes (helper := GkrSourceBodies.helper29Helper) table
  callback : (callbackLaw model).Realizes (helper := GkrSourceBodies.helper30Helper) table
  scan : (scanLaw model).Realizes (helper := GkrSourceBodies.helper95Helper) table
  wrapper : (wrapperLaw model).Realizes (helper := GkrSourceBodies.helper96Helper) table
  element : (elementLaw model).Realizes (helper := GkrSourceBodies.helper97Helper) table
  after : (afterLaw model).Realizes (helper := GkrSourceBodies.helper98Helper) table

theorem install (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions) :
    Laws model (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) := by
  install_reference_laws using linked with bodies

end ZkcSecurity.Realizations.Gkr.HonestHelpers.ReadbackCompanion
