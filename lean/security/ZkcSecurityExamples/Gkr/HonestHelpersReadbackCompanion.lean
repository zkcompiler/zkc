module

public import ZkcSecurityExamples.Gkr.HonestHelpersReadbackGoals
public import Zkc.Algorithms.ListReadback

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

noncomputable def zeroWrapperLibrary :=
  forward_reference% ZeroWrapper.body using (zeroLaw model)

def zeroWrapperCondition := fun table =>
  (zeroLaw model).Realizes (helper := GkrSourceBodies.helper46Helper) table

theorem zeroWrapper : ZeroWrapper.Goal model (.returned ⟨0⟩) (zeroWrapperCondition model) := by
  apply ZeroWrapper.of_law model _ _ (zeroWrapperLibrary model) rfl
  · rfl
  · intro table dependency; exact dependency _

noncomputable def zeroWrapperLaw :=
  ZeroWrapper.law model (.returned ⟨0⟩) (zeroWrapperCondition model) (zeroWrapper model)

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

noncomputable def callbackLibrary :=
  forward_reference% Callback.body using (stepLaw model)

def callbackReference (current : model.Field scalarDomain) (index : Nat)
    (value : model.Field scalarDomain) (_source : List (model.Field scalarDomain)) (position : Nat) :
    PIR.Outcome (Callback.Output model) :=
  match ListReadback.step indexLimit position (current, index) value with
  | .returned state => .returned ⟨state.1, state.2⟩
  | .stopped reason => .stopped reason

def callbackCondition := fun table (_ : model.Field scalarDomain) (_ : Nat)
    (_ : model.Field scalarDomain) (_ : List (model.Field scalarDomain)) (_ : Nat) =>
  (stepLaw model).Realizes (helper := GkrSourceBodies.helper53Helper) table

theorem callback : Callback.Goal model (callbackReference model) (callbackCondition model) := by
  apply Callback.of_law model _ _ (callbackLibrary model) rfl
  · intro current index value source position
    change Step.encodeOutcome model (stepReference model current index value position) = _
    cases outcome : ListReadback.step indexLimit position (current, index) value <;>
      simp [stepReference, callbackReference, outcome, Step.encodeOutcome, Callback.encodeOutcome,
        Step.encode, Callback.encode]
  · intro table current index value source position dependency; exact dependency _

noncomputable def callbackLaw :=
  Callback.law model (callbackReference model) (callbackCondition model) (callback model)

def scanReference (source : List (model.Field scalarDomain)) (current : model.Field scalarDomain)
    (index position : Nat) : PIR.Outcome (Scan.Output model) :=
  if source.length < indexLimit then
    match ListReadback.scan indexLimit position source current index with
    | .returned state => .returned ⟨state.1, state.2⟩
    | .stopped reason => .stopped reason
  else .stopped .exhausted

def scanCondition := fun table (_ : List (model.Field scalarDomain))
    (_ : model.Field scalarDomain) (_ _ : Nat) =>
  (callbackLaw model).Realizes (helper := GkrSourceBodies.helper54Helper) table

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
      simp [foldSpec, GkrSourceLaws.fold?, GkrSourceBodies.scopedHelper82Body,
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
        change invoke table GkrSourceBodies.helper54Helper (Callback.Inputs.pack
          { current := state.1, index := state.2, value, source, position }) = _
        rw [call]
        change primitiveOutcome (Callback.encodeOutcome model
          (callbackReference model state.1 state.2 value source position)) = _
        cases state with | mk current index =>
          cases outcome : ListReadback.step indexLimit position (current, index) value <;>
            simp [callbackReference, outcome, Callback.encodeOutcome, Callback.encode,
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
      simp [foldSpec, GkrSourceLaws.fold?, GkrSourceBodies.scopedHelper82Body,
        DomainSpec.admit, DomainBody.admit, DomainNode.admit, Collection.values,
        DomainArguments.pack, Item.pack, Values.get, bounded, Finite.continueWith]
    dsimp only [DomainArguments.pack] at exhausted
    simp only [Evaluation.denoteFoldOn, Values.split]
    erw [exhausted]
    simp [scanReference, bounded, Finite.admitThen, PIR.Process.bind, primitiveOutcome]

noncomputable def scanLaw := Scan.law model (scanReference model) (scanCondition model) (scan model)

noncomputable def wrapperLibrary :=
  forward_reference% ScanWrapper.body using (scanLaw model)

def wrapperReference (current : model.Field scalarDomain) (index position : Nat)
    (source : List (model.Field scalarDomain)) : PIR.Outcome (ScanWrapper.Output model) :=
  ScanWrapper.decodeOutcome model
    (Scan.encodeOutcome model (scanReference model source current index position))

def wrapperCondition := fun table (_ : model.Field scalarDomain) (_ _ : Nat)
    (_ : List (model.Field scalarDomain)) =>
  (scanLaw model).Realizes (helper := GkrSourceBodies.scopedHelper82Helper) table

/-- Only the complete ABI transport is generated; the chosen scan mathematics
and its dependency premise are retained by the named reference and condition. -/
theorem wrapper : ScanWrapper.Goal model (wrapperReference model) (wrapperCondition model) := by
  intro table current index position source dependency
  exact ScanWrapper.of_installed model (wrapperLibrary model) rfl
    table current index position source (dependency _)

noncomputable def wrapperLaw :=
  ScanWrapper.law model (wrapperReference model) (wrapperCondition model) (wrapper model)

def elementReference (source : List (model.Field scalarDomain)) (position : Nat) :
    PIR.Outcome (Element.Output model) :=
  match scanReference model source 0 0 position with
  | .returned result => .returned ⟨result.selected⟩
  | .stopped reason => .stopped reason

def elementCondition := fun table (_ : List (model.Field scalarDomain)) (_ : Nat) =>
  (zeroWrapperLaw model).Realizes (helper := GkrSourceBodies.scopedHelper74Helper) table ∧
  (wrapperLaw model).Realizes (helper := GkrSourceBodies.helper56Helper) table

theorem element : Element.Goal model (elementReference model) (elementCondition model) := by
  intro table source position dependencies
  have zeroCall := dependencies.1 (Zero.Inputs.pack (Value := model.Value) {})
  have scanCall := dependencies.2 (ScanWrapper.Inputs.pack
    { current := 0, index := 0, position, source })
  simp only [Element.run, Environment.prepend, Environment.push, Values.get, PIR.Process.bind_done]
  dsimp only [Zero.Inputs.pack] at zeroCall
  rw [zeroCall]
  simp only [zeroWrapperLaw, ZeroWrapper.law, ZeroWrapper.encodeOutcome, ZeroWrapper.encode,
    primitiveOutcome, PIR.Process.bind, Environment.prepend, Environment.push, Values.get,
    Primitive.evaluateOn, show 0 < indexLimit by decide +kernel, ↓reduceIte]
  change invoke table GkrSourceBodies.helper56Helper _ =
    primitiveOutcome (ScanWrapper.encodeOutcome model (wrapperReference model 0 0 position source)) at scanCall
  dsimp only [ScanWrapper.Inputs.pack] at scanCall
  rw [scanCall]
  simp only [wrapperReference, elementReference]
  cases outcome : scanReference model source 0 0 position <;>
    simp [outcome, ScanWrapper.decodeOutcome, Scan.encodeOutcome, Scan.encode,
      ScanWrapper.encodeOutcome, primitiveOutcome, PIR.Process.bind, Element.decode, ScanWrapper.encode,
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
  (elementLaw model).Realizes (helper := GkrSourceBodies.helper57Helper) table

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
  zero : (zeroLaw model).Realizes (helper := GkrSourceBodies.helper46Helper) table
  zeroWrapper : (zeroWrapperLaw model).Realizes (helper := GkrSourceBodies.scopedHelper74Helper) table
  step : (stepLaw model).Realizes (helper := GkrSourceBodies.helper53Helper) table
  callback : (callbackLaw model).Realizes (helper := GkrSourceBodies.helper54Helper) table
  scan : (scanLaw model).Realizes (helper := GkrSourceBodies.scopedHelper82Helper) table
  wrapper : (wrapperLaw model).Realizes (helper := GkrSourceBodies.helper56Helper) table
  element : (elementLaw model).Realizes (helper := GkrSourceBodies.helper57Helper) table
  after : (afterLaw model).Realizes (helper := GkrSourceBodies.helper70Helper) table

theorem install (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions) :
    Laws model (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) := by
  have zero := (zeroLaw model).realizes (helper := GkrSourceBodies.helper46Helper) definitions linked bodies.zero (by
    intro arguments
    obtain ⟨view, rfl⟩ := Zero.Inputs.pack_surjective arguments
    trivial)
  have step := (stepLaw model).realizes (helper := GkrSourceBodies.helper53Helper) definitions linked bodies.step (by
    intro arguments
    obtain ⟨view, rfl⟩ := Step.Inputs.pack_surjective arguments
    trivial)
  have zeroWrapper := (zeroWrapperLaw model).realizes (helper := GkrSourceBodies.scopedHelper74Helper) definitions linked bodies.zeroWrapper (by
    intro arguments
    obtain ⟨view, rfl⟩ := Zero.Inputs.pack_surjective arguments
    exact zero)
  have callback := (callbackLaw model).realizes (helper := GkrSourceBodies.helper54Helper) definitions linked bodies.callback (by
    intro arguments
    obtain ⟨view, rfl⟩ := Callback.Inputs.pack_surjective arguments
    exact step)
  have scan := (scanLaw model).realizes (helper := GkrSourceBodies.scopedHelper82Helper) definitions linked bodies.scan (by
    intro arguments
    obtain ⟨view, rfl⟩ := Scan.Inputs.pack_surjective arguments
    exact callback)
  have wrapper := (wrapperLaw model).realizes (helper := GkrSourceBodies.helper56Helper) definitions linked bodies.scanWrapper (by
    intro arguments
    obtain ⟨view, rfl⟩ := ScanWrapper.Inputs.pack_surjective arguments
    exact scan)
  have element := (elementLaw model).realizes (helper := GkrSourceBodies.helper57Helper) definitions linked bodies.element (by
    intro arguments
    obtain ⟨view, rfl⟩ := Element.Inputs.pack_surjective arguments
    exact ⟨zeroWrapper, wrapper⟩)
  have after := (afterLaw model).realizes (helper := GkrSourceBodies.helper70Helper) definitions linked bodies.after (by
    intro arguments
    obtain ⟨view, rfl⟩ := Element.Inputs.pack_surjective arguments
    exact element)
  exact ⟨zero, zeroWrapper, step, callback, scan, wrapper, element, after⟩

end ZkcSecurity.Realizations.Gkr.HonestHelpers.ReadbackCompanion
