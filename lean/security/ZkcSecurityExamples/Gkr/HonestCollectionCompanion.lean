module

public import ZkcSecurityExamples.Gkr.HonestCollectionGoals
public meta import ZkcTools.StructuredSource.CollectionProofs

@[expose] public section

/-! List representations for the actual producer's collection helpers. Names
come from the generated goals; iteration belongs to the generic list library.
Dependency laws apply in the caller's actual table, with exact stopped outcomes. -/
namespace ZkcSecurity.Realizations.Gkr.HonestHelpers.CollectionCompanion
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open CollectionGoals

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

attribute [local implicit_reducible] Op.arguments Op.results Op.regions

variable (model : DomainModel)

def encode (xs : List (model.Field scalarDomain)) : Values model.Value appendSpec.state :=
  CollectionState.pack ⟨xs⟩

def repeatReference (initial : List (model.Field scalarDomain))
    (value : model.Field scalarDomain) (count : Nat) : PIR.Outcome (Repeat.Output model) :=
  .returned ⟨initial ++ List.replicate count value⟩

theorem repeated : Repeat.Goal model (repeatReference model) (fun _ _ _ _ => True) := by
  intro table initial value count _
  collection_loop (Repeat.run) with_encoder (encode model) with_chunk ([value]) using [repeatReference, Repeat.decode, encode, CollectionState.pack]

noncomputable def repeatLaw :=
  Repeat.law model (repeatReference model) (fun _ _ _ _ => True) (repeated model)

noncomputable def repeatWrapperLaw := forward_reference% RepeatWrapper.body using (repeatLaw model)
noncomputable def replicateStepLaw := forward_reference% ReplicateStep.body using (repeatWrapperLaw model)

def replicateFoldReference (source initial : List (model.Field scalarDomain)) (count : Nat) :
    PIR.Outcome (ReplicateFold.Output model) :=
  if source.length < indexLimit then .returned ⟨initial ++ source.flatMap (List.replicate count)⟩
  else .stopped .exhausted

theorem replicateFold : ReplicateFold.Goal model (replicateFoldReference model)
    (fun table _ _ _ => (replicateStepLaw model).Realizes (helper := GkrSourceBodies.helper22Helper) table) := by
  intro table source initial count dependency
  dsimp only [ReferenceLaw.Realizes, GkrSourceBodies.helper22Helper] at dependency
  collection_fold (ReplicateFold.run) over (source) with_encoder (encode model)
    with_chunk (List.replicate count) using [dependency, replicateStepLaw, repeatWrapperLaw,
      repeatLaw, Repeat.law, repeatReference, Repeat.encodeOutcome, Repeat.encode,
      replicateFoldReference, ReplicateFold.decode, encode, CollectionState.pack]

noncomputable def replicateFoldLaw := ReplicateFold.law model (replicateFoldReference model)
  (fun table _ _ _ => (replicateStepLaw model).Realizes (helper := GkrSourceBodies.helper22Helper) table)
  (replicateFold model)

noncomputable def replicateWrapperLaw := forward_reference% ReplicateWrapper.body using (replicateFoldLaw model)

def replicateReference (source : List (model.Field scalarDomain)) (count : Nat) :
    PIR.Outcome (Replicate.Output model) :=
  if source.length < indexLimit then .returned ⟨source.flatMap (List.replicate count)⟩
  else .stopped .exhausted

theorem replicated : Replicate.Goal model (replicateReference model)
    (fun table _ _ => (replicateWrapperLaw model).Realizes (helper := GkrSourceBodies.helper24Helper) table) := by
  intro table source count dependency
  dsimp only [ReferenceLaw.Realizes, GkrSourceBodies.helper24Helper] at dependency
  collection_simp [Replicate.run, dependency, replicateWrapperLaw, replicateFoldLaw,
    ReplicateFold.law, replicateFoldReference, ReplicateFold.encodeOutcome, ReplicateFold.encode,
    replicateReference, Replicate.decode]
  by_cases bounded : source.length < indexLimit <;> collection_simp [bounded]

noncomputable def replicateLaw := Replicate.law model (replicateReference model)
  (fun table _ _ => (replicateWrapperLaw model).Realizes (helper := GkrSourceBodies.helper24Helper) table)
  (replicated model)

noncomputable def appendLaw := ReferenceLibrary.appendVector model scalarDomain "s2"
noncomputable def appendStepLaw := forward_reference% AppendStep.body using (appendLaw model)

def appendFoldReference (source initial : List (model.Field scalarDomain)) :
    PIR.Outcome (AppendFold.Output model) :=
  if source.length < indexLimit then .returned ⟨initial ++ source⟩ else .stopped .exhausted

theorem appendFold : AppendFold.Goal model (appendFoldReference model)
    (fun table _ _ => (appendStepLaw model).Realizes (helper := GkrSourceBodies.helper27Helper) table) := by
  intro table source initial dependency
  dsimp only [ReferenceLaw.Realizes, GkrSourceBodies.helper27Helper] at dependency
  collection_fold (AppendFold.run) over (source) with_encoder (encode model)
    with_chunk (fun value => [value]) using [dependency, appendStepLaw, appendLaw,
      ReferenceLibrary.appendVector, appendFoldReference, AppendFold.decode, encode,
      CollectionState.pack, List.flatMap_singleton']

noncomputable def appendFoldLaw := AppendFold.law model (appendFoldReference model)
  (fun table _ _ => (appendStepLaw model).Realizes (helper := GkrSourceBodies.helper27Helper) table)
  (appendFold model)

noncomputable def concatenateLaw := forward_reference% Concatenate.body using (appendFoldLaw model)

def tileReference (source : List (model.Field scalarDomain)) (count : Nat) :
    PIR.Outcome (Tile.Output model) :=
  match Finite.repeatAppend
      (if source.length < indexLimit then .returned source else .stopped .exhausted) count [] with
  | .returned values => .returned ⟨values⟩
  | .stopped reason => .stopped reason

theorem tiled : Tile.Goal model (tileReference model)
    (fun table _ _ => (concatenateLaw model).Realizes (helper := GkrSourceBodies.helper29Helper) table) := by
  intro table source count dependency
  dsimp only [ReferenceLaw.Realizes, GkrSourceBodies.helper29Helper] at dependency
  by_cases bounded : source.length < indexLimit <;>
    collection_checked_loop (Tile.run) with_encoder (encode model)
    with_chunk (if source.length < indexLimit then .returned source else .stopped .exhausted)
    using [bounded, Finite.repeatAppend, Finite.continueWith, dependency, concatenateLaw, appendFoldLaw, AppendFold.law, appendFoldReference,
      AppendFold.encodeOutcome, AppendFold.encode, tileReference, Tile.decode,
      encode, CollectionState.pack]

noncomputable def tileLaw := Tile.law model (tileReference model)
  (fun table _ _ => (concatenateLaw model).Realizes (helper := GkrSourceBodies.helper29Helper) table)
  (tiled model)

/-- Every dependency is installed against its actual body and linked table. -/
structure Laws (table : Evaluation.MeaningsOn model.toCarriers closedInterface) : Prop where
  repeated : (repeatLaw model).Realizes (helper := GkrSourceBodies.helper20Helper) table
  repeatWrapper : (repeatWrapperLaw model).Realizes (helper := GkrSourceBodies.helper21Helper) table
  replicateStep : (replicateStepLaw model).Realizes (helper := GkrSourceBodies.helper22Helper) table
  replicateFold : (replicateFoldLaw model).Realizes (helper := GkrSourceBodies.scopedHelper45Helper) table
  replicateWrapper : (replicateWrapperLaw model).Realizes (helper := GkrSourceBodies.helper24Helper) table
  replicated : (replicateLaw model).Realizes (helper := GkrSourceBodies.helper25Helper) table
  appended : (appendLaw model).Realizes (helper := GkrSourceBodies.helper26Helper) table
  appendStep : (appendStepLaw model).Realizes (helper := GkrSourceBodies.helper27Helper) table
  appendFold : (appendFoldLaw model).Realizes (helper := GkrSourceBodies.scopedHelper48Helper) table
  concatenate : (concatenateLaw model).Realizes (helper := GkrSourceBodies.helper29Helper) table
  tiled : (tileLaw model).Realizes (helper := GkrSourceBodies.helper30Helper) table

theorem install (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions) : Laws model (closedMeaningsOn model definitions) := by
  have repeated := install_collection% (repeatLaw model) for_helper GkrSourceBodies.helper20Helper in_definitions definitions
    linked_by linked body_at bodies.repeated view_by RepeatArguments.pack_surjective requiring True.intro
  have repeatWrapper := install_collection% (repeatWrapperLaw model) for_helper GkrSourceBodies.helper21Helper in_definitions definitions
    linked_by linked body_at bodies.repeatWrapper view_by RepeatArguments.pack_surjective requiring repeated
  have replicateStep := install_collection% (replicateStepLaw model) for_helper GkrSourceBodies.helper22Helper in_definitions definitions
    linked_by linked body_at bodies.replicateStep view_by ReplicateStepArguments.pack_surjective requiring repeatWrapper
  have replicateFold := install_collection% (replicateFoldLaw model) for_helper GkrSourceBodies.scopedHelper45Helper in_definitions definitions
    linked_by linked body_at bodies.replicateFold view_by ReplicateFoldArguments.pack_surjective requiring replicateStep
  have replicateWrapper := install_collection% (replicateWrapperLaw model) for_helper GkrSourceBodies.helper24Helper in_definitions definitions
    linked_by linked body_at bodies.replicateWrapper view_by ReplicateWrapperArguments.pack_surjective requiring replicateFold
  have replicated := install_collection% (replicateLaw model) for_helper GkrSourceBodies.helper25Helper in_definitions definitions
    linked_by linked body_at bodies.replicate view_by ReplicateArguments.pack_surjective requiring replicateWrapper
  have appended := install_collection% (appendLaw model) for_helper GkrSourceBodies.helper26Helper in_definitions definitions
    linked_by linked body_at bodies.append view_by AppendArguments.pack_surjective requiring True.intro
  have appendStep := install_collection% (appendStepLaw model) for_helper GkrSourceBodies.helper27Helper in_definitions definitions
    linked_by linked body_at bodies.appendStep view_by AppendStepArguments.pack_surjective requiring appended
  have appendFold := install_collection% (appendFoldLaw model) for_helper GkrSourceBodies.scopedHelper48Helper in_definitions definitions
    linked_by linked body_at bodies.appendFold view_by AppendFoldArguments.pack_surjective requiring appendStep
  have concatenate := install_collection% (concatenateLaw model) for_helper GkrSourceBodies.helper29Helper in_definitions definitions
    linked_by linked body_at bodies.concatenate view_by ConcatenateArguments.pack_surjective requiring appendFold
  have tiled := install_collection% (tileLaw model) for_helper GkrSourceBodies.helper30Helper in_definitions definitions
    linked_by linked body_at bodies.tile view_by ReplicateArguments.pack_surjective requiring concatenate
  exact ⟨repeated, repeatWrapper, replicateStep, replicateFold, replicateWrapper,
    replicated, appended, appendStep, appendFold, concatenate, tiled⟩

end ZkcSecurity.Realizations.Gkr.HonestHelpers.CollectionCompanion
