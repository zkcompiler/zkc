module

public import Zkc.Applications.Security.Gkr.HonestCollectionGoals
public meta import Zkc.Tools.IR.StructuredSource.CollectionProofs

public meta import Zkc.Tools.IR.StructuredSource.ReferenceInstallation

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
    (fun table _ _ _ => (replicateStepLaw model).Realizes (helper := GkrSourceBodies.helper16Helper) table) := by
  intro table source initial count dependency
  dsimp only [ReferenceLaw.Realizes, GkrSourceBodies.helper16Helper] at dependency
  collection_fold (ReplicateFold.run) over (source) with_encoder (encode model)
    with_chunk (List.replicate count) using [dependency, replicateStepLaw, repeatWrapperLaw,
      repeatLaw, Repeat.law, repeatReference, Repeat.encodeOutcome, Repeat.encode,
      replicateFoldReference, ReplicateFold.decode, encode, CollectionState.pack]

noncomputable def replicateFoldLaw := ReplicateFold.law model (replicateFoldReference model)
  (fun table _ _ _ => (replicateStepLaw model).Realizes (helper := GkrSourceBodies.helper16Helper) table)
  (replicateFold model)

noncomputable def replicateWrapperLaw := forward_reference% ReplicateWrapper.body using (replicateFoldLaw model)

def replicateReference (source : List (model.Field scalarDomain)) (count : Nat) :
    PIR.Outcome (Replicate.Output model) :=
  if source.length < indexLimit then .returned ⟨source.flatMap (List.replicate count)⟩
  else .stopped .exhausted

theorem replicated : Replicate.Goal model (replicateReference model)
    (fun table _ _ => (replicateWrapperLaw model).Realizes (helper := GkrSourceBodies.helper59Helper) table) := by
  intro table source count dependency
  dsimp only [ReferenceLaw.Realizes, GkrSourceBodies.helper59Helper] at dependency
  collection_simp [Replicate.run, dependency, replicateWrapperLaw, replicateFoldLaw,
    ReplicateFold.law, replicateFoldReference, ReplicateFold.encodeOutcome, ReplicateFold.encode,
    replicateReference, Replicate.decode]
  by_cases bounded : source.length < indexLimit <;> collection_simp [bounded]

noncomputable def replicateLaw := Replicate.law model (replicateReference model)
  (fun table _ _ => (replicateWrapperLaw model).Realizes (helper := GkrSourceBodies.helper59Helper) table)
  (replicated model)

noncomputable def appendLaw := ReferenceLibrary.appendVector model scalarDomain "s2"
noncomputable def appendStepLaw := forward_reference% AppendStep.body using (appendLaw model)

def appendFoldReference (source initial : List (model.Field scalarDomain)) :
    PIR.Outcome (AppendFold.Output model) :=
  if source.length < indexLimit then .returned ⟨initial ++ source⟩ else .stopped .exhausted

theorem appendFold : AppendFold.Goal model (appendFoldReference model)
    (fun table _ _ => (appendStepLaw model).Realizes (helper := GkrSourceBodies.helper18Helper) table) := by
  intro table source initial dependency
  dsimp only [ReferenceLaw.Realizes, GkrSourceBodies.helper18Helper] at dependency
  collection_fold (AppendFold.run) over (source) with_encoder (encode model)
    with_chunk (fun value => [value]) using [dependency, appendStepLaw, appendLaw,
      ReferenceLibrary.appendVector, appendFoldReference, AppendFold.decode, encode,
      CollectionState.pack, List.flatMap_singleton']

noncomputable def appendFoldLaw := AppendFold.law model (appendFoldReference model)
  (fun table _ _ => (appendStepLaw model).Realizes (helper := GkrSourceBodies.helper18Helper) table)
  (appendFold model)

noncomputable def concatenateLaw := forward_reference% Concatenate.body using (appendFoldLaw model)

def tileReference (source : List (model.Field scalarDomain)) (count : Nat) :
    PIR.Outcome (Tile.Output model) :=
  match Finite.repeatAppend
      (if source.length < indexLimit then .returned source else .stopped .exhausted) count [] with
  | .returned values => .returned ⟨values⟩
  | .stopped reason => .stopped reason

theorem tiled : Tile.Goal model (tileReference model)
    (fun table _ _ => (concatenateLaw model).Realizes (helper := GkrSourceBodies.helper62Helper) table) := by
  intro table source count dependency
  dsimp only [ReferenceLaw.Realizes, GkrSourceBodies.helper62Helper] at dependency
  by_cases bounded : source.length < indexLimit <;>
    collection_checked_loop (Tile.run) with_encoder (encode model)
    with_chunk (if source.length < indexLimit then .returned source else .stopped .exhausted)
    using [bounded, Finite.repeatAppend, Finite.continueWith, dependency, concatenateLaw, appendFoldLaw, AppendFold.law, appendFoldReference,
      AppendFold.encodeOutcome, AppendFold.encode, tileReference, Tile.decode,
      encode, CollectionState.pack]

noncomputable def tileLaw := Tile.law model (tileReference model)
  (fun table _ _ => (concatenateLaw model).Realizes (helper := GkrSourceBodies.helper62Helper) table)
  (tiled model)

/-- Every dependency is installed against its actual body and linked table. -/
structure Laws (table : Evaluation.MeaningsOn model.toCarriers closedInterface) : Prop where
  repeated : (repeatLaw model).Realizes (helper := GkrSourceBodies.helper14Helper) table
  repeatWrapper : (repeatWrapperLaw model).Realizes (helper := GkrSourceBodies.helper15Helper) table
  replicateStep : (replicateStepLaw model).Realizes (helper := GkrSourceBodies.helper16Helper) table
  replicateFold : (replicateFoldLaw model).Realizes (helper := GkrSourceBodies.helper58Helper) table
  replicateWrapper : (replicateWrapperLaw model).Realizes (helper := GkrSourceBodies.helper59Helper) table
  replicated : (replicateLaw model).Realizes (helper := GkrSourceBodies.helper60Helper) table
  appended : (appendLaw model).Realizes (helper := GkrSourceBodies.helper17Helper) table
  appendStep : (appendStepLaw model).Realizes (helper := GkrSourceBodies.helper18Helper) table
  appendFold : (appendFoldLaw model).Realizes (helper := GkrSourceBodies.helper61Helper) table
  concatenate : (concatenateLaw model).Realizes (helper := GkrSourceBodies.helper62Helper) table
  tiled : (tileLaw model).Realizes (helper := GkrSourceBodies.helper63Helper) table

theorem install (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions) : Laws model (closedMeaningsOn model definitions) := by
  install_reference_laws using linked with bodies

end ZkcSecurity.Realizations.Gkr.HonestHelpers.CollectionCompanion
