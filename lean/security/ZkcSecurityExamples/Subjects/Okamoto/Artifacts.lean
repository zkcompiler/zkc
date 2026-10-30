module

public import ZkcSecurity.Claims.Subject
public import ZkcTools.ConstructionBindings.Admission
public import ZkcExamples.Construction.OkamotoArtifact
public import ZkcExamples.Construction.OkamotoProof

@[expose] public section

/-! Generated artifacts of the subject `okamoto-proof` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::Proof` Entry, the types of the inputs its policy publishes.
Every fact below is a generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.Okamoto
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::Proof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.OkamotoProof.snapshot
  participant := ZkcExamples.Construction.OkamotoProof.participant
  publics := [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1"]
  program := none

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.OkamotoProof.imported
  compiled := ZkcExamples.Construction.OkamotoProof.compiled
  selection := ZkcExamples.Construction.OkamotoProof.selection
  selected := ZkcExamples.Construction.OkamotoProof.selected
  checked := ZkcExamples.Construction.OkamotoProof.selection_checked
  publics := by decide +kernel
  occurrences := by decide +kernel
  sourceConnection := some ⟨ZkcExamples.Construction.OkamotoProof.sourceConnected⟩

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | .cons value0 (.cons value1 (.cons value2 .nil)) => exact ZkcExamples.Construction.OkamotoProof.compiled_transform challenge value0 value1 value2 handle initial proof

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:d5c028a6e977a8225e1f83d0f0da8c04b74c60391d56702a5b953c6c5bea894b", "zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:991878e1a11f6f19f82e5c262fbdd5751eaa2770ec5a6d5ff1caa26ae5971626"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:991878e1a11f6f19f82e5c262fbdd5751eaa2770ec5a6d5ff1caa26ae5971626"⟩]⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.Okamoto
