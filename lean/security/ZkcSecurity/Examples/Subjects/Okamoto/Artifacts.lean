module

public import ZkcSecurity.Claims.Subject
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

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | .cons value0 (.cons value1 (.cons value2 .nil)) => exact ZkcExamples.Construction.OkamotoProof.compiled_transform challenge value0 value1 value2 handle initial proof

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:aa1b8536620f3ead19faad512fe95ba5fb4b6de8683309571e8829c44d99af21", "zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:aeb809a3cb390e2bfe4c881e361a4925fb787faa27d5b181d5436d279797a08e"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:aeb809a3cb390e2bfe4c881e361a4925fb787faa27d5b181d5436d279797a08e"⟩]⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  []

end ZkcSecurity.Examples.Subjects.Okamoto
