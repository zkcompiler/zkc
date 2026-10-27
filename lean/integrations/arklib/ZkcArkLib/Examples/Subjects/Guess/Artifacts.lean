module

public import ZkcSecurity.Claims.Subject
public import ZkcExamples.Construction.GuessArtifact
public import ZkcExamples.Construction.GuessProof

@[expose] public section

/-! Generated artifacts of the subject `guess` and their checked facts. Regenerate
with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::Proof` Entry, the types of the inputs its policy publishes.
Every fact below is a generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.Guess
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::Proof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.GuessProof.snapshot
  participant := ZkcExamples.Construction.GuessProof.participant
  publics := [.field "bls12-381.fr"]
  program := none

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.GuessProof.imported
  compiled := ZkcExamples.Construction.GuessProof.compiled
  selection := ZkcExamples.Construction.GuessProof.selection
  selected := ZkcExamples.Construction.GuessProof.selected
  checked := ZkcExamples.Construction.GuessProof.selection_checked
  publics := by decide +kernel
  occurrences := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | .cons value0 .nil => exact ZkcExamples.Construction.GuessProof.compiled_transform challenge value0 handle initial proof

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:2d6581776370c9e834d35c333ac1287a112e6b791fef5bd1b46a7cbf9515bbed", "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:58627dd075b34a1f236b8ff703a18631ce9868dd376ebcaf059c2b54896e1e0e"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:58627dd075b34a1f236b8ff703a18631ce9868dd376ebcaf059c2b54896e1e0e"⟩]⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  [{ label := "challenge", native := "label_6368616c6c656e6765",
      delivery := "label_64656c6976657279_0", selected := by decide +kernel,
      request := compiled.context.request.getD (.draw ""), requestSelected := by decide +kernel }]

end ZkcSecurity.Examples.Subjects.Guess
