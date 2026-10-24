module

public import ZkcSecurity.Claims.Subject
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

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:a8d1bea6d483deced3f3bf980562590465f706ddf0a35141b00487c43f1bdeca", "zkl_0b54718f8917b00c23a9aa21bf26256a990c3ad40b71cda5b44d6ecd85e5e748", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:50a1ba771f35a6d0a8d362e89aeb9720e39cc985d82778e2b1b4b35e6ad8e7e2"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:50a1ba771f35a6d0a8d362e89aeb9720e39cc985d82778e2b1b4b35e6ad8e7e2"⟩]⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  [{ label := "challenge", native := "label_6368616c6c656e6765",
      delivery := "label_64656c6976657279_0", selected := by decide +kernel,
      request := compiled.context.request.getD (.draw ""), requestSelected := by decide +kernel }]

end ZkcSecurity.Examples.Subjects.Guess
