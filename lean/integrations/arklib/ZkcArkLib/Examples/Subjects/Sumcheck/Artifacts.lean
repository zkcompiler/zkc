module

public import ZkcSecurity.Claims.Subject
public import ZkcExamples.Construction.SumcheckProof
public import ZkcExamples.Executable.SumcheckProof

@[expose] public section

/-! Generated artifacts of the subject `sumcheck` and their checked facts.
Regenerate with `lean/bridges/subject.py --write`.

The artifacts are the original export and the constructed validator of the
compiled `example::Proof` Entry, the types of the inputs its policy publishes
and the executable validator of the deployed program. Every fact below is a
generated per-Entry fact the kernel checked. -/

namespace ZkcSecurity.Examples.Subjects.Sumcheck
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `example::Proof` Entry. -/
def artifacts : Artifacts where
  original := ZkcExamples.Construction.SumcheckProof.snapshot
  participant := ZkcExamples.Construction.SumcheckProof.participant
  publics := [.vector "bls12-381.fr", .field "bls12-381.fr", .index]
  program := some ZkcExamples.Executable.SumcheckProof.validator

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := ZkcExamples.Construction.SumcheckProof.imported
  compiled := ZkcExamples.Construction.SumcheckProof.compiled
  selection := ZkcExamples.Construction.SumcheckProof.selection
  selected := ZkcExamples.Construction.SumcheckProof.selected
  checked := ZkcExamples.Construction.SumcheckProof.selection_checked
  publics := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The executable validator, accepted by the lowering rule. -/
def lowering : LoweringEvidence artifacts compiled F G where
  validator := ZkcExamples.Executable.SumcheckProof.validator
  program := rfl
  lowered := ZkcExamples.Executable.SumcheckProof.lowered
  accepted := ZkcExamples.Executable.SumcheckProof.accepted
  prepared := ZkcExamples.Executable.SumcheckProof.prepared
  sorted := ZkcExamples.Executable.SumcheckProof.helpersSorted
  admits statement := by
    match statement with
    | .cons value0 (.cons value1 (.cons value2 .nil)) => exact ZkcExamples.Executable.SumcheckProof.admitted value0 value1 value2

/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨"sha256:c7bd8f9e5ecf095602373f1aea9324ff67dc00870477a4d72aafb35f4ff6fef1", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", "sha256:5a57b102cd46cb4fc6e5e9f1aa86f59c88e726a6df18b5d5405041a146f9f7e3"⟩]
    | .executableBytes => [⟨"constructed-participant", "sha256:5a57b102cd46cb4fc6e5e9f1aa86f59c88e726a6df18b5d5405041a146f9f7e3"⟩, ⟨"verifier-program", "sha256:9c11f210ff0771b8a692e9b1af11dd52bf4d8932928058a0339475c8b57039c0"⟩]⟩

/-- Actual full construction occurrences selected by native source paths. -/
def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=
  [{ label := "reduce.challenge", native := "apply_18_label_726564756365_label_6368616c6c656e6765",
      delivery := "apply_18_label_726564756365_label_64656c6976657279_0", selected := by decide +kernel,
      request := compiled.context.request.getD (.draw ""), requestSelected := by decide +kernel }]

end ZkcSecurity.Examples.Subjects.Sumcheck
