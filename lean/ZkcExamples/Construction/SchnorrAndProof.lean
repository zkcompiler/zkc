module

public import ZkcExamples.Construction.SchnorrAndProofData
public import ZkcExamples.Construction.SchnorrAndProofParticipant
public import Zkc.Construction.Compiled

@[expose] public section

/-! The compiled non-interactive Schnorr AND verifier of the Sigma example.

`examples/projects/sigma` declares `example::AndProof` over the `SchnorrAnd`
protocol of `libraries/sigma`: two Schnorr statements with independent witnesses and one shared challenge, whose verifier checks both equations. `SchnorrAndProofData` is the Entry's
original export and `SchnorrAndProofParticipant` its constructed validator, in
which the final conjunction of the two checked equations is a Boolean
conjunction.

No typed bodies are authored for this original: the kernel evaluates its
admission (`admissible`), and `program` is the admitted program. The composed
transcript-construction and participant projection check accepts the export
(`compiled`), so the generic composition theorem gives the Fiat–Shamir
transform equation for every related input (`compiled_transform`) with no
proof specific to this Entry. No security theorem about the compiled verifier
is stated here; the Fiat–Shamir theorems of the Sigma compositions are about
the transforms of the imported interactive verifiers.
-/

namespace ZkcExamples.Construction.SchnorrAndProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

abbrev snapshot := SchnorrAndProofData.snapshot
abbrev participant := SchnorrAndProofParticipant.participant

set_option smartUnfolding true in
/-- The original admits. -/
theorem admissible : (Structured.check snapshot).toOption.isSome = true := by decide +kernel

/-- The admitted original program. -/
def program : Structured.Program := (Structured.check snapshot).toOption.get admissible

theorem admitted : Structured.check snapshot = .ok program := by
  have found : (Structured.check snapshot).toOption = some program := (Option.some_get admissible).symm
  revert found
  cases Structured.check snapshot <;> simp [Except.toOption]

set_option smartUnfolding true in
/-- The composed per-compile check accepts the actual export. -/
theorem compiled : checkCompiled snapshot program participant = .ok () := by decide +kernel

set_option smartUnfolding true in
/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context := (exportContext snapshot participant).get (by decide +kernel)

theorem context_admitted : exportContext snapshot participant = some context := by
  rw [context, Option.some_get]

/-- For every challenge function, the compiled verifier's ideal meaning, read
through any selection of its returned values that agrees with a selection of
the validator's outputs, is the Fiat–Shamir transform of the original
validator's process, for every input related to the published inputs. The
context is the one the check derives (`context_admitted`). -/
theorem compiled_transform (F G : Type) [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq G] :
    ∃ context, exportContext snapshot participant = some context ∧
      ∀ {m : Type → Type} [Monad m] [LawfulMonad m] {B : Type} (challenge : History F G → m F)
        (select : List (Value F G) → B) (decide : List (Option (Value F G)) → B),
        (∀ values, values.length = participant.returned.length →
          select values = decide (values.dropLast.map some)) →
        ∀ (handle : Nat) (data : List (Value F G)) (initial : History F G) (proof : Proof F G)
          (inputs : Values (Component (assignment F G)) program.payload.entry.inputs),
          HoldsValues handle (data ++ [.transcript initial])
            (inputSlots context participant.policy program.payload.entry.inputs) inputs →
          data.length = participant.policy.publicInputs.length →
          (fun result => (mapOutcome select result.1, result.2)) <$>
              ideal context challenge (helperTable program F G) participant.returned
                participant.instructions (data ++ [.transcript initial]) proof =
            transform context challenge
              (((program.participant F G context.validator inputs).bind fun outputs =>
                .done (decide (validatorOutputs context.validator program.payload.entry.outputScopes
                  outputs))).interpret CommonAdapter.project) initial proof :=
  Zkc.Construction.compiled_transform snapshot program participant compiled

end ZkcExamples.Construction.SchnorrAndProof
