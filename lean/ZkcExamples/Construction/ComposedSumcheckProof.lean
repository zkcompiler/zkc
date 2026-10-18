module

public import ZkcExamples.Construction.ComposedSumcheckProofData
public import ZkcExamples.Construction.ComposedSumcheckProofParticipant
public import Zkc.Construction.Compiled

@[expose] public section

/-! The compiled non-interactive verifier of the composed Sumcheck example.

`examples/projects/sumcheck/composed` declares `example::Proof` over the
`TwoSums` protocol: two applications of the Sumcheck `Reduce` protocol at the
sites `left` and `right`, each with its own repeat, sharing one challenge
service, followed by two terminal checks and their conjunction by the Math
helper `zkc::boolean::both`. `ComposedSumcheckProofData` is the Entry's
original export and `ComposedSumcheckProofParticipant` its constructed
validator, in which the compiler inlined `both` as a Boolean conjunction.

No typed bodies are authored for this original: the kernel evaluates its
admission (`admissible`), and `program` is the admitted program. The composed
check accepts the export (`compiled`), so the generic composition theorem gives
the Fiat–Shamir transform equation for every related input
(`compiled_transform`) with no proof specific to this Entry.
-/

namespace ZkcExamples.Construction.ComposedSumcheckProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction

abbrev snapshot := ComposedSumcheckProofData.snapshot
abbrev participant := ComposedSumcheckProofParticipant.participant

set_option smartUnfolding true in
/-- The original admits. -/
theorem admissible : (Structured.check snapshot).toOption.isSome = true := by decide +kernel

/-- The admitted original program. -/
def program : Structured.Program := (Structured.check snapshot).toOption.get admissible

theorem admitted : Structured.check snapshot = .ok program := by
  have found : (Structured.check snapshot).toOption = some program := (Option.some_get admissible).symm
  revert found
  cases Structured.check snapshot <;> simp [Except.toOption]

/-- The admitted original. -/
def imported : Structured.Imported snapshot := ⟨program, admitted⟩

set_option smartUnfolding true in
/-- The composed per-compile check accepts the actual export against the
admitted original. -/
theorem compiled : checkCompiled imported participant = .ok () := by decide +kernel

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
                  outputs))).interpret CommonAdapter.project) initial proof := by
  have composed := Zkc.Construction.compiled_transform (F := F) (G := G) imported participant compiled
  dsimp only [imported] at composed
  exact composed

end ZkcExamples.Construction.ComposedSumcheckProof
