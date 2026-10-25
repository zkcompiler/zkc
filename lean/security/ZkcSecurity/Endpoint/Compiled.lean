module

public import Zkc.Construction.Compiled
public import Zkc.Executable.Soundness

@[expose] public section

/-! # The artifacts of a compiled Proof Entry and their checked facts

A claim about a compiled Proof Entry is indexed by its artifacts (`Artifacts`):
the original export the source compiles to, the constructed validator export,
the types of the inputs the export's policy publishes, in policy order, and,
when the claim covers program bytes, the executable validator of the deployed
program. A policy statement (`Artifacts.Statement`) is a list of values of the
published types: every statement a host can bind, malformed ones included.

`Compiled art` collects the facts the kernel checks for those artifacts and
that every endpoint needs: the admitted original, the composed
transcript-construction and participant projection check accepting the export
against it, and the selection of the export's inputs and acceptance output,
constructed in Lean from the admitted original and the policy and checked
against the export (`Zkc.Construction.select`, `Selection.check`). The
generated per-Entry modules provide each fact by kernel evaluation.

From these facts alone, `Compiled.transform_eq` states the compiled verifier's
ideal meaning on a statement (`Compiled.verifier`) as the Fiat–Shamir transform
of the admitted original validator on that statement (`Compiled.original`),
for every challenge function in any lawful monad, service handle, initial
transcript and proof. It is `Zkc.Construction.compiled_selected`, whose
positional premises the checked selection discharges; no equation specific to
an Entry is involved.

Host acceptance of an ideal run (`Zkc.Executable.Accepts` of its observation)
is the complete acceptance of the compiled verifier's result (`verdict_eq`),
and implies its acceptance (`accepted_of_accepts`), the event the soundness
endpoints bound.
-/

set_option autoImplicit false

namespace ZkcSecurity.Endpoint
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- The artifacts of a compiled Proof Entry: the original export, the
constructed validator export, the types of the published inputs in policy
order, and the executable validator of the deployed program when a claim covers
program bytes. -/
structure Artifacts where
  original : Structured.Snapshot
  participant : Participant
  publics : List Ty
  program : Option Zkc.Executable.Validator

namespace Artifacts

/-- A policy statement of the artifacts: values of the published input types, in
policy order. Every value of these types is a statement a host can bind,
malformed ones included. -/
abbrev Statement (art : Artifacts) (F G : Type) : Type := Values (assignment F G) art.publics

end Artifacts

/-- Values at one list of types, read at an equal list of types. -/
def retype {F G : Type} {tys tys' : List Ty} (same : tys = tys') (values : Values (assignment F G) tys) :
    Values (assignment F G) tys' :=
  same ▸ values

theorem encodeValues_retype {F G : Type} {tys tys' : List Ty} (same : tys = tys')
    (values : Values (assignment F G) tys) : encodeValues (retype same values) = encodeValues values := by
  subst same
  rfl

/-- The checked compilation of artifacts: the admitted original, the composed
transcript-construction and participant projection check accepting the export
against it, and the selection of the export's inputs and acceptance output,
constructed from the admitted original and the policy, checked against the
export, and publishing the artifacts' published types. -/
structure Compiled (art : Artifacts) where
  imported : Structured.Imported art.original
  compiled : checkCompiled imported art.participant = .ok ()
  selection : Selection imported.program.payload.entry.outputs
  selected : select imported art.participant = some selection
  checked : selection.check imported art.participant = true
  publics : selection.publics = art.publics

namespace Compiled
variable {art : Artifacts} (c : Compiled art)

/-- The occurrence context the construction check derives. -/
abbrev context : Context := c.selection.context

/-- Where the export returns its selected acceptance output. -/
abbrev position : Nat := c.selection.position

section Meaning
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The compiled verifier: the ideal meaning of the constructed validator under
the checked occurrence context, with helper calls read by the admitted
original's checked helpers, on a statement's published values and the initial
transcript, read through the acceptance output the policy selects. -/
def verifier {m : Type → Type} [Monad m] (challenge : History F G → m F) (statement : art.Statement F G)
    (initial : History F G) (proof : Proof F G) : m (PIR.Outcome (Option Bool) × Proof F G) :=
  (fun result => (mapOutcome (acceptanceAt c.position) result.1, result.2)) <$>
    ideal c.context challenge (helperTable c.imported.program F G) art.participant.returned
      art.participant.instructions (encodeValues statement ++ [.transcript initial]) proof

/-- The admitted original validator on a statement's published values, with the
replaced service at `handle`, read through its acceptance output. -/
def original (statement : art.Statement F G) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  ((c.imported.program.participant F G c.context.validator
      (heldInputs handle (encodeValues statement) c.selection.slots
        c.imported.program.payload.entry.inputs)).bind
    fun outputs => .done (outputs.get c.selection.output)).interpret CommonAdapter.project

/-- The composed rules on the artifacts: for every challenge function in any
lawful monad, statement, service handle, initial transcript and proof, the
compiled verifier is the Fiat–Shamir transform of the admitted original
validator. -/
theorem transform_eq {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (statement : art.Statement F G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    c.verifier challenge statement initial proof =
      transform c.context challenge (c.original statement handle) initial proof := by
  have composed := (compiled_selected (F := F) (G := G) c.imported art.participant c.compiled c.selected
    c.checked).2 challenge handle (retype c.publics.symm statement) initial proof
  rw [encodeValues_retype] at composed
  exact composed

end Meaning

end Compiled

section Verdict
variable {F G : Type}

/-- Complete acceptance of a compiled verifier's result: the selected output is
true and the whole proof was read. -/
def verdict (result : PIR.Outcome (Option Bool) × Proof F G) : Bool :=
  match result.1, result.2 with
  | .returned (some decision), [] => decision
  | _, _ => false

/-- Host acceptance of an ideal run's observation is the complete acceptance of
the result read through the acceptance output at the same position. -/
theorem verdict_eq (position : Nat) (result : PIR.Outcome (List (Value F G)) × Proof F G) :
    verdict (mapOutcome (acceptanceAt position) result.1, result.2) =
      Zkc.Executable.Accepts position (Zkc.Executable.idealObservation result) := by
  rcases result with ⟨outcome, unread⟩
  cases outcome with
  | stopped stop =>
      simp [verdict, mapOutcome, Zkc.Executable.Accepts, Zkc.Executable.idealObservation,
        Zkc.Executable.observation, Zkc.Executable.Decision]
  | returned values =>
      simp only [mapOutcome, Zkc.Executable.idealObservation, Zkc.Executable.observation,
        Zkc.Executable.Accepts, Zkc.Executable.Decision, acceptanceAt, Zkc.Executable.selectedTrue]
      cases values[position]? with
      | none => cases unread <;> simp [verdict]
      | some value =>
          cases value with
          | data payload =>
              cases payload with
              | boolean decision => cases unread <;> cases decision <;> simp [verdict]
              | field => cases unread <;> simp [verdict]
              | group => cases unread <;> simp [verdict]
          | index => cases unread <;> simp [verdict]
          | vector => cases unread <;> simp [verdict]
          | transcript => cases unread <;> simp [verdict]
          | indices => cases unread <;> simp [verdict]
          | unsupported => cases unread <;> simp [verdict]

/-- Complete acceptance is acceptance of the outcome. -/
theorem accepted_of_verdict {result : PIR.Outcome (Option Bool) × Proof F G}
    (accepted : verdict result = true) : Zkc.Transcript.Accepted (· = some true) result.1 := by
  rcases result with ⟨outcome, unread⟩
  cases outcome with
  | stopped => simp [verdict] at accepted
  | returned value =>
      cases value with
      | none => simp [verdict] at accepted
      | some decision =>
          cases unread with
          | nil =>
              simp only [verdict] at accepted
              subst accepted
              rfl
          | cons => simp [verdict] at accepted

/-- Host acceptance of an ideal run implies acceptance of the result read through
the acceptance output. -/
theorem accepted_of_accepts {position : Nat} {result : PIR.Outcome (List (Value F G)) × Proof F G}
    (accepts : Zkc.Executable.Accepts position (Zkc.Executable.idealObservation result) = true) :
    Zkc.Transcript.Accepted (· = some true) (mapOutcome (acceptanceAt position) result.1) := by
  rw [← verdict_eq] at accepts
  exact accepted_of_verdict accepts

end Verdict

end ZkcSecurity.Endpoint
