module

public import ZkcSecurity.Endpoint.DomainCompiled
public import Zkc.Construction.ScalarVerifier
public import Zkc.Executable.Program

@[expose] public section

/-! Fixed artifacts, checked static admission and actual Domain execution.
Source correspondence is separate checked evidence whose two processes are
fixed here. Structural admission does not imply that correspondence. -/

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
def Artifacts.domain (art : Artifacts) : Domain.Artifacts :=
  ⟨art.original, art.participant, art.publics⟩

structure Compiled (art : Artifacts) extends Domain.Compiled art.domain

namespace Compiled
variable {art : Artifacts} (c : Compiled art)

/-- The occurrence context the construction check derives. -/
abbrev context : Context := c.selection.context

/-- Where the export returns its selected acceptance output. -/
abbrev position : Nat := c.selection.position

section Meaning
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual Domain execution under the fixed retained scalar oracle ABI. -/
def verifier {m : Type → Type} [Monad m] (challenge : History F G → m F) (statement : art.Statement F G)
    (initial : History F G) (proof : Proof F G) : m (PIR.Outcome (Option Bool) × Proof F G) :=
  ScalarVerifier.verify c.imported.program c.context art.participant c.position challenge
    (encodeValues statement) initial proof

/-- The admitted original validator on a statement's published values, with the
replaced service at `handle`, read through its acceptance output. -/
def original (statement : art.Statement F G) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  ((c.imported.program.participant F G c.context.validator
      (ScalarVerifier.sourceInputs handle (encodeValues statement) c.selection.slots
        c.imported.program.payload.entry.inputs)).bind
    fun outputs => .done (outputs.get c.selection.output)).interpret CommonAdapter.project

/-- A source connection relates exactly the actual artifact and the admitted
source fixed by this compilation. It cannot select a verifier, source, oracle
map, extractor or resource boundary. Every maintained instance has a kernel
proof from its all-reply artifact binding. -/
structure SourceConnection : Prop where
  equation : ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (statement : art.Statement F G) (handle : Nat) (initial : History F G) (proof : Proof F G),
    c.verifier challenge statement initial proof =
      transform c.context challenge (c.original statement handle) initial proof

theorem transform_eq (connection : c.SourceConnection (F := F) (G := G))
    {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (statement : art.Statement F G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    c.verifier challenge statement initial proof =
      transform c.context challenge (c.original statement handle) initial proof :=
  connection.equation challenge statement handle initial proof

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

end Verdict

end ZkcSecurity.Endpoint
