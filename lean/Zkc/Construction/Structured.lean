module

public import Zkc.Construction.FiatShamir
public import Zkc.Source.Structured.Vocabulary

@[expose] public section

/-! The transcript-construction rule applied to an original structured export.

`admit` reads the original entry's role roster and port scopes, checks that the
exported policy publishes exactly the validator's data inputs, derives the
occurrence context from that roster and the policy, and runs the construction
rule. Public coverage is a deployment requirement: the host's initial binding
absorbs exactly these inputs, so a policy omitting part of the statement would
leave it out of every challenge.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source

/-- The original entry's protocol signature and roster. -/
def entryInterface (original : Structured.Snapshot) :
    Option (List Structured.Ty × Structured.ProtocolInterface) :=
  match original.definitions.find? (·.name == original.entry) with
  | some (.function function) => function.interface.map (function.inputs, ·)
  | _ => none

/-- Original input positions available to `role` that carry data rather than a
service reference, in original order. -/
def dataInputs (inputs : List Structured.Ty) (scopes : List (List String)) (role : String) :
    List Nat :=
  ((inputs.zip scopes).zipIdx.filter fun ((ty, scope), _) =>
    scope.contains role && !(ty matches .service _)).map (·.2)

/-- The occurrence context fixed by the policy and the original roster. Only
the installed native construction with one replaced service is admitted. -/
def Context.ofPolicy (policy : Policy) (roles : List String) : Option Context :=
  match policy.services with
  | [service] =>
      if policy.construction = "" ∧ policy.producer ∈ roles ∧ policy.validator ∈ roles ∧
          policy.producer ≠ policy.validator then
        some ⟨policy.entry, roles, roles.idxOf policy.producer, roles.idxOf policy.validator,
          service, policy.suite, policy.draws⟩
      else none
  | _ => none

def exportContext (original : Structured.Snapshot) (participant : Participant) : Option Context :=
  match entryInterface original with
  | some (inputs, interface) =>
      if participant.policy.entry = original.entry ∧
          participant.policy.publicInputs =
            dataInputs inputs interface.inputScopes participant.policy.validator then
        Context.ofPolicy participant.policy interface.roles
      else none
  | none => none

/-- The complete per-compile check of a constructed validator against its
original export. -/
def checkExport (original : Structured.Snapshot) (participant : Participant) : Bool :=
  match exportContext original participant with
  | some context => check context participant
  | none => false

theorem checkExport_sound {original : Structured.Snapshot} {participant : Participant}
    (accepted : checkExport original participant = true) :
    ∃ context, exportContext original participant = some context ∧
      check context participant = true := by
  unfold checkExport at accepted
  split at accepted
  · rename_i context found
    exact ⟨context, found, accepted⟩
  · cases accepted

end Zkc.Construction
