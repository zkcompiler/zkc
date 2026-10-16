module

public import Zkc.Construction.FiatShamir
public import Zkc.Source.Structured.Vocabulary

@[expose] public section

/-! The transcript-construction rule applied to an original structured export.

`checkExport` reads the original entry's role roster, port types and scopes;
checks that the exported policy publishes exactly the validator's data inputs,
that these are the exported validator's data inputs, and that the replaced
service is a validator service input; derives the occurrence context from the
roster, the policy and that service's contract; and runs the construction
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

/-- The data sort of an original input type, if it is a scalar. -/
def dataSort? : Structured.Ty → Option Common.Native.Ty
  | .boolean => some .boolean
  | .field domain => some (.field domain)
  | .group domain => some (.group domain)
  | _ => none

/-- The occurrence context fixed by the policy, the original roster and the
replaced service's contract. Only the installed native construction with one
replaced service is admitted. -/
def Context.ofPolicy (policy : Policy) (roles : List String) (contract : String) :
    Option Context :=
  match policy.services with
  | [service] =>
      if policy.construction = "" ∧ service < 1024 ∧ policy.producer ∈ roles ∧
          policy.validator ∈ roles ∧ policy.producer ≠ policy.validator ∧
          policy.draws.Nodup then
        some ⟨policy.entry, roles, roles.idxOf policy.producer, roles.idxOf policy.validator,
          service, contract, policy.suite, policy.draws⟩
      else none
  | _ => none

/-- The context of an export checked against its original entry: same entry;
the policy publishes exactly the validator's data inputs, which are the
exported data inputs with the same sorts; the replaced service is a validator
service input of the original, whose contract the challenges must carry. -/
def exportContext (original : Structured.Snapshot) (participant : Participant) : Option Context :=
  match entryInterface original with
  | some (inputs, interface) =>
      let policy := participant.policy
      match policy.services with
      | [service] =>
          match inputs[service]?, interface.inputScopes[service]? with
          | some (.service contract), some scope =>
              if policy.entry = original.entry ∧ scope.contains policy.validator ∧
                  policy.publicInputs = dataInputs inputs interface.inputScopes policy.validator ∧
                  participant.inputs.dropLast.map some =
                    policy.publicInputs.map (fun index =>
                      (inputs[index]? >>= dataSort?).map ValueSort.data) then
                Context.ofPolicy policy interface.roles contract
              else none
          | _, _ => none
      | _ => none
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
