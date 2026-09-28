import Tools.Interactive.GenericModule
import Tools.Interactive.Projection

/-! Independently reconstruct the bounded closed-root realization from source.
Generated spelling is internal; correspondence compares alpha-normalized actual
participants and the entire actual sampler body and binding application. -/

set_option autoImplicit false

namespace Tools.Interactive.Generic

structure RootPort where
  binding : Name
  role : Name
  root : Name
  service : Name
  stateType : Ty
  input : Name
  output : Nat
  deriving BEq, Repr

structure RootRealization where
  participants : List Participant
  functions : List Explicit.Function := []
  ports : List RootPort := []

def realizeRoots (source : Source) (participants : List Participant) : Result RootRealization := do
  if source.roots.isEmpty then return ⟨participants, [], []⟩
  ensure ((participants.map Participant.binding).eraseDups.length == 1)
    "interactive-root-realization-instances"
  for p in participants do
    for instruction in p.body do
      ensure (!(instruction matches .call ..) && !(instruction matches .loop ..))
        "interactive-root-realization-control"
  let .explicit bindings := source.environment
  let mut result := RootRealization.mk participants [] []
  for (root, index) in source.roots.zipIdx do
    let [owner] := root.owners | throw "interactive-root-realization-owners"
    let service ← lookup root.service (bindings.map fun b => (b.name, b))
    let (stateType, replyType) ← Bindings.entropyService service
    let uses := result.participants.filter fun p => p.body.any fun i =>
      match i with | .query _ _ name _ _ => name == root.name | _ => false
    if uses.isEmpty then continue
    let [participant] := uses | throw "interactive-root-realization-owner"
    ensure (participant.role == owner) "interactive-root-realization-owner"
    let origin := "query_" ++ toString index
    let key := "@" ++ origin
    let function : Function := ⟨key, [("state", stateType.spelling)],
      [replyType.spelling, stateType.spelling], some [
        .op "draw" root.service [] ["state"] ["reply", "next"], .ret ["reply", "next"]]⟩
    result := { result with functions := result.functions ++ [⟨function, some ⟨origin, []⟩⟩] }
    -- '@' is excluded from authored names, so introduced binders cannot alias
    -- an authored input or result. Only their incidence survives normalization.
    let input := "@root_input_" ++ toString index
    let mut current := input
    let mut body := []
    for (instruction, occurrence) in participant.body.zipIdx do
      match instruction with
      | .query site role name inputs outputs =>
          if name == root.name then
            ensure (role.isEmpty && inputs.isEmpty && outputs.length == 1)
              "interactive-query-signature"
            let next := "@root_state_" ++ toString index ++ "_" ++ toString occurrence
            body := .localCall site "" key [current] (outputs ++ [next]) :: body
            current := next
          else body := instruction :: body
      | .ret values => body := .ret (values ++ [current]) :: body
      | other => body := other :: body
    let realized := { participant with
      arguments := participant.arguments ++ [(input, stateType.spelling)]
      results := participant.results ++ [stateType.spelling]
      body := body.reverse }
    result := { result with
      participants := result.participants.map fun p =>
        if p.name == participant.name then realized else p
      ports := result.ports ++ [⟨participant.binding, owner, root.name, service.contract,
        stateType.spelling, input, participant.results.length⟩] }
  return result

end Tools.Interactive.Generic
