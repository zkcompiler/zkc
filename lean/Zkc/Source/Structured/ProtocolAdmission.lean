module

public import Zkc.Source.Structured.Checked

@[expose] public section

namespace Zkc.Source.Structured

def resolveRole (roles : List String) (name : String) : Except String Nat := do
  if !roles.contains name then throw "structured-role"
  return roles.findIdx (· == name)

def resolveScope (roles scope : List String) : Except String (List Nat) := do
  if scope.isEmpty || scope.eraseDups.length != scope.length then throw "structured-scope"
  scope.mapM (resolveRole roles)

def ProtocolInterface.resolve (interface : ProtocolInterface) (inputs outputs : List Ty) :
    Except String (List (List Nat) × List (List Nat)) := do
  if interface.roles.isEmpty || interface.roles.length > 16 ||
      !interface.roles.all validProtocolIdentifier ||
      interface.roles.eraseDups.length != interface.roles.length then throw "structured-roster"
  if interface.inputScopes.length != inputs.length ||
      interface.outputScopes.length != outputs.length then throw "structured-scope-count"
  let inputScopes ← interface.inputScopes.mapM (resolveScope interface.roles)
  let outputScopes ← interface.outputScopes.mapM (resolveScope interface.roles)
  for (type, scope) in inputs.zip inputScopes do
    if type.isService && scope.length != 1 then throw "structured-service-owner"
  return (inputScopes, outputScopes)

/-- Resolve every original protocol header before any body is lowered. -/
def resolveProtocolSignature (function : Function) : Except String ProtocolSignature := do
  if function.kind != .protocol || function.visibility != .publicDef ||
      !validProtocolIdentifier function.name then
    throw "structured-root-kind"
  let some interface := function.interface | throw "structured-protocol-interface"
  let (inputs, outputs) ← interface.resolve function.inputs function.outputs
  return ⟨function.name, interface.roles, function.inputs, function.outputs, inputs, outputs⟩

def Snapshot.protocolFunctions (snapshot : Snapshot) : List Function :=
  snapshot.definitions.filterMap fun definition => match definition with
    | .function f => if f.kind == .protocol then some f else none
    | _ => none

theorem Snapshot.mem_protocolFunctions {snapshot : Snapshot} {function : Function} :
    function ∈ snapshot.protocolFunctions ↔
      .function function ∈ snapshot.definitions ∧ function.kind = .protocol := by
  simp only [Snapshot.protocolFunctions, List.mem_filterMap]
  constructor
  · rintro ⟨definition, member, selected⟩
    cases definition with
    | function original =>
      change (if original.kind == .protocol then some original else none) = some function at selected
      by_cases kind : original.kind = .protocol
      · simp only [kind, beq_self_eq_true, ↓reduceIte] at selected
        cases Option.some.inj selected
        exact ⟨member, kind⟩
      · simp [kind] at selected
    | finite _ | realization _ | map _ => contradiction
  · rintro ⟨member, kind⟩
    exact ⟨.function function, member, by simp [kind]⟩

/-- Resolution retains all six signature fields and the exact original scope computation. -/
theorem resolveProtocolSignature_fields {function : Function} {signature : ProtocolSignature}
    (accepted : resolveProtocolSignature function = .ok signature) :
    ∃ interface, function.interface = some interface ∧
      signature.name = function.name ∧ signature.roles = interface.roles ∧
      signature.inputs = function.inputs ∧ signature.outputs = function.outputs ∧
      interface.resolve function.inputs function.outputs =
        .ok (signature.inputScopes, signature.outputScopes) := by
  unfold resolveProtocolSignature at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    exact ⟨_, by assumption, rfl, rfl, rfl, rfl, by assumption⟩

def collectProtocolHeaders (snapshot : Snapshot) : Except String (List ProtocolSignature) :=
  snapshot.protocolFunctions.mapM resolveProtocolSignature

/-- Validate the finite numerical substitution itself; the total role function's
arbitrary out-of-range default never contributes admission authority. -/
def resolveRoleSubstitution (caller : ProtocolInterface) (signature : ProtocolSignature)
    (roles : List String) : Except String (List Nat) := do
  if roles.length != signature.roles.length then throw "structured-role-substitution"
  let indices ← roles.mapM (resolveRole caller.roles)
  if indices.length = signature.roles.length ∧
      (∀ role ∈ indices, role < caller.roles.length) ∧ indices.Nodup then
    return indices
  else throw "structured-role-substitution"

theorem resolveRoleSubstitution_valid {caller : ProtocolInterface}
    {signature : ProtocolSignature} {roles : List String} {indices : List Nat}
    (accepted : resolveRoleSubstitution caller signature roles = .ok indices) :
    indices.length = signature.roles.length ∧
      (∀ role ∈ indices, role < caller.roles.length) ∧ indices.Nodup := by
  unfold resolveRoleSubstitution at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    assumption

/-- The retained original edge is checked independently of lowered signatures. -/
def resolveProtocolApplication (snapshot : Snapshot) (headers : List ProtocolSignature)
    (caller : ProtocolInterface) (name : String) (roles : List String) :
    Except String (ProtocolSignature × List Nat) := do
  if !validString name then throw "structured-protocol-callee"
  let callee ← lookupDefinition snapshot name
  if !callee.acceptsEdge .protocolApply then throw "structured-call-kind"
  let .function function := callee | throw "structured-call-kind"
  let signature ← resolveProtocolSignature function
  if !headers.contains signature then throw "structured-protocol-header"
  let .block instructions _ := function.body
  if instructions.any (fun (.instruction descriptor _ _ _ _) =>
      match descriptor with | .statement .. => true | _ => false) then
    throw "structured-applied-statement"
  let indices ← resolveRoleSubstitution caller signature roles
  return (signature, indices)

theorem resolveProtocolApplication_roles {snapshot : Snapshot} {headers : List ProtocolSignature}
    {caller : ProtocolInterface} {name : String} {roles : List String}
    {signature : ProtocolSignature} {indices : List Nat}
    (accepted : resolveProtocolApplication snapshot headers caller name roles = .ok (signature, indices)) :
    indices.length = signature.roles.length ∧
      (∀ role ∈ indices, role < caller.roles.length) ∧ indices.Nodup := by
  unfold resolveProtocolApplication at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    exact resolveRoleSubstitution_valid (by assumption)

/-- Successful application resolution identifies the original function and its
complete signature, and proves the actual source statement check succeeded.
This is a source-body check, not a property inferred from the signature. -/
theorem resolveProtocolApplication_source {snapshot : Snapshot} {headers : List ProtocolSignature}
    {caller : ProtocolInterface} {name : String} {roles : List String}
    {signature : ProtocolSignature} {indices : List Nat}
    (accepted : resolveProtocolApplication snapshot headers caller name roles = .ok (signature, indices)) :
    ∃ function instructions terminal,
      lookupDefinition snapshot name = .ok (.function function) ∧
      (Definition.function function).acceptsEdge .protocolApply = true ∧
      resolveProtocolSignature function = .ok signature ∧ signature ∈ headers ∧
      function.body = .block instructions terminal ∧
      instructions.any (fun (.instruction descriptor _ _ _ _) =>
        match descriptor with | .statement .. => true | _ => false) = false ∧
      resolveRoleSubstitution caller signature roles = .ok indices := by
  unfold resolveProtocolApplication at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    refine ⟨_, _, _, by assumption, ?_, by assumption, ?_, by assumption, ?_, by assumption⟩
    all_goals simp_all

/-- Complete signatures, including roster and scopes, resolve in the strict prefix. -/
def ProtocolDeclarationsLinked (helpers : List Helper)
    (available : List ProtocolSignature) : List CheckedProtocol → Prop
  | [] => True
  | definition :: rest =>
      definition.name ∉ available.map (·.name) ∧
      (∀ helper ∈ definition.helpers, helper ∈ helpers) ∧
      (∀ protocol ∈ definition.protocols, protocol ∈ available) ∧
      ProtocolDeclarationsLinked helpers (definition.signature :: available) rest

instance protocolDeclarationsLinkedDecidable (helpers : List Helper)
    (available : List ProtocolSignature) (definitions : List CheckedProtocol) :
    Decidable (ProtocolDeclarationsLinked helpers available definitions) :=
  match definitions with
  | [] => isTrue trivial
  | definition :: rest =>
    let _ := protocolDeclarationsLinkedDecidable helpers (definition.signature :: available) rest
    inferInstanceAs (Decidable
      (definition.name ∉ available.map (·.name) ∧
       (∀ helper ∈ definition.helpers, helper ∈ helpers) ∧
       (∀ protocol ∈ definition.protocols, protocol ∈ available) ∧
       ProtocolDeclarationsLinked helpers (definition.signature :: available) rest))

theorem ProtocolDeclarationsLinked.helpers {helpers : List Helper}
    {available : List ProtocolSignature} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked helpers available definitions) :
    ∀ definition ∈ definitions, ∀ helper ∈ definition.helpers, helper ∈ helpers := by
  induction definitions generalizing available with
  | nil => simp
  | cons head tail ih =>
    intro definition member
    rcases List.mem_cons.mp member with rfl | member
    · exact linked.2.1
    · exact ih linked.2.2.2 definition member

structure OrderedProtocol where
  definition : CheckedProtocol
  depth : Nat

/-- Remove exactly the first ready declaration, retaining every other body. -/
def takeReadyProtocol (ready : CheckedProtocol → Bool) :
    List CheckedProtocol → Option (CheckedProtocol × List CheckedProtocol)
  | [] => none
  | definition :: rest =>
    if ready definition then some (definition, rest)
    else (takeReadyProtocol ready rest).map fun (selected, pending) =>
      (selected, definition :: pending)

theorem takeReadyProtocol_perm {ready : CheckedProtocol → Bool}
    {pending : List CheckedProtocol} {selected : CheckedProtocol} {rest : List CheckedProtocol}
    (found : takeReadyProtocol ready pending = some (selected, rest)) :
    pending.Perm (selected :: rest) := by
  induction pending generalizing rest with
  | nil => simp [takeReadyProtocol] at found
  | cons definition pending ih =>
    simp only [takeReadyProtocol] at found
    split at found
    · cases Option.some.inj found
      exact .refl _
    · cases next : takeReadyProtocol ready pending with
      | none => simp [next] at found
      | some pair =>
        rcases pair with ⟨head, tail⟩
        simp only [next, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
        rcases found with ⟨rfl, rfl⟩
        exact (List.Perm.cons definition (ih next)).trans (List.Perm.swap _ _ _)

/-- Structured dependency edges count a leaf as zero, independently of native summaries. -/
def orderProtocols (helperDepths : List OrderedDefinition) :
    Nat → List CheckedProtocol → List OrderedProtocol → Except String (List OrderedProtocol)
  | _, [], ordered => .ok ordered
  | 0, _ :: _, _ => .error "structured-protocol-cycle"
  | remaining + 1, pending, ordered => do
    let some (next, rest) := takeReadyProtocol (fun definition =>
      definition.protocols.all (fun signature =>
        ordered.any (·.definition.signature == signature))) pending |
      throw "structured-protocol-cycle"
    let protocols : List OrderedProtocol ← next.protocols.mapM fun signature =>
      requireSome (ordered.find? (·.definition.signature == signature)) "structured-protocol-link"
    let helpers : List OrderedDefinition ← next.helpers.mapM fun helper =>
      requireSome (helperDepths.find? (·.definition.helper == helper)) "structured-root-link"
    let depth := ((protocols.map (fun value : OrderedProtocol => value.depth + 1)) ++ (helpers.map (fun value : OrderedDefinition => value.depth + 1))).foldl max 0
    if depth > 64 then throw "structured-reference-depth"
    orderProtocols helperDepths remaining rest
      (ordered ++ [⟨next, depth⟩])

/-- Topological ordering preserves every complete checked body in both directions. -/
theorem orderProtocols_perm {helpers : List OrderedDefinition} {fuel : Nat}
    {pending : List CheckedProtocol} {ordered result : List OrderedProtocol}
    (accepted : orderProtocols helpers fuel pending ordered = .ok result) :
    (result.map OrderedProtocol.definition).Perm
      (ordered.map OrderedProtocol.definition ++ pending) := by
  induction fuel generalizing pending ordered with
  | zero =>
    cases pending with
    | nil =>
      have same : ordered = result := by simpa [orderProtocols] using accepted
      subst result
      simp
    | cons head tail => simp [orderProtocols] at accepted
  | succ fuel ih =>
    cases pending with
    | nil =>
      have same : ordered = result := by simpa [orderProtocols] using accepted
      subst result
      simp
    | cons head tail =>
      simp only [orderProtocols, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
      split at accepted
      · rename_i next rest selected
        repeat' first | contradiction | split at accepted
        all_goals
          have preserved := ih accepted
          have picked := takeReadyProtocol_perm selected
          simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.cons_append, List.nil_append] at preserved
          exact preserved.trans
            (List.Perm.append_left (ordered.map OrderedProtocol.definition) picked.symm)
      · contradiction

end Zkc.Source.Structured
