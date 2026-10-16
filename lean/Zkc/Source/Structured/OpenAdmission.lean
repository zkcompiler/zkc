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
      !interface.roles.all validString ||
      interface.roles.eraseDups.length != interface.roles.length then throw "structured-roster"
  if interface.inputScopes.length != inputs.length ||
      interface.outputScopes.length != outputs.length then throw "structured-scope-count"
  let inputScopes ← interface.inputScopes.mapM (resolveScope interface.roles)
  let outputScopes ← interface.outputScopes.mapM (resolveScope interface.roles)
  for (type, scope) in inputs.zip inputScopes do
    if type.isService && scope.length != 1 then throw "structured-service-owner"
  return (inputScopes, outputScopes)

def Relation.valid (relation : Relation) : Bool :=
  validString relation.name && validString relation.kind && validString relation.key &&
  validString relation.revision && validTypes relation.inputs &&
  !relation.inputs.any Ty.isService && relation.outputs == [.boolean] &&
  relation.purposes.length == relation.inputs.length &&
  relation.purposes.all (fun purpose => ["parameter", "statement", "witness"].contains purpose)

def resolveProtocolOp (snapshot : Snapshot) (domains : List DomainSpec)
    (function : Function) (interface : ProtocolInterface) (inputScopes : List (List Nat))
    (context : List Ty) (origins : List (Option Nat)) (facts : Facts) (identities : List Nat)
    (descriptor : Descriptor) (operands : List Nat) (results : List Ty) (site : String) :
    LowerM ProtocolOp := do
  if !validRefs operands || !validTypes results || results.any Ty.isService then
    throw "structured-protocol-signature"
  let arguments ← typesAt context operands
  let role := resolveRole interface.roles
  match descriptor with
  | .localCall name owner =>
    recordSite site true
    let owner ← role owner
    let callee ← lookupDefinition snapshot name
    if callee.kind != .local then throw "structured-call-kind"
    match callee with
    | .finite _ => throw "structured-call-kind"
    | .function _ => pure ()
    return .localCall ⟨name, .local, callee.inputs, callee.outputs⟩ rfl owner site
  | .guard owner =>
    recordSite site true
    return .guard (← role owner) site
  | .exchange sender receiver =>
    recordSite site true
    let sender ← role sender
    let receiver ← role receiver
    if sender == receiver then throw "structured-exchange-endpoints"
    let [type] := arguments | throw "structured-exchange-signature"
    if type.isService then throw "structured-service-use"
    return .exchange type sender receiver site
  | .restrict selected =>
    if !site.isEmpty then throw "structured-pure-site"
    recordSite site false
    let [type] := arguments | throw "structured-restrict-signature"
    if type.isService then throw "structured-service-use"
    return .restrict type (← resolveScope interface.roles selected)
  | .draw owner field =>
    recordSite site true
    if field != scalarDomain then throw "structured-field-domain"
    let owner ← role owner
    let [operand] := operands | throw "structured-draw-signature"
    let some (some input) := origins[operand]? | throw "structured-service-root"
    if inputScopes[input]? != some [owner] then throw "structured-service-owner"
    if arguments != [.service scalarServiceContract] then throw "structured-service-contract"
    return .draw owner field site
  | .statement relation selectors acceptance =>
    if !site.isEmpty then throw "structured-pure-site"
    recordSite site false
    let some declaration := snapshot.relations.find? (·.name == relation) |
      throw "structured-unknown-relation"
    if arguments != declaration.inputs || !results.isEmpty || arguments.any Ty.isService then
      throw "structured-statement-signature"
    if selectors.length != operands.length || function.outputs[acceptance]? != some .boolean then
      throw "structured-statement-acceptance"
    for (operand, selector) in operands.zip selectors do
      let selected ← role selector
      let some (some input) := origins[operand]? | throw "structured-statement-input"
      if !(inputScopes[input]?.getD []).contains selected then throw "structured-statement-selector"
    return .statement relation arguments selectors acceptance
  | _ =>
    let op ← resolveOp snapshot domains .protocol context facts identities descriptor operands results site
    if allowed : op.isCalculation = true then return .calculate op allowed
    else throw "structured-protocol-operation"

/-- Protocol roots have no nested regions in this profile. Their SSA and typed
formation are still the shared RawRegion/Region formation, not a second IR. -/
def lowerProtocolInstructions (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (function : Function) (interface : ProtocolInterface)
    (scopes : List (List Nat)) (terminal : Terminator) :
    List Ty → List (Option Nat) → Facts → List Nat → List Instruction →
      LowerM (RawRegion Ty ProtocolOp)
  | _, _, _, _, [] => do
    let .ret refs := terminal | throw "structured-protocol-terminator"
    if !validRefs refs then throw "structured-reference-limit"
    return .ret refs
  | context, origins, facts, identities, .instruction descriptor operands results regions site :: rest => do
    if !regions.isEmpty then throw "structured-protocol-region"
    let op ← resolveProtocolOp snapshot domains function interface scopes context origins facts identities
      descriptor operands results site
    let operandOrigins := operands.map fun index => identities[index]?
    let resultOrigins := (resultIdentities summaries descriptor operandOrigins results.length).zipIdx.map
      fun (source, result) => match source with
        | some original => original + results.length
        | none => result
    let next ← lowerProtocolInstructions snapshot domains summaries function interface scopes terminal
      (results ++ context) (List.replicate results.length none ++ origins)
      (facts.shift results.length) (resultOrigins ++ identities.map (· + results.length)) rest
    return .letOp (.mark site) [] [] .nil (.letOp op operands results .nil next)

def checkProtocol (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (function : Function) : Except String CheckedProtocol := do
  if function.kind != .protocol then throw "structured-root-kind"
  let some interface := function.interface | throw "structured-protocol-interface"
  let (inputScopes, outputScopes) ← interface.resolve function.inputs function.outputs
  let .block instructions terminal := function.body
  let raw ← (lowerProtocolInstructions snapshot domains summaries function interface inputScopes terminal
    function.inputs ((List.range function.inputs.length).map some) []
    (List.range function.inputs.length) instructions).run' {}
  match formed : raw.elaborate (dialect := protocolDialect) function.inputs function.outputs with
  | .error _ => throw "structured-formation"
  | .ok body => return ⟨function.name, interface.roles, function.inputs, function.outputs,
      inputScopes, outputScopes, raw, body, formed⟩

/-- Closed value profile. Group values retain the same explicit F/G assignment;
service capabilities remain at the open boundary. -/
def Ty.closedValue : Ty → Bool
  | .boolean | .index | .field _ | .vector _ | .group _ => true
  | .service _ => false

def Op.closedValues (op : Op) : Bool := (op.arguments ++ op.results).all Ty.closedValue

def ProtocolOp.closed (op : ProtocolOp) : Except String Op :=
  match op with
  | .calculate calculation _ =>
    if calculation.closedValues then .ok calculation else .error "structured-closed-type"
  | .localCall helper _ 0 _ => .ok (.invoke helper)
  | .guard 0 _ => .ok .guard
  | .mark site => .ok (.mark site)
  | _ => .error "structured-open-profile"

def closedRootTree : RawRegion Ty ProtocolOp → Except String (RawRegion Ty Op)
  | .ret refs => .ok (.ret refs)
  | .stop _ => .error "structured-protocol-terminator"
  | .letOp op args results .nil next => do
    return .letOp (← op.closed) args results .nil (← closedRootTree next)
  | .letOp _ _ _ (.cons ..) _ => .error "structured-protocol-region"
  | .bind mid body next => do
    return .bind mid (← closedRootTree body) (← closedRootTree next)

end Zkc.Source.Structured
