module

public import Zkc.Source.Structured.OpenAdmission

@[expose] public section

namespace Zkc.Source.Structured

/-- Resolve one role-local boundary port. Equal-typed ports and other role copies
are never interchangeable. This is a structural check only. -/
def ContractSelector.resolve (signature : ProtocolSignature) (selector : ContractSelector) :
    Except String Ty := do
  let (types, scopes) := match selector.direction with
    | .input => (signature.inputs, signature.inputScopes)
    | .output => (signature.outputs, signature.outputScopes)
  let type ← requireSome types[selector.port]? "structured-contract-port"
  let role ← resolveRole signature.roles selector.role
  if !(scopes[selector.port]?.getD []).contains role then
    throw "structured-contract-role"
  if type.isService then throw "structured-contract-service"
  return type

def RelationApplication.check (snapshot : Snapshot) (signature : ProtocolSignature)
    (application : RelationApplication) : Except String Unit := do
  let relation ← requireSome (snapshot.relations.find? (·.name == application.relation))
    "structured-contract-relation"
  if application.selectors.length > 512 then throw "structured-contract-limit"
  let types ← application.selectors.mapM (ContractSelector.resolve signature)
  if types != relation.inputs then throw "structured-contract-arguments"

def RelationApplication.hasOutput (application : RelationApplication) : Bool :=
  application.selectors.any (·.direction == .output)

def ContractClause.check (snapshot : Snapshot) (signature : ProtocolSignature)
    (clause : ContractClause) : Except String Unit := do
  if !validString clause.name then throw "structured-contract-name"
  clause.subject.check snapshot signature
  if ((clause.kind == .input || clause.kind == .continuation) && clause.subject.hasOutput) ||
      (clause.kind == .output && !clause.subject.hasOutput) then
    throw "structured-contract-direction"
  match clause.kind, clause.residual with
  | .continuation, some residual =>
    residual.check snapshot signature
    if !residual.hasOutput then throw "structured-contract-residual"
  | .continuation, none => throw "structured-contract-residual"
  | _, some _ => throw "structured-contract-residual"
  | _, none => pure ()
  match clause.decision with
  | none => if clause.kind == .target then throw "structured-contract-decision"
  | some decision =>
    if clause.kind == .input || decision.direction != .output then
      throw "structured-contract-decision"
    if (← decision.resolve signature) != .boolean then throw "structured-contract-decision"

/-- Formula references must select a retained private Math definition with the
entire declared ABI. Preconditions are retained, not discharged by this check. -/
def checkFormulaLinks (snapshot : Snapshot) : Except String Unit := do
  for relation in snapshot.relations do
    match relation.kind, relation.formula with
    | "zkc.language.formula/0", some name =>
      let definition ← lookupDefinition snapshot name
      if !definition.acceptsEdge .call || definition.inputs != relation.inputs ||
          definition.outputs != relation.outputs then throw "structured-relation-formula"
    | "zkc.language.formula/0", none => throw "structured-relation-formula"
    | _, some _ => throw "structured-relation-formula"
    | _, none => pure ()

/-- An exhaustive owner table: every protocol exactly once, including unused
protocols and empty contracts. No proof claim follows from successful checking. -/
def checkContracts (snapshot : Snapshot) (headers : List ProtocolSignature) : Except String Unit := do
  if snapshot.contracts.length > 128 then throw "structured-contract-limit"
  let owners := snapshot.contracts.map (·.owner)
  if owners.eraseDups.length != owners.length || owners.length != headers.length ||
      !headers.all (fun header => owners.contains header.name) then
    throw "structured-contract-owners"
  for contract in snapshot.contracts do
    let signature ← requireSome (headers.find? (·.name == contract.owner))
      "structured-contract-owner"
    if contract.clauses.length > 512 then throw "structured-contract-limit"
    let names := contract.clauses.map (·.name)
    if names.eraseDups.length != names.length then throw "structured-contract-duplicate"
    for clause in contract.clauses do clause.check snapshot signature
  checkFormulaLinks snapshot

end Zkc.Source.Structured
