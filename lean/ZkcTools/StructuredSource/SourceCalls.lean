module

public import Zkc.Source.Structured.ContractCalls
public meta import ZkcTools.Generation.Commands
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.Meta.Reduce

@[expose] public section

/-! Source-derived call headers for companions. Labels and role maps are read
from the retained typed occurrence. The materialized header is connected to
that exact occurrence by a kernel-checked equation; a lookup is no reachability
or execution proof. -/
public meta section
namespace ZkcTools.StructuredSource.SourceCalls
open Lean Meta Elab Command Term
open Zkc.Source Zkc.Source.Structured

/-- An untrusted proposal carries a fully typed constructor witness. It walks
only the source spine rather than reducing a dependent inventory and its filters
again at each projection. The kernel checks the resulting occurrence term. -/
structure Candidate where
  header : Expr
  witness : Expr
  path : List Nat
  deriving Inhabited

partial def candidates (source signature : Expr) : MetaM (Array Candidate) := do
  let source ← whnf source
  let args := source.getAppArgs
  if source.isAppOf ``Region.ret || source.isAppOf ``Region.stop then return #[]
  if source.isAppOf ``Region.bind then
    let body := args[args.size - 2]!
    let next := args.back!
    let first ← (← candidates body signature).mapM fun candidate => do
      return { candidate with
        path := 0 :: candidate.path
        witness := ← mkAppM ``CallOccurrence.bindBody #[body, next, candidate.witness] }
    let rest ← (← candidates next signature).mapM fun candidate => do
      return { candidate with
        path := 1 :: candidate.path
        witness := ← mkAppM ``CallOccurrence.bindNext #[body, next, candidate.witness] }
    return first ++ rest
  unless source.isAppOf ``Region.letOp do
    throwError "protocol-call-selection: source structure is not statically known"
  let op := args[args.size - 4]!
  let operands := args[args.size - 3]!
  let bodies := args[args.size - 2]!
  let next := args.back!
  let operation ← whnf op
  let mut result := #[]
  if operation.isAppOf ``ProtocolOp.protocolApply then
    let actual := operation.getAppArgs[0]!
    if ← isDefEq actual signature then
      let roles := operation.getAppArgs[1]!
      let site := operation.getAppArgs[2]!
      let witness ← mkAppM ``CallOccurrence.here #[actual, roles, site, operands, next]
      let header ← mkAppM ``CallOccurrence.callSite #[witness]
      result := result.push ⟨← reduce header, witness, []⟩
  for candidate in ← candidates next signature do
    result := result.push { candidate with
      path := 1 :: candidate.path
      witness := ← mkAppM ``CallOccurrence.next #[op, operands, bodies, next, candidate.witness] }
  if operation.isAppOf ``ProtocolOp.repeat then
    let regions ← whnf bodies
    unless regions.isAppOf ``Regions.cons do throwError "protocol-call-selection: malformed repeat"
    let body := regions.getAppArgs[regions.getAppArgs.size - 2]!
    for candidate in ← candidates body signature do
      result := result.push { candidate with
        path := 0 :: candidate.path
        witness := ← mkAppM ``CallOccurrence.repeatBody
          #[operation.getAppArgs[0]!, operation.getAppArgs[1]!, operands, body, next, candidate.witness] }
  return result

syntax (name := protocolCall) "protocol_call " ident " from " term
  " to " term (" at " term)? : command

def generate : CommandElab := fun stx => do
  let `(protocol_call $name:ident from $source:term to $callee:term $[at $path:term]?) := stx
    | throwUnsupportedSyntax
  let fullName := (← getCurrNamespace) ++ name.getId
  let selected := mkIdent (name.getId.appendAfter "_occurrence")
  let fullSelected := (← getCurrNamespace) ++ selected.getId
  liftTermElabM <| withoutErrToSorry do
    let expression ← elabTerm source none
    let signature ← elabTermEnsuringType callee (Lean.mkConst ``ProtocolSignature)
    synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    let signature ← instantiateMVars signature
    if expression.hasFVar || expression.hasMVar || signature.hasFVar || signature.hasMVar then
      throwError "protocol-call-open-source: instantiate static parameters first"
    let mut found ← candidates expression signature
    if let some path := path then
      let requested ← elabTermEnsuringType path (mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``Nat))
      synthesizeSyntheticMVarsNoPostponing
      found ← found.filterM fun candidate => do
        isDefEq requested (← mkListLit (Lean.mkConst ``Nat) (candidate.path.map mkNatLit))
    unless found.size == 1 do
      throwError "protocol-call-selection: expected one matching typed occurrence; select an explicit path when ambiguous"
    let candidate := found[0]!
    let header ← instantiateMVars candidate.header
    let witness ← instantiateMVars candidate.witness
    if header.hasMVar || header.hasFVar || witness.hasMVar || witness.hasFVar then
      throwError "protocol-call-generation: unresolved source coordinates"
    let occurrenceType ← mkAppM ``CallOccurrence #[expression]
    for (declarationName, type, value) in
        [(fullName, Lean.mkConst ``CallSite, header), (fullSelected, occurrenceType, witness)] do
      let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
      addDecl (.defnDecl {
        name := declarationName
        levelParams := []
        type := type
        value := value
        hints := hints
        safety := .safe
      })
        (forceExpose := true)
      modifyEnv fun environment => addNoncomputable environment declarationName
  let equation := mkIdent (name.getId.appendAfter "_selected")
  let signatureEq := mkIdent (name.getId.appendAfter "_signature")
  elabCommand (← `(command| theorem $equation : ($selected).callSite = $name := by rfl))
  elabCommand (← `(command| theorem $signatureEq : ($name).signature = $callee := by rfl))

@[command_elab protocolCall]
def elabProtocolCall : CommandElab := fun stx =>
  ZkcTools.Generation.Commands.atomic "protocol-call-generation" (generate stx)

end ZkcTools.StructuredSource.SourceCalls
