module

public import Zkc.Frontend.Emit.Root
public import Zkc.Frontend.Typed.Find
public import Zkc.Core.Admission.Check

@[expose] public section
set_option autoImplicit false
namespace Zkc.Frontend.Emit
open Static
open Typing (EmitM EmitFailure)

/-- Source diagnostic groups interpreted from a concrete Core refusal. -/
inductive Requirement where
  | ordered | positive | position | slice | size | bound | domain | maximum
  | core (rule : Core.Rule)
  deriving DecidableEq, Repr, Inhabited

inductive Condition where
  | order | upperSize | upperLength | other
  deriving Inhabited

structure Explained where
  requirement : Requirement
  condition : Condition := .other
  operands : Nat → Option Core.Range := fun _ => none

structure Finding where
  node : Option Typed.NodeId
  role : Option Nat
  explained : Explained

def explainOperation {V : Core.Vocabulary} (op : Core.LocalRaw V) (q : Core.Requirement (Core.LocalRaw V))
    (ranges : List (Option Core.Range)) : Explained :=
  let operandRange (index : Nat) := (q.operands.zip ranges).findSome? fun
    | (.arg i, r) => if i == index then r else none
    | _ => none
  let (requirement, condition) : Requirement × Condition := match op with
    | .owned .natSub .. => (.ordered, .other)
    | .owned .natDiv .. | .owned .natRem .. => (.positive, .other)
    | .owned .seqAt .. => (.position, .other)
    | .owned .seqSlice types _ =>
      let why := match q with
        | .le (.arg 1) (.arg 2) => Condition.order
        | .le _ (.apply ..) => if types.head? matches some (.seq _ (some _)) then .upperSize else .upperLength
        | _ => .other
      (.slice, why)
    | .owned .seqSized .. => (.size, .other)
    | .owned .natBelow .. => (.bound, .other)
    | .row _ => (.domain, .other)
    | _ => (.core .domain, .other)
  ⟨requirement, condition, operandRange⟩

def localFinding {V : Core.Vocabulary} (nodes : Array Typed.NodeId) (r : Core.ProgramRefusal V) : Finding :=
  let explained : Explained := match r.detail with
    | .unjustified op q ranges => explainOperation op q ranges
    | _ => { requirement := .core r.rule }
  ⟨r.place.instruction.bind fun k => nodes[k.number]?, r.place.role, explained⟩

/-- Check the actual executable definition against previously resolved call signatures. -/
def checkFunction (state : Compile.State) (inst : InstanceId) (body : Typed.FunctionBody) (result : ClosedType) :
    Except EmitFailure (List Finding) := (do
  let calls := calledIn body
  let b ← bindCalls {} calls
  let headers ← calleeHeaders b calls
  let (definition, nodes) ← Named.functionDefinition (← bodyContext b) ⟨inst⟩ result body
  match Core.check headers definition with
  | .ok _ => return []
  | .error errors => errors.mapM fun
    | .definition (.fn failure) => pure (localFinding nodes failure)
    | _ => Typing.defect "non-function refusal during function checking" : EmitM _).run state

structure ProtocolChecked where
  origin : DefinitionOrigin
  findings : List Finding

/-- Recover the source diagnostic group from the exact clause reported by the role checker. -/
def roleFinding {V : Core.Vocabulary} (nodes : Array Typed.NodeId) (r : Core.Refusal (Core.LTy V) (Core.RoleRaw V)) :
    Finding :=
  let explained : Explained := match r.detail with
    | .unjustifiedAssertion (.compute holders op) clause =>
      match ((Core.localOpFacts ([] : List (Core.FnHeader V))).requires op).find? (fun q =>
          Core.BodyAnalysis.RoleContracts.clause holders (Core.BodyAnalysis.builtinClause q) == clause) with
      | some q => explainOperation op q []
      | none => {requirement := .core r.rule}
    | _ => {requirement := .core r.rule}
  ⟨r.place.instruction.bind fun k => nodes[k.number]?, r.place.role, explained⟩

def checkProtocol (state : Compile.State) (inst : InstanceId) : Except EmitFailure ProtocolChecked := do
  let root ← Typing.emitRoot state inst
  let some origin := root.origins.back? | throw (.defect "missing protocol origin")
  unless origin.definition.number == inst do throw (.defect "wrong root definition")
  match Core.admitFrom .empty [] root.named.definitions with
  | .ok (_, bounds) =>
    let missing := origin.dynamicLoops.toList.flatMap fun (key, roles) =>
      roles.filterMap fun role =>
        if bounds.any (fun (place, _) => place.definition == origin.definition &&
            place.instruction == some key && place.role == some role) then none
        else some (⟨origin.nodes[key.number]?, some role, { requirement := .maximum }⟩ : Finding)
    return ⟨origin, missing⟩
  | .error errors =>
    let findings ← errors.mapM (fun refusal => match refusal with
      | .projection r => do
        unless r.place.definition.number == inst do throw (.defect "previously checked dependency refused")
        pure (roleFinding origin.nodes r)
      | .definition (.protocol r) => pure ⟨r.place.instruction.bind fun k => origin.nodes[k.number]?,
          r.place.role, {requirement := .core r.rule}⟩
      | _ => throw (.defect "non-protocol refusal during protocol checking"))
    return ⟨origin, findings⟩

end Zkc.Frontend.Emit
