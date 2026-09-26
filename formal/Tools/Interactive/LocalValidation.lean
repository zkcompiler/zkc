import Tools.Interactive.GenericModule
import Tools.Interactive.Admission

/-! Validate a selected local body against original generic source. Physical
conversions occur exactly at the required operand/result crossings; the source
order, logical sites and consumed resources cannot be changed by the candidate.
This check is one component of whole-source correspondence, not admission alone. -/

set_option autoImplicit false

namespace Tools.Interactive.Generic

private def boundaryType (physical : Bool) (ty : Bindings.ValueType) : Bindings.ValueType :=
  if physical then { ty with representation := Bindings.defaultRepresentation ty.kind ty.identity } else ty

private abbrev Environment := List (Name × (Name × Bindings.ValueType))

private def operationBinding (candidate : Explicit.CandidateLocals) (name : Name) : Result Bindings.Declaration :=
  lookup name (candidate.bindings.map fun b => (b.name, b))

private def firstLogical (candidate : Explicit.CandidateLocals) : List Instruction → Result Bindings.Declaration
  | .op _ binding _ _ _ :: rest => do
      let binding ← operationBinding candidate binding
      if binding.contract == "table.relayout" then firstLogical candidate rest else pure binding
  | _ => .error "local-operation-correspondence"

private def crossing (candidate : Explicit.CandidateLocals) (input : Name × Bindings.ValueType)
    (target : Bindings.ValueType) (body : List Instruction) : Result (Name × List Instruction) := do
  if input.2 == target then return (input.1, body)
  ensure (candidate.physical && input.2.kind == "table" && target.kind == "table" &&
    input.2.identity == target.identity) "local-representation-crossing"
  let .op _ binding attrs operands outputs :: rest := body | throw "local-missing-conversion"
  let binding ← operationBinding candidate binding
  ensure (binding.contract == "table.relayout" && attrs.isEmpty && operands == [input.1])
    "local-conversion-correspondence"
  let signature ← Bindings.resolve true binding
  ensure (signature.inputs == [input.2] && signature.outputs == [target]) "local-conversion-endpoints"
  let [output] := outputs | throw "local-conversion-arity"
  return (output, rest)

private def crossOperands (candidate : Explicit.CandidateLocals) (env : Environment)
    (inputs : List Name) (types : List Bindings.ValueType) (body : List Instruction) :
    Result (List Name × List Instruction) := do
  ensure (inputs.length == types.length) "local-operand-arity"
  let mut result := []
  let mut rest := body
  for (input, ty) in inputs.zip types do
    let (value, tail) ← crossing candidate (← lookup input env) ty rest
    result := result ++ [value]
    rest := tail
  return (result, rest)

/-- Control ports use the default representation. Consume crossings in operand
order and retain source names for checking the region against converted values.
This environment is local to the use; later uses require their own crossings. -/
private def crossControlOperands (candidate : Explicit.CandidateLocals) (env : Environment)
    (inputs : List Name) (body : List Instruction) : Result (Environment × List Instruction) := do
  let types ← inputs.mapM fun input => do return boundaryType candidate.physical (← lookup input env).2
  let (values, rest) ← crossOperands candidate env inputs types body
  return (inputs.zip (values.zip types), rest)

structure LocalCorrespondence where
  configuration : Name
  function : Name
  arguments : List (Name × Name)
  deriving BEq, Repr

private def compareBody (bindings : List OperationBinding) (candidate : Explicit.CandidateLocals) :
    Nat → Bool → Environment → List Bindings.ValueType → List Instruction → List Instruction → Result Unit
  | 0, _, _, _, _, _ => .error "body-depth-limit"
  | depth + 1, region, initial, outputTypes, original, body => do
      let mut rest := body
      let mut env := initial
      for instruction in original do
        match instruction with
        | .op site key expectedAttrs operands results =>
            let expected ← lookup key (bindings.map fun b => (b.name, b))
            let binding ← firstLogical candidate rest
            ensure (binding.contract == expected.contract && binding.arguments == expected.arguments)
              "local-binding-correspondence"
            if !expected.implementation.isEmpty then
              ensure (binding.implementation == expected.implementation) "local-selection-correspondence"
            let signature ← Bindings.resolve candidate.physical binding
            let (inputs, tail) ← crossOperands candidate env operands signature.inputs rest
            let .op actualSite name attrs actual outputs :: tail := tail | throw "local-operation-correspondence"
            ensure (actualSite == site && name == binding.name && actual == inputs) "local-operation-correspondence"
            ensure (attrs == expectedAttrs) "local-attributes-correspondence"
            Bindings.attributes false binding.contract attrs (binding.arguments.headD Bindings.fr)
            ensure (outputs.length == results.length && outputs.length == signature.outputs.length)
              "local-result-correspondence"
            env := env ++ (results.zip (outputs.zip signature.outputs))
            rest := tail
        | .variant site ty alternative payload output =>
            let parsed ← Bindings.valueType false ty
            let target := boundaryType candidate.physical parsed
            let types ← (← Bindings.variantPayload target.spelling alternative).mapM (Bindings.valueType candidate.physical)
            let (inputs, tail) ← crossOperands candidate env payload types rest
            let .variant actualSite actualTy actualAlternative actualPayload actualOutput :: tail := tail
              | throw "local-variant-correspondence"
            ensure (site == actualSite && target.spelling == actualTy && alternative == actualAlternative &&
              inputs == actualPayload) "local-variant-correspondence"
            env := env ++ [(output, (actualOutput, target))]
            rest := tail
        | .localMatch site input captures arms outputs =>
            let (operands, tail) ← crossControlOperands candidate env (input :: captures) rest
            let .localMatch actualSite actualInput actualCaptures actualArms actualOutputs :: tail := tail
              | throw "local-control-correspondence"
            let scrutinee ← lookup input operands
            let captured := operands.drop 1
            ensure (site == actualSite && actualInput == scrutinee.1 &&
              actualCaptures == captured.map (fun (_, value, _) => value) &&
              arms.map Prod.fst == actualArms.map Prod.fst) "local-control-correspondence"
            let mut resultTypes : Option (List Ty) := none
            for (label, payload, nested) in arms do
              let leaves ← Bindings.variantPayload {scrutinee.2 with representation := ""}.spelling label
              let context := (payload.zip leaves).map (fun (n, ty) => Port.mk n "" ty) ++
                captured.map (fun (n, _, ty) => Port.mk n "" {ty with representation := ""}.spelling)
              let result ← admitLocalFlow (environmentSignature (.explicit bindings) "logical") false [] limits.depth true context resultTypes nested
              if let some types := result then resultTypes := some types
            let types ← (resultTypes.getD []).mapM fun ty => do return boundaryType candidate.physical (← Bindings.valueType false ty)
            for ((label, payload, nested), (_, actualPayload, actualNested)) in arms.zip actualArms do
              let leaves ← (← Bindings.variantPayload scrutinee.2.spelling label).mapM (Bindings.valueType candidate.physical)
              ensure (payload.length == actualPayload.length && payload.length == leaves.length) "local-result-correspondence"
              let inner := payload.zip (actualPayload.zip leaves) ++ captured
              compareBody bindings candidate depth true inner types nested actualNested
            ensure (outputs.length == actualOutputs.length && outputs.length == types.length) "local-result-correspondence"
            env := env ++ outputs.zip (actualOutputs.zip types)
            rest := tail
        | .stop site owner reason =>
            ensure (rest == [.stop site owner reason]) "local-stop-correspondence"
            rest := []
        | .conditional site condition captures yes no outputs =>
            let (operands, tail) ← crossControlOperands candidate env (condition :: captures) rest
            let .conditional actualSite actualCondition actualCaptures actualYes actualNo actualOutputs :: tail := tail
              | throw "local-control-correspondence"
            let captured := operands.drop 1
            ensure (site == actualSite && actualCondition == (← lookup condition operands).1 &&
              actualCaptures == captured.map (fun (_, value, _) => value)) "local-control-correspondence"
            let sourceContext := captured.map fun (n, _, ty) => Port.mk n "" {ty with representation := ""}.spelling
            let yesTypes ← admitLocalFlow (environmentSignature (.explicit bindings) "logical") false [] limits.depth true sourceContext none yes
            let noTypes ← admitLocalFlow (environmentSignature (.explicit bindings) "logical") false [] limits.depth true sourceContext yesTypes no
            let types ← (yesTypes.or noTypes |>.getD []).mapM fun ty => do return boundaryType candidate.physical (← Bindings.valueType false ty)
            compareBody bindings candidate depth true captured types yes actualYes
            compareBody bindings candidate depth true captured types no actualNo
            ensure (outputs.length == actualOutputs.length && outputs.length == types.length) "local-result-correspondence"
            env := env ++ outputs.zip (actualOutputs.zip types)
            rest := tail
        | .forLoop site induction lower upper carried captures nested outputs =>
            let (operands, tail) ← crossControlOperands candidate env
              ([lower, upper] ++ carried.map Prod.snd ++ captures) rest
            let .forLoop actualSite actualInduction actualLower actualUpper actualCarried actualCaptures actualBody actualOutputs :: tail := tail
              | throw "local-control-correspondence"
            let initial := (operands.drop 2).take carried.length
            let captured := operands.drop (2 + carried.length)
            ensure (site == actualSite && actualLower == (← lookup lower operands).1 && actualUpper == (← lookup upper operands).1 &&
              actualCarried.map Prod.snd == initial.map (fun (_, value, _) => value) &&
              actualCaptures == captured.map (fun (_, value, _) => value)) "local-control-correspondence"
            let types := initial.map (fun (_, _, ty) => ty)
            let inner := [(induction, (actualInduction, (← lookup lower operands).2))] ++
              (carried.map Prod.fst).zip ((actualCarried.map Prod.fst).zip types) ++ captured
            ensure (carried.length == actualCarried.length) "local-result-correspondence"
            compareBody bindings candidate depth true inner types nested actualBody
            ensure (outputs.length == actualOutputs.length && outputs.length == types.length) "local-result-correspondence"
            env := env ++ outputs.zip (actualOutputs.zip types)
            rest := tail
        | .ret values | .yield values =>
            ensure (match instruction with | .yield _ => region | _ => !region) "local-terminal-context"
            let (returns, tail) ← crossOperands candidate env values outputTypes rest
            ensure (tail == [if region then .yield returns else .ret returns]) "local-return-correspondence"
            rest := []
        | _ => throw "invalid-local-instruction"
      ensure rest.isEmpty "local-trailing-instructions"

/-- Shared relation for generic instances and explicitly bound local functions. -/
def validateClosed (logical : Explicit.Function) (bindings : List OperationBinding)
    (candidate : Explicit.CandidateLocals) (functionName : Name) : Result LocalCorrespondence := do
  admitFunctionWith (environmentSignature (.explicit bindings) "logical") logical.code
  let function ← lookup functionName (candidate.functions.map fun f => (f.code.name, f))
  if candidate.physical then PhysicalFormation.check candidate.bindings function.code
  ensure (function.origin == logical.origin) "local-origin-correspondence"
  if logical.origin.isNone then
    ensure (function.code.name == logical.code.name) "local-function-identity"
  let code := if candidate.physical then eraseStorageReleases function.code else function.code
  admitFunctionWith (environmentSignature (.explicit candidate.bindings) (if candidate.physical then "physical" else "logical")) code
  let inputTypes ← logical.code.arguments.mapM fun (_, ty) => do
    return boundaryType candidate.physical (← Bindings.valueType false ty)
  let outputTypes ← logical.code.results.mapM fun ty => do
    return boundaryType candidate.physical (← Bindings.valueType false ty)
  ensure (code.arguments.map Prod.snd == inputTypes.map Bindings.ValueType.spelling &&
    code.results == outputTypes.map Bindings.ValueType.spelling) "local-signature-correspondence"
  let some body := code.body | throw "external-function"
  let some original := logical.code.body | throw "external-function"
  let env : Environment := (logical.code.arguments.zip (code.arguments.zip inputTypes)).map
    fun ((source, _), ((target, _), ty)) => (source, (target, ty))
  compareBody bindings candidate limits.depth false env outputTypes original body
  return ⟨logical.code.name, functionName,
    (logical.code.arguments.map Prod.fst).zip (code.arguments.map Prod.fst)⟩

def validateLocal (library : Library) (configurationName : Name)
    (candidate : Explicit.CandidateLocals) (functionName : Name) : Result LocalCorrespondence := do
  let configuration ← library.configuration configurationName
  let checked ← library.definition configuration.definition
  let _ ← configuration.closedArguments checked.definition
  let prepared ← prepare library [configurationName]
  let logical ← lookup configurationName (prepared.functions.map fun f => (f.code.name, f))
  let .explicit bindings := prepared.source.environment
  validateClosed logical bindings candidate functionName

end Tools.Interactive.Generic
