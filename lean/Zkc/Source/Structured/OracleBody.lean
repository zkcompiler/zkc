module

public import Zkc.Source.Structured.DomainComponent
public import Zkc.Source.Structured.Admission
public import Zkc.Source.RegionDerivation

@[expose] public section

/-! Source-associated retained oracle bodies. Execution uses `Region.denote`; an ordered
footprint is never substituted for the actual body. OracleAdmission constructs the checked unit. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- Closed Math calculations permitted in a retained answer body. Helper closure checking
below checks every stored helper and every exact reference, including unused calculations. -/
def Op.oraclePure (op : Op) : Bool :=
  match op with
  | .invoke helper => helper.kind == .math
  | .mark _ | .boundedAt _ | .exec _ => true
  | .fold spec => spec.kind == .math
  | _ => op.isCalculation

def oracleMathBody : RawRegion Ty Op → Bool
  | .ret _ => true
  | .letOp (.branch ..) _ _ (.cons _ _ yes (.cons _ _ no .nil)) next =>
      oracleMathBody yes && oracleMathBody no && oracleMathBody next
  | .letOp op _ _ .nil next => op.oraclePure && oracleMathBody next
  | .bind _ body next => oracleMathBody body && oracleMathBody next
  | _ => false

structure OracleMathEnvironment where
  definitions : List CheckedDefinition
  linked : DeclarationsLinked [] definitions
  pureBodies : ∀ definition ∈ definitions, definition.kind = .math ∧
    oracleMathBody definition.raw = true

/-- Helper meanings are constructed from the checked original bodies by the existing
component evaluator. The execution API accepts no replacement helper interpretation. -/
def OracleMathEnvironment.tables (math : OracleMathEnvironment) (model : DomainModel)
    (interface : PIR.Signature) : Evaluation.ComponentTablesOn model.toCarriers interface :=
  math.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩

/-- The complete Math environment is tied to the unchanged source, in both directions.
Exact lowering equations are structural obligations; they cannot choose helper semantics. -/
def OracleMathEnvironment.Associated (math : OracleMathEnvironment)
    (snapshot : Snapshot) (domains : List DomainSpec) : Prop :=
  (∀ checked ∈ math.definitions, ∃ function,
    Definition.function function ∈ snapshot.definitions ∧ function.kind = .math ∧
    checked.helper = ⟨function.name, .math, function.inputs, function.outputs⟩ ∧
    (lowerBlock snapshot domains [] .math Limits.nesting function.inputs
      (function.preconditions.map (fun bound ↦ (bound.index, bound.container)))
      .function function.body).run' {} = .ok checked.raw) ∧
  (∀ function, Definition.function function ∈ snapshot.definitions → function.kind = .math →
    ∃ checked ∈ math.definitions,
      checked.helper = ⟨function.name, .math, function.inputs, function.outputs⟩)

/-- Output dependency sets are computed from retained helper bodies. Calls use their summaries;
other calculations conservatively union their operands. Structural aggregate precision and
a general dependency correctness theorem remain separate obligations. This analysis cannot
change operation meaning or erase an unused source instruction. -/
def oracleMathDependencies (summaries : List (Helper × List (List Nat))) :
    RawRegion Ty Op → List (List Nat) → List (List Nat)
  | .ret refs, environment => refs.map (fun index ↦ environment[index]?.getD [])
  | .stop _, _ => []
  | .bind _ body next, environment =>
      oracleMathDependencies summaries next
        (oracleMathDependencies summaries body environment ++ environment)
  | .letOp op refs results _ next, environment =>
      let arguments := refs.map (fun index ↦ environment[index]?.getD [])
      let dependencies := match op with
        | .invoke helper =>
          match summaries.find? (fun summary ↦ summary.1 == helper) with
          | some (_, outputs) => outputs.map (fun output ↦
              (output.flatMap (fun input ↦ arguments[input]?.getD [])).eraseDups)
          | none => List.replicate results.length arguments.flatten.eraseDups
        | _ => List.replicate results.length arguments.flatten.eraseDups
      oracleMathDependencies summaries next (dependencies ++ environment)

def OracleMathEnvironment.dependencies (environment : OracleMathEnvironment) :
    List (Helper × List (List Nat)) :=
  environment.definitions.foldl (fun summaries definition ↦
    (definition.helper, oracleMathDependencies summaries definition.raw
      ((List.range definition.inputs.length).map (fun index ↦ [index]))) :: summaries) []

structure OracleBodyError where
  code : String
  definition : Nat
  row : List Nat
  deriving DecidableEq, Repr

namespace OracleBody

def checkHeader (snapshot : Snapshot) (declaration : OracleDeclaration) : Except String Unit := do
  if !validString declaration.name || !validString declaration.admissibility ||
      declaration.inputs.length > Limits.listEntries then throw "oracle-body-header"
  let sources := declaration.inputs.takeWhile (fun type ↦ match type with
    | .oracle _ => true | _ => false)
  let parameters := declaration.inputs.drop sources.length
  if parameters.isEmpty || parameters.getLast? != some .index ||
      parameters.any Ty.isHandle then throw "oracle-body-signature"
  if declaration.kind.answer.isHandle then throw "oracle-body-answer"
  let dataInputs := declaration.inputs.dropLast.map (fun type ↦ match type with
    | .oracle kind => kind.data | type => type)
  snapshot.catalogue.check
  snapshot.catalogue.agrees admittedCatalogue
  (dataInputs ++ [declaration.kind.answer]).forM
    (snapshot.catalogue.checkType admittedCatalogue)
  match declaration.kind with
  | .table _ (some fixed) =>
    if fixed ≥ indexLimit || !declaration.shapeArguments.isEmpty ||
        !declaration.shapeBounds.isEmpty then throw "oracle-body-shape"
  | .table _ none =>
    let [("rows", input)] := declaration.shapeArguments | throw "oracle-body-shape"
    let [("rows", maximum)] := declaration.shapeBounds | throw "oracle-body-shape"
    if input < sources.length || input + 1 ≥ declaration.inputs.length ||
        declaration.inputs[input]? != some .index || maximum ≥ indexLimit then
      throw "oracle-body-shape"
  let some relation := snapshot.relations.find? (·.name == declaration.admissibility)
    | throw "oracle-body-admissibility"
  if relation.inputs != dataInputs || relation.outputs != [.boolean] ||
      relation.kind != "zkc.language.formula/0" then throw "oracle-body-admissibility"
  let some formula := relation.formula | throw "oracle-body-admissibility"
  let some (.function function) := snapshot.definitions.find? (·.name == formula)
    | throw "oracle-body-admissibility"
  if function.kind != .math || function.inputs != relation.inputs ||
      function.outputs != [.boolean] then throw "oracle-body-admissibility"

/-- Lower actual source rows once. Only inherited queries of original source parameters are
admitted; answer-dependent positions refuse even when hidden inside a Math helper. -/
def lowerInstructions (snapshot : Snapshot) (domains : List DomainSpec)
    (math : OracleMathEnvironment) (definition : Nat) (inputs : List Ty)
    (terminal : Terminator) (sites : List String) :
      List Instruction → List Ty → List (List Nat) → Nat →
      Except OracleBodyError (RawRegion Ty ProtocolOp)
  | [], _, _, _ =>
    match terminal with
    | .ret refs => if validRefs refs then .ok (.ret refs)
        else .error ⟨"oracle-body-reference-limit", definition, [7, 2]⟩
    | _ => .error ⟨"oracle-body-terminal", definition, [7, 2]⟩
  | .instruction descriptor operands results regions site :: rest, context, dependencies, index => do
    let row := [7, 1, index]
    let failure := fun code ↦ OracleBodyError.mk code definition row
    if !validRefs operands || !validTypes results then
      throw (failure "oracle-body-instruction-limit")
    if !regions.isEmpty then throw (failure "oracle-body-region")
    let arguments := operands.map (fun operand ↦ dependencies[operand]?.getD [])
    let (op, outputs) ← match descriptor with
      | .oracle (.query none kind) => do
        if !validString site then throw (failure "oracle-body-query-site")
        if sites.contains site then throw (failure "oracle-body-duplicate-site")
        let [source, position] := operands | throw (failure "oracle-body-query-arity")
        let shift := context.length - inputs.length
        if source < shift || inputs[source - shift]? != some (.oracle kind) then
          throw (failure "oracle-body-source")
        if !(dependencies[position]?.getD [inputs.length]).all (· < inputs.length) then
          throw (failure "oracle-body-adaptive-position")
        let location : OracleLocation := ⟨⟨definition, []⟩, definition, row⟩
        pure (ProtocolOp.oracle (.query kind none) location, [[inputs.length]])
      | .oracle _ => throw (failure "oracle-body-operation")
      | descriptor => do
        let resolved := (resolveOp snapshot domains .math context [] (List.range context.length)
          descriptor operands results site).run {}
        let (op, _) ← resolved.mapError (fun code ↦ failure code)
        if allowed : op.isCalculation = true then
          if !op.oraclePure then throw (failure "oracle-body-partial-math")
          for helper in op.helpers do
            if !(math.definitions.any (fun definition ↦ definition.helper == helper)) then
              throw (failure "oracle-body-helper-link")
          let outputs := match op with
            | .invoke helper =>
              match math.dependencies.find? (fun summary ↦ summary.1 == helper) with
              | some (_, outputs) => outputs.map (fun output ↦
                  (output.flatMap (fun input ↦ arguments[input]?.getD [])).eraseDups)
              | none => List.replicate results.length arguments.flatten.eraseDups
            | _ => List.replicate results.length arguments.flatten.eraseDups
          pure (ProtocolOp.calculate op allowed, outputs)
        else throw (failure "oracle-body-operation")
    let next ← lowerInstructions snapshot domains math definition inputs terminal
      (if site.isEmpty then sites else site :: sites) rest
      (results ++ context) (outputs ++ dependencies) (index + 1)
    pure (.letOp op operands results .nil next)

def lower (snapshot : Snapshot) (domains : List DomainSpec) (math : OracleMathEnvironment)
    (definition : Nat) (declaration : OracleDeclaration) :
    Except OracleBodyError (RawRegion Ty ProtocolOp) := do
  if !snapshot.instructionsWithin Limits.instructions then
    throw ⟨"oracle-body-instruction-limit", definition, []⟩
  (checkHeader snapshot declaration).mapError (fun code ↦ ⟨code, definition, []⟩)
  let .block instructions terminal := declaration.body
  lowerInstructions snapshot domains math definition declaration.inputs terminal [] instructions
    declaration.inputs ((List.range declaration.inputs.length).map (fun index ↦ [index])) 0

end OracleBody

structure CheckedOracle (snapshot : Snapshot) (domains : List DomainSpec)
    (math : OracleMathEnvironment) where
  mathAssociated : math.Associated snapshot domains
  declaration : OracleDeclaration
  sourceIndex : Nat
  sourceExact : snapshot.definitions[sourceIndex]? = some (.oracle declaration)
  raw : RawRegion Ty ProtocolOp
  lowered : OracleBody.lower snapshot domains math sourceIndex declaration = .ok raw
  body : Region protocolDialect declaration.inputs [declaration.kind.answer]
  formed : raw.elaborate (dialect := protocolDialect) declaration.inputs
    [declaration.kind.answer] = .ok body

def checkOracle (snapshot : Snapshot) (domains : List DomainSpec) (math : OracleMathEnvironment)
    (associated : math.Associated snapshot domains)
    (sourceIndex : Nat) : Except OracleBodyError (CheckedOracle snapshot domains math) := do
  match sourceExact : snapshot.definitions[sourceIndex]? with
  | some (.oracle declaration) =>
    match lowered : OracleBody.lower snapshot domains math sourceIndex declaration with
    | .error error => throw error
    | .ok raw =>
      match formed : raw.elaborate (dialect := protocolDialect) declaration.inputs
          [declaration.kind.answer] with
      | .error _ => throw ⟨"oracle-body-formation", sourceIndex, [7]⟩
      | .ok body => pure ⟨associated, declaration, sourceIndex, sourceExact, raw, lowered, body, formed⟩
  | _ => throw ⟨"oracle-body-declaration", sourceIndex, []⟩

/-- Check all stored Oracle declarations, including dormant ones, in source order. The canonical
unit checker partitions ordinary helpers/protocols and retains this exact table. -/
def checkOracles (snapshot : Snapshot) (domains : List DomainSpec) (math : OracleMathEnvironment)
    (associated : math.Associated snapshot domains) :
    Except OracleBodyError (List (CheckedOracle snapshot domains math)) :=
  ((List.range snapshot.definitions.length).filter (fun index ↦
    match snapshot.definitions[index]? with
    | some (.oracle _) => true
    | _ => false)).mapM (checkOracle snapshot domains math associated)

structure OracleRead where
  kind : OracleKind
  anchor : OracleAnchor
  position : Nat
  location : OracleLocation
  expansion : List (OracleAnchor × OracleLocation) := []

abbrev oracleReadInterface (carriers : Carriers) : PIR.Signature where
  Op := OracleRead
  Reply request := carriers.Value request.kind.answer

/-- Ordinary closed mathematics is reused unchanged. The oracle branch only emits a typed
child request; its actual domain check and provider stopping belong to the store handler. -/
def oracleBodyMeaning (model : DomainModel)
    (tables : Evaluation.ComponentTablesOn model.toCarriers (oracleReadInterface model.toCarriers)) :
    RegionMeaning protocolDialect (oracleReadInterface model.toCarriers) where
  Value := Component model.Value
  operation op args _ := match op, args with
    | .calculate op allowed, args =>
        Evaluation.componentOperationOn model (.silent _) tables op args
          (by change Values _ op.regions; rw [op.calculation_no_regions allowed]; exact .nil)
    | .oracle (.query kind none) location, .cons anchor (.cons position .nil) =>
      match anchor, position with
      | some anchor, some position =>
          .call ⟨kind, anchor, position, location, []⟩
            (fun answer ↦ .done (.cons (some answer) .nil))
      | _, _ => .halt .incomplete
    | _, _ => .halt .refused

def CheckedOracle.denote {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} (checked : CheckedOracle snapshot domains math)
    (model : DomainModel)
    (arguments : Values (Component model.Value) checked.declaration.inputs) :
    PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer]) :=
  checked.body.denote
    (oracleBodyMeaning model (math.tables model (oracleReadInterface model.toCarriers))) arguments.get

theorem CheckedOracle.exactBody {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} (checked : CheckedOracle snapshot domains math) :
    checked.body.erase = checked.raw :=
  RawRegion.erase_of_elaborate (dialect := protocolDialect) checked.raw checked.formed

end Zkc.Source.Structured
