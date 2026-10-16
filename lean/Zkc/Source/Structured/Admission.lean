module

public import Zkc.Source.Structured.Operations
public import Zkc.Source.Structured.Format
public import Zkc.Source.Structured.Provenance

@[expose] public section

/-! Independent static admission and lowering. Bound facts name exact SSA
positions; prepending results shifts both ends. No equal-length substitution,
callee premise, or loop-state invariant is silently assumed. -/

namespace Zkc.Source.Structured

def requireSome {α : Type} (value : Option α) (error : String) : Except String α :=
  match value with | some value => .ok value | none => .error error

abbrev Facts := List (Nat × Nat)

def validString (value : String) (empty : Bool := false) : Bool :=
  value.utf8ByteSize ≤ 512 && (empty || !value.isEmpty)
def validType : Ty → Bool
  | .boolean | .index => true
  | .field d | .vector d => d == scalarDomain
  | .group d => d == groupDomain
  | .service contract => contract == scalarServiceContract
def Ty.isService : Ty → Bool
  | .service _ => true
  | _ => false

def validTypes (types : List Ty) : Bool := types.length ≤ 512 && types.all validType
def validRefs (refs : List Nat) : Bool := refs.length ≤ 512 && refs.all (· ≤ 4096)

/-- Remove empty instruction lists without charging an instruction. -/
def nextInstruction : List (List Instruction) → Option (Instruction × List (List Instruction))
  | [] => none
  | [] :: rest => nextInstruction rest
  | (instruction :: instructions) :: rest => some (instruction, instructions :: rest)

/-- Bound a structural preflight before helper analysis. The budget counts
stored instructions, including nested regions, rather than expanded calls. -/
def instructionWorkWithin : Nat → List (List Instruction) → Bool
  | 0, work => (nextInstruction work).isNone
  | remaining + 1, work => match nextInstruction work with
    | none => true
    | some (.instruction _ _ _ regions _, rest) =>
      let children := regions.map fun (.region _ _ (.block instructions _)) => instructions
      instructionWorkWithin remaining (children ++ rest)

def Snapshot.instructionsWithin (snapshot : Snapshot) (limit : Nat) : Bool :=
  let finiteCount := snapshot.definitions.filterMap (fun definition =>
    match definition with | .finite _ => some () | _ => none) |>.length
  let work := snapshot.definitions.filterMap fun definition =>
    match definition with
    | .function function => let .block instructions _ := function.body; some instructions
    | .finite _ => none
  finiteCount ≤ limit && instructionWorkWithin (limit - finiteCount) work

def Domain.resolve (domain : Domain) : Except String DomainSpec := do
  if !validString domain.name || !validTypes domain.inputs then throw "structured-domain"
  let (index, indices) ← match domain.constructor with
    | .elements index => pure (index, false)
    | .indices index 0 => pure (index, true)
    | .indices _ _ => throw "structured-domain-axis"
  let some (.vector field) := domain.inputs[index]? | throw "structured-domain-container"
  let container ← decodeVariable domain.inputs (.vector field) index |>.mapError
    fun _ => "structured-domain-container"
  return ⟨domain.name, domain.inputs, field, container, indices⟩

def Bound.valid (inputs : List Ty) (bound : Bound) : Bool :=
  bound.axis == 0 && inputs[bound.index]? == some .index &&
    (match inputs[bound.container]? with | some (.vector _) => true | _ => false)

def Definition.headerValid (definition : Definition) : Bool :=
  validString definition.name && validTypes definition.inputs && validTypes definition.outputs &&
  definition.preconditions.length ≤ 512 &&
  definition.preconditions.all (Bound.valid definition.inputs) &&
  (match definition with
  | .function f =>
    (match f.kind, f.interface with
      | .protocol, some _ => true
      | .math, none | .local, none => true
      | _, _ => false) &&
    (f.kind == .protocol || !(f.inputs ++ f.outputs).any Ty.isService) &&
    !f.outputs.any Ty.isService &&
    (f.kind != .math || f.visibility == .privateDef) &&
    (f.kind == .math || f.preconditions.isEmpty) &&
    (match f.kind, f.origin with
    | .local, some (name, bindings) => validString name && bindings.length ≤ 128 &&
      (bindings.map Prod.fst).eraseDups.length == bindings.length &&
      bindings.all (fun (key, value) => validString key && validString value)
    | .local, none => false
    | _, none => true
    | _, some _ => false)
  | .finite f => !(f.inputs ++ f.outputs).any Ty.isService &&
    validString f.domain && validString f.step && validString f.predicate true)

def lookupDefinition (snapshot : Snapshot) (name : String) : Except String Definition :=
  requireSome (snapshot.definitions.find? (·.name == name)) "structured-unknown-helper"
def lookupDomain (domains : List DomainSpec) (name : String) : Except String DomainSpec :=
  requireSome (domains.find? (·.name == name)) "structured-unknown-domain"

def typesAt (context : List Ty) (indices : List Nat) : Except String (List Ty) :=
  indices.mapM fun index => requireSome context[index]? "structured-operand"

def Facts.shift (facts : Facts) (count : Nat) : Facts :=
  facts.map fun (index, container) => (index + count, container + count)

def discharge (facts : Facts) (operands : List Nat) (premises : List Bound) : Bool :=
  premises.all fun bound => match operands[bound.index]?, operands[bound.container]? with
    | some index, some container => facts.contains (index, container)
    | _, _ => false

/-- State changes on each step. Only invariant A/C facts and the domain's exact
item/container fact can discharge a helper premise for every iteration. -/
def dischargeFold (facts : Facts) (spec : FoldSpec) (operands : List Nat)
    (stateCount : Nat) (premises : List Bound) : Bool :=
  let domainCount := spec.domain.inputs.length
  let invariantArgs := operands.take domainCount ++ operands.drop (domainCount + spec.state.length)
  premises.all fun bound =>
    (spec.domain.indices && bound.index == stateCount && bound.container > stateCount &&
      match invariantArgs[bound.container - stateCount - 1]?,
          invariantArgs[spec.domain.container.index]? with
      | some container, some selected => container == selected
      | _, _ => false) ||
    (bound.index > stateCount && bound.container > stateCount &&
      match invariantArgs[bound.index - stateCount - 1]?,
          invariantArgs[bound.container - stateCount - 1]? with
      | some index, some container => facts.contains (index, container)
      | _, _ => false)

def resolveFold (snapshot : Snapshot) (domains : List DomainSpec) (kind : Kind)
    (domainName stepName predicateName : String) (argumentTypes state : List Ty)
    (operands : List Nat) (facts : Facts) : Except String FoldSpec := do
  let domain ← lookupDomain domains domainName
  if argumentTypes.length < domain.inputs.length + state.length then throw "structured-fold-arguments"
  let captures := argumentTypes.drop (domain.inputs.length + state.length)
  let helperKind ← match kind with
    | .math => pure HelperKind.math
    | .local => pure HelperKind.local
    | .protocol => throw "structured-fold-kind"
  let spec : FoldSpec := ⟨domain, state, captures, stepName, predicateName, helperKind⟩
  if argumentTypes != spec.arguments then throw "structured-fold-arguments"
  let step ← lookupDefinition snapshot stepName
  if step.kind != kind || step.visibility != .privateDef ||
      step.inputs != spec.stepHelper.inputs || step.outputs != state then throw "structured-fold-step"
  match step with
  | .finite _ => throw "structured-fold-step"
  | .function _ => pure ()
  if !dischargeFold facts spec operands state.length step.preconditions then
    throw "structured-fold-premise"
  if !predicateName.isEmpty then
    let predicate ← lookupDefinition snapshot predicateName
    if predicate.kind != kind || predicate.visibility != .privateDef ||
        predicate.inputs != spec.predicateHelper.inputs || predicate.outputs != [.boolean] then
      throw "structured-fold-predicate"
    match predicate with
    | .finite _ => throw "structured-fold-predicate"
    | .function _ => pure ()
    if !dischargeFold facts spec operands 0 predicate.preconditions then
      throw "structured-fold-premise"
  return spec

structure LowerState where
  sites : List String := []

abbrev LowerM := StateT LowerState (Except String)

def recordSite (site : String) (required : Bool) : LowerM Unit := do
  if !validString site (!required) then throw "structured-site"
  if !site.isEmpty then
    let state ← get
    if state.sites.contains site then throw "structured-duplicate-site"
    modify fun state => { state with sites := site :: state.sites }

/-- Instruction ownership is independent of which facts happen to be available.
In particular, acquiring a bound cannot authorize a Protocol-level read. -/
def Descriptor.admittedIn (descriptor : Descriptor) (kind : Kind) : Bool :=
  match descriptor with
  | .exec .. => kind == .local
  | .booleanConstant _ => true
  | .indexConstant .. | .indexEqual | .fieldConstant .. | .fieldAdd .. | .fieldSubtract .. | .fieldMultiply .. |
    .fieldEqual .. | .booleanAnd | .booleanOr | .booleanXor | .booleanEqual |
    .booleanNotEqual | .select .. | .call .. | .fold .. |
    .groupIdentity .. | .groupAdd .. | .groupScale .. | .groupEqual .. => kind != .local
  | .boundedAt .. => kind == .math
  | .localCall .. | .guard .. | .restrict .. | .exchange .. | .draw .. | .statement .. =>
    kind == .protocol
  | .apply .. | .branch | .loop | .loopCondition => kind == .local

/-- Resolve the exact operation/contract pair and parameters independently of
wire parsing. Direct constructor subjects pass the same checks. -/
def resolvePrimitive (snapshot : Snapshot) (operation name : String)
    (parameters : List String) : Except String Primitive := do
  let binding ← requireSome (snapshot.bindings.find? (·.name == name)) "structured-unknown-binding"
  if !binding.valid then throw "structured-binding"
  let pair ← match operation with
    | "algebra.exec.index_constant" => pure ("index.constant", Primitive.indexConstant 0)
    | "algebra.exec.index_equal" => pure ("index.equal", Primitive.indexEqual)
    | "algebra.exec.index_less" => pure ("index.less", Primitive.indexLess)
    | "algebra.exec.index_add" => pure ("index.add", Primitive.indexAdd)
    | "algebra.exec.index_mul" => pure ("index.mul", Primitive.indexMul)
    | "algebra.exec.index_sub" => pure ("index.sub", Primitive.indexSub)
    | "algebra.exec.index_div" => pure ("index.div", Primitive.indexDiv)
    | "algebra.exec.index_mod" => pure ("index.mod", Primitive.indexMod)
    | "algebra.exec.vector_empty" => pure ("vector.empty", Primitive.vectorEmpty scalarDomain)
    | "algebra.exec.vector_length" => pure ("vector.length", Primitive.vectorLength scalarDomain)
    | "algebra.exec.vector_sum" => pure ("vector.sum", Primitive.vectorSum scalarDomain)
    | "algebra.exec.vector_split" => pure ("vector.split", Primitive.vectorSplit scalarDomain)
    | "algebra.exec.vector_append" => pure ("vector.append", Primitive.vectorAppend scalarDomain)
    | "algebra.exec.vector_equal" => pure ("vector.equal", Primitive.vectorEqual scalarDomain)
    | "algebra.exec.field_equal" => pure ("field.equal", Primitive.fieldEqual scalarDomain)
    | _ => throw "structured-primitive-operation"
  if binding.contract != pair.1 then throw "structured-binding-contract"
  if operation == "algebra.exec.index_constant" then
    let [text] := parameters | throw "structured-primitive-parameters"
    return .indexConstant (← Format.indexDecimal text)
  else
    if !parameters.isEmpty then throw "structured-primitive-parameters"
    return pair.2

def resolveOp (snapshot : Snapshot) (domains : List DomainSpec) (kind : Kind)
    (context : List Ty) (facts : Facts) (identities : List Nat)
    (descriptor : Descriptor) (operands : List Nat)
    (results : List Ty) (site : String) : LowerM Op := do
  if !validRefs operands || !validTypes results then throw "structured-instruction-limit"
  if !descriptor.admittedIn kind then
    throw (match kind with
      | .local => "structured-local-operation"
      | .math => "structured-math-operation"
      | .protocol => "structured-protocol-operation")
  let argumentTypes ← typesAt context operands
  let factOperands := operands.map fun index => identities[index]?.getD index
  let required := match descriptor with
    | .exec .. | .apply _ | .localCall .. | .branch | .loop | .loopCondition | .guard _ => true
    | .booleanConstant _ => kind == .local
    | _ => false
  if kind == .math && !site.isEmpty then throw "structured-math-site"
  if !required && !site.isEmpty then throw "structured-pure-site"
  recordSite site required
  let resolveCall := fun (name : String) (expected : Kind) (ordinary : Bool) => do
    let callee ← lookupDefinition snapshot name
    if callee.kind != expected || name == snapshot.entry then throw "structured-call-kind"
    if ordinary then
      match callee with
      | .finite _ => throw "structured-call-kind"
      | .function _ => pure ()
    if !discharge facts factOperands callee.preconditions then throw "structured-call-premise"
    let helperKind ← match expected with
      | .math => pure HelperKind.math
      | .local => pure HelperKind.local
      | .protocol => throw "structured-call-kind"
    pure (Op.invoke ⟨name, helperKind, callee.inputs, callee.outputs⟩)
  let checkField := fun (d : String) =>
    if d == scalarDomain then pure () else (throw "structured-field-domain" : LowerM Unit)
  match descriptor with
  | .exec operation binding parameters =>
    return .exec (← resolvePrimitive snapshot operation binding parameters)
  | .indexConstant text => return .indexConstant (← Format.indexDecimal text)
  | .indexEqual => return .indexEqual
  | .fieldConstant d text =>
    checkField d
    let value ← Format.decimal text
    if value ≥ scalarModulus then throw "structured-field-canonical"
    return .fieldConstant d value
  | .fieldAdd d => checkField d; return .fieldAdd d
  | .fieldSubtract d => checkField d; return .fieldSubtract d
  | .fieldMultiply d => checkField d; return .fieldMultiply d
  | .fieldEqual d => checkField d; return .fieldEqual d
  | .groupIdentity d =>
    if d != groupDomain then throw "structured-group-domain"
    return .groupIdentity d
  | .groupAdd d =>
    if d != groupDomain then throw "structured-group-domain"
    return .groupAdd d
  | .groupScale g f =>
    if g != groupDomain || f != scalarDomain then throw "structured-group-domain"
    return .groupScale g f
  | .groupEqual d =>
    if d != groupDomain then throw "structured-group-domain"
    return .groupEqual d
  | .booleanConstant value => return .booleanConstant value
  | .booleanAnd => return .booleanAnd
  | .booleanOr => return .booleanOr
  | .booleanXor => return .booleanXor
  | .booleanEqual => return .booleanEqual
  | .booleanNotEqual => return .booleanNotEqual
  | .select type =>
    if !validType type || type.isService then throw "structured-type-unsupported"
    return .select type
  | .boundedAt d =>
    checkField d
    match factOperands with
    | [container, index] =>
      if !facts.contains (index, container) then throw "structured-bounded-at-premise"
      return .boundedAt d
    | _ => throw "structured-bounded-at-arguments"
  | .call name => resolveCall name .math true
  | .apply name => resolveCall name .local false
  | .localCall .. => throw "structured-open-operation"
  | .fold domain step predicate =>
    let spec ← resolveFold snapshot domains .math domain step predicate argumentTypes results factOperands facts
    return .fold spec
  | .branch => return .branch (argumentTypes.drop 1) results
  | .loop | .loopCondition =>
    if argumentTypes.length < 2 + results.length then throw "structured-loop-arguments"
    let captures := argumentTypes.drop (2 + results.length)
    return if descriptor == .loop then .loop results captures else .loopCondition results captures
  | .guard .. | .restrict .. | .exchange .. | .draw .. | .statement .. =>
    throw "structured-open-operation"

inductive ExitKind where
  | function | yield | condition
  deriving DecidableEq

def lowerTerminator (kind : Kind) (expected : ExitKind) (terminal : Terminator) :
    LowerM (RawRegion Ty Op) := do
  match terminal with
  | .stop reason site =>
    if kind == .math then throw "structured-math-stop"
    if kind != .local then throw "structured-local-stop"
    if expected == .condition then throw "structured-terminator-kind"
    recordSite site true
    return .letOp (.mark site) [] [] .nil (.stop reason)
  | .ret refs | .yield refs | .condition refs =>
    if !validRefs refs then throw "structured-reference-limit"
    let actual := match terminal with
      | .ret _ => ExitKind.function
      | .condition _ => ExitKind.condition
      | _ => ExitKind.yield
    if actual != expected then throw "structured-terminator-kind"
    return .ret refs

/-- A continuing LocalFor returns each original capture at its exact input
position, shifted by all body results. Same-typed substitutes are refused. -/
def forwardsCaptures (stateCount captureCount : Nat) (conditional : Bool) (body : Block) : Bool :=
  let .block instructions terminal := body
  let added := instructions.foldl (fun n instruction =>
    match instruction with | .instruction _ _ results _ _ => n + results.length) 0
  let expected := (List.range captureCount).map (· + added + 1 + stateCount)
  match terminal with
  | .stop .. => true
  | .yield values => !conditional && values.drop stateCount == expected
  | .condition values => conditional && values.drop (stateCount + 1) == expected
  | .ret _ => false

/-- Structural list traversal is separate from region-depth recursion. Keeping
these recursors separate makes successful admission reduce in the kernel without
unfolding a generated well-founded mutual recursion over both dimensions. -/
def lowerInstructions (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (kind : Kind)
    (child : List Ty → Facts → ExitKind → Block → LowerM (RawRegion Ty Op))
    (exitKind : ExitKind) (terminal : Terminator) :
    List Ty → Facts → List Nat → List Instruction → LowerM (RawRegion Ty Op)
  | _, _, _, [] => lowerTerminator kind exitKind terminal
  | context, facts, identities, .instruction descriptor operands results regions site :: rest => do
    let op ← resolveOp snapshot domains kind context facts identities descriptor operands results site
    if regions.length > 2 then throw "structured-region-count"
    let bodies ← regions.mapM fun (.region inputs outputs body) => do
      if !validTypes inputs || !validTypes outputs then throw "structured-region-signature"
      let (bodyFacts, bodyExit) ← match op with
        -- Only Local control has regions, and Local has no bound premises.
        | .branch .. => pure ([], ExitKind.yield)
        | .loop state captures | .loopCondition state captures => do
          let conditional := match op with | .loopCondition .. => true | _ => false
          if !forwardsCaptures state.length captures.length conditional body then
            throw "structured-capture-forwarding"
          pure ([],
            if conditional then ExitKind.condition else ExitKind.yield)
        | _ => throw "structured-unexpected-region"
      let raw ← child inputs bodyFacts bodyExit body
      pure (inputs, outputs, raw)
    let rawBodies := bodies.foldr (fun (inputs, outputs, body) rest =>
      RawRegions.cons inputs outputs body rest) .nil
    let operandOrigins := operands.map fun index => identities[index]?
    let resultOrigins := (resultIdentities summaries descriptor operandOrigins results.length).zipIdx.map
      fun (source, result) => match source with
        | some original => original + results.length
        | none => result
    let next ← lowerInstructions snapshot domains summaries kind child exitKind terminal
      (results ++ context) (facts.shift results.length)
      (resultOrigins ++ identities.map (· + results.length)) rest
    let node := RawRegion.letOp op operands results rawBodies next
    return if kind == .math then node else .letOp (.mark site) [] [] .nil node

def lowerBlock (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (kind : Kind) :
    Nat → List Ty → Facts → ExitKind → Block → LowerM (RawRegion Ty Op)
  | 0, _, _, _, _ => throw "structured-region-depth"
  | depth + 1, context, facts, exitKind, .block instructions terminal =>
    lowerInstructions snapshot domains summaries kind (lowerBlock snapshot domains summaries kind depth)
      exitKind terminal context facts (List.range context.length) instructions

end Zkc.Source.Structured
