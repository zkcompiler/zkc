module

public meta import ZkcTools.ConstructionBindings.TargetPlacement
public meta import ZkcTools.ConstructionBindings.Interface
public meta import ZkcTools.ConstructionBindings.Syntax
public meta import Lean.Meta.AbstractMVars

public meta section

/-! Candidate interfaces for actual target slices. This module generalizes
syntax, not a derivation: the existing alignment constructors check the open
body before it is installed. Physical references are proposed relative to the
entire caller layout, independently of the source application map. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Family
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionTargetPlacement

register_option zkc.connection.generateReusableBodies : Bool := {
  defValue := false
  descr := "install checked symbolic families from actual callee placements"
}

register_option zkc.connection.collectFamilyPremises : Bool := {
  defValue := false
  descr := "internal: leave finite structural interface facts for family abstraction"
}

def collecting : CoreM Bool :=
  return (← getOptions).getBool `zkc.connection.collectFamilyPremises false

private partial def nodes (value : Expr) : MetaM (Array Expr) := do
  let value ← whnf value
  if value.isAppOf ``List.nil then return #[]
  unless value.isAppOf ``List.cons do throwError "connection-family-nonfinite-row"
  return #[value.getAppArgs[1]!] ++ (← nodes value.getAppArgs[2]!)

private partial def head (value : Expr) : MetaM Expr := do
  let mut value := (← instantiateMVars value).consumeMData
  while value.isHeadBetaTarget do value := value.headBeta.consumeMData
  if [``Domain.View.sequence, ``Domain.View.empty, ``Domain.View.receive,
      ``Domain.View.send, ``Domain.View.calculation, ``Domain.View.helper,
      ``Domain.View.guard, ``Domain.View.loop, ``Domain.View.indicesEmpty,
      ``Domain.View.indicesAppend, ``Domain.View.observe, ``Domain.View.challenge,
      ``Domain.View.localService].any value.isAppOf then return value
  if let .letE _ _ v b _ := value then return ← head (b.instantiate1 v)
  if let some next ← withTransparency .all <| reduceRecMatcher? value then return ← head next
  if let some next ← withTransparency .all <| reduceProj? value.getAppFn then
    return ← head (mkAppN next value.getAppArgs)
  if let some next ← unfoldDefinition? value then return ← head next
  throwError "connection-family-target-view: {value}"

private def referenceFields (name : Name) : List Nat × List Nat :=
  if name == ``Domain.View.calculation then ([], [2])
  else if name == ``Domain.View.helper then ([], [3])
  else if name == ``Domain.View.guard then ([1], [])
  else if name == ``Domain.View.send then ([4], [])
  else if name == ``Domain.View.indicesAppend then ([1,2], [])
  else if name == ``Domain.View.observe then ([4,5,6], [])
  else if name == ``Domain.View.challenge then ([5,6], [])
  else if name == ``Domain.View.localService then ([], [5,6])
  else if name == ``Domain.View.loop then ([3], [2,4])
  else ([], [])

private def valueFields (name : Name) : List Nat :=
  if name == ``Domain.View.receive || name == ``Domain.View.send then [3]
  else if name == ``Domain.View.observe then [3]
  else if name == ``Domain.View.challenge then [4]
  else if name == ``Domain.View.localService then [4]
  else []

private structure Fields where
  references : Array Nat := #[]
  values : Array Expr := #[]

private partial def collect (base : Nat) (view : Expr) (state : Fields) : MetaM Fields := do
  let view ← head view
  let name := view.getAppFn.constName!
  let args := view.getAppArgs
  if name == ``Domain.View.sequence then
    return ← collect base args[2]! (← collect base args[1]! state)
  let mut state := state
  let (single, rows) := referenceFields name
  let mut references := single.map (args[·]!) |>.toArray
  for index in rows do references := references ++ (← nodes args[index]!)
  for reference in references do
    let some value ← getNatValue? (← whnf reference)
      | throwError "connection-family-nonstatic-reference"
    if value < base && !state.references.contains value then
      state := {state with references := state.references.push value}
  for index in valueFields name do
    let value := args[index]!
    unless state.values.contains value do state := {state with values := state.values.push value}
  if name == ``Domain.View.loop then state ← collect base args[6]! state
  return state

private def ref (base : Nat) (size : Expr) (fields : Fields) (parameters : Array Expr)
    (value : Expr) : MetaM Expr := do
  let some value ← getNatValue? (← whnf value) | throwError "connection-family-reference"
  if value < base then
    let some index := fields.references.idxOf? value | throwError "connection-family-reference-index"
    return parameters[index]!
  if value == base then return size
  return mkApp2 (mkConst ``Nat.add) size (mkNatLit (value - base))

private unsafe def stringValue (expression : Expr) : MetaM String := do
  if let some literal := getStringValue? (← whnf expression) then return literal
  let expression ← withTransparency .all <| reduce expression (explicitOnly := false) (skipTypes := false)
  evalExpr String (mkConst ``String) expression

private def qualifiedSite (oldPrefix newPrefix expression : Expr) : MetaM Expr := do
  let actual ← unsafe stringValue expression
  let marker ← mkAppM ``qualifyProtocolSite #[oldPrefix, mkStrLit "connection_probe"]
  let marker ← unsafe stringValue marker
  let stem := (marker.dropEnd "connection_probe".length).toString
  unless actual.isEmpty || actual.startsWith stem do throwError "connection-family-site-prefix"
  let relative := if actual.isEmpty then "" else (actual.drop stem.length).toString
  mkAppM ``qualifyProtocolSite #[newPrefix, mkStrLit relative]

private partial def target (base : Nat) (size oldPrefix newPrefix : Expr) (fields : Fields)
    (parameters : Array Expr) (view : Expr) : MetaM Expr := do
  let view ← head view
  let name := view.getAppFn.constName!
  let mut args := view.getAppArgs
  if name == ``Domain.View.sequence then
    args := args.set! 1 (← target base size oldPrefix newPrefix fields parameters args[1]!)
    args := args.set! 2 (← target base size oldPrefix newPrefix fields parameters args[2]!)
  else
    let (single, rows) := referenceFields name
    for index in single do args := args.set! index (← ref base size fields parameters args[index]!)
    for index in rows do
      let row ← (← nodes args[index]!).mapM (ref base size fields parameters)
      args := args.set! index (← mkListLit (mkConst ``Nat) row.toList)
    for index in valueFields name do
      let some offset := fields.values.idxOf? args[index]!
        | throwError "connection-family-value-index"
      args := args.set! index parameters[fields.references.size + offset]!
    if name == ``Domain.View.receive || name == ``Domain.View.send then
      for index in [1,2] do args := args.set! index (← qualifiedSite oldPrefix newPrefix args[index]!)
    if name == ``Domain.View.loop then
      args := args.set! 6 (← target base size oldPrefix newPrefix fields parameters args[6]!)
  return mkAppN view.getAppFn args

private partial def binderIndex (binder : Expr) : MetaM Nat := do
  let binder ← whnf binder
  if binder.isAppOf ``Zkc.Source.Var.here then return 0
  if binder.isAppOf ``Zkc.Source.Var.there then return (← binderIndex binder.getAppArgs.back!) + 1
  throwError "connection-family-count-binder"

/-- A loop rule requires a present count. Keep that finite input shape while
allowing other optional components to vary, including hidden captures. -/
private partial def countInputs (form : Expr) (depth : Nat := 0) : MetaM (Array Nat) := do
  let form ← whnf form
  let name := form.getAppFn.constName!
  let mut type := (← getConstInfo name).type
  let mut result := #[]
  let binds := [``NormalForm.Form.receive, ``NormalForm.Form.query, ``NormalForm.Form.math,
    ``NormalForm.Form.owned, ``NormalForm.Form.strict, ``NormalForm.Form.compute,
    ``NormalForm.Form.repeat, ``NormalForm.Form.apply].contains name
  for value in form.getAppArgs do
    let .forallE field _ body _ := type | throwError "connection-family-source-form"
    if name == ``NormalForm.Form.repeat && field == `count then
      let count ← whnf value
      if count.isAppOf ``Comp.input then
        let index ← binderIndex count.getAppArgs.back!
        if index ≥ depth then result := result.push (index - depth)
    if field == `next || field == `absent || field == `present then
      let nextDepth := if (field == `next && binds) || field == `present then depth + 1 else depth
      result := result ++ (← countInputs value nextDepth)
    type := body.instantiate1 value
  return result

private partial def arguments {α : Type} [Inhabited α] (scope actual : Expr)
    (required : Array Nat) (offset : Nat) (next : Expr → TacticM α) : TacticM α := do
  let actual ← whnf actual
  if actual.isAppOf ``Values.nil then
    next (← mkAppOptM ``Values.nil #[some (mkConst ``Slot), some (← mkAppM ``Argument #[← mkListLit (mkConst ``LawKey) [], scope])])
  else
    unless actual.isAppOf ``Values.cons do throwError "connection-family-arguments"
    let args := actual.getAppArgs
    let value ← whnf args[args.size - 2]!
    let valueType ← whnf (← inferType value)
    let laws ← mkListLit (mkConst ``LawKey) []
    let (type, wrap) ← if valueType.isAppOf ``NormalForm.Term then
        pure (← mkAppM ``NormalForm.Term #[laws, scope, valueType.getAppArgs.back!], false)
      else if valueType.isAppOf ``Comp then
        if required.contains offset then
          unless value.isAppOf ``Comp.present do throwError "connection-family-count-not-present"
          pure (← mkAppM ``NormalForm.Term #[laws, scope, valueType.getAppArgs.back!], true)
        else pure (← mkAppM ``Comp #[laws, scope, valueType.getAppArgs.back!], false)
      else throwError "connection-family-argument-sort: {valueType}"
    withLocalDeclD `argument type fun parameter => do
      let parameter ← if wrap then mkAppM ``Comp.present #[parameter] else pure parameter
      arguments scope args.back! required (offset + 1) fun tail => do
        -- Rebuild Values at the new argument functor and scope.
        let result ← mkAppOptM ``Values.cons #[some (mkConst ``Slot),
          some (← mkAppM ``Argument #[laws, scope]), some args[2]!, some args[3]!, some parameter, some tail]
        next result

private partial def spine (block model : Expr) : MetaM Expr := do
  let block ← head block
  if block.isAppOf ``Domain.View.empty then return mkConst ``ConnectionTargetPrefix.Prefix.empty
  unless block.isAppOf ``Domain.View.sequence do throwError "connection-family-prefix-shape"
  mkAppM ``ConnectionTargetPrefix.Prefix.step
    #[← mkLambdaFVars #[model] block.getAppArgs[1]!, ← spine block.getAppArgs[2]! model]

private partial def returns {α : Type} [Inhabited α] (actual : Expr)
    (next : Expr → TacticM α) : TacticM α := do
  let actual ← whnf actual
  if actual.isAppOf ``Values.nil then return ← next actual
  unless actual.isAppOf ``Values.cons do throwError "connection-family-selection"
  withLocalDeclD `keep (mkConst ``Bool) fun keep =>
    returns actual.getAppArgs.back! fun tail => do
      next (mkAppN actual.getAppFn ((actual.getAppArgs.set! (actual.getAppArgs.size - 2) keep).set! (actual.getAppArgs.size - 1) tail))

structure Cost where
  name : Name
  proposalNanos : Nat
  kernelNanos : Nat
  parameters : Nat
  deriving Repr

initialize costs : IO.Ref (Array Cost) ← IO.mkRef #[]

structure Application where
  entry : Expr
  routing : Expr
  selection : Expr
  placement : Expr
  guide : Expr

/-- Named fields of a fully applied constructor. Names describe its telescope,
not the positions of the indices in the resulting inductive type. -/
def constructorFields (expression : Expr) : MetaM (Array (Name × Expr)) := do
  let some name := expression.getAppFn.constName?
    | throwError "connection-family-expected-constructor"
  let .ctorInfo info ← getConstInfo name
    | throwError "connection-family-expected-constructor: {name}"
  unless expression.getAppNumArgs == info.numParams + info.numFields do
    throwError "connection-family-constructor-arity: {name}, found {expression.getAppNumArgs}"
  let mut type := info.type
  let mut fields := #[]
  for argument in expression.getAppArgs do
    let .forallE name _ body _ := type | throwError "connection-family-application-arity"
    fields := fields.push (name, argument)
    type := body.instantiate1 argument
  return fields

/-- Use only the guide's finite cut shape. All target instructions and their
operands come from the current target; no old placement is transported. -/
def splitTarget (shape target : Expr) : MetaM (Expr × Expr) := do
  let mut shape ← whnf shape
  let mut count := 0
  while shape.isAppOf ``ConnectionTargetPrefix.Prefix.step do
    count := count + 1
    shape ← whnf shape.getAppArgs.back!
  unless shape.isConstOf ``ConnectionTargetPrefix.Prefix.empty do
    throwError "connection-family-cut-shape"
  withLocalDeclD `cutModel (mkConst ``DomainModel) fun model => do
    let mut rest ← head (mkApp target model)
    let mut actions := #[]
    for _ in [:count] do
      unless rest.isAppOf ``Domain.View.sequence do throwError "connection-family-cut-target"
      actions := actions.push (← mkLambdaFVars #[model] rest.getAppArgs[1]!)
      rest ← head rest.getAppArgs[2]!
    let mut cut := mkConst ``ConnectionTargetPrefix.Prefix.empty
    for action in actions.reverse do
      cut ← mkAppM ``ConnectionTargetPrefix.Prefix.step #[action, cut]
    return (cut, ← mkLambdaFVars #[model] rest)

/-- Recover exact placement indices from a typed application constructor.
Nested replay uses these indices to match the already checked child family. -/
def application (expression : Expr) : MetaM Application := do
  let fields ← constructorFields expression
  let field := fun name => do
    let some (_, value) := fields.find? (·.1 == name)
      | throwError "connection-family-application-field: {name}"
    pure value
  let entry ← mkAppM ``ConnectionLibrary.Library.entry #[← field `library, ← field `callee]
  let key := (← inferType entry).getAppArgs.back!
  let bodyType ← whnf (← inferType (← field `bodyCertificate))
  let indices := bodyType.getAppArgs
  let placement ← mkAppOptM ``Placement.mk #[some key, some indices[1]!, some indices[10]!,
    some (← field `arguments), some indices[11]!, some indices[12]!,
    some (← field `calleeOutputs), some (← field `calleeHistory), some (← field `returnSelection),
    some (← field `spine), some (← field `extent)]
  return ⟨entry, indices[0]!, indices[4]!, placement, ← field `bodyCertificate⟩

def applications (value : Expr) : CoreM (Array Expr) := do
  let result ← IO.mkRef (#[] : Array Expr)
  let names := [``ConnectionCertificate.Alignment.application,
    ``ConnectionCertificate.Alignment.applicationRetainedHistory]
  let mut arities : Array (Name × Nat) := #[]
  for name in names do
    arities := arities.push (name, (← getConstInfo name).type.getForallArity)
  value.forEach fun expression => do
    if arities.any (fun (name, count) => expression.isAppOfArity name count) then
      result.modify (·.push expression)
  return ← result.get

/-- Generate a telescope from one actual placement, and check its open body.
The build callback is the existing typed derivation proposer. It may leave
only typed finite structural facts; all of those become explicit parameters.
No derivation of the original closed placement is retained here. -/
def install (entry routing selection actual : Expr) (build : MVarId → TacticM Unit) : TacticM Name := do
  let start ← IO.monoNanosNow
  let key := (← inferType entry).getAppArgs.back!
  let field := fun name => mkAppM name #[actual]
  let layout ← field ``Placement.layout
  let some base ← getNatValue? (← whnf (← mkAppM ``List.length #[layout]))
    | throwError "connection-family-prefix-size"
  let some extent ← getNatValue? (← whnf (← field ``Placement.extent))
    | throwError "connection-family-extent"
  unless extent ≥ base do throwError "connection-family-negative-extent"
  let actualSpine ← field ``Placement.spine
  let actualBlock ← mkAppM ``ConnectionTargetPrefix.Prefix.block #[actualSpine]
  let actualContext ← field ``Placement.context
  let required ← countInputs (← mkAppM ``ConnectionLibrary.Entry.form #[entry])
  let oldPrefix ← mkAppM ``ProtocolContext.applicationPrefix #[actualContext]
  withLocalDeclD `scope (mkConst ``Scope) fun scope => do
    withLocalDeclD `context (mkConst ``ProtocolContext) fun context => do
    let newPrefix ← mkAppM ``ProtocolContext.applicationPrefix #[context]
    withLocalDeclD `frames (← mkAppM ``ConnectionFrame.ScopedFrames #[scope]) fun frames => do
    withLocalDeclD `layout (← mkAppM ``ConnectionFrame.Layout #[scope]) fun layout => do
    withLocalDeclD `outputs (← mkAppM ``List #[mkConst ``Original.Location]) fun outputs => do
    withLocalDeclD `history (← mkAppM ``Option #[mkConst ``Nat]) fun history => do
    arguments scope (← field ``Placement.arguments) required 0 fun arguments => do
    returns (← field ``Placement.returns) fun returns => do
    withLocalDeclD `model (mkConst ``DomainModel) fun model => do
      let view ← head (mkApp actualBlock model)
      let fields ← collect base view {}
      let descriptors := fields.references.map (fun _ => (`reference, mkConst ``Nat)) ++
        (← fields.values.mapM fun value => return (`targetValue, ← inferType value))
      withLocalDeclsDND descriptors fun parameters => do
        let size ← mkAppM ``List.length #[layout]
        let view ← target base size oldPrefix newPrefix fields parameters view
        let targetPrefix ← spine view model
        let size := if extent == base then size else mkApp2 (mkConst ``Nat.add) size (mkNatLit (extent - base))
        let placement ← mkAppOptM ``Placement.mk #[some key, some context, some scope,
          some arguments, some frames, some layout, some outputs, some history, some returns,
          some targetPrefix, some size]
        let expected ← mkAppM ``CheckedBody #[entry, routing, selection, placement]
        let body ← mkFreshExprSyntheticOpaqueMVar expected
        withOptions (·.setBool `zkc.connection.collectFamilyPremises true) <| build body.mvarId!
        let value ← instantiateMVars body
        -- Lambda congruence can lift an operand hole across an unused model
        -- binder. Hoist such constant facts back to their finite type.
        for hole in ← getMVars value do
          let mut type ← whnf (← instantiateMVars (← hole.getType))
          let mut binders : Array (Name × Expr × BinderInfo) := #[]
          while let .forallE name domain rest bi := type do
            if rest.hasLooseBVars then break
            binders := binders.push (name, domain, bi)
            type ← whnf rest
          unless binders.isEmpty do
            let mut fact ← mkFreshExprMVar type
            for (name, domain, bi) in binders.reverse do fact := .lam name domain fact bi
            hole.assign fact
        let value ← instantiateMVars value
        for hole in ← getMVars value do
          let type ← whnf (← instantiateMVars (← hole.getType))
          unless (← Interface.structural type) || (← Interface.finiteData type) do
            throwError "connection-family-nonstructural-premise: {type}"
        let abstracted ← abstractMVars value
        let closed ← Closure.mkValueTypeClosure (← inferType abstracted.expr) abstracted.expr false
        if closed.value.hasMVar || closed.value.hasFVar || closed.value.hasSorry ||
            closed.type.hasMVar || closed.type.hasFVar then
          throwError "connection-family-unfinished-declaration"
        let name := (← getCurrNamespace) ++ (← mkFreshUserName `reusableConnectionBody)
        let (type, value) := _root_.ShareCommon.shareCommon' (closed.type, closed.value)
        Interface.auditFamilyType type
        let proposed ← IO.monoNanosNow
        let declaration ← mkDefinitionValInferringUnsafe name closed.levelParams.toList type value
          (.regular (getMaxHeight (← getEnv) value + 1))
        withExporting <| withOptions (Elab.async.set · false) <|
          addDecl (.defnDecl declaration) (forceExpose := true)
        let checked ← IO.monoNanosNow
        modifyEnv fun env => addNoncomputable (TargetPlacement.checkedBodies.addEntry env name) name
        costs.modify (·.push ⟨name, proposed - start, checked - proposed, closed.exprArgs.size + abstracted.numMVars⟩)
        logInfo m!"CONNECTION-FAMILY {name}: proposal_ns={proposed-start}; kernel_ns={checked-proposed}; interface={abstracted.numMVars}"
        return name

end ZkcTools.ConstructionBindings.Family
