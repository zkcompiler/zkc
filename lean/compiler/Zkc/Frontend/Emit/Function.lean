module

public import Zkc.Frontend.Elab.Function
public import Zkc.Frontend.Emit.Wording
public import Zkc.Frontend.Typed.Printer
public import Zkc.Frontend.Typed.Number
public import Zkc.Frontend.Semantics.Instantiate.Roots
public import Zkc.Frontend.Elab.Linear

@[expose] public section

set_option autoImplicit false

/-!
# The body of a function instance by the typed tree

The body of a function instance is elaborated to the typed tree, and the tree is emitted as the
local code of the function, with the frontend's facts deciding what a fact must justify. After
the emission come the checks that need to know whether the body can stop: FN3 for a function
named `at`, FN5 for a kernel.

A function bound to a row applies the row: `def f(…) = primitive("row", args)` is the row at the
written static arguments, or, when none are written, at the instance's values. A function bound
to the formal library is its header.
-/

namespace Zkc.Frontend.Emit

open Syntax
open Static
open Typing (RowStatic RowRequest Row FunctionCode BodyState)

/-- Whether a closed type mentions `rational`. -/
partial def mentionsRational : ClosedType → Bool
  | .rational => true
  | .nonzero inner => mentionsRational inner
  | .seq element _ => mentionsRational element
  | .tuple components _ => components.any mentionsRational
  | _ => false

/-- The header of a specification function bound to the formal library (NL9): its signature and
its external name. -/
def header (description : String) (parameters : Array ClosedType) (result : ClosedType)
    (external : String) : FunctionCode :=
  { name := description, inputs := parameters, outputs := #[result]
    canStop := false, specificationOnly := true, external := some external }

/-- The row that a `def` bound to the vocabulary applies, at an instance. -/
def primitiveRow (inst : InstanceId) (found : Declaration) (row : String)
    (arguments : Array Lowered.StaticArgument) (parameters : Array ClosedType) (result : ClosedType) :
    CompileM Typing.RowId := do
  let state ← get
  let entry := state.table.entries[inst]!
  let env := instanceEnv state.program found entry.key.arguments entry.key.specification
  let mut statics : Array RowStatic := #[]
  let written := arguments.filterMap fun
    | .term _ _ term => some term
    | _ => none
  let values ← if written.isEmpty then pure entry.key.arguments
    else written.mapM (evalAny env ·)
  for value in values do
    match value with
    | .natural n => statics := statics.push (.nat n)
    | .type type => statics := statics.push (.type type)
    | .«module» _ => throw (.waiting "a row at a module argument")
  -- a row of the vocabulary has its kind and type there; a row that a project binds, the
  -- declaration's
  let request : RowRequest := { name := row, statics }
  let place := (found.name.map (·.span)).getD default
  let found : Row ← match Typing.rowOf? request with
    | some known =>
      -- the signature written is the row's at this instance (NL9)
      let same := known.inputs.size == parameters.size &&
        (known.inputs.zip parameters).all (fun (one, other) => typeEq one other) &&
        known.outputs.size == 1 && known.outputs.all (typeEq · result)
      unless same do
        let state ← get
        let render (types : Array ClosedType) : String :=
          ", ".intercalate (types.map (renderType state)).toList
        refuse "NL9" place
          s!"the signature written is not that of the row `{row}` at this instance: the row takes ({render known.inputs}) and gives ({render known.outputs})"
      pure known
    | none =>
      -- a name of the vocabulary at static arguments for which it has no row is no row of a
      -- project
      if Zkc.Core.Vocabulary.table.rows.any (·.name == row) then
        refuse "NL9" place
          s!"`{row}` is a row of the vocabulary, and the vocabulary has no row of that name at the static arguments of this instance; write them: `primitive(\"{row}\", …)`"
      pure { key := request.key, kind := .pure, inputs := parameters, outputs := #[result] }
  internRow found

mutual
  /-- The function instances that an expression applies, added to those found, each once. -/
  partial def calledInExpr (found : Array InstanceId) : Typed.Expr → Array InstanceId
    | .literal .. | .staticValue .. | .local .. => found
    | .apply _ callee arguments =>
      let found := match callee with
        | .instance inst => if found.contains inst then found else found.push inst
        | _ => found
      arguments.foldl calledInExpr found
    | .construct _ _ parts => parts.foldl calledInExpr found
    | .project _ target _ _ => calledInExpr found target
    | .convert _ _ value _ => calledInExpr found value
    | .conditional _ _ condition onTrue onFalse =>
      calledInExpr (calledInExpr (calledInExpr found condition) onTrue) onFalse
    | .block _ statements result => calledInExpr (statements.foldl calledInStmt found) result
    | .error _ evaluated => evaluated.foldl calledInExpr found

  partial def calledInStmt (found : Array InstanceId) : Typed.Stmt → Array InstanceId
    | .bind _ _ value _ | .unpack _ _ value _ | .update _ _ value _ => calledInExpr found value
    | .guard _ condition _ _ => calledInExpr found condition
    | .if _ condition onTrue onFalse _ =>
      onFalse.foldl calledInStmt (onTrue.foldl calledInStmt (calledInExpr found condition))
    | .match _ scrutinee _ _ cases _ =>
      cases.foldl (init := calledInExpr found scrutinee) fun found (.case _ _ _ body) =>
        body.foldl calledInStmt found
    | .for _ (.loop _ domain _ body) _ =>
      let found := match domain with
        | .range start stop _ => calledInExpr (calledInExpr found start) stop
        | .collection source _ _ => calledInExpr found source
      match body with
      | .uniform statements values => values.foldl calledInExpr (statements.foldl calledInStmt found)
      | .stepped iterations =>
        iterations.foldl (init := found) fun found (Typed.Iteration.iteration _ statements values) =>
          values.foldl calledInExpr (statements.foldl calledInStmt found)
      | .empty .. => found
    | .scope _ body => body.foldl calledInStmt found
    | .event _ _ what =>
      match what with
      | .send _ payload _ _ => calledInExpr found payload
      | .apply _ _ arguments _ _ _ => arguments.foldl calledInExpr found
      | .draw .. | .sample .. | .attempt .. => found
    | .error .. => found
end

/-- The function instances that a body applies, each once. -/
def calledIn (body : Typed.FunctionBody) : Array InstanceId :=
  calledInExpr (body.statements.foldl calledInStmt #[]) body.result

/-- What the session keeps of a function body that elaboration typed: whether it can stop and
what it waits for, read from the tree and from its callees, after the core has checked the
facts of the body. A refusal of facts is worded at its node and logged; a body with one is
refused. `refused` says that elaboration refused something of the body: a refusal of facts
before the first error node in the order of the tree is reported beside it. -/
def checkedFunction (description : String) (tree : Typed.FunctionBody) (result : ClosedType)
    (specification : Bool) (refused : Bool) : CompileM FunctionCode := do
  -- the numbers of the nodes are the tags by which the core names them
  let body := match (Typed.Body.function tree).numbered.1 with
    | .function numbered => numbered
    | _ => tree
  let state ← get
  let results := state.results
  let stops (callee : InstanceId) : Bool := match results.body? callee with
    | some (.done code) => code.canStop
    | _ => false
  let restricted (callee : InstanceId) : Bool := match results.body? callee with
    | some (.row row) =>
      (match (results.rows[row]?).map fun (entry : Typing.Row) => entry.kind with
        | some (Typing.RowKind.restricted _) => true
        | _ => false)
    | _ => false
  let (found, unchecked) ← match checkFunction state { stops, restricted } specification body result with
    | .ok found => pure (found, none)
    | .error (.defect message) => throw (.defect message)
    -- a form of a later layer in the body: its facts are not checked here, and the function
    -- waits for the form, so that no package holds it unchecked
    | .error (.waiting reason) | .error (.noCoreForm reason) =>
      pure (([] : List Finding), some reason)
  -- with an error node in the body, only what comes before it is reported
  let firstError := body.firstError?
  let reported := found.filter fun finding =>
    match firstError, finding.node with
    | some error, some node => node < error
    | some _, none => false
    | none, _ => true
  for finding in reported do
    let worded ← word (finding.node.bind body.find?) finding.explained
    logError worded.rule worded.span (.ofText worded.message) (origin := .instances)
  if !reported.isEmpty || refused || firstError.isSome then throw .abandoned
  let waiting := unchecked.orElse fun _ => (calledIn body).findSome? fun callee =>
    match results.body? callee with
    | some (.done code) => code.waiting
    | _ => none
  return { name := description, inputs := body.parameters.map (·.type), outputs := #[result]
           canStop := body.canStop stops, waiting }

/-- The module instance whose member a member definition instance defines, and the interface
member it defines. -/
def memberOwner (found : Declaration) (values : Array StaticValue) :
    CompileM (Option (InstanceId × DeclarationId × Declaration)) := do
  let state ← get
  let some ns := state.program.namespaces[found.namespace]? | return none
  let some inst := state.table.find? { declaration := ns.owner, arguments := values } | return none
  let some (.«module» interfaces _) := state.table.content? inst | return none
  let name := (found.name.map (·.text)).getD ""
  for (interface, _) in interfaces do
    let some inner := (state.program.declarations[interface]?).bind (·.inner) | continue
    if let some (.declaration member) := (state.program.namespaces[inner]?).bind (·.names[name]?) then
      if let some memberDeclaration := state.program.declarations[member]? then
        return some (inst, member, memberDeclaration)
  return none

/-- The interface that declares a member of a module instance, and its static arguments. -/
def memberInterface (inst : InstanceId) (name : String) :
    CompileM (DeclarationId × Declaration × Array StaticValue) := do
  let state ← get
  let some (.«module» interfaces _) := state.table.content? inst
    | throw (.waiting "a module whose members are not evaluated")
  for (interface, args) in interfaces do
    let some inner := (state.program.declarations[interface]?).bind (·.inner) | continue
    if let some (.declaration member) := (state.program.namespaces[inner]?).bind (·.names[name]?) then
      if let some found := state.program.declarations[member]? then
        return (interface, found, args)
  throw (.waiting s!"the member `{name}` of a module")

/-- The parameter types and the result type of a signature that is evaluated, or the wait for
the first of its types that is not. -/
def signatureTypes (inst : InstanceId) : CompileM (Array ClosedType × Option ClosedType) := do
  match (← get).table.content? inst with
  | some (.signature parameters result) =>
    if parameters.all (·.2.isSome) then
      return (parameters.map fun (_, type) => type.getD default, result)
    throw (.waiting (← Elab.signatureWait inst))
  | _ => throw (.waiting (← Elab.signatureWait inst))

/-- Whether a declaration's instances are generic over a module parameter (SP12). -/
def genericOverModule (found : Declaration) : CompileM Bool := do
  for (reference, _) in deployedParameters (← program) found do
    if (← parameterClass reference) == .«module» then return true
  return false

/-- A body elaborated to the typed tree and emitted, at the types of its signature; for a
definition generic over a module parameter, with the places its opaque elaboration resolved to
members of the parameter's interface (SP12). The code, and those places. -/
def elaborateBody (inst : InstanceId) (description : String) (env : Env)
    (parameters : Array (Lowered.Binder × ClosedType)) (result : ClosedType) (body : Lowered.Expr)
    (specification : Bool) (locals : Nat) (typeBody : InstanceId → Span → CompileM Unit)
    (resolutions : Std.HashMap Typing.ResolvedPlace ParameterRef := {}) :
    CompileM (FunctionCode × Array (Typing.ResolvedPlace × ParameterRef) × Typed.FunctionBody × Nat) := do
  -- every refusal of the body is reported: a statement that is refused is an error node, and
  -- the statements after it are elaborated
  let context : Elab.Context :=
    { env, «instance» := inst, name := description, typeBody, specification, resolutions }
  let errors := (← get).log.errors
  let (tree, state) ← Elab.runElab context locals (Elab.elabFunctionBody parameters result body)
  trace "elab.tree" fun _ => .ofText s!"{description}:\n{(Typed.Body.function tree).print}"
  let code ← checkedFunction description tree result specification ((← get).log.errors > errors)
  -- the uses of the linear values (LN1, LN2)
  unless specification do
    if let .error (span, message) := Linear.check tree then refuse "LN2" span message
  return (code, state.resolved, tree, state.nextLocal)

/-- The type members of a module parameter that a `where` in scope equates with a type: in both
elaborations they are that type (SP12). -/
def equatedMembers (found : Declaration) (reference : ParameterRef) : CompileM (Array String) := do
  let program ← program
  let mut result : Array String := #[]
  for scope in found.scopes do
    let some entry := program.scopes[scope]? | continue
    let some whereClause := entry.whereClause | continue
    for constraint in whereClause.constraints do
      let .compare _ .equal left right := constraint | continue
      for side in [left, right] do
        let .path _ path := side | continue
        let steps ← recover (stepsOf { file := entry.file } path) (pure #[])
        let kinds : List Step := (steps.map (·.step)).toList
        if let [Step.parameter other, Step.member name _] := kinds then
          if other == reference && !result.contains name then result := result.push name
  return result

/-- The values of an instance in its opaque elaboration: each module parameter stands for its
module with fresh type members (SP12); and each parameter with its bound, as the chain line writes
it. -/
def opaqueValues (found : Declaration) (values : Array StaticValue) :
    CompileM (Array StaticValue × Array String) := do
  let program ← program
  let parameters := deployedParameters program found
  let mut result := values
  let mut over : Array String := #[]
  for index in [0:parameters.size] do
    let (reference, parameter) := parameters[index]!
    unless (← parameterClass reference) == .«module» do continue
    let some (.«module» real) := values[index]? | continue
    let inst ← Instances.opaqueModule reference (← equatedMembers found reference) real
    result := result.set! index (.«module» inst)
    let boundText := (parameter.bound.map fun bound => " + ".intercalate (bound.sorts.toList.map fun
      | .path path => exprText (.path path.span path)
      | .nat _ => "nat"
      | .linear _ => "linear")).getD ""
    over := over.push s!"`{parameter.name.text}: {boundText}`"
  return (result, over)

/-- The opaque elaboration of a definition generic over a module parameter (SP12): its body at
the instance's values, each module parameter standing for its module with fresh type members,
under the chain line that names it. It is emitted too, and its code not kept; it gives the places
it resolved to members of the parameters' interfaces. `signature` gives the environments of the
signature and of the body at the opaque values. -/
def opaqueResolutions (inst : InstanceId) (description name : String) (found : Declaration)
    (values : Array StaticValue) (binders : Array Lowered.Binder) (types : Array Lowered.TypeTerm)
    (result : Option Lowered.TypeTerm) (resultDefault : ClosedType) (body : Lowered.Expr)
    (specification : Bool) (locals : Nat) (typeBody : InstanceId → Span → CompileM Unit)
    (signature : Array StaticValue → CompileM (Env × Env)) :
    CompileM (Std.HashMap Typing.ResolvedPlace ParameterRef × Typed.FunctionBody) := do
  let (opaqueArguments, over) ← opaqueValues found values
  let overText := ", ".intercalate over.toList
  let frame : ChainFrame :=
    { subject := .ofText s!"the opaque typing of `{name}` over {overText}"
      span := (found.name.map (·.span)).getD default }
  withChainFrame frame do
    let (signatureEnv, bodyEnv) ← signature opaqueArguments
    let parameterTypes ← types.mapM (evalType signatureEnv)
    let resultType ← match result with
      | some type => evalType signatureEnv type
      | none => pure resultDefault
    let (_, resolved, tree, _) ← elaborateBody inst description bodyEnv (binders.zip parameterTypes)
      resultType body specification locals typeBody
    return (resolved.foldl (init := {}) fun map (place, reference) => map.insert place reference, tree)

/-- Keeps the typed tree of a body: the request for the tree of the instance is done with it.
The check of its facts and the emission of a package read it. -/
def recordTree (definition : Typed.Definition) (place : Span) : CompileM Unit := do
  -- the tree is kept with its nodes numbered; the generic definition has numbers of its own
  let (body, nodes) := definition.body.numbered
  let definition := { definition with body, nodes, generic := definition.generic.map (·.numbered.1) }
  let requested : ChainFrame := { subject := .ofPart (.instance definition.instance), span := place }
  modifyResults fun results => results.modifyTrees fun table =>
    (table.intern definition.instance requested none).1.setStateOf definition.instance (.done definition)

/-- The code of a function instance: its lowered body elaborated at the instance, and emitted.
`typeBody` asks for the body of a callee from the place of a call. -/
def functionBody (inst : InstanceId) (typeBody : InstanceId → Span → CompileM Unit) :
    CompileM BodyState := do
  let state ← get
  let some entry := state.table.entries[inst]? | throw .abandoned
  let found ← declaration entry.key.declaration
  let name := state.program.nameOf entry.key.declaration
  let description ← describeInstance entry.key.declaration entry.key.arguments
    entry.key.specification entry.key.owner
  let some lowered := (← getModules).lowered? entry.key.declaration
    | throw (.defect "a declaration without its lowered form")
  let place := (found.name.map (·.span)).getD default
  try
    match found.node, lowered.content with
    | .«def» node, .function head body =>
      let (parameters, result) ← signatureTypes inst
      let some result := result | throw (.waiting (← Elab.signatureWait inst))
      let specification := node.modifier matches some (.spec _)
      match body with
      | .primitive _ row arguments =>
        let id ← primitiveRow inst found row arguments parameters result
        recordTree { «instance» := inst, body := .row { name := row } } place
        return .row id
      | .external _ external =>
        recordTree { «instance» := inst, body := .external external } place
        return .done (header description parameters result external)
      | .absent => throw (.defect "a function without a body")
      | .body expr =>
        -- `rational` is a type of specifications only (TY1)
        unless specification do
          for (parameter, type) in head.parameters.zip parameters do
            if mentionsRational type then
              refuse "TY1" (Lowered.Expr.span (.type parameter.type)) "`rational` is a specification type"
          if mentionsRational result then
            if let some written := head.result then
              refuse "TY1" (Lowered.Expr.span (.type written)) "`rational` is a specification type"
        let env := instanceEnv state.program found entry.key.arguments entry.key.specification
        -- a definition generic over a module parameter is elaborated twice: the opaque
        -- elaboration first, whose resolutions the elaboration at the instance uses (SP12)
        let (resolutions, generic) ← if ← genericOverModule found then do
            let (resolutions, generic) ← opaqueResolutions inst description name found entry.key.arguments
              (head.parameters.map (·.binder)) (head.parameters.map (·.type)) head.result .unit expr
              specification lowered.locals typeBody fun values =>
                let env := instanceEnv state.program found values entry.key.specification
                pure (env, env)
            pure (resolutions, some generic)
          else pure ({}, none)
        let (code, _, tree, locals) ← elaborateBody inst description env
          ((head.parameters.map (·.binder)).zip parameters) result expr specification lowered.locals typeBody
          resolutions
        recordTree { «instance» := inst, body := .function tree, generic := generic.map .function, locals
                     waiting := code.waiting, specificationOnly := specification } place
        -- the instance keeps the resolutions of its generic definition
        let code := { code with specificationOnly := specification, resolved := resolutions.toArray }
        if name == "at" && code.canStop then
          refuse "FN3" node.name.span "`at` can stop; the function that indexing applies cannot stop"
        if let some kernel := node.kernel then
          if code.canStop then
            refuse "FN5" kernel.span s!"`{name}` can stop; a kernel is attached to a `def` whose body cannot stop"
        return .done code
    | .memberDef node, .memberDefinition binders body =>
      -- the module's values, then the values of the member's own static parameters (SP8)
      let moduleCount := (deployedParameters state.program found).size
      let moduleValues := entry.key.arguments.extract 0 moduleCount
      let ownValues := entry.key.arguments.extract moduleCount entry.key.arguments.size
      let some (moduleInst, memberId, member) ← memberOwner found moduleValues
        | throw (.waiting "a member definition whose module is not evaluated")
      let .member (.defMember _ modifier _ _ _ _ _) := member.node
        | throw (.waiting "a member definition of another kind")
      let some memberLowered := (← getModules).lowered? memberId
        | throw (.defect "a member without its lowered form")
      let .function memberHead _ := memberLowered.content
        | throw (.waiting "a member definition of another kind")
      let own := ownParameters state.program member
      let (interface, _, interfaceArgs) ← memberInterface moduleInst name
      let interfaceDeclaration ← declaration interface
      let ownEnv (env : Env) : Env :=
        { env with values := (own.zip ownValues).foldl (init := env.values) fun map (reference, value) =>
            map.insert reference value }
      let env : Env := ownEnv { instanceEnv state.program interfaceDeclaration interfaceArgs with
        file := member.file, self? := some (.«module» moduleInst) }
      let types ← memberHead.parameters.mapM fun parameter => evalType env parameter.type
      let resultType ← match memberHead.result with
        | some type => evalType env type
        | none => pure ClosedType.unit
      match body with
      | .primitive _ row arguments =>
        let id ← primitiveRow inst found row arguments types resultType
        recordTree { «instance» := inst, body := .row { name := row } } place
        return .row id
      | .external _ external =>
        recordTree { «instance» := inst, body := .external external } place
        return .done (header description types resultType external)
      | .absent => throw (.defect "a member definition without a body")
      | .body expr =>
        let bodyEnv := ownEnv (instanceEnv state.program found moduleValues entry.key.specification)
        -- a member definition generic over a module parameter of its module is elaborated twice:
        -- the opaque elaboration first, with `Self` the module at the parameter's opaque module
        let (resolutions, generic) ← if ← genericOverModule found then do
            let some ns := state.program.namespaces[found.namespace]? | throw .abandoned
            let (resolutions, generic) ← opaqueResolutions inst description name found moduleValues binders
              (memberHead.parameters.map (·.type)) memberHead.result .unit expr node.spec lowered.locals
              typeBody fun values => do
                let opaqueInst ← instantiate ns.owner values { description := "", span := place }
                let (opaqueInterface, _, opaqueArgs) ← memberInterface opaqueInst name
                let opaqueDeclaration ← declaration opaqueInterface
                let signatureEnv : Env := ownEnv { instanceEnv state.program opaqueDeclaration opaqueArgs with
                  file := member.file, self? := some (.«module» opaqueInst) }
                pure (signatureEnv, ownEnv (instanceEnv state.program found values entry.key.specification))
            pure (resolutions, some generic)
          else pure ({}, none)
        let (code, _, tree, locals) ← elaborateBody inst description bodyEnv (binders.zip types) resultType
          expr node.spec lowered.locals typeBody resolutions
        recordTree { «instance» := inst, body := .function tree, generic := generic.map .function, locals
                     waiting := code.waiting, specificationOnly := node.spec } place
        let code := { code with specificationOnly := node.spec, resolved := resolutions.toArray }
        if code.canStop && !(modifier matches some (.«partial» _)) then
          let moduleName := state.program.nameOf (state.table.entries[moduleInst]!.key.declaration)
          refuse "SP9" node.name.span
            s!"`{moduleName}::{name}` can stop; `{state.program.nameOf interface}` declares `{name}` without `partial`"
        if let some kernel := node.kernel then
          if code.canStop then
            refuse "FN5" kernel.span s!"`{name}` can stop; a kernel is attached to a `def` whose body cannot stop"
        return .done code
    | .relation node, .function head body =>
      let (parameters, _) ← signatureTypes inst
      match body with
      | .external _ external =>
        recordTree { «instance» := inst, body := .external external } place
        return .done (header description parameters .bool external)
      | .body expr =>
        let env := instanceEnv state.program found entry.key.arguments entry.key.specification
        let (resolutions, generic) ← if ← genericOverModule found then do
            let (resolutions, generic) ← opaqueResolutions inst description name found entry.key.arguments
              (head.parameters.map (·.binder)) (head.parameters.map (·.type)) none .bool expr true
              lowered.locals typeBody fun values =>
                let env := instanceEnv state.program found values entry.key.specification
                pure (env, env)
            pure (resolutions, some generic)
          else pure ({}, none)
        let (code, _, tree, locals) ← elaborateBody inst description env
          ((head.parameters.map (·.binder)).zip parameters) .bool expr true lowered.locals typeBody resolutions
        recordTree { «instance» := inst, body := .function tree, generic := generic.map .function, locals
                     waiting := code.waiting, specificationOnly := true } place
        -- the formula of a relation cannot stop (FN3, SX3)
        if code.canStop then
          refuse "FN3" node.name.span
            s!"the formula of `{name}` can stop; a relation needs an expression that cannot stop"
        return .done { code with specificationOnly := true }
      | _ => throw (.defect "a relation without a body")
    | .law node, .function head (.body expr) | .member (.lawMember node), .function head (.body expr) =>
      let (parameters, _) ← signatureTypes inst
      let env := { instanceEnv state.program found entry.key.arguments entry.key.specification with
        self? := entry.key.owner.map StaticValue.module }
      let (code, _, tree, locals) ← elaborateBody inst description env
        ((head.parameters.map (·.binder)).zip parameters) .bool expr true lowered.locals typeBody
      recordTree { «instance» := inst, body := .function tree, locals, waiting := code.waiting
                   specificationOnly := true } place
      -- a law is a `bool` specification expression that cannot stop (SP10, FN3)
      if code.canStop then
        refuse "SP10" node.name.span s!"the law `{name}` can stop; a law is an expression that cannot stop"
      -- the obligation it leaves: of the module instance it is typed at, or of its module
      let «module» := match entry.key.owner with
        | some owner => renderInstance state owner
        | none =>
          let owner := (state.program.namespaces[found.namespace]?).map (·.owner)
          (owner.map state.program.nameOf).getD "?"
      let law ← describeInstance entry.key.declaration entry.key.arguments entry.key.specification
      let obligation : Typing.Obligation := { «module», law, place := node.name.span }
      modifyResults fun results => { results with obligations := results.obligations.push obligation }
      return .done { code with specificationOnly := true }
    | _, _ => throw (.defect s!"the typing of bodies does not expect the body of {Names.kindWord found.kind}")
  catch failure =>
    match failure with
    | .staticIndex index => return .waiting s!"the index `{index}` in a static position"
    | other => throw other

end Zkc.Frontend.Emit
