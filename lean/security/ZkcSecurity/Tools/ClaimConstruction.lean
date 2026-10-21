module

public import Lean
public meta import Zkc.Claims.Wire
public import Zkc.Claims.Methods
public import Zkc.Claims.Interactive
public import ZkcSecurity.Claims.Resolution
public import ZkcSecurity.Claims.Endpoint
public import ZkcSecurity.Claims.ReceiptAdmission

@[expose] public section

/-! Infrastructure for source request clients. Python supplies only wire data.
Typed registries compute the proposition before a registered author-library
method is applied. Every generated declaration is checked by the kernel.
Names in `Library` locate Lean exports; they never define property meanings.
-/

universe u

namespace ZkcSecurity.Tools.ClaimConstruction
open Lean Meta Elab Tactic Command
open Zkc.Claims ZkcSecurity.Claims ZkcSecurity.Endpoint

/-- Physical author-library exports. Missing methods remain unsupported attempts.
The resolved/evaluated indices, rather than these names, determine proof types. -/
structure Library where
  subject : Name
  bytesSubject : Option Name := none
  properties : Name
  models : Name
  interactiveSubject : Option Name := none
  interactiveModels : Option Name := none
  normalization : List Name := []
  methods : List (Identifier × Name) := []
  theoremMethods : List (Identifier × Name) := []
  receiptMethods : List (Identifier × Name) := []
  deriving Inhabited

/-- Kernel checked normalization of a reflexive symbolic comparison. -/
@[simp] theorem naturalReflexiveRec {α : Sort u} (value : Nat)
    (no : (¬ value = value) → α) (yes : (value = value) → α) :
    @Decidable.rec (value = value) (fun _ => α) no yes (instDecidableEqNat value value) =
      yes rfl := by
  cases decision : instDecidableEqNat value value with
  | isFalse impossible => exact (impossible rfl).elim
  | isTrue proof => rfl

/-- Reflexive Boolean comparisons can occur after reducing an `Except` bind. -/
@[simp] theorem naturalBneRec {α : Sort u} (value : Nat)
    (no : (¬ (value != value) = true) → α) (yes : ((value != value) = true) → α) :
    @Decidable.rec ((value != value) = true) (fun _ => α) no yes
      (instDecidableEqBool (value != value) true) = no (by simp) := by
  cases decision : instDecidableEqBool (value != value) true with
  | isFalse proof => rfl
  | isTrue impossible => simp at impossible

/-- Evaluate concrete diagnostic Strings without treating pretty-printed terms
as identifiers. Literal concatenation and natural versions use their actual
standard operations; other unresolved values are refused. -/
private meta def concreteString : Nat → Expr → MetaM String
  | 0, _ => throwError "missing-definition identifier exceeds diagnostic limit"
  | fuel + 1, expression => do
    if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars then
      throwError "missing-definition identifier has unresolved variables: {expression}"
    if let some value := getStringValue? expression then return value
    let arguments := expression.getAppArgs
    if expression.isAppOfArity ``HAppend.hAppend 6 ||
        expression.isAppOfArity ``String.append 2 then
      let left := arguments[arguments.size - 2]!
      let right := arguments.back!
      unless ← isDefEq expression (← mkAppM ``String.append #[left, right]) do
        throwError "missing-definition identifier uses a nonstandard append"
      return (← concreteString fuel left) ++ (← concreteString fuel right)
    if expression.isAppOfArity ``toString 3 || expression.isAppOfArity ``Nat.repr 1 then
      let natural := arguments.back!
      unless ← isDefEq expression (← mkAppM ``Nat.repr #[natural]) do
        throwError "missing-definition identifier uses a nonstandard version conversion"
      let some value ← getNatValue? (← withTransparency .all (whnf natural))
        | throwError "missing-definition version is not concrete"
      return toString value
    let reduced ← withTransparency .all (whnf expression)
    if reduced == expression then
      throwError "missing-definition identifier is not a concrete String: {expression}"
    concreteString fuel reduced

/-- Metadata reflects constructor cases of the typed resolver, not diagnostic text. -/
private meta def missingNames (value : Expr) : MetaM (List String) := do
  let mut value ← mkAppM ``Incomplete.definitions #[value]
  let mut names := []
  for _ in [:256] do
    let reduced ← whnf value
    if reduced.isAppOf ``List.nil then return names.reverse
    unless reduced.isAppOf ``List.cons do throwError "unresolved missing-definition list"
    let arguments := reduced.getAppArgs
    let item := arguments[arguments.size - 2]!
    let name ← concreteString 4096 (← instantiateMVars item)
    names := name :: names
    value := arguments.back!
  throwError "missing-definition list exceeds metadata limit"

private meta def semanticError (expression : Expr) : MetaM (Option Json) := do
  let reduced ← whnf expression
  if reduced.isAppOf ``Except.error then
    let value := reduced.getAppArgs.back!
    let type ← whnf (← inferType value)
    if type.isConstOf ``Incomplete then
      return some (Json.mkObj [("status", toJson "incomplete"),
        ("definitions", toJson (← missingNames value))])
    if type.isConstOf ``ResolutionError then
      return some (Json.mkObj [("status", toJson "refused"),
        ("definitions", toJson ([] : List String)), ("error", toJson (toString (← ppExpr value)))])
  return none

private meta def throwSemantic {α : Type} (resolution : Json) (message : MessageData) : MetaM α :=
  throwError (MessageData.tagged (.str `zkc.claimResolution resolution.compress) message)

private meta def okArgument (expression : Expr) : MetaM Expr := do
  let reduced ← whnf expression
  unless reduced.isAppOf ``Except.ok do
    if let some resolution ← semanticError reduced then
      throwSemantic resolution m!"typed claim resolution: {reduced}"
    throwError "claim construction did not resolve to .ok: {reduced}"
  return reduced.getAppArgs.back!

private meta def someArgument (expression : Expr) : MetaM Expr := do
  let reduced ← whnf expression
  unless reduced.isAppOf ``Option.some do
    throwSemantic (Json.mkObj [("status", toJson "incomplete"),
      ("definitions", toJson ["registered property definition"])])
      m!"registered property has no definition"
  return reduced.getAppArgs.back!

/-- The actual selected model is admitted independently of any property export. -/
def modelResolution {F G : Type} [Field F] [Fintype F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    {art : Artifacts} {endpoint : Semantics} (registry : ModelRegistry)
    (_subject : Subject F G art endpoint) (request : Wire.Request) :=
  resolveModel registry F art.original endpoint request.model

private meta def normalizationNames : List Name :=
  [``soundnessProperty, ``knowledgeProperty, ``soundnessArguments,
    ``knowledgeArguments, ``resolveModel, ``modelResolution, ``modelSchema, ``checkCapabilities,
    ``checkArguments, ``named, ``reference, ``Subject.check,
    ``Subject.targetReference, ``Subject.acceptance, ``Numeric.natural, ``Numeric.cardinality,
    ``models, ``Registry.lookup, ``Wire.TargetRef.matches, ``exactUniform,
    ``forking, ``naturalReflexiveRec, ``naturalBneRec, ``ModelContext.parameter, ``ModelContext.resolveApplication]

-- Lean otherwise creates shared unfolding equations lazily in each client,
-- with different private matcher proofs under the same public equation name.
-- Materialize them once so every client imports the same checked declarations.
run_cmd liftTermElabM do
  for declaration in normalizationNames do
    discard <| getEqnsFor? declaration

private meta def normalizeResolution (expression : Expr) (declarations : Array (TSyntax `ident)) :
    TacticM (Expr × Expr) := do
  let names := declarations ++ normalizationNames.toArray.map mkIdent
  let lemmas ← names.mapM fun id => `(Parser.Tactic.simpLemma| $id:term)
  let configuration ← mkSimpContext
    (← `(tactic| simp +instances [$lemmas,*])) false
  let mut value := expression
  let mut normalization ← mkEqRefl expression
  for _ in [:4] do
    let (step, _) ← configuration.dischargeWrapper.with fun discharge? => do
      Meta.simp (← whnf value) configuration.ctx configuration.simprocs discharge?
    normalization ← mkEqTrans normalization (← step.getProof)
    value := step.expr
  return (value, normalization)

elab "claim_model" "normalizing" "[" declarations:ident,* "]" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  unless target.isAppOf ``Exists do throwError "expected an actual model admission goal"
  let predicate := target.getAppArgs.back!
  let expression ← lambdaTelescope predicate fun _ body => do
    unless body.isAppOf ``Eq do throwError "expected the model resolution equation"
    return body.getAppArgs[1]!
  let arguments := expression.getAppArgs
  unless expression.isAppOf ``modelResolution do throwError "expected the actual subject's model resolution"
  let _ ← okArgument (← mkAppM ``Subject.check #[arguments[arguments.size - 2]!, arguments.back!])
  let (value, normalization) ← normalizeResolution expression declarations.getElems
  let model ← okArgument (← okArgument value)
  let proof ← mkAppOptM ``Exists.intro #[some (mkConst ``Model), some predicate,
    some model, some normalization]
  goal.assign proof
  replaceMainGoal []

/-- Construct the actual typed Resolved record; lookup and elaboration equations
are checked rather than accepted from the native export. -/
elab "claim_resolve" models:term "normalizing" "[" declarations:ident,* "]" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let arguments := target.getAppArgs
  unless target.isAppOf ``Resolved && arguments.size == 5 do
    throwError "expected a typed Resolved goal"
  let registry := arguments[1]!
  let subject := arguments[3]!
  let request := arguments[4]!
  -- Common admission precedes extension lookup, including unavailable exports.
  let _ ← okArgument (← mkAppM ``Subject.check #[subject, request])
  let modelRegistry ← Term.elabTerm models (some (mkConst ``ModelRegistry))
  let model ← mkAppM ``Wire.Request.model #[request]
  let identifier ← mkAppM ``Wire.Application.identifier #[model]
  let _ ← okArgument (← mkAppM ``Registry.lookup #[modelRegistry, identifier])
  let propertyId ← mkAppM ``Wire.Request.property #[request]
  let lookup ← mkAppM ``Registry.lookup #[registry, propertyId]
  let entry ← okArgument lookup
  let definition ← mkAppM ``Export.definition #[entry]
  let property ← someArgument definition
  let elaborate ← mkAppM ``PropertyExport.elaborate #[property, request, subject]
  let (expression, normalization) ← normalizeResolution elaborate declarations.getElems
  let values ← okArgument expression
  let subjectEq ← mkEqRefl (← mkAppM ``Wire.Request.subject #[request])
  let registered ← mkEqRefl lookup
  let defined ← mkEqRefl definition
  let elaborated := normalization
  let value ← mkAppOptM ``Resolved.mk #[some arguments[0]!, some registry,
    some arguments[2]!, some subject, some request, some subjectEq, some entry,
    some registered, some property, some defined, some values, some elaborated]
  goal.assign value
  replaceMainGoal []

elab "claim_evaluate" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  unless target.isAppOf ``Evaluated do throwError "expected an Evaluated goal"
  let resolved := target.getAppArgs.back!
  let expression ← mkAppM ``Resolved.meaning #[resolved]
  let reduced ← whnf expression
  if let some resolution ← semanticError reduced then
    throwSemantic resolution m!"typed meaning resolution: {reduced}"
  let proposition ← okArgument expression
  let value ← mkAppM ``Evaluated.mk #[proposition, ← mkEqRefl expression]
  goal.assign value
  replaceMainGoal []

private structure Failure where
  diagnostic : String
  resolution : Option Json := none

private meta partial def resolutionTag : MessageData → Option Json
  | .tagged (.str parent payload) message =>
    if parent == `zkc.claimResolution then (Json.parse payload).toOption else resolutionTag message
  | .withContext _ message | .withNamingContext _ message | .nest _ message |
    .group message | .ofOriginatingSyntax _ message => resolutionTag message
  | .compose first second => resolutionTag first <|> resolutionTag second
  | .trace _ message messages => resolutionTag message <|> messages.findSome? resolutionTag
  | _ => none

/-- Failure leaves request data in the environment, without an invented proof. -/
private meta def checkedCommand (commandSyntax : Syntax) : CommandElabM (Option Failure) := do
  let saved ← get
  try
    -- A deferred theorem failure must not leave a provisional declaration or
    -- let later method construction report a receipt before the error arrives.
    withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false })
      (elabCommand commandSyntax)
    let current ← get
    if current.messages.hasErrors then
      let messages := current.messages.toList.filter (·.severity == .error)
      let diagnostic := String.intercalate "\n" (← messages.mapM (·.data.toString))
      let resolution := messages.findSome? (resolutionTag ·.data)
      set saved
      return some ⟨diagnostic, resolution⟩
    return none
  catch error =>
    set saved
    return some ⟨← error.toMessageData.toString, resolutionTag error.toMessageData⟩

private meta def result (request : Name) (receipt : Option Name)
    (attempts : List (String × String)) (failure : Option Failure := none) : CommandElabM Unit := do
  let resolution := failure.map fun failure =>
    (failure.resolution.getD (Json.mkObj [("status", toJson "open"),
      ("definitions", toJson ([] : List String))])).setObjVal! "diagnostic" (toJson failure.diagnostic)
  let attempts := if (resolution.bind fun value => (value.getObjValAs? String "status").toOption) == some "refused"
    then attempts ++ [("refused", (failure.map (·.diagnostic)).getD "typed resolution refused")]
    else attempts
  let object := Json.mkObj [
    ("request", toJson request.toString),
    ("receipt", toJson (receipt.map Name.toString)),
    ("attempts", toJson (attempts.map fun (status, reason) =>
      Json.mkObj [("status", toJson status), ("reason", toJson reason)]))]
  let object := match resolution with
    | none => object
    | some resolution => object.setObjVal! "resolution" resolution
  logInfo ("SOURCE_CLAIM_RESULT " ++ object.compress)

/-- The command emits ordinary declarations, retaining universal type and
application binders. Lookup, argument evaluation, method execution and proofs
are checked independently of the native export and Python renderer. -/
syntax (name := claimRequest) "claim_request " ident " using " term " method " term : command

@[command_elab claimRequest] meta unsafe def elaborateClaim : CommandElab
  | `(claim_request $data:ident using $library:term method $planTerm:term) => do
    let exports ← liftTermElabM <| Term.evalTerm Library (mkConst ``Library) library
    let wire ← liftTermElabM <| Term.evalTerm Wire.Request (mkConst ``Wire.Request) data
    let plan ← liftTermElabM <| Term.evalTerm (Option Wire.Application)
      (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Wire.Application)) planTerm
    let application := mkIdent `application
    let currentNamespace ← getCurrNamespace
    let stem := data.getId.toString.dropEnd 4 |>.toString
    let name (suffix : String) := mkIdent (Name.mkSimple (stem ++ suffix))
    let requestName := currentNamespace ++ data.getId
    let resolved := name "Resolved"
    let evaluated := name "Evaluated"
    let receipt := name "Receipt"
    let subject := mkIdent (if wire.subject.stage == .executableBytes
      then exports.bytesSubject.getD exports.subject else exports.subject)
    let properties := mkIdent exports.properties
    let models := mkIdent exports.models
    let normalization := (exports.normalization ++ [currentNamespace ++ data.getId]).toArray.map mkIdent
    if wire.subject.stage == .interactive then
      match exports.interactiveSubject, exports.interactiveModels with
      | some subjectName, some modelsName =>
        let interactive := mkIdent subjectName
        let models := mkIdent modelsName
        let resolution := name "Resolution"
        let checked := name "RegisteredIncomplete"
        elabCommand (← `(def $resolution := InteractiveSubject.resolveRequest $models $interactive $data))
        let refused ← liftTermElabM do
          return (← whnf (← Term.elabTerm resolution none)).isAppOf ``Except.error
        let equation ← if refused then
            let checked := name "Refused"
            `(theorem $checked : ∃ error, $resolution = .error error := by exact ⟨_, rfl⟩)
          else
            `(theorem $checked : ∃ missing, $resolution = .ok (.error missing) := by exact ⟨_, rfl⟩)
        let failed ← checkedCommand equation
        if let some failed := failed then result requestName none [] (some failed)
        else
          let outcome ← liftTermElabM do
            let expression ← Term.elabTerm resolution none
            let outer ← whnf expression
            if outer.isAppOf ``Except.ok then semanticError outer.getAppArgs.back!
            else semanticError outer
          result requestName none [] (some ⟨"interactive typed resolver result", outcome⟩)
      | _, _ => result requestName none [] (some ⟨"no admitted interactive subject library", none⟩)
      return
    let endpoint ← if wire.subject.stage == .compiledIdeal then `(.idealMeaning) else `(.executableBytes)
    elabCommand (← `(section))
    elabCommand (← `(set_option linter.unusedSectionVars false))
    let field := mkIdent `F
    let group := mkIdent `G
    elabCommand (← `(variable {$field $group : Type} [Field $field] [Fintype $field] [DecidableEq $field]
      [Inhabited $field] [SampleableType $field] [AddCommGroup $group] [Module $field $group]
      [DecidableEq $group] [SampleableType $group]))
    let modelAdmission := name "ModelAdmission"
    let failed ← checkedCommand (← `(theorem $modelAdmission ($application : String) :
        ∃ actual, modelResolution ($models $endpoint $application)
          ($subject (F := $field) (G := $group)) $data = .ok (.ok actual) := by
        claim_model normalizing [$normalization,*]))
    if let some error := failed then
      result requestName none [] (some error)
      elabCommand (← `(end))
      return
    let failed ← checkedCommand (← `(noncomputable def $resolved ($application : String) : Resolved
      ($properties (F := $field) (G := $group) $endpoint $application) Subject.reference
      ($subject (F := $field) (G := $group)) $data := by
        claim_resolve ($models $endpoint $application) normalizing [$normalization,*]))
    if let some error := failed then
      result requestName none [] (some error)
      elabCommand (← `(end))
      return
    let resolution := name "Resolution"
    elabCommand (← `(theorem $resolution ($application : String) :
      resolveRequest ($properties (F := $field) (G := $group) $endpoint $application)
        ($models $endpoint $application) ($subject (F := $field) (G := $group)) $data =
          .ok (.ok ($resolved (F := $field) (G := $group) $application)) :=
      resolveRequest_eq rfl rfl _))
    let failed ← checkedCommand (← `(noncomputable def $evaluated ($application : String) : Evaluated
      ($resolved (F := $field) (G := $group) $application) := by claim_evaluate))
    if let some error := failed then
      result requestName none [] (some error)
      elabCommand (← `(end))
      return
    match plan with
    | none => result requestName none []
    | some plan =>
      let methods := exports.methods.map (fun (key, name) => (key, name, 0)) ++
        exports.theoremMethods.map (fun (key, name) => (key, name, 1)) ++
        exports.receiptMethods.map (fun (key, name) => (key, name, 2))
      match methods.filter (fun entry => entry.1 == plan.identifier) with
      | [] => result requestName none [("unsupported", "unregistered method or version")]
      | [(_, prove, route)] =>
        if !plan.arguments.isEmpty then
          result requestName none [("unsupported", "method parameters")]
        else
          let prove := mkIdent prove
          let proof ← if route == 2 then
              `(by exact $prove _ rfl ($subject (F := $field) (G := $group)).stageLinkProofs)
            else if route == 1 then
              `(by
                exact Receipt.ofTheorem (meaning := $evaluated (F := $field) (G := $group) $application)
                  ($prove (F := $field) (G := $group) $application) (provenance := ⟨.theorem, $(quote prove.getId.toString),
                  ⟨$(quote plan.identifier.name), $(quote plan.identifier.version)⟩, [], []⟩)
                  (links := ($subject (F := $field) (G := $group)).stageLinkProofs))
            else
              `(by
                exact Receipt.ofEndpoint (meaning := $evaluated (F := $field) (G := $group) $application)
                  (by first
                    | exact $prove (F := $field) (G := $group) (endpoint := $endpoint) _
                    | exact $prove (F := $field) (G := $group) _)
                  (provenance := ⟨.endpoint, $(quote prove.getId.toString),
                  ⟨$(quote plan.identifier.name), $(quote plan.identifier.version)⟩, [], []⟩)
                  (links := ($subject (F := $field) (G := $group)).stageLinkProofs))
          let failed ← checkedCommand (← `(noncomputable def $receipt ($application : String) :
              AdmittedReceipt ($models $endpoint $application)
                ($evaluated (F := $field) (G := $group) $application) := {
              receipt := $proof
              checked := rfl
              modelAdmitted := $modelAdmission (F := $field) (G := $group) $application }))
          if let some error := failed then
            result requestName none [("refused", error.diagnostic)]
          else
            let methods := name "Methods"
            let executed := name "MethodExecuted"
            elabCommand (← `(noncomputable def $methods ($application : String) :
                Registry (MethodExport ($evaluated (F := $field) (G := $group) $application)) :=
              ⟨[⟨⟨$(quote plan.identifier.name), $(quote plan.identifier.version)⟩,
                "zkc.method.author-library/0", some ⟨fun supplied =>
                  if supplied.arguments.isEmpty then .ok (.proved (($receipt (F := $field) (G := $group) $application).receipt))
                  else .error (.schema "method takes no parameters")⟩⟩]⟩))
            elabCommand (← `(theorem $executed ($application : String) :
              runMethod ($methods (F := $field) (G := $group) $application)
                ⟨⟨$(quote plan.identifier.name), $(quote plan.identifier.version)⟩, []⟩ =
                .ok (.proved (($receipt (F := $field) (G := $group) $application).receipt)) := rfl))
            result requestName (some (currentNamespace ++ receipt.getId)) []
      | _ => result requestName none [("refused", "conflicting registered methods")]
    elabCommand (← `(end))
  | _ => throwUnsupportedSyntax

end ZkcSecurity.Tools.ClaimConstruction
