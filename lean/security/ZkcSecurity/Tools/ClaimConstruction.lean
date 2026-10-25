module

public import Lean
public meta import Mathlib.Tactic.Convert
public meta import Zkc.Claims.Wire
public meta import Zkc.Claims.ClosedString
public import Zkc.Claims.Methods
public import Zkc.Claims.Interactive
public import ZkcSecurity.Claims.Resolution
public import ZkcSecurity.Claims.Endpoint
public meta import ZkcSecurity.Claims.Canonical
public import ZkcSecurity.Claims.Canonical

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

meta initialize registerTraceClass `zkc.claimConstruction

/-- Physical author-library exports. Missing methods remain unsupported attempts.
The resolved/evaluated indices, rather than these names, determine proof types. -/
structure Library where
  subject : Name
  authority : Option Name := none
  context : Option Name := none
  bytesSubject : Option Name := none
  properties : Name
  models : Name
  interactiveSubject : Option Name := none
  interactiveModels : Option Name := none
  normalization : List Name := []
  /-- Mathematical normalization for applying theorem exports. Keep this
  separate from source/registry normalization to avoid unfolding source data
  in the proof being applied. Every rewrite is checked by the kernel. -/
  theoremNormalization : List Name := []
  methods : List (Identifier × Name) := []
  theoremMethods : List (Identifier × Name) := []
  receiptMethods : List (Identifier × Name) := []
  deriving Inhabited

/-- Normalize a reflected decision without evaluating its carrier. The resolver
can expose this dependent Boolean eliminator while reducing an `Except` bind;
rewriting its discriminator alone would change the type of the reflection proof. -/
theorem reflectedTrue {p : Prop} [Decidable p] {α : Sort u}
    (no : ¬ p → α) (yes : p → α) (holds : p) :
    @Bool.rec (fun b => b.Reflects p → α) no yes (decide p)
      (Decidable.reflects_decide p) = yes holds := by
  cases ‹Decidable p› with
  | isFalse noProof => exact (noProof holds).elim
  | isTrue _ => rfl

/-- The negative branch preserves the same reflection evidence. -/
theorem reflectedFalse {p : Prop} [Decidable p] {α : Sort u}
    (no : ¬ p → α) (yes : p → α) (fails : ¬ p) :
    @Bool.rec (fun b => b.Reflects p → α) no yes (decide p)
      (Decidable.reflects_decide p) = no fails := by
  cases ‹Decidable p› with
  | isFalse _ => rfl
  | isTrue proof => exact (fails proof).elim

/-- Admit a carrier cardinality as symbolic arithmetic before evaluating any
finite enumeration. The selected carrier still supplies the cardinality. -/
@[simp] theorem nonnegativeCardinality (cardinality : String → Except Incomplete Nat)
    (identity : String) :
    Numeric.nonnegativeWith cardinality
        (.application "cardinality" none [(none, .reference identity)]) =
      (cardinality identity).map (fun count => (count : ℚ≥0)) := by
  cases selected : cardinality identity with
  | error missing =>
    simp [Numeric.nonnegativeWith, Numeric.normalizeWith, selected, Except.map]
    rfl
  | ok count =>
    simp [Numeric.nonnegativeWith_cardinality cardinality identity count selected, Except.map]

/-- Keep a natural-over-cardinality bound symbolic. Unadmitted carriers and
zero denominators retain the arithmetic interpreter's refusal; no carrier is
enumerated merely to construct the checked rational value. -/
@[simp] theorem nonnegativeDivideCardinality
    (cardinality : String → Except Incomplete Nat) (identity : String) (numerator : Nat) :
    Numeric.nonnegativeWith cardinality
      (.binary .div (.natural numerator)
        (.application "cardinality" none [(none, .reference identity)])) = (do
          let count ← cardinality identity
          if count = 0 then .error ⟨["nonzero denominator"]⟩
          else .ok ((numerator : ℚ≥0) / (count : ℚ≥0))) := by
  cases selected : cardinality identity with
  | error missing =>
    simp [Numeric.nonnegativeWith, Numeric.normalizeWith, selected, evaluateNonnegative]
    rfl
  | ok count =>
    by_cases zero : count = 0
    · subst count
      simp [Numeric.nonnegativeWith, Numeric.normalizeWith, selected,
        evaluateNonnegative, evaluate]
      rfl
    · simp [Numeric.nonnegativeWith, Numeric.normalizeWith, selected,
        evaluateNonnegative, evaluate, zero,
        div_nonneg (Nat.cast_nonneg numerator : (0 : ℚ) ≤ numerator)
          (Nat.cast_nonneg count : (0 : ℚ) ≤ count)]
      rfl

/-- Evaluate concrete diagnostic Strings without treating pretty-printed terms
as identifiers. Literal concatenation and natural versions use their actual
standard operations; other unresolved values are refused. -/
private meta def concreteString (fuel : Nat) (expression : Expr) : MetaM String := do
  if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars then
    throwError "missing-definition identifier has unresolved variables: {expression}"
  Zkc.Claims.ClosedString.read fuel expression

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
    ``knowledgeArguments, ``responseDifference, ``ExtractionProfile.registry, ``Subject.extractionProfile, ``resolveModel, ``modelResolution, ``modelSchema, ``modelSchemaWith, ``premiseKeys, ``checkCapabilities,
    ``checkArguments, ``named, ``reference, ``Subject.check,
    ``Subject.targetReference, ``Subject.acceptance, ``Numeric.natural, ``Numeric.cardinality,
    ``models, ``Registry.lookup, ``Wire.TargetRef.matches, ``exactUniform,
    ``CanonicalAuthority.check, ``CanonicalAuthority.reference, ``CanonicalAuthority.resolveModel,
    ``CanonicalAuthority.modelEntry, ``CanonicalAuthority.propertyEntry, ``CanonicalAuthority.properties,
    ``Domain.Subject.check, ``Domain.Subject.reference, ``Domain.Subject.targetReference, ``Domain.Subject.acceptance,
    ``Domain.soundnessProperty, ``Domain.soundnessArguments, ``Domain.resolveModel, ``Domain.modelSchema,
    ``Domain.chargeSchedule,
    ``Domain.modelEntry, ``Domain.ModelExport.elaborate, ``HonestPair.ModelExport.elaborate,
    ``HonestPair.modelEntry, ``HonestPair.resolveModel, ``HonestPair.Subject.check, ``HonestPair.Subject.reference,
    ``HonestPair.Subject.targetReference, ``HonestPair.Subject.acceptance,
    ``HonestPair.completenessProperty, ``HonestPair.completenessArguments,
    ``completenessParameters, ``knowledgeParameters, ``emptyParameters,
    ``decodeSoundnessParameters, ``requireExactSoundness,
    ``checkDefaultRelation, ``defaultRelationHelper, ``defaultRelationOperation,
    ``HonestPair.resolveHonestModel, ``HonestPair.honestModelEntry, ``HonestPair.honestModelSchema,
    ``forking, ``reflectedTrue, ``reflectedFalse, ``beq_self_eq_true, ``decide_true, ``decide_false, ``ModelContext.parameter, ``ModelContext.resolveApplication,
    ``Fintype.card_ne_zero, ``NeZero.ne, ``Domain.Capabilities.cardinality, ``Bound.elaborateWith, ``Except.map]

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
    (← `(tactic| simp [$lemmas,*])) false
  let mut value ← instantiateMVars expression
  let mut normalization ← mkEqRefl expression
  for _ in [:8] do
    let previous := value
    let (step, _) ← configuration.dischargeWrapper.with fun discharge? => do
      let methods := match discharge? with
        | none => Simp.mkDefaultMethodsCore configuration.simprocs
        | some discharge => Simp.mkMethods configuration.simprocs discharge
            (wellBehavedDischarge := false)
      let symbolic := { methods with
        pre := fun term => do
          -- Retained occurrences are checked metadata. Their projections may
          -- reduce, but simplification must not traverse the embedded program
          -- and correspondence proofs to normalize a numerical charge.
          if term.isApp || term.isConst then
            if (← whnf (← inferType term)).isAppOf ``Domain.ChargeSite then
              return .done { expr := term }
          -- These checks only inspect source metadata. Reduce the result before
          -- `simp` traverses the imported source record and its proof fields.
          -- Cardinalities and property propositions remain symbolic below.
          if [``CanonicalAuthority.check, ``Domain.Subject.check,
              ``HonestPair.Subject.check, ``Subject.check,
              ``checkDefaultRelation,
              ``Domain.selectChargeSites,
              ``Zkc.Source.Structured.Catalogue.identitySort].any term.isAppOf && !term.hasMVar then
            let reduced ← withTransparency .all (whnf term)
            if [``Except.ok, ``Except.error, ``Option.some, ``Option.none].any reduced.isAppOf then
              return .done { expr := reduced, proof? := some (← mkEqRefl term) }
          methods.pre term
        dpre := fun term => do
          if term.isApp || term.isConst then
            if (← whnf (← inferType term)).isAppOf ``Domain.ChargeSite then
              return .done term
          if [``CanonicalAuthority.check, ``Domain.Subject.check,
              ``HonestPair.Subject.check, ``Subject.check,
              ``Domain.selectChargeSites,
              ``Zkc.Source.Structured.Catalogue.identitySort].any term.isAppOf && !term.hasMVar then
            let reduced ← withTransparency .all (whnf term)
            if [``Except.ok, ``Except.error, ``Option.some, ``Option.none].any reduced.isAppOf then
              return .done reduced
          methods.dpre term }
      Simp.mainCore value configuration.ctx (methods := symbolic)
    normalization ← mkEqTrans normalization (← step.getProof)
    value := step.expr
    if value == previous then
      -- Only a stuck, already simplified continuation needs head reduction.
      -- Reducing the original resolver first can open a complete imported
      -- subject before the metadata guards above have hidden its proof fields.
      let reduced ← whnf value
      if reduced == value then break
      value := reduced
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

/-- The same typed resolution record for a closed dependent authority. -/
elab "claim_resolve_for " authority:term " using_models " models:term "normalizing"
    "[" declarations:ident,* "]" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let arguments := target.getAppArgs
  unless target.isAppOf ``Resolved && arguments.size == 5 do throwError "expected a typed Resolved goal"
  let registry := arguments[1]!
  let subject := arguments[3]!
  let request := arguments[4]!
  let authority ← Term.elabTerm authority none
  trace[zkc.claimConstruction] "checking subject"
  let _ ← okArgument (← mkAppM ``CanonicalAuthority.check #[authority, subject, request])
  trace[zkc.claimConstruction] "subject checked; resolving registry"
  let modelType ← mkAppM ``CanonicalAuthority.ModelExport #[authority]
  let modelRegistry ← Term.elabTerm models (some (← mkAppM ``Registry #[modelType]))
  let model ← mkAppM ``Wire.Request.model #[request]
  let identifier ← mkAppM ``Wire.Application.identifier #[model]
  let _ ← okArgument (← mkAppM ``Registry.lookup #[modelRegistry, identifier])
  let propertyId ← mkAppM ``Wire.Request.property #[request]
  let lookup ← mkAppM ``Registry.lookup #[registry, propertyId]
  let entry ← okArgument lookup
  let definition ← mkAppM ``Export.definition #[entry]
  let property ← someArgument definition
  let elaborate ← mkAppM ``PropertyExport.elaborate #[property, request, subject]
  trace[zkc.claimConstruction] "normalizing property arguments"
  let (expression, normalization) ← normalizeResolution elaborate declarations.getElems
  trace[zkc.claimConstruction] "normalized arguments; checking result constructor"
  trace[zkc.claimConstruction] "normalized arguments: {expression}"
  let values ← okArgument expression
  trace[zkc.claimConstruction] "constructing checked resolution"
  goal.assign (← mkAppOptM ``Resolved.mk #[some arguments[0]!, some registry,
    some arguments[2]!, some subject, some request,
    some (← mkEqRefl (← mkAppM ``Wire.Request.subject #[request])), some entry,
    some (← mkEqRefl lookup), some property, some (← mkEqRefl definition), some values, some normalization])
  replaceMainGoal []

elab "claim_authority_model" "normalizing" "[" declarations:ident,* "]" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  unless target.isAppOf ``Exists do throwError "expected successful model resolution"
  let predicate := target.getAppArgs.back!
  let expression ← lambdaTelescope predicate fun _ body => do
    unless body.isAppOf ``Eq do throwError "expected model resolution equation"
    return body.getAppArgs[1]!
  let (value, normalization) ← normalizeResolution expression declarations.getElems
  let model ← okArgument (← okArgument value)
  goal.assign (← mkAppOptM ``Exists.intro #[none, some predicate, some model, some normalization])
  replaceMainGoal []

/-- Propose the context of the selected model export. The receipt separately
proves equality of the complete export, so this search cannot authorize a model. -/
elab "claim_context " models:term ", " request:term : tactic => withMainContext do
  let goal ← getMainGoal
  let registry ← Term.elabTerm models (some (mkConst ``ModelRegistry))
  let request ← Term.elabTerm request (some (mkConst ``Wire.Request))
  let application ← mkAppM ``Wire.Request.model #[request]
  let identifier ← mkAppM ``Wire.Application.identifier #[application]
  let entry ← okArgument (← mkAppM ``Registry.lookup #[registry, identifier])
  let definition ← someArgument (← mkAppM ``Export.definition #[entry])
  let elaborator ← whnfD definition
  let some schema := elaborator.find? (fun expression =>
      expression.isAppOf ``modelSchema && expression.getAppNumArgs >= 4)
    | throwError "no canonical model context candidate"
  let context := schema.getAppArgs[3]!
  if context.hasLooseBVars then throwError "model context depends on elaborator-local values"
  goal.assign context
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

/-- Normalize the type of a registered theorem before unification. This lets
one parametric export serve many source-selected models and quantities, without
per-request wrapper theorems. Normalization produces equality proofs; applying
the theorem and discharging its remaining premises still require kernel terms.
-/
elab "claim_apply_theorem " theoremTerm:term " normalizing "
    "[" declarations:ident,* "]" : tactic => withMainContext do
  let proof ← Term.elabTerm theoremTerm none
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let names := declarations.getElems ++ #[``Bound.value, ``Domain.SoundnessArguments.meaning,
    ``ennreal_nnrat_zero, ``ennreal_nnrat_one, ``ennreal_nnrat_natural,
    ``ennreal_nnrat_ofNat, ``ennreal_nnrat_inv, ``NeZero.ne,
    ``nsmul_eq_mul, ``mul_one_div, ``div_eq_mul_inv].map mkIdent
  let lemmas ← names.mapM fun id => `(Parser.Tactic.simpLemma| $id:term)
  let configuration ← mkSimpContext (← `(tactic| simp [$lemmas,*])) false
  let normalize (expression : Expr) : TacticM Simp.Result := do
    let (result, _) ← Simp.main (← instantiateMVars expression) configuration.ctx
      (methods := Simp.mkDefaultMethodsCore configuration.simprocs)
    pure result
  let normalized ← normalize (← inferType proof)
  let proof ← mkEqMP (← normalized.getProof) proof
  let goal ← getMainGoal
  let target ← normalize (← goal.getType)
  let goal ← goal.replaceTargetEq target.expr (← target.getProof)
  let goals ← withTransparency .all (goal.apply proof)
  replaceMainGoal goals
  evalTactic (← `(tactic| all_goals first
    | rfl
    | solve | simp [$lemmas,*]))

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

/-- Closed authority libraries use the same core resolution/evaluation/receipt
types. This branch does not manufacture uniform carrier or query parameters. -/
private meta def elaborateAuthorityClaimCore (exports : Library) (authorityName : Name)
    (wire : Wire.Request) (data : TSyntax `ident) (plan : Option Wire.Application)
    (application : Option (TSyntax `ident)) : CommandElabM Unit := do
  let use (name : Name) : CommandElabM (TSyntax `term) := do
    let identifier := mkIdent name
    match application with
    | none => `($identifier)
    | some application => `($identifier $application)
  let authority := mkIdent authorityName
  let context ← match exports.context with
    | some name => use name
    | none => liftTermElabM do
      let actual ← Term.elabTerm authority none
      let contextType ← whnf (← mkAppM ``CanonicalAuthority.Context #[actual])
      if ← isDefEq contextType (mkConst ``ModelContext) then `(ModelContext.empty)
      else if ← isDefEq contextType (mkConst ``Unit) then `(())
      else throwError "unsupported canonical authority context"
  let subject := mkIdent exports.subject
  let properties ← use exports.properties
  let models ← use exports.models
  let currentNamespace ← getCurrNamespace
  let stem := data.getId.toString.dropEnd 4 |>.toString
  let name (suffix : String) := mkIdent (Name.mkSimple (stem ++ suffix))
  let resolved := name "Resolved"
  let evaluated := name "Evaluated"
  let receipt := name "Receipt"
  let resolvedValue ← use resolved.getId
  let evaluatedValue ← use evaluated.getId
  let receiptValue ← use receipt.getId
  let normalization := (exports.normalization ++ [currentNamespace ++ data.getId]).toArray.map mkIdent
  let theoremNormalization := exports.theoremNormalization.toArray.map mkIdent
  let failed ← checkedCommand (← `(noncomputable def $resolved : Resolved $properties
      (CanonicalAuthority.reference $authority) $subject $data := by
    claim_resolve_for $authority using_models $models normalizing [$normalization,*]))
  if let some failure := failed then
    result (currentNamespace ++ data.getId) none [] (some failure)
    return
  let failed ← checkedCommand (← `(noncomputable def $evaluated : Evaluated $resolvedValue := by claim_evaluate))
  if let some failure := failed then
    result (currentNamespace ++ data.getId) none [] (some failure)
    return
  trace[zkc.claimConstruction] "canonical proposition constructed"
  let some plan := plan | result (currentNamespace ++ data.getId) none []; return
  let methods : List (Identifier × Name × Nat) := exports.methods.map (fun (key, name) => (key, name, 0)) ++
    exports.theoremMethods.map (fun (key, name) => (key, name, 1)) ++
    exports.receiptMethods.map (fun (key, name) => (key, name, 2))
  let matching := methods.filter (fun entry => entry.1 == plan.identifier)
  if matching.length > 1 then
    result (currentNamespace ++ data.getId) none [("refused", "conflicting registered methods")]
    return
  let [(_, method, route)] := matching
    | result (currentNamespace ++ data.getId) none [("unsupported", "unregistered method or version")]; return
  if !plan.arguments.isEmpty then
    result (currentNamespace ++ data.getId) none [("unsupported", "method parameters")]; return
  let methodName := method
  let method ← use methodName
  let rawMethod := mkIdent methodName
  let proof ← if route == 2 then
      `(by exact $method _ rfl (CanonicalAuthority.linkProofs $authority $subject))
    else if route == 1 then
      `(Receipt.ofTheorem (by
        dsimp only [$evaluated:term]
        first
        | claim_apply_theorem $method normalizing [$theoremNormalization,*]
        | claim_apply_theorem $rawMethod normalizing [$theoremNormalization,*])
        ⟨.theorem, $(quote methodName.toString), ⟨$(quote plan.identifier.name), $(quote plan.identifier.version)⟩, [], []⟩
        (CanonicalAuthority.linkProofs $authority $subject))
    else
      `(Receipt.ofEndpoint $method
        ⟨.endpoint, $(quote methodName.toString), ⟨$(quote plan.identifier.name), $(quote plan.identifier.version)⟩, [], []⟩
        (CanonicalAuthority.linkProofs $authority $subject))
  let modelProof ← `(by refine ⟨rfl, ?_⟩; claim_authority_model normalizing [$normalization,*])
  let receiptType ← match PropertyKey.ofIdentifier? wire.property with
    | some key =>
      let key := mkIdent (match key with
        | .soundness => ``PropertyKey.soundness | .knowledge => ``PropertyKey.knowledge
        | .completeness => ``PropertyKey.completeness | .specialSoundness => ``PropertyKey.specialSoundness)
      `(CanonicalReceipt $authority $models $context $key $evaluatedValue)
    | none => `(AuthorExtensionReceipt $authority $models $context $evaluatedValue)
  let failed ← checkedCommand (← `(noncomputable def $receipt : $receiptType :=
    ⟨$proof, $modelProof, by exact ⟨rfl, rfl⟩⟩))
  if failed.isNone then
    let methods := name "Methods"
    let executed := name "MethodExecuted"
    let methodsValue ← use methods.getId
    elabCommand (← `(noncomputable def $methods : Registry (MethodExport $evaluatedValue) :=
      ⟨[⟨⟨$(quote plan.identifier.name), $(quote plan.identifier.version)⟩,
        "zkc.method.author-library/0", some ⟨fun supplied =>
          if supplied.arguments.isEmpty then .ok (.proved ($receiptValue).receipt)
          else .error (.schema "method takes no parameters")⟩⟩]⟩))
    elabCommand (← `(theorem $executed :
      runMethod $methodsValue ⟨⟨$(quote plan.identifier.name), $(quote plan.identifier.version)⟩, []⟩ =
        .ok (.proved ($receiptValue).receipt) := rfl))
  result (currentNamespace ++ data.getId) (if failed.isNone then some (currentNamespace ++ receipt.getId) else none)
    [(if failed.isNone then "proved" else "failed", "closed authority method")] failed

/-- A parameterized registered context retains the source application binder.
Canonical model admission still checks the entire selected export and context. -/
private meta def elaborateAuthorityClaim (exports : Library) (authorityName : Name)
    (wire : Wire.Request) (data : TSyntax `ident) (plan : Option Wire.Application) : CommandElabM Unit := do
  let parameterized ← match exports.context with
    | none => pure false
    | some context => liftTermElabM do
      let type ← inferType (← Term.elabTerm (mkIdent context) none)
      isDefEq type (← mkArrow (mkConst ``String) (mkConst ``ModelContext))
  if parameterized then
    let application := mkIdent `application
    elabCommand (← `(section))
    elabCommand (← `(variable ($application : String)))
    elaborateAuthorityClaimCore exports authorityName wire data plan (some application)
    elabCommand (← `(end))
  else elaborateAuthorityClaimCore exports authorityName wire data plan none

/-- The command emits ordinary declarations, retaining universal type and
application binders. Lookup, argument evaluation, method execution and proofs
are checked independently of the native export and Python renderer. -/
syntax (name := claimRequest) "claim_request " ident " using " term " method " term : command

/-- Evaluate closed configuration data after definitional reduction. A static
projection may discard noncomputable semantic fields of its enclosing record;
genuine choices and other unresolved noncomputable data still fail compilation.
This only guides declaration construction: resolution and receipt proofs retain
the original request term and are checked independently by the kernel. -/
meta unsafe def evalClosedData (α : Type) (type : Expr) (stx : Syntax) : TermElabM α :=
    withoutModifyingEnv do
  let expression ← Term.elabTermEnsuringType stx type
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasMVar || expression.hasFVar || expression.hasLooseBVars then
    throwError "claim configuration must be closed data"
  let normalized ← withTransparency .all (reduce expression)
  evalExpr α type normalized

@[command_elab claimRequest] meta unsafe def elaborateClaim : CommandElab
  | `(claim_request $data:ident using $library:term method $planTerm:term) => do
    let exports ← liftTermElabM <| Term.evalTerm Library (mkConst ``Library) library
    let wire ← liftTermElabM <| evalClosedData Wire.Request (mkConst ``Wire.Request) data
    let plan ← liftTermElabM <| Term.evalTerm (Option Wire.Application)
      (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Wire.Application)) planTerm
    if let some authority := exports.authority then
      elaborateAuthorityClaim exports authority wire data plan
      return
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
    -- Requests using the same wire model in this source namespace share the
    -- certificate. Its type contains the exact subject snapshot and stage.
    let modelStem := "admittedModel" ++ toString (reprStr wire.model).hash
    let modelContext := mkIdent (Name.mkSimple (modelStem ++ "Context"))
    let selectedModel := mkIdent (Name.mkSimple modelStem)
    unless (← getEnv).contains (currentNamespace ++ selectedModel.getId) do
      elabCommand (← `(def $modelContext ($application : String) : ModelContext := by
        claim_context ($models $endpoint $application), $data))
      let failed ← checkedCommand (← `(theorem $selectedModel ($application : String) :
          CanonicalModelAdmission (CanonicalAuthority.ofUniformSubject ($subject (F := $field) (G := $group))) ($models $endpoint $application) ($modelContext $application)
            ($subject (F := $field) (G := $group)) ($data).model := by
          exact ⟨rfl, $modelAdmission (F := $field) (G := $group) $application⟩))
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
          let receiptType ← match PropertyKey.ofIdentifier? wire.property with
            | some key =>
              let key := mkIdent (match key with
                | .soundness => ``PropertyKey.soundness | .knowledge => ``PropertyKey.knowledge
                | .completeness => ``PropertyKey.completeness | .specialSoundness => ``PropertyKey.specialSoundness)
              `(CanonicalReceipt (CanonicalAuthority.ofUniformSubject ($subject (F := $field) (G := $group))) ($models $endpoint $application) ($modelContext $application) $key
                ($evaluated (F := $field) (G := $group) $application))
            | none => `(AuthorExtensionReceipt (CanonicalAuthority.ofUniformSubject ($subject (F := $field) (G := $group))) ($models $endpoint $application) ($modelContext $application)
                ($evaluated (F := $field) (G := $group) $application))
          let association ← if (PropertyKey.ofIdentifier? wire.property).isSome then
              `(by exact ⟨rfl, rfl⟩)
            else `(by exact ⟨rfl, by decide⟩)
          let failed ← checkedCommand (← `(noncomputable def $receipt ($application : String) :
              $receiptType := {
              receipt := $proof
              association := $association
              modelAdmission := $selectedModel (F := $field) (G := $group) $application }))
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
