module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import ZkcSecurity.Claims.Knowledge
public import ZkcSecurity.Claims.StageLinks

@[expose] public section

/-! Typed registry elaboration for the current compiled Fiat-Shamir model.
The schema is extensible by new exports, without core or grammar branches for
protocol families. Unsupported interpretations are explicit incomplete values. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint

def named (arguments : List (Option String × Wire.Expr)) (name : String) : Option Wire.Expr :=
  (arguments.find? (fun argument => argument.1 == some name)).map Prod.snd

def reference (expression : Wire.Expr) : Except ResolutionError String :=
  match expression with
  | .reference name => .ok name
  | _ => .error (.schema "expected a registered reference")

/-- Closed schemas reject unknown, positional and duplicate named arguments. -/
def checkArguments (allowed : List String) (arguments : List (Option String × Wire.Expr)) :
    Except ResolutionError Unit := do
  let names ← arguments.mapM fun argument => match argument.1 with
    | some name => if name ∈ allowed then .ok name else .error (.schema ("unknown argument: " ++ name))
    | none => .error (.schema "unexpected positional argument")
  if names.Nodup then pure () else throw (.schema "duplicate argument")

def modelSchema (F : Type) [Fintype F] (snapshot : Snapshot) (context : ModelContext) (endpoint : Semantics)
    (application : Wire.Application) : Except ResolutionError (Except Incomplete Model) := do
  checkArguments ["level", "statement", "oracle", "challenges", "queries", "application", "validator_cost", "budget_symbol"] application.arguments
  let level ← reference (named application.arguments "level" |>.getD (.reference "levels.ideal"))
  if level != (match endpoint with | .idealMeaning => "levels.ideal" | .executableBytes => "levels.bytes") then
    throw .stageMismatch
  let form ← match ← reference (named application.arguments "statement" |>.getD (.reference "statements.fixed")) with
    | "statements.fixed" => pure Form.fixed
    | "statements.adaptive" => pure Form.adaptive
    | _ => throw (.schema "unsupported statement form")
  let oracle := named application.arguments "oracle" |>.getD
    (.application "oracles.random" (some 0) [(none, .reference "construction.provider")])
  match oracle with
  | .application "oracles.random" (some 0) [(none, .reference "construction.provider")] => pure ()
  | .application name (some version) _ => throw (.unknownIdentifier ⟨name, version⟩)
  | _ => throw (.schema "expected the exact typed-history random oracle")
  let challenge ← reference (named application.arguments "challenges" |>.getD (.reference "challenges.exact_uniform"))
  if challenge != "challenges.exact_uniform" then
    return .error ⟨["challenge regime: " ++ challenge]⟩
  let budgetSymbol ← reference (named application.arguments "budget_symbol" |>.getD (.reference "budgets.queries"))
  let binding ← match named application.arguments "application", form with
    | some _, .fixed => throw (.schema "fixed model has no application context")
    | some expression, .adaptive => do
      pure (some (← context.resolveApplication (← reference expression)))
    | none, .fixed => pure none
    | none, .adaptive => throw (.schema "adaptive model requires application")
  let queries := named application.arguments "queries" |>.getD (.reference budgetSymbol)
  let limit := match queries with
    | .reference name => if name = budgetSymbol then .ok (.symbolic name) else
        QueryLimit.fixed <$> Numeric.natural F snapshot queries
    | _ => QueryLimit.fixed <$> Numeric.natural F snapshot queries
  let validatorCost := Bound.elaborate F snapshot budgetSymbol
    (named application.arguments "validator_cost" |>.getD (.natural 0))
  return do
    return ⟨form, ← limit, budgetSymbol, binding.map (·.value) |>.getD "", ← validatorCost, binding⟩

def models (context : ModelContext) (endpoint : Semantics) : ModelRegistry :=
  ⟨[⟨exactUniform, "zkc.model.fiat-shamir/0",
    some (fun F finite snapshot actual application =>
      if actual = endpoint then @modelSchema F finite snapshot context actual application
      else .error .stageMismatch)⟩]⟩

def resolveModel (registry : ModelRegistry) (F : Type) [Fintype F] (snapshot : Snapshot)
    (endpoint : Semantics) (application : Wire.Application) :
    Except ResolutionError (Except Incomplete Model) :=
  match registry.lookup application.identifier with
  | .error error => .error error
  | .ok entry => match entry.definition with
    | none => .ok (.error ⟨["model definition: " ++ application.identifier.name]⟩)
    | some elaborate => elaborate F inferInstance snapshot endpoint application

section
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [Fintype F] [Inhabited F] {art : Artifacts} {endpoint : Semantics}

def schedule (subject : Subject F G art endpoint)
    (model : Model) (charges : List (String × Wire.Expr)) :
    Except ResolutionError (Except Incomplete (ChargeSchedule subject)) := do
  let selected ← charges.mapM fun (name, expression) =>
    match subject.sites.find? (fun site => site.label == name) with
    | none => .error (.siteMismatch name)
    | some site => .ok (site, expression)
  return do
    let entries ← selected.mapM fun (site, expression) => do
      return (site, ← Bound.elaborate F art.original model.budgetSymbol expression)
    if nonempty : entries ≠ [] then
      if unique : (entries.map (fun entry => entry.1.label)).Nodup then
        if nativeUnique : (entries.map (fun entry => entry.1.native)).Nodup then
          return ⟨entries, nonempty, unique, nativeUnique⟩
        else .error ⟨["distinct construction occurrences"]⟩
      else .error ⟨["distinct charge sites"]⟩
    else .error ⟨["nonempty charge schedule"]⟩

def checkCapabilities (request : Wire.Request) : Except ResolutionError Unit := do
  let identifiers := request.capabilities.map (·.identifier)
  if !identifiers.Nodup then throw (.schema "duplicate capability")
  for capability in request.capabilities do
    if capability.identifier != chargedReduction then throw (.unknownIdentifier capability.identifier)
    if !capability.arguments.isEmpty then throw (.schema "charged reduction takes its schedule from the quantity")

def soundnessArguments (registry : ModelRegistry)
    (request : Wire.Request) (subject : Subject F G art endpoint) :
    Except ResolutionError (Except Incomplete (SoundnessRequest subject)) := do
  subject.check request
  checkCapabilities request
  if request.parameters.isSome then throw (.schema "soundness has no additional parameters")
  let model ← resolveModel registry F art.original endpoint request.model
  match model with
  | .error missing => return .error missing
  | .ok model =>
    match request.quantity with
    | .scalar expression =>
      if !request.capabilities.isEmpty then return .error ⟨["charged capability requires a charge schedule"]⟩
      return do return ⟨model, .scalar (← Bound.elaborate F art.original model.budgetSymbol expression)⟩
    | .charged charges =>
      let resolved ← schedule subject model charges
      return resolved.map (fun schedule => ⟨model, .charged schedule⟩)
    | .guarantee _ => throw (.schema "soundness requires an error or charge quantity")

def knowledgeArguments (registry : ModelRegistry) (request : Wire.Request)
    (subject : Subject F G art endpoint) :
    Except ResolutionError (Except Incomplete (KnowledgeRequest subject)) := do
  subject.check request
  checkCapabilities request
  if request.parameters.isSome then throw (.schema "knowledge has no additional parameters")
  if !request.capabilities.isEmpty then return .error ⟨["knowledge capability interpretation"]⟩
  if (named request.model.arguments "validator_cost").isSome then
    throw (.schema "knowledge model has no validator cost")
  if (named request.model.arguments "application").isSome then
    throw (.schema "knowledge model has no application context")
  let guarantee ← match request.quantity with
    | .guarantee form => pure form
    | _ => throw (.schema "knowledge requires a guarantee")
  if guarantee.identifier != forking then throw (.unknownIdentifier guarantee.identifier)
  checkArguments ["challenges", "cost"] guarantee.arguments
  let expectedCost := named guarantee.arguments "cost" |>.getD
    (.application "prover_runs" none [(none, .natural 2)])
  match expectedCost with
  | .application "prover_runs" none [(none, .natural 2)] => pure ()
  | _ => return .error ⟨["two-run replay extraction cost"]⟩
  let challenges := named guarantee.arguments "challenges"
  match challenges with
  | none => pure ()
  | some expression =>
    match Numeric.natural F art.original expression with
    | .error missing => return .error missing
    | .ok count =>
      if count != Fintype.card F then return .error ⟨["exact field challenge cardinality"]⟩
  let model ← resolveModel registry F art.original endpoint request.model
  match model with
  | .error missing => return .error missing
  | .ok model =>
    if fixed : model.form = .fixed then
      match selected : subject.target with
      | .retained target => return .ok ⟨target, selected, model, fixed⟩
      | .importedLanguage _ => return .error ⟨["retained relation for replay knowledge"]⟩
    else return .error ⟨["adaptive replay knowledge model"]⟩

/-- A public typed export lets generators construct and kernel-check explicit
resolved values without duplicating the semantic function. -/
noncomputable def soundnessProperty (registry : ModelRegistry) :
    PropertyExport (Subject F G art endpoint) where
  Arguments subject := Except Incomplete (SoundnessRequest subject)
  elaborate := soundnessArguments registry
  meaning _ arguments := arguments.map SoundnessRequest.meaning
  requiredLinks subject _ := subject.stageLinks

noncomputable def knowledgeProperty (registry : ModelRegistry) :
    PropertyExport (Subject F G art endpoint) where
  Arguments subject := Except Incomplete (KnowledgeRequest subject)
  elaborate := knowledgeArguments registry
  meaning _ arguments := arguments.map KnowledgeRequest.meaning
  requiredLinks subject _ := subject.stageLinks

/-- Built-ins are ordinary typed exports. A user property extends this list by
`Registry.register`, supplying a typed elaborator and a Lean meaning function. -/
noncomputable def properties (registry : ModelRegistry) :
    Registry (PropertyExport (Subject F G art endpoint)) := ⟨[
  ⟨⟨"soundness", 0⟩, "zkc.property.soundness/0", some (soundnessProperty registry)⟩,
  ⟨⟨"knowledge", 0⟩, "zkc.property.knowledge/0", some (knowledgeProperty registry)⟩,
  ⟨⟨"completeness", 0⟩, "zkc.property.completeness/0", none⟩,
  ⟨⟨"special_soundness", 0⟩, "zkc.property.special-soundness/0", none⟩]⟩

/-- Common structural/model admission also runs for a registered property whose
interpretation is absent. Unknown model versions do not become Incomplete. -/
def resolveRequest (propertyRegistry : Registry (PropertyExport (Subject F G art endpoint)))
    (modelRegistry : ModelRegistry) (subject : Subject F G art endpoint) (request : Wire.Request) :
    Except ResolutionError (Except Incomplete (Resolved propertyRegistry Subject.reference subject request)) :=
  match subject.check request with
  | .error error => .error error
  | .ok () => match modelRegistry.lookup request.model.identifier with
    | .error error => .error error
    | .ok _ => resolve propertyRegistry Subject.reference subject request

omit [SampleableType F] [Fintype F] [Inhabited F] in
/-- Structural admission and the actual model lookup lift a checked property
resolution through the security resolver. The equations stay kernel checked. -/
theorem resolveRequest_eq
    {propertyRegistry : Registry (PropertyExport (Subject F G art endpoint))}
    {modelRegistry : ModelRegistry} {subject : Subject F G art endpoint} {request : Wire.Request}
    (checked : subject.check request = .ok ())
    {entry : Export ((F : Type) → Fintype F → Snapshot → Semantics → Wire.Application →
      Except ResolutionError (Except Incomplete Model))}
    (registered : modelRegistry.lookup request.model.identifier = .ok entry)
    (resolved : Resolved propertyRegistry Subject.reference subject request) :
    resolveRequest propertyRegistry modelRegistry subject request = .ok (.ok resolved) := by
  simpa only [resolveRequest, checked, registered] using resolved.resolve_eq

end
end ZkcSecurity.Claims

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``ZkcSecurity.Claims.reference
