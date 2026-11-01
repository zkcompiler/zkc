module

public import Zkc.Semantics.ReturnView
public import Zkc.Source.Structured.ReferenceLaws
public import Zkc.Source.Structured.BodyBindings
public meta import ZkcTools.Companions.Goals
public meta import ZkcTools.Generation.Commands
public meta import ZkcTools.StructuredSource.NamedValues
public meta import Lean.Elab.Tactic.Simp

@[expose] public section

/-! Named, complete presentations of typed helper templates.

`helper_presentation Name inputs [left, right] outputs [value] := actualBody`
derives its ABI from an existing closed `Region dialect inputs outputs` term.
It generates `Name.Inputs`, `Name.Output`, a curried `Name.run`, its structural `Name.equation`,
and `Name.Goal model reference condition` before any mathematical proof exists.
Use ordinary `companion_goal` headers to fix a chosen reference before proving it.
The reference returns `PIR.Outcome (Name.Output model)`; every output and stop
is retained. `Name.law` assembles a proved goal into the existing `ReferenceLaw`.
Its application still requires the actual declaration's checked `BodyIn`.

Names label ABI positions, never select mathematics. The command derives only
source structure. Collection, dependency and mathematical laws remain ordinary
proof obligations. No companion registration is necessary for direct use;
generated goal types also work with the existing companion resolver.

`run_eq` and `equation` are kernel-checked structural equations. The latter
has the independently generated `SourceEquation` type. `of_law` transports an
ordinary installed law after checking its exact body, complete reference and
premises. `law` performs the converse assembly from a proof of `Goal`; it does
not discharge dependency premises or the caller's final relation link.
-/

set_option autoImplicit false
namespace ZkcTools.StructuredSource.HelperPresentation
open Zkc.Source Zkc.Source.Structured

public meta section
open Lean Meta Elab Command Term

/-- Reduce only structural interpretation and finite ABI plumbing. Operation
semantics keep their existing owners; in particular collect and helper calls
are not recursively executed or expanded into another source interpreter. -/
def structural (body decoder expression : Expr) : MetaM Simp.Result := do
  -- Expand only the selected source tree, retaining the shared dialect and
  -- type indices used by the existing interpretation equations.
  let expanded ← reduce body
  let expression := expression.replace fun term => if term == body then some expanded else none
  let mut rules : SimpTheorems := {}
  for name in #[``Region.denote, ``Regions.denote, ``Operands.eval,
      ``Environment.prepend, ``Environment.push, ``Values.get,
      ``Evaluation.meaningOn, ``RegionMeaning.operation,
      ``Evaluation.operationOn, ``PIR.Process.bind,
      ``SiteObservations.closed, ``SiteObservations.silent] do
    rules ← rules.addDeclToUnfold name
  if let some name := body.getAppFn.constName? then
    rules := rules.addDeclToUnfoldCore name
  if let some name := decoder.getAppFn.constName? then
    rules ← rules.addDeclToUnfold name
  return (← simp expression (← Simp.mkContext (simpTheorems := #[rules]))).1

/-- An internal term producer. Its result must still have the original type
and the separately generated equation is checked by the kernel. -/
elab "helper_structure% " body:term " decoding " decoder:term " in " expression:term : term <= expected =>
  Term.withoutErrToSorry do
    let body ← elabTerm body none
    let decoder ← elabTerm decoder none
    let expression ← elabTermEnsuringType expression expected
    synthesizeSyntheticMVarsNoPostponing
    return (← structural body decoder (← instantiateMVars expression)).expr

elab "helper_structure_equation% " body:term " decoding " decoder:term : term <= expected =>
  Term.withoutErrToSorry do
    let body ← elabTerm body none
    let decoder ← elabTerm decoder none
    let some (_, expression, right) := expected.eq? |
      throwError "helper_structure_equation% expects the complete structural equation"
    synthesizeSyntheticMVarsNoPostponing
    let result ← structural body decoder (← instantiateMVars expression)
    unless ← withTransparency .all <| isDefEq result.expr right do
      throwError "helper presentation normalization mismatch:\nrun: {← whnf right}\nequation: {result.expr}"
    result.getProof

partial def types (list : Expr) : MetaM (List Expr) := do
  let list ← whnf list
  if list.isAppOf ``List.nil then return []
  unless list.isAppOf ``List.cons do
    throwError "helper_presentation requires a statically known complete ABI"
  return list.getAppArgs[1]! :: (← types list.getAppArgs[2]!)

def printTerm (expression : Expr) : MetaM String :=
  withOptions (fun options => options.setBool `pp.fullNames true) do
    return toString (← ppExpr expression)

def values (items : List String) : String :=
  items.foldr (fun item rest => "(.cons (" ++ item ++ ") " ++ rest ++ ")") ".nil"

def position (index : Nat) : String :=
  (List.replicate index ()).foldl (fun rest _ => "(.there " ++ rest ++ ")") ".here"

def pattern (items : List String) : String := values items

def command (source : String) : CommandElabM Unit := do
  let environment ← getEnv
  match Parser.runParserCategory environment `command source with
  | .error error => throwError "helper_presentation generated invalid syntax: {error}\n{source}"
  | .ok stx =>
    let before := (← get).messages.toList.length
    elabCommand stx
    let errors := (← get).messages.toList.drop before |>.filter (·.severity == .error)
    unless errors.isEmpty do
      throwError "helper_presentation: generated declaration failed to check\n{MessageData.joinSep (errors.map (·.data)) m!"\n"}"

syntax (name := helperPresentation) "helper_presentation " ident
  &"inputs " "[" ident,* "]" &"outputs " "[" ident,* "]" " := " term : command

def generate : CommandElab := fun stx => do
  let `(helper_presentation $name:ident inputs [$ins:ident,*]
      outputs [$outs:ident,*] := $body:term) := stx | throwUnsupportedSyntax
  let inputNames := ins.getElems.toList.map (·.getId.toString)
  let outputNames := outs.getElems.toList.map (·.getId.toString)
  let reserved := ["model", "table", "reference", "condition", "arguments", "result", "proof",
    "body", "run", "encode", "decode", "premise", "installed", "same", "reference_eq", "premises",
    "Inputs", "Output", "Goal", "SourceEquation", "encodeOutcome", "encode_decode", "decode_encode",
    "run_eq", "equation", "of_law", "law", "mk", "Values", "Region", "DomainModel",
    "Evaluation", "PIR", "Closed", "ReferenceLaw", "primitiveOutcome"]
  for names in [inputNames, outputNames] do
    unless names.eraseDups.length == names.length do
      throwError "helper_presentation requires distinct field names"
    for name in names do
      if reserved.contains name || name.contains '.' then
        throwError "helper_presentation field name is reserved or qualified: {name}"
  let (bodyText, inputTypes, outputTypes) ← runTermElabM fun _ => Term.withoutErrToSorry do
    let expression ← elabTerm body none
    synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasFVar || expression.hasMVar then
      throwError "helper_presentation expects a closed typed helper/template; instantiate its static parameters first"
    let type ← whnf (← inferType expression)
    unless type.isAppOfArity ``Region 3 do
      throwError "helper_presentation expects an actual typed helper Region"
    unless ← isDefEq type.getAppArgs[0]! (mkConst ``dialect) do
      throwError "helper_presentation expects the existing closed helper dialect"
    return (← printTerm expression, ← (← types type.getAppArgs[1]!).mapM (fun type => do printTerm (← reduce type)),
      ← (← types type.getAppArgs[2]!).mapM (fun type => do printTerm (← reduce type)))
  unless inputNames.length == inputTypes.length && outputNames.length == outputTypes.length do
    throwError "helper_presentation names must cover every input and output in ABI order"
  let binders := String.intercalate " " (inputNames.zip inputTypes |>.map fun (name, type) =>
    "(" ++ name ++ " : model.Value (" ++ type ++ "))")
  let arguments := String.intercalate " " inputNames
  let arrows := String.join (inputTypes.map fun type => "model.Value (" ++ type ++ ") → ")
  let decode := "{ " ++ String.intercalate ", " (outputNames.zipIdx |>.map fun (name, index) =>
    name ++ " := result.get " ++ position index) ++ " }"
  let packed := values (outputNames.map fun name => "result." ++ name)
  let inputPattern := pattern inputNames
  let goalBinders := "(model : DomainModel) (reference : " ++ arrows ++
    "PIR.Outcome (Output model)) (condition : Evaluation.MeaningsOn model.toCarriers closedInterface → " ++
    arrows ++ "Prop)"
  let destruct := String.join (inputNames.map fun name =>
    "cases arguments with | cons " ++ name ++ " arguments => ") ++ "cases arguments; "
  command ("namespace " ++ name.getId.toString)
  command "set_option Elab.async false"
  command "open Zkc.Source Zkc.Source.Structured"
  command "attribute [local implicit_reducible] Op.arguments Op.results Op.regions"
  command ("noncomputable abbrev body : Region dialect [" ++ String.intercalate ", " inputTypes ++ "] [" ++ String.intercalate ", " outputTypes ++ "] := " ++ bodyText)
  command ("named_values Inputs [" ++ String.intercalate ", " inputNames ++ "] := ([" ++
    String.intercalate ", " inputTypes ++ "] : List Zkc.Source.Structured.Ty)")
  command ("structure Output (model : DomainModel) where\n" ++
    String.join (outputNames.zip outputTypes |>.map fun (name, type) =>
      "  " ++ name ++ " : model.Value (" ++ type ++ ")\n"))
  command ("@[reducible] def encode (model : DomainModel) (result : Output model) : Values model.Value [" ++
    String.intercalate ", " outputTypes ++ "] := " ++ packed)
  command ("@[reducible] def decode (model : DomainModel) (result : Values model.Value [" ++
    String.intercalate ", " outputTypes ++ "]) : Output model := " ++ decode)
  command ("def encodeOutcome (model : DomainModel) (outcome : PIR.Outcome (Output model)) : PIR.Outcome (Values model.Value [" ++
    String.intercalate ", " outputTypes ++ "]) := match outcome with\n" ++
    "| .returned result => .returned (encode model result) | .stopped reason => .stopped reason")
  command ("theorem encode_decode (model : DomainModel) (arguments : Values model.Value [" ++
    String.intercalate ", " outputTypes ++ "]) : encode model (decode model arguments) = arguments := by\n  " ++
    String.join (outputNames.map fun name => "cases arguments with | cons " ++ name ++ " arguments => ") ++
    "cases arguments; rfl")
  command "theorem decode_encode (model : DomainModel) (result : Output model) : decode model (encode model result) = result := by cases result; rfl"
  let rawView := "(body.denote (Evaluation.meaningOn model SiteObservations.closed table) (" ++
    values inputNames ++ " : Values model.Value [" ++ String.intercalate ", " inputTypes ++
    "]).get).bind (fun result => .done (decode model result))"
  command ("noncomputable def run (model : DomainModel) " ++
    "(table : Evaluation.MeaningsOn model.toCarriers closedInterface) " ++ binders ++
    " : Closed (Output model) := helper_structure% body decoding decode in\n" ++
    rawView)
  command ("theorem run_eq (model : DomainModel) " ++
    "(table : Evaluation.MeaningsOn model.toCarriers closedInterface) " ++ binders ++ " :\n" ++
    rawView ++ " = run model table " ++ arguments ++ " :=\n" ++
    "helper_structure_equation% body decoding decode")
  command ("companion_goal SourceEquation in theorem equation (model : DomainModel) " ++
    "(table : Evaluation.MeaningsOn model.toCarriers closedInterface) " ++ binders ++ " :\n" ++
    "  body.denote (Evaluation.meaningOn model SiteObservations.closed table) (" ++ values inputNames ++
    " : Values model.Value [" ++ String.intercalate ", " inputTypes ++ "]).get = (run model table " ++ arguments ++ ").bind (fun result => .done (encode model result)) :=\n" ++
    "by\n  rw [← run_eq]\n  exact PIR.Process.restore_return (encode model) (decode model) (encode_decode model) _")
  let goalProposition :=
    "∀ (table : Evaluation.MeaningsOn model.toCarriers closedInterface) " ++ binders ++
    ", condition table " ++ arguments ++ " → run model table " ++ arguments ++
    " = primitiveOutcome (reference " ++ arguments ++ ")"
  command ("def Goal " ++ goalBinders ++ " : Prop :=\n  " ++ goalProposition)
  let encodedReference := "(encodeOutcome model (reference " ++ arguments ++ "))"
  let abi := "ReferenceLaw model [" ++ String.intercalate ", " inputTypes ++ "] [" ++
    String.intercalate ", " outputTypes ++ "]"
  let forallInputs := if inputNames.isEmpty then "" else "∀ " ++ binders ++ ", "
  command ("theorem of_law " ++ goalBinders ++ " (installed : " ++ abi ++ ") (same : installed.body = body)\n" ++
    "  (reference_eq : " ++ forallInputs ++ "installed.reference (" ++ values inputNames ++ ") = " ++ encodedReference ++ ")\n" ++
    "  (premises : ∀ table " ++ binders ++ ", condition table " ++ arguments ++
    " → installed.Requires table (" ++ values inputNames ++ ")) : Goal model reference condition := by\n" ++
    "  intro table " ++ arguments ++ " premise\n" ++
    "  rw [← run_eq]\n" ++
    "  rw [← same, installed.valid table _ (premises table " ++ arguments ++ " premise), reference_eq]\n" ++
    "  cases reference " ++ arguments ++ " <;> simp only [encodeOutcome, primitiveOutcome, PIR.Process.bind, decode_encode]")
  -- Goal is the author-facing name of this complete equation. The installer
  -- consumes the equation itself, so its generated equation lemmas introduce
  -- no new named hypothesis schema for each source helper. All conditions and
  -- arbitrary-table quantification remain in its kernel-checked proof input.
  command ("noncomputable def law " ++ goalBinders ++ " (proof : " ++ goalProposition ++ ") :\n" ++
    "  ReferenceLaw model [" ++ String.intercalate ", " inputTypes ++ "] [" ++
    String.intercalate ", " outputTypes ++ "] where\n" ++
    "  body := body\n" ++
    "  Requires table arguments := match arguments with | " ++ inputPattern ++
    " => condition table " ++ arguments ++ "\n" ++
    "  reference arguments := match arguments with | " ++ inputPattern ++
    " => " ++ encodedReference ++ "\n" ++
    "  valid table arguments premise := by\n    " ++ destruct ++
    "change _ = primitiveOutcome " ++ encodedReference ++ "; " ++
    "rw [equation, proof table " ++ arguments ++ " premise]; " ++
    "cases reference " ++ arguments ++ " <;> rfl")
  command ("end " ++ name.getId.toString)

/-- Failed generation restores declarations, local attributes and namespaces.
Resource and internal exceptions propagate, never become a missing-law result. -/
@[command_elab helperPresentation]
def elabHelperPresentation : CommandElab := fun stx =>
  ZkcTools.Generation.Commands.atomic "helper_presentation" (generate stx)

end
end ZkcTools.StructuredSource.HelperPresentation
