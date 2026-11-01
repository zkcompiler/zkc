module

public import Zkc.Source.Structured.Vocabulary
public import Zkc.Source.Component
public meta import ZkcTools.Generation.Commands
public meta import Lean.Elab.Command
public meta import Lean.Meta.Reduce

@[expose] public section

/-! Complete named views of retained typed rows and normal-form scopes. Labels decorate positions;
the supplied source row determines every field type and its order. Instantiate
the carrier with `Component model.Value` to retain all optional coordinates.
Visibility is a separate projection, whose preservation requires a proof.

The commands produce ordinary declarations checked by Lean. They neither
interpret a protocol nor select a mathematical meaning or companion.
-/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.NamedValues

public meta section
open Lean Meta Elab Command Term
open ZkcTools.Generation.Commands (termText)
open Zkc.Source Zkc.Source.Structured

partial def rowTypes (expression : Expr) : MetaM (List Expr) := do
  let expression ← whnf expression
  if expression.isAppOfArity ``List.nil 1 then return []
  unless expression.isAppOfArity ``List.cons 3 do
    throwError "named_values requires a statically known complete typed row"
  return expression.getAppArgs[1]! :: (← rowTypes expression.getAppArgs[2]!)

def printTerm (expression : Expr) : MetaM String :=
  withOptions (fun options => options.setBool `pp.fullNames true) do
    return (toString (← ppExpr expression)).replace "\n" " "

def command (source : String) : CommandElabM Unit := do
  let environment ← getEnv
  match Parser.runParserCategory environment `command source with
  | .error error => throwError "named_values generated invalid syntax: {error}\n{source}"
  | .ok stx =>
    let before := (← get).messages.toList.length
    elabCommand stx
    let errors := (← get).messages.toList.drop before |>.filter (·.severity == .error)
    unless errors.isEmpty do
      throwError "named_values declaration failed to check\n{MessageData.joinSep (errors.map (·.data)) m!"\n"}"

def labels (names : Array (TSyntax `ident)) : CommandElabM (List String) := do
  let result := names.toList.map (·.getId.toString)
  unless result.eraseDups.length == result.length do
    throwError "named_values requires distinct field labels"
  for name in result do
    if name.contains '.' || name == "Value" then
      throwError "named_values reserved or qualified field label: {name}"
  return result

def values (items : List String) : String :=
  items.foldr (fun item rest => "(.cons (" ++ item ++ ") " ++ rest ++ ")") ".nil"

def position (index : Nat) : String :=
  (List.replicate index ()).foldl (fun rest _ => "(.there " ++ rest ++ ")") ".here"

syntax (name := namedValues) "named_values " ident " [" ident,* "]" " := " term : command

def elaborateNamedValues : CommandElab := fun stx => do
  let `(named_values $name:ident [$items:ident,*] := $schema:term) := stx
    | throwUnsupportedSyntax
  let names ← labels items.getElems
  let (schemaText, indexType, types) ← liftTermElabM <| Term.withoutErrToSorry do
    let expression ← elabTerm schema none
    synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasFVar || expression.hasMVar then
      throwError "named_values requires a closed retained schema"
    let schemaType ← whnf (← inferType expression)
    unless schemaType.isAppOfArity ``List 1 do
      throwError "named_values requires an ordered list schema"
    let indexType := schemaType.getAppArgs[0]!
    unless ← isDefEq (← inferType indexType) (mkSort (.succ .zero)) do
      throwError "named_values schema indices must inhabit Type"
    return (← printTerm expression, ← printTerm indexType,
      ← (← rowTypes expression).mapM fun type => do printTerm (← reduce type))
  unless names.length == types.length do
    throwError "named_values field labels must cover every retained coordinate in order"
  command ("namespace " ++ name.getId.toString)
  command "set_option Elab.async false"
  command "open Zkc.Source Zkc.Source.Structured"
  command ("abbrev types : List (" ++ indexType ++ ") := [" ++ String.intercalate ", " types ++ "]")
  command ("theorem schema_eq : " ++ schemaText ++ " = types := rfl")
  command ("structure View (Value : " ++ indexType ++ " → Type) where\n" ++
    String.join (names.zip types |>.map fun (name, type) => "  " ++ name ++ " : Value (" ++ type ++ ")\n"))
  command ("@[reducible] def pack {Value : " ++ indexType ++ " → Type} (view : View Value) : Values Value types := " ++
    values (names.map ("view." ++ ·)))
  command ("@[reducible] def unpack {Value : " ++ indexType ++ " → Type} (row : Values Value types) : View Value := { " ++
    String.intercalate ", " (names.zipIdx |>.map fun (name, index) => name ++ " := row.get " ++ position index) ++ " }")
  command ("theorem pack_unpack {Value : " ++ indexType ++ " → Type} (row : Values Value types) : pack (unpack row) = row := by\n  " ++
    String.join (names.map fun name => "cases row with | cons " ++ name ++ " row => ") ++ "cases row; rfl")
  command ("theorem unpack_pack {Value : " ++ indexType ++ " → Type} (view : View Value) : unpack (pack view) = view := by cases view; rfl")
  command ("theorem pack_surjective {Value : " ++ indexType ++ " → Type} (row : Values Value types) : ∃ view, row = pack view := ⟨unpack row, (pack_unpack row).symm⟩")
  command ("def map {Value Other : " ++ indexType ++ " → Type} (transform : ∀ ty, Value ty → Other ty) (view : View Value) : View Other := { " ++
    String.intercalate ", " (names.zip types |>.map fun (name, type) => name ++ " := transform (" ++ type ++ ") view." ++ name) ++ " }")
  command ("def project {Value : " ++ indexType ++ " → Type} (transform : Values Value types → Values Value types) (view : View Value) : View Value := unpack (transform (pack view))")
  command ("theorem pack_project {Value : " ++ indexType ++ " → Type} (transform : Values Value types → Values Value types) (view : View Value) : pack (project transform view) = transform (pack view) := pack_unpack _")
  command ("theorem project_eq_self {Value : " ++ indexType ++ " → Type} (transform : Values Value types → Values Value types) (view : View Value) (preserves : transform (pack view) = pack view) : project transform view = view := by unfold project; rw [preserves, unpack_pack]")
  command ("end " ++ name.getId.toString)

/-- A typed projection between named records. Source and target rows remain
independently fixed; projection is not advertised as a complete raw inverse. -/
syntax (name := namedValuesProjection) "named_values_projection " ident
  " (" ident " : " term ")" " := " ident term " => " ident term
  " with " "[" ident,* "]" : command

def elaborateProjection : CommandElab := fun stx => do
  let `(named_values_projection $name:ident ($parameter:ident : $parameterType:term) :=
      $source:ident $sourceCarrier:term => $target:ident $targetCarrier:term with [$items:ident,*]) := stx
    | throwUnsupportedSyntax
  let names ← labels items.getElems
  let parameterBinder := "(" ++ parameter.getId.toString ++ " : " ++ (← termText parameterType.raw) ++ ")"
  let sourceType := source.getId.toString ++ ".View (" ++ (← termText sourceCarrier.raw) ++ ")"
  let targetType := target.getId.toString ++ ".View (" ++ (← termText targetCarrier.raw) ++ ")"
  command ("def " ++ name.getId.toString ++ " " ++ parameterBinder ++ " (view : " ++ sourceType ++ ") : " ++ targetType ++ " := { " ++
    String.intercalate ", " (names.map fun name => name ++ " := view." ++ name) ++ " }")

/-- A record correspondence uses field labels only to construct projections.
Both inverse theorems check the complete correspondence, including additional
record fields supplied explicitly to readback. An omitted or changed field
cannot acquire an inverse theorem merely by having the same carrier type. -/
syntax (name := namedValuesBridge) "named_values_bridge " ident
  " (" ident " : " term ")" " : " term " := " ident term
  " with " "[" ident,* "]" bracketedBinder* : command

def elaborateBridge : CommandElab := fun stx => do
  let `(named_values_bridge $name:ident ($parameter:ident : $parameterType:term) : $recordType:term :=
      $view:ident $carrier:term with [$items:ident,*] $extraBinders:bracketedBinder*) := stx
    | throwUnsupportedSyntax
  let names ← labels items.getElems
  let mut extraNames : Array (TSyntax `ident) := #[]
  let mut extraTypes : List (TSyntax `term) := []
  for binder in extraBinders do
    let `(bracketedBinder| ($name:ident : $type:term)) := binder | throwError "named_values_bridge expects named typed extra fields"
    extraNames := extraNames.push name
    extraTypes := extraTypes ++ [type]
  let additional ← labels extraNames
  let parameter := parameter.getId.toString
  let parameterType := (← termText parameterType.raw)
  let recordType := (← termText recordType.raw)
  let carrier := (← termText carrier.raw)
  let view := view.getId.toString
  let parameterBinder := "(" ++ parameter ++ " : " ++ parameterType ++ ")"
  let extraBinders := String.intercalate " " (← (additional.zip extraTypes).mapM fun (name, type) => do
    pure ("(" ++ name ++ " : " ++ (← termText type.raw) ++ ")"))
  let extraArguments := String.intercalate " " additional
  let read := "fromView " ++ parameter ++ " view " ++ extraArguments
  command ("namespace " ++ name.getId.toString)
  command "set_option Elab.async false"
  command ("def toView " ++ parameterBinder ++ " (record : " ++ recordType ++ ") : " ++ view ++ ".View (" ++ carrier ++ ") := { " ++
    String.intercalate ", " (names.map fun name => name ++ " := record." ++ name) ++ " }")
  command ("def fromView " ++ parameterBinder ++ " (view : " ++ view ++ ".View (" ++ carrier ++ ")) " ++ extraBinders ++ " : " ++ recordType ++ " := { " ++
    String.intercalate ", " ((names.map fun name => name ++ " := view." ++ name) ++ (additional.map fun name => name ++ " := " ++ name)) ++ " }")
  command ("theorem toView_fromView " ++ parameterBinder ++ " (view : " ++ view ++ ".View (" ++ carrier ++ ")) " ++ extraBinders ++
    " : toView " ++ parameter ++ " (" ++ read ++ ") = view := by cases view; rfl")
  command ("theorem fromView_toView " ++ parameterBinder ++ " (record : " ++ recordType ++ ") : fromView " ++ parameter ++ " (toView " ++ parameter ++ " record) " ++
    String.intercalate " " (additional.map ("record." ++ ·)) ++ " = record := by cases record; rfl")
  command ("end " ++ name.getId.toString)

@[command_elab namedValues] def elaborateNamedValuesAtomic : CommandElab := fun stx =>
  ZkcTools.Generation.Commands.atomic "namedValues" (elaborateNamedValues stx)

@[command_elab namedValuesProjection] def elaborateProjectionAtomic : CommandElab := fun stx =>
  ZkcTools.Generation.Commands.atomic "namedValuesProjection" (elaborateProjection stx)

@[command_elab namedValuesBridge] def elaborateBridgeAtomic : CommandElab := fun stx =>
  ZkcTools.Generation.Commands.atomic "namedValuesBridge" (elaborateBridge stx)

end
end ZkcTools.StructuredSource.NamedValues
