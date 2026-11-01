module

public meta import Lean.Elab.Declaration
public meta import Lean.Linter.UnusedVariables

public meta section

/-! Generate an obligation from a declaration's explicit signature before its
proof is elaborated. This command supplies a type, never a proof or assumption.
It is deliberately limited to single theorems and definitions. -/
namespace ZkcTools.Companions
open Lean Meta Elab Command Term

syntax (name := companionGoal) "companion_goal " ident " in " command : command
syntax (name := companionTheoremGoal) "companion_goal " ident " for " "theorem "
  declId declSig : command
syntax (name := companionDefinitionGoal) "companion_goal " ident " for " "def "
  declId optDeclSig : command

-- Header premises intentionally have no proof body in which to be used.
@[unused_variables_ignore_fn]
def ignoreGoalHeaderPremises : Lean.Linter.IgnoreFunction := fun _ stack _ =>
  stack.any fun (node, _) => node.isOfKind ``companionTheoremGoal ||
    node.isOfKind ``companionDefinitionGoal

private def addGoal (goal command : Syntax) : CommandElabM Unit := do
  unless command.isOfKind ``Parser.Command.declaration do
    throwError "companion_goal requires a theorem or definition with an explicit type"
  let declaration := command[1]
  let kind := declaration.getKind
  unless kind == ``Parser.Command.theorem || kind == ``Parser.Command.definition do
    throwError "companion_goal requires a single theorem or definition"
  let (binders, type?) := if kind == ``Parser.Command.theorem then
      let (binders, type) := expandDeclSig declaration[2]
      (binders, some type)
    else expandOptDeclSig declaration[2]
  let some typeSyntax := type?
    | throwError "companion_goal requires an explicit independently fixed type"
  let modifiers ← elabModifiers ⟨command[0]⟩
  let scope ← getScope
  runTermElabM fun variables => do
    let scopeLevels ← getLevelNames
    let sectionVariables := (← read).sectionFVars
    let included := sectionVariables.foldl (fun ids uid expression =>
      if scope.includedVars.contains uid then ids.push expression.fvarId! else ids) #[]
    let omitted := sectionVariables.foldl (fun ids uid expression =>
      if scope.omittedVars.contains uid then ids.push expression.fvarId! else ids) #[]
    let ⟨_, _, levels, _⟩ ← Term.expandDeclId (← getCurrNamespace) scopeLevels declaration[1] modifiers
    withLevelNames levels <| elabBinders binders.getArgs fun parameters => do
      let expected ← elabType typeSyntax
      synthesizeSyntheticMVarsNoPostponing
      let closed ← mkForallFVars parameters (← instantiateMVars expected)
      -- Match Lean's header-based section-variable selection, including
      -- explicitly included premises and instances over selected variables.
      let (_, used) ← (do
        closed.collectFVars
        for localVariable in variables do
          if included.contains localVariable.fvarId! then
            modify fun state => state.add localVariable.fvarId!
        get >>= (·.addDependencies) >>= set
        for localVariable in variables do
          let localDeclaration ← getFVarLocalDecl localVariable
          if omitted.contains localVariable.fvarId! then continue
          let dependencies := (← localDeclaration.type.collectFVars.run {}).2.fvarIds
          let state ← get
          if localDeclaration.binderInfo.isInstImplicit &&
              dependencies.all state.fvarSet.contains then
            modify fun state => state.add localVariable.fvarId!
        : StateRefT CollectFVars.State MetaM Unit).run {}
      let selected := if kind == ``Parser.Command.theorem then
          variables.filter fun localVariable => used.fvarSet.contains localVariable.fvarId!
        else variables
      let closed ← mkForallFVars selected closed
      let closed ← levelMVarToParam closed
      if closed.hasFVar || closed.hasMVar then
        throwError "companion_goal requires a closed type without metavariables"
      let levelParams := (collectLevelParams {} closed).params.toList
      let name := (← getCurrNamespace) ++ goal.getId
      -- Goal values must be exposed across module boundaries: exporting this
      -- type alias as an opaque declaration would hide the fixed proposition.
      withOptions (Elab.async.set · false) <| addDecl (.defnDecl {
        name, levelParams, type := ← inferType closed, value := closed,
        hints := .abbrev, safety := .safe }) (forceExpose := true)

@[command_elab companionGoal]
def elabCompanionGoal : CommandElab := fun stx => do
  addGoal stx[1] stx[3]
  elabCommand stx[3]

/-- Header-only mode generates the same closed goal without declaring or
elaborating a consumer. The dummy body is syntax only and is never elaborated. -/
elab_rules : command
  | `(companion_goal $goal:ident for theorem $name:declId $signature:declSig) => do
      addGoal goal (← `(theorem $name:declId $signature:declSig := by trivial))
  | `(companion_goal $goal:ident for def $name:declId $signature:optDeclSig) => do
      addGoal goal (← `(def $name:declId $signature:optDeclSig := by trivial))

/-- Print an ordinary declaration header from an independently checked goal.
The output expands the alias so the consumer keeps its original declaration
type. It is generated source, to be elaborated and kernel checked again. -/
def goalHeader (goal declaration : Name) (isTheorem : Bool) : MetaM String := do
  let info ← getConstInfo goal
  let some expected := info.value? | throwError "companion goal must be a type definition: {goal}"
  unless !expected.hasFVar && !expected.hasLooseBVars && !expected.hasMVar do
    throwError "companion header requires a fixed closed type: {goal}"
  let type ← withOptions (fun options => options
      |>.setBool `pp.fullNames true |>.setBool `pp.universes true
      |>.setBool `pp.explicit true |>.setBool `pp.notation false
      |>.setBool `pp.piBinderNames true |>.setBool `pp.piBinderNames.hygienic true
      |>.setBool `pp.proofs true) do
    return toString (← ppExpr expected)
  let levels := if info.levelParams.isEmpty then "" else
    ".{" ++ String.intercalate ", " (info.levelParams.map Name.toString) ++ "}"
  return (if isTheorem then "theorem " else "noncomputable def ") ++
    "_root_." ++ declaration.toString ++ levels ++ " :\n    " ++
    type.replace "\n" "\n    " ++ " :=\n"

end ZkcTools.Companions
