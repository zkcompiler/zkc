import Tools.Interactive.GenericSource

/-! Immutable partial configurations. Known consequences are checked without
turning inferred equalities into implicit assignments of missing parameters. -/

set_option autoImplicit false

namespace Tools.Interactive.Generic
open Lean (Json)
open Zkc.Source.Requirements

structure ConfigurationDeclaration where
  name : Name
  base : Name
  arguments : List (Name × String)
  implementations : List (Name × String)
  deriving Repr

structure Configuration where
  name : Name
  definition : Name
  arguments : List (Name × String)
  implementations : List (Name × String)
  deriving Repr

def decodeConfiguration (json : Json) : Result ConfigurationDeclaration := do
  let [.str "configure", name, base, arguments, implementations] ← Decode.array json
    | throw "generic-configuration"
  return ⟨← Decode.name name, ← Decode.name base,
    ← Decode.pairs (fun j => Decode.name j) Decode.string arguments,
    ← Decode.pairs (fun j => Decode.name j) Decode.string implementations⟩

def termIdentity (arguments : List (Name × String)) : Term → Result String
  | .root name => lookup name arguments
  | .project base member => do Bindings.associatedIdentity (← termIdentity arguments base) member
  | .apply _ _ => throw "generic-application"

def specializeType (arguments : List (Name × String)) (ty : ValueType) : Result Bindings.ValueType := do
  let identity ← match ty.domain with
    | none => pure ""
    | some term => termIdentity arguments term
  let result := Bindings.ValueType.mk ty.kind identity ""
  ensure (result.valid false) "generic-specialized-type"
  return result

private def knownIdentity (known : List (Term × String)) : Term → Option String
  | .root name => (known.find? fun p => decide (p.1 = .root name)).map Prod.snd
  | .project base member =>
      match known.find? (fun p => decide (p.1 = .project base member)) with
      | some p => some p.2
      | none => do (Bindings.associatedIdentity (← knownIdentity known base) member).toOption
  | .apply _ _ => none

private def addKnown (known : List (Term × String)) (term : Term) (value : String) : Result (List (Term × String)) := do
  if let some existing := knownIdentity known term then
    ensure (existing == value) "binding-requirement"
    return known
  return (term, value) :: known


def consistent (checked : CheckedDefinition) (arguments : List (Name × String)) : Result Unit := do
  ensure (unique (arguments.map Prod.fst)) "generic-configuration-rebinding"
  for (name, identity) in arguments do
    let sort ← lookup name checked.definition.parameters
    ensure (sort.accepts identity) "generic-configuration-sort"
  let mut known : List (Term × String) := arguments.map fun (name, value) => (.root name, value)
  let facts := checked.closure.facts.toList.map Subtype.val
  for _ in [:129] do
    let before := known.length
    for p in facts do
      if let .equal a b := p then
        match knownIdentity known a, knownIdentity known b with
        | some x, some y => ensure (x == y) "binding-requirement"
        | some x, none => known ← addKnown known b x
        | none, some y => known ← addKnown known a y
        | none, none => pure ()
    -- An associated identity inferred before its root was fixed must agree
    -- with that root once it becomes known.
    for (term, value) in known do
      if let .project base member := term then
        if let some root := knownIdentity known base then
          ensure ((← Bindings.associatedIdentity root member) == value) "binding-requirement"
    if known.length == before then break
  for p in facts do
    if let .relation name terms := p then
      let arguments := terms.map (knownIdentity known)
      if arguments.all Option.isSome then
        ensure (← closedRelation name (arguments.filterMap id)) "binding-requirement"

def resolveConfiguration (definitions : List CheckedDefinition)
    (declarations : List ConfigurationDeclaration) : Nat → List Name → Name → Result Configuration
  | 0, _, _ => .error "generic-configuration-depth"
  | depth + 1, active, name => do
    ensure (!(active.contains name)) "generic-configuration-cycle"
    let declaration ← lookup name (declarations.map fun d => (d.name, d))
    let inherited ← match definitions.find? (fun d => d.definition.name == declaration.base) with
      | some definition => pure (Configuration.mk name definition.definition.name [] [])
      | none => resolveConfiguration definitions declarations depth (name :: active) declaration.base
    let definition ← lookup inherited.definition (definitions.map fun d => (d.definition.name, d))
    let extend := fun (current extra : List (Name × String)) => do
      ensure (unique (extra.map Prod.fst) && extra.all (fun p => !(current.any fun q => p.1 == q.1)))
        "generic-configuration-rebinding"
      return current ++ extra
    let arguments ← extend inherited.arguments declaration.arguments
    let implementations ← extend inherited.implementations declaration.implementations
    for (site, implementation) in implementations do
      let op ← lookup site (definition.definition.operations.map fun op => (op.site, op))
      ensure (!op.application && Bindings.implementationName op.contract implementation)
        "binding-implementation"
    consistent definition arguments
    return ⟨name, inherited.definition, arguments, implementations⟩

structure Library where
  definitions : List CheckedDefinition
  configurations : List Configuration
  common : Json


def Library.definition (library : Library) (name : Name) : Result CheckedDefinition :=
  lookup name (library.definitions.map fun d => (d.definition.name, d))

def Library.configuration (library : Library) (name : Name) : Result Configuration :=
  lookup name (library.configurations.map fun c => (c.name, c))

def Configuration.closedArguments (configuration : Configuration) (definition : Definition) : Result (List (Name × String)) := do
  definition.parameters.mapM fun (name, _) => do
    let some value := configuration.arguments.lookup name | throw "generic-open-instance"
    return (name, value)

/-- A call supplies the residual parameters in the base declaration's order. -/
def applicationArguments (definition : Definition) (fixed : List (Name × String))
    (parameters : Parameters) (actual : List Term) : Result (List (Name × Term)) := do
  let remaining := definition.parameters.filter fun p => !(fixed.any fun q => q.1 == p.1)
  ensure (remaining.length == actual.length) "generic-static-arity"
  for (parameter, term) in remaining.zip actual do
    ensure ((← termSort parameters term) == parameter.2) "generic-static-sort"
  return fixed.map (fun (name, identity) => (name, .root ("$" ++ identity))) ++
    (remaining.map Prod.fst).zip actual

def substituteTerm (arguments : List (Name × Term)) : Term → Result Term
  | .root name => lookup name arguments
  | .project parent member => return .project (← substituteTerm arguments parent) member
  | .apply _ _ => throw "generic-application"

def applicationSignature (definition : Definition) (arguments : List (Name × Term)) : Result Signature := do
  let ty := fun (value : ValueType) => do
    return { value with domain := ← value.domain.mapM (substituteTerm arguments) }
  let needs ← definition.requirements.mapM fun p => do
    match p with
    | .equal a b => return .equal (← substituteTerm arguments a) (← substituteTerm arguments b)
    | .relation name args => return .relation name (← args.mapM (substituteTerm arguments))
  return ⟨← definition.arguments.mapM (fun p => ty p.2), ← definition.results.mapM ty, needs⟩

def applicationTarget (definitions : List Definition) (configurations : List Configuration)
    (name : Name) : Result (Definition × Configuration) := do
  if let some definition := definitions.find? (fun d => d.name == name) then
    return (definition, ⟨"", name, [], []⟩)
  let selected ← lookup name (configurations.map fun c => (c.name, c))
  let definition ← lookup selected.definition (definitions.map fun d => (d.name, d))
  return (definition, selected)

private def callHeight (definitions : List Definition) (configurations : List Configuration) :
    Nat → List Name → Definition → StateT (List (Name × Nat)) Result Nat
  | 0, _, _ => throw "algorithm-call-depth"
  | fuel + 1, active, definition => do
      ensure (!(active.contains definition.name)) "algorithm-call-cycle"
      if let some height := (← get).lookup definition.name then
        ensure (active.length + height ≤ 65) "algorithm-call-depth"
        return height
      let mut height := 1
      for op in definition.operations do
        if op.application then
          let (callee, _) ← applicationTarget definitions configurations op.contract
          let child ← callHeight definitions configurations fuel (definition.name :: active) callee
          height := max height (child + 1)
      ensure (active.length + height ≤ 65) "algorithm-call-depth"
      modify fun known => (definition.name, height) :: known
      return height

def library (json : Json) : Result Library := do
  let [.str "zkc.library/1", declarations, configurations, common] ← Decode.array json
    | throw "generic-library"
  let definitions ← (← Decode.array declarations limits.definitions).mapM decodeDefinition
  let configurations ← (← Decode.array configurations limits.definitions).mapM decodeConfiguration
  let names := definitions.map Definition.name ++ configurations.map ConfigurationDeclaration.name
  ensure (unique names && names.all (fun n => !(n.contains '.'))) "generic-duplicate-name"
  -- Provisional records check configurations against public signatures only;
  -- every body is checked below before any record escapes formation.
  let signatures ← definitions.mapM fun d => do
    return CheckedDefinition.mk d [] (← Requirements.close d.requirements [])
  let configurations ← configurations.mapM fun c => resolveConfiguration signatures configurations 64 [] c.name
  let _ ← (definitions.mapM (callHeight definitions configurations 65 [])).run []
  let checked ← definitions.mapM fun definition =>
    checkDefinition definition fun op => do
      let (callee, configuration) ← applicationTarget definitions configurations op.contract
      applicationSignature callee (← applicationArguments callee configuration.arguments definition.parameters op.arguments)
  return ⟨checked, configurations, common⟩

end Tools.Interactive.Generic
