module

public import Zkc.Frontend.Semantics.Instantiate.Roots

@[expose] public section

set_option autoImplicit false

/-!
# The check of instances

After the check of names: the checks of declarations, the roots and their instances, the
instances that comments ask for, and the default instances of public declarations that no root
reaches (SP7), as the phase of instances (`instantiateProgram`), in the bottom layer; the typing
of bodies continues in the same monad from the state it leaves.
-/

namespace Zkc.Frontend

open Instances
open Static

namespace Instances

/-- The indexes of a program whose names resolve: the sorts of `zkc::algebra`, the declarations of
every namespace in the order of the text, the names the program gives the rows of the
vocabulary, the owners of scopes, and the implementers of each interface. -/
def indexesOf (modules : ModuleStore) : ProgramIndexes := Id.run do
  let program := modules.program
  let mut sortNames : Std.HashMap DeclarationId String := {}
  if let some algebra := program.modules["zkc::algebra"]? then
    if let some inner := (program.declarations[algebra]?).bind (·.inner) then
      for name in #["Group", "Ring", "PrimeOrderGroup", "Field", "PrimeField", "ExtensionField",
          "TwoAdicField"] do
        if let some (.declaration id) := (program.namespaces[inner]?).bind (·.names[name]?) then
          sortNames := sortNames.insert id name
  let mut members : Std.HashMap NamespaceId (Array DeclarationId) := {}
  let mut rowNames : Std.HashMap String String := {}
  let mut scopeOwners : Std.HashMap ScopeId DeclarationId := {}
  let mut implementers : Std.HashMap DeclarationId (Array DeclarationId) := {}
  for index in [0:program.declarations.size] do
    let declaration := program.declarations[index]!
    members := members.insert declaration.namespace
      ((members.getD declaration.namespace #[]).push index)
    if let some scope := declaration.ownScope then scopeOwners := scopeOwners.insert scope index
    if let .typeDecl (.type _ _ name _ (.primitive primitive)) := declaration.node then
      unless rowNames.contains primitive.row.content do
        rowNames := rowNames.insert primitive.row.content name.text
    if let some bound := Names.implementing? declaration then
      for sort in bound.sorts do
        if let .path path := sort then
          if let some resolution := modules.resolution? declaration.file path then
            if let some { step := .declaration interface, .. } := resolution.segments.back? then
              implementers := implementers.insert interface
                ((implementers.getD interface #[]).push index)
  return { sortNames, members, rowNames, scopeOwners, implementers }

/-- A state of the bottom layer with the indexes of its program. -/
def withIndexes (state : Compile.State) : Compile.State :=
  { state with env := { state.env with modules :=
    { state.env.modules with indexes := indexesOf state.env.modules } } }

/-- The phase of instances: the indexes of the program, then the checks of declarations, the
roots and the instances that comments ask for. The default instances are formed after the
bodies are typed (`defaultProgram`). -/
def instantiateProgram : CompileM Unit := do
  modifyModules fun modules => { modules with indexes := indexesOf modules }
  checkProgram (← getModules).instantiations

end Instances

namespace Instances

/-- An instance's content as text: `= T` for a type or a natural, `{a: T, …}` for a record,
`A(T) | B` for a variant, `(x: T, …) -> R` for a signature, the interfaces and members of a
module. A type that is not evaluated here is `?`. -/
def renderContent (state : Compile.State) : InstanceContent → String
  | .alias type | .vocabularyType type => s!"= {renderType state type}"
  | .record linear fields =>
    let body := ", ".intercalate (fields.toList.map fun (name, type) => s!"{name}: {renderType state type}")
    s!"{if linear then "linear " else ""}\{{body}}"
  | .«variant» alternatives =>
    " | ".intercalate (alternatives.toList.map fun (name, payload) =>
      if payload.isEmpty then name
      else s!"{name}({", ".intercalate (payload.toList.map (renderType state))})")
  | .staticName value => s!"= {value}"
  | .signature parameters result =>
    let typed (entry : String × Option ClosedType) : String :=
      s!"{entry.1}: {(entry.2.map (renderType state)).getD "?"}"
    s!"({", ".intercalate (parameters.toList.map typed)}) -> {(result.map (renderType state)).getD "?"}"
  | .protocol ports results =>
    let typed (entry : String × Option ClosedType) : String :=
      s!"{entry.1}: {(entry.2.map (renderType state)).getD "?"}"
    s!"({", ".intercalate (ports.toList.map typed)}) -> ({", ".intercalate (results.toList.map typed)})"
  | .«module» interfaces members =>
    let named := interfaces.toList.map fun (id, args) =>
      let name := state.program.nameOf id
      if args.isEmpty then name else s!"{name}<{", ".intercalate (args.toList.map (renderValue state))}>"
    let member (entry : String × MemberValue) : String :=
      match entry.2 with
      | .type type => s!"{entry.1} = {renderType state type}"
      | .natural value => s!"{entry.1} = {value}"
      | .«module» id => s!"{entry.1} = {renderInstance state id}"
      | .definition _ => s!"{entry.1} defined"
      | .row row => s!"{entry.1} = row {row}"
      | .opaqueType _ => s!"{entry.1} opaque"
    s!"{" + ".intercalate named}: {", ".intercalate (members.toList.map member)}"
  | .unevaluated => "not evaluated"
  | .waits reason => s!"waits for {reason}"

end Instances

/-- What a summary calls the instances of a kind of declaration. -/
def kindLabel : DeclarationKind → String
  | .alias => "aliases"
  | .vocabularyType => "types of the vocabulary"
  | .specType => "specification types"
  | .record => "records"
  | .«variant» => "variants"
  | .function => "functions"
  | .oracleFunction => "oracle functions"
  | .protocol => "protocols"
  | .relation => "relations"
  | .staticName => "naturals"
  | .«module» => "modules"
  | .law => "laws"
  | _ => "others"

/-- The number of instances formed, by the kind of their declaration. -/
def countsByKind (state : Compile.State) : Array (String × Nat) := Id.run do
  let program := state.program
  let mut counts : Array (String × Nat) := #[]
  for entry in state.table.entries do
    let some declaration := program.declarations[entry.key.declaration]? | continue
    let kind := kindLabel declaration.kind
    match counts.findIdx? (·.1 == kind) with
    | some index => counts := counts.modify index fun (name, count) => (name, count + 1)
    | none => counts := counts.push (kind, 1)
  return counts

end Zkc.Frontend
