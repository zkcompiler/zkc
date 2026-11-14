module

public import Zkc.Frontend.Environment.Module
public import Zkc.Frontend.Environment.Results

@[expose] public section

set_option autoImplicit false

/-!
# The environment

Two stores, threaded through every phase as one persistent value. The store of files holds what
does not depend on an instance and is indexed by file. The store of results holds what was
computed from static values and is keyed by what was asked. A phase reads both and adds to one
of them: loading, assembly and lowering to the first, everything from instantiation on to the
second.
-/

namespace Zkc.Frontend

structure Environment where
  modules : ModuleStore := {}
  results : ResultStore := {}
  deriving Inhabited

namespace Environment

def program (environment : Environment) : Program := environment.modules.program

mutual
  /-- A static value as source writes it. -/
  partial def valueText (environment : Environment) : StaticValue → String
    | .type type => typeText environment type
    | .natural value => toString value
    | .module id => instanceText environment id

  /-- An instance as source writes it: `name<values>`, positionally. -/
  partial def instanceText (environment : Environment) (id : InstanceId) : String :=
    match environment.results.key? id with
    | some key =>
      let name := environment.program.nameOf key.declaration
      let base :=
        if key.arguments.isEmpty then name
        else s!"{name}<{", ".intercalate (key.arguments.toList.map (valueText environment))}>"
      match key.owner with
      | some owner => s!"{base} at {instanceText environment owner}"
      | none => base
    | none => s!"instance#{id}"

  /-- A closed type as a message writes it. -/
  partial def typeText (environment : Environment) : ClosedType → String
    | .bool => "bool"
    | .nat => "nat"
    | .rational => "rational"
    | .index bound => s!"index<{bound}>"
    | .nonzero field => s!"nonzero<{typeText environment field}>"
    | .seq element (some size) => s!"[{typeText environment element}; {size}]"
    | .seq element none => s!"[{typeText environment element}]"
    | .tuple components names =>
      let parts := (components.zip names).map fun (component, name) =>
        match name with
        | some name => s!"{name}: {typeText environment component}"
        | none => typeText environment component
      s!"({", ".intercalate parts.toList})"
    | .nominal row arguments =>
      if arguments.isEmpty then row
      else s!"{row}<{", ".intercalate (arguments.toList.map (valueText environment))}>"
    | .record id | .variant id | .specification id => instanceText environment id
    | .opaque «module» member arguments _ =>
      let base := s!"{instanceText environment «module»}::{member}"
      if arguments.isEmpty then base
      else s!"{base}<{", ".intercalate (arguments.toList.map (valueText environment))}>"
end

/-- A declaration at values, as a chain line writes it: `name<parameter = value, …>`. -/
def instantiationText (environment : Environment) (declaration : DeclarationId)
    (arguments : Array StaticValue) : String :=
  let program := environment.program
  let name := program.nameOf declaration
  match program.declarations[declaration]? with
  | some found =>
    let parameters := (program.parameters found).filter fun (_, parameter) => !parameter.spec
    let parts := (parameters.zip arguments).map fun ((_, parameter), value) =>
      s!"{parameter.name.text} = {valueText environment value}"
    if parts.isEmpty then name else s!"{name}<{", ".intercalate parts.toList}>"
  | none => name

/-- The renderer of messages that knows the names of this program. -/
def renderer (environment : Environment) : Renderer where
  type := typeText environment
  value := valueText environment
  «instance» := instanceText environment
  instantiation := instantiationText environment
  declaration := environment.program.nameOf

end Environment

end Zkc.Frontend
