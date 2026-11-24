module

public import Zkc.Frontend.Static.Types

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Static

/-- The request for a row at the static values of the function or member. -/
def rowRequest (name : String) (values : Array StaticValue) : CompileM Typing.RowRequest := do
  let statics ← values.mapM fun
    | .natural n => pure (Typing.RowStatic.nat n)
    | .type t => pure (.type t)
    | .«module» _ => throw (.waiting "a row at a module argument")
  return ⟨name, statics⟩

/-- Resolve a primitive binding against the independently instantiated source signature.
A project supplies the implementation of a name outside the vocabulary. -/
def checkedRow (request : Typing.RowRequest) (inputs : Array ClosedType) (result : ClosedType)
    (place : Syntax.Span) (member : Option String := none) : CompileM Typing.Row := do
  let rule := if member.isSome then "SP8" else "NL9"
  if let some row := Typing.rowOf? request then
    unless row.inputs.size == inputs.size && (row.inputs.zip inputs).all (fun (a, b) => typeEq a b) &&
        row.outputs.size == 1 && row.outputs.all (typeEq · result) do
      let state ← get
      let render (ts : Array ClosedType) := ", ".intercalate (ts.map (renderType state)).toList
      let subject := member.elim "the signature written" (fun name => s!"the signature of `{name}`")
      refuse rule place s!"{subject} is not that of the row `{request.name}` at this instance: the row takes ({render row.inputs}) and gives ({render row.outputs})"
    return row
  if Typing.reservedRow request.name then
    let message := s!"`{request.name}` is a row of the vocabulary, and the vocabulary has no row of that name at the static arguments of this instance"
    match member with
    | some name => refuse rule place s!"the binding of `{name}`: {message}"
    | none => refuse rule place (message ++ s!"; write them: `primitive(\"{request.name}\", …)`")
  return { key := request.key, kind := .pure, inputs, outputs := #[result] }

end Zkc.Frontend.Static
