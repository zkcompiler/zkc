module

public import Zkc.Frontend.Static.Evaluate

@[expose] public section
namespace Zkc.Frontend.Static

/-- Pair each proof argument exactly once. Shared parameters are identified by declaration
scope, so shadowing in a different declaration cannot capture them. -/
def specificationClosure (env : Env) (target : Declaration)
    (supplied : Array (Syntax.Span × String × Lowered.Expr)) (shared : Array ScopeId)
    (place : Syntax.Span) : CompileM (Option SpecificationClosure) := do
  let parameters := specificationParameters (← program) target
  let mut written : Std.HashMap ParameterRef Lowered.Expr := {}
  for (span, name, term) in supplied do
    let some (ref, _) := parameters.find? (·.2.name.text == name)
      | refuse "SP11" span s!"unknown specification-only parameter `{name}`"
    if written.contains ref || shared.contains ref.scope then
      refuse "SP11" span s!"specification-only parameter `{name}` is already bound"
    written := written.insert ref term
  if parameters.isEmpty then return none
  let arguments ← parameters.mapM fun (ref, parameter) => do
    let term := written[ref]?
    unless term.isSome || shared.contains ref.scope do
      refuse "SP11" place s!"missing specification-only argument `{parameter.name.text}`"
    return (ref, term)
  return some ⟨env, arguments⟩

/-- A caller with an open proof parameter defers the affected application until a goal
supplies its value. A fully closed application checks its constraints during elaboration. -/
def SpecificationClosure.isClosed (closure : SpecificationClosure) : CompileM Bool :=
  closure.arguments.allM fun (ref, term) => do
    match term with
    | none => return closure.lexical.values.contains ref
    | some expr => return !(← mentionsSpecParameter expr)

/-- Evaluate in the caller, then check the callee's specification conjuncts at the result.
The values stay outside the deployed instance table. -/
def SpecificationClosure.close (closure : SpecificationClosure) (callee : InstanceId)
    (parent : StaticEnvironment) (place : Syntax.Span) : CompileM (Array Nat) := do
  let combined := parent.fold (init := closure.lexical.values) fun values ref value =>
    values.insert ref value
  let env := { closure.lexical with values := combined }
  let values ← closure.arguments.mapM fun (ref, term) => do
    if let some expr := term then return ← evalSize env expr
    let some (.natural n) := env.values[ref]? | refuse "SP11" place "unbound shared parameter"
    return n
  let state ← get
  let some entry := state.table.entries[callee]? | throw .abandoned
  let target ← declaration entry.key.declaration
  let closed := instanceEnv state.program target entry.key.arguments values
  checkWheres closed target (state.program.nameOf entry.key.declaration) false (fun _ => pure false)
    (specification := true)
  return values

/-- Checking an already closed proof argument can itself instantiate source declarations.
Keep those instances out of the numbering of deployed definitions. An index of a uniform
loop needs an occurrence-specific value and cannot force the loop to be stepped. -/
def SpecificationClosure.checkApplication (closure : SpecificationClosure) (callee : InstanceId)
    (place : Syntax.Span) : CompileM Unit := do
  unless ← closure.isClosed do return
  let (result, after) := (closure.close callee {} place).run (← read) (← get)
  match result with
  | .ok _ | .error (.staticIndex _) => pure ()
  | .error failure =>
    modify fun s => {s with log := after.log}
    throw failure

end Zkc.Frontend.Static
