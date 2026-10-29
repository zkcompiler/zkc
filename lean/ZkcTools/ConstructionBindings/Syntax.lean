module

public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Closure
public meta import Lean.Compiler.NoncomputableAttr
public import Zkc.Construction.ConnectionCertificate

public meta section

/-! Checked, ordinary syntax declarations for the connection proposer. The
cache is an elaboration aid: declarations contain syntax, never equations or
semantic assumptions. Normalization and every use still pass the kernel. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Syntax
open Lean Meta Elab
open Zkc.Source Zkc.Source.Structured Zkc.Construction

initialize checkedSyntax : SimplePersistentEnvExtension Name (Std.HashSet Name) ←
  registerSimplePersistentEnvExtension {
    -- A proof-local cache must not synchronize with other theorem tasks.
    -- Main-branch declarations remain exported; asynchronous additions only
    -- accelerate their own branch and carry no semantic authority.
    asyncMode := .local
    addEntryFn := fun names name => names.insert name
    addImportedFn := fun imported => imported.foldl (fun names next =>
      next.foldl (fun names name => names.insert name) names) {}
  }

-- Save-state backtracking rewinds Lean's auxiliary name generator, whereas
-- the proposal cache survives it. Never recycle a syntax name for another
-- candidate: mere name presence would otherwise admit a stale cache hit.
initialize syntaxSerial : IO.Ref Nat ← IO.mkRef 0

structure Cache where
  reductions : IO.Ref (Std.HashMap Expr Name)
  declarations : IO.Ref (Std.HashSet Name)
  kernelNanos : IO.Ref Nat

def newCache : IO Cache := do
  return ⟨← IO.mkRef {}, ← IO.mkRef {}, ← IO.mkRef 0⟩

/-- Only closed syntax is memoized, so it cannot depend on a candidate's
metavariables or capture an enclosing certificate under construction. -/
def freeze (cache : Cache) (value : Expr) : TermElabM Expr := do
  let value ← instantiateMVars value
  if value.hasMVar || value.hasFVar then return value
  if value.isConst || value.isLit then return value
  if let some name := (← cache.reductions.get)[value]? then
    if (← getEnv).contains name then return mkConst name
  let type ← inferType value
  let (type, value) := _root_.ShareCommon.shareCommon' (type, value)
  let serial ← syntaxSerial.modifyGet fun serial => (serial, serial + 1)
  let name ← mkAuxDeclName (.num `connectionSyntax serial)
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
  let start ← IO.monoNanosNow
  withOptions (Elab.async.set · false) <|
    addDecl (.defnDecl {name, levelParams := [], type, value, hints, safety := .safe})
  let elapsed := (← IO.monoNanosNow) - start
  cache.kernelNanos.modify (· + elapsed)
  modifyEnv fun environment => addNoncomputable (checkedSyntax.addEntry environment name) name
  cache.reductions.modify (·.insert value name)
  cache.declarations.modify (·.insert name)
  let count := (← cache.declarations.get).size
  if count % 100 == 0 && (← getOptions).getBool `zkc.connection.trace false then
    let destination := (← getOptions).get `zkc.connection.traceFile ("" : String)
    if !destination.isEmpty then
      let now ← IO.monoMsNow
      IO.FS.withFile destination .append fun handle =>
        handle.putStrLn s!"{now} syntax declarations={count}; type={type.getAppFn.constName?}"
  return mkConst name

private def syntaxType (type : Expr) : Bool :=
  [``NormalForm.Form, ``NormalForm.Term, ``NormalForm.Terms, ``NormalForm.Comp,
    ``Values, ``ConnectionFrame.Cell, ``List, ``NormalForm.InputPattern,
    ``ProtocolSignature, ``NormalForm.CalleeKey, ``NormalForm.Slot,
    ``NormalForm.State].any type.isAppOf

/-- A single memoized reduction builds a DAG of checked syntax constants.
Unlike repeated whole-residual reduction, visiting a cached continuation or
operand stops at its declaration. Renaming/substitution unfolds it only when
that operation actually needs its constructor. -/
partial def normalize (cache : Cache) (expression : Expr) : TermElabM Expr := do
  let expression ← instantiateMVars expression
  if let .const name _ := expression then
    if (checkedSyntax.getState (← getEnv)).contains name then return expression
  if let some name := (← cache.reductions.get)[expression]? then
    if (← getEnv).contains name then return mkConst name
  if (← isType expression) || (← isProof expression) then return expression
  let type ← whnf (← inferType expression)
  -- Callback regions remain source-owned templates. Their role normalization
  -- is staged when the repeat constructor requests its body certificate.
  if type.isAppOf ``Region || type.isForall then return expression
  -- Normalize data operands before reducing a transformation. In particular,
  -- stacked state projections, renamings and substitutions must not expand
  -- their common input independently at each use.
  let mut prepared := expression
  if syntaxType type then
    if expression.isApp then
      let function := expression.getAppFn
      let constructor := match (← getEnv).find? (function.constName?.getD .anonymous) with
        | some (.ctorInfo _) => true
        | _ => false
      unless constructor do
        let mut arguments := expression.getAppArgs
        for index in [:arguments.size] do
          arguments := arguments.set! index (← normalize cache arguments[index]!)
        prepared := mkAppN function arguments
    else if let .proj name index record := expression then
      prepared := mkProj name index (← normalize cache record)
  let start ← IO.monoMsNow
  let head ← whnf prepared
  let elapsed := (← IO.monoMsNow) - start
  if elapsed > 1000 && (← getOptions).getBool `zkc.connection.trace false then
    let destination := (← getOptions).get `zkc.connection.traceFile ("" : String)
    if !destination.isEmpty then
      IO.FS.withFile destination .append fun handle =>
        handle.putStrLn s!"syntax whnf_ms={elapsed}; head={expression.getAppFn.constName?}; type={type.getAppFn.constName?}"
  let result ← match head with
    | .app .. => do
      let function := head.getAppFn
      let mut fields := head.getAppArgs
      for index in [:fields.size] do
        fields := fields.set! index (← normalize cache fields[index]!)
      pure (mkAppN function fields)
    | .lam .. => lambdaTelescope head fun binders body => do
        mkLambdaFVars binders (← normalize cache body)
    | _ => pure head
  let result ← if syntaxType type then freeze cache result else pure result
  if let .const name _ := result then
    if (← cache.declarations.get).contains name then
      cache.reductions.modify (·.insert expression name)
  return result

end ZkcTools.ConstructionBindings.Syntax
