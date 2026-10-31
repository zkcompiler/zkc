module

public import Zkc.Construction.ConnectionTargetPlacement
public import Zkc.Construction.ConnectionStaticRoutes
public meta import Lean.Meta.Basic
public meta import Lean.Compiler.ExternAttr
public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.Compiler.IR.CompilerM

public meta section

/-! The residual interface of a generated body family contains syntax and
finite readback certificates. Its telescope excludes arbitrary semantic proof
parameters, and its finite equations exclude unsupported reflective
computations. This is an elaboration policy with explicit computation/owner
boundaries, not a semantic noninterference theorem. The kernel still checks
the complete family application.
-/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Interface
open Lean Meta
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction

initialize registerTraceClass `zkc.connection.interface

/-- Fixed typed syntax owners already admitted by the family interface. -/
private def syntaxType (type : Expr) : Bool :=
  -- Request contains only a method name, finite operand references and Ty.
  [``Ty, ``Slot, ``Template, ``Request, ``Original.Location, ``ValueSort, ``Helper, ``ProtocolSignature,
    ``NormalForm.LawKey, ``NormalForm.InputPattern, ``NormalForm.CalleeKey,
    ``NormalForm.Term, ``NormalForm.Terms, ``NormalForm.Comp, ``NormalForm.Subject,
    ``NormalForm.Form, ``ConnectionFrame.Cell, ``ConnectionFrame.ScopedFrame].any type.isAppOf

/-- Admit containers only when their elements belong to the finite syntax
vocabulary. In particular, `List` and `Option` do not hide semantic premises. -/
partial def finiteData (type : Expr) : MetaM Bool := do
  let type ← whnf (← instantiateMVars type)
  if syntaxType type || [``Nat, ``Bool, ``String, ``Profile, ``Domain.Mode].any type.isAppOf then return true
  if type.isAppOf ``List || type.isAppOf ``Option then
    return ← finiteData type.getAppArgs.back!
  if type.isAppOf ``Prod || type.isAppOf ``Except then
    return (← finiteData type.getAppArgs[0]!) && (← finiteData type.getAppArgs[1]!)
  if type.isAppOf ``Values then
    let functor := type.getAppArgs[1]!
    -- These dependent rows contain syntax even when their index is symbolic.
    if [``NormalForm.Argument, ``NormalForm.Comp, ``NormalForm.Term,
        ``NormalForm.Input].any functor.isAppOf then return true
    let functorType ← whnf (← inferType functor)
    if let .forallE name index _ _ := functorType then
      return ← withLocalDeclD name index fun item => finiteData (mkApp functor item)
  return false

/-- A bounded declaration-graph inspection, not evaluation of a reflected
check. Sharing this state across a telescope avoids revisiting definitions. -/
private structure ReflectionState where
  seen : NameSet := {}
  remaining : Nat := 20000

/-- Typed syntax and its finite containers are owner boundaries. Inspecting
their interpretation or full normalization would repeat the source/body work. -/
private partial def syntaxData (type : Expr) : MetaM Bool := do
  let type ← whnf type
  if syntaxType type then return true
  if type.isAppOf ``List || type.isAppOf ``Option then
    return ← syntaxData type.getAppArgs.back!
  if type.isAppOf ``Prod || type.isAppOf ``Except then
    unless ← finiteData type do return false
    return (← syntaxData type.getAppArgs[0]!) || (← syntaxData type.getAppArgs[1]!)
  if type.isAppOf ``Values then return ← finiteData type
  return false

/-- Inspect computational dependencies, including transparent wrappers.
Proofs and types are erased; typed syntax and the fixed
source/routing/library owners are boundaries, as are the parameters checked
separately by `auditFamilyType`. In particular this does not interpret source
syntax or rerun its normalizer while checking a finite interface equation.
No theorem about an arbitrary equality is assumed or synthesized here.

Compiled transparent declarations and declared runtime primitives are trusted
computation boundaries. Uncompiled wrappers are inspected; opaque/axiomatic data outside
those boundaries is refused. A `noncomputable` annotation alone is not a
refusal: Lean also uses it on constructive logical definitions such as Boolean
conjunction. This is deliberately conservative, including for dead
branches; exhaustion also refuses the candidate. Plain finite parameters are
allowed without auditing where a caller obtained their values. This does not
classify every semantic encoding in finite data, source syntax or owners, nor
certify compiler substitutions or native primitive implementations. -/
private partial def reflected (state : IO.Ref ReflectionState) (value : Expr) : MetaM Bool := do
  let current ← state.get
  if current.remaining == 0 then
    trace[zkc.connection.interface] "reflection inspection budget exhausted"
    return false
  state.set { current with remaining := current.remaining - 1 }
  if (← isProof value) || (← isType value) then return true
  let type ← whnf (← inferType value)
  if [``ProtocolContext, ``ConnectionLibrary.Entry, ``Original.Routing,
      ``ConnectionLibrary.Selection].any type.isAppOf then return true
  if ← syntaxData type then return true
  match value with
  | .const name _ =>
    if (← state.get).seen.contains name then return true
    state.modify fun current => { current with seen := current.seen.insert name }
    match ← getConstInfo name with
    | .defnInfo info =>
      -- Executable declarations are a computation boundary, not an operation
      -- whitelist. Uncompiled generated wrappers still have their body read.
      let environment ← getEnv
      if !isNoncomputable environment name && (IR.findEnvDecl environment name).isSome then
        return true
      reflected state info.value
    | .axiomInfo _ | .opaqueInfo _ =>
      if isExtern (← getEnv) name then return true
      trace[zkc.connection.interface] "unsupported opaque/axiomatic data dependency: {name}"
      return false
    | _ => return true
  | .app function argument =>
    unless ← reflected state function do return false
    reflected state argument
  | .lam name domain body bi =>
    withLocalDecl name bi domain fun parameter => reflected state (body.instantiate1 parameter)
  | .letE name type value body _ =>
    unless ← reflected state value do return false
    withLetDecl name type value fun parameter => reflected state (body.instantiate1 parameter)
  | .proj _ _ record => reflected state record
  | .mdata _ value => reflected state value
  -- Telescope parameters are checked separately. This inspection runs only
  -- after family closure, so unresolved expression holes are not supported.
  | .fvar _ | .lit _ | .sort _ | .forallE .. => return true
  | .mvar _ | .bvar _ => return false

/-- Equality is permitted over finite operands, never over processes,
functions, propositions or semantic blocks. A finite source-form equality
is a normalization obligation, not an equality of its interpreted process.
Readback/routing certificates
have their fixed, independently proved interpretation in the core. -/
def structural (type : Expr) : MetaM Bool := do
  let type ← whnf (← instantiateMVars type)
  if type.isAppOf ``Eq then return ← finiteData type.getAppArgs[0]!
  return [``ConnectionFrame.Readback, ``ConnectionCertificate.GuardReadback,
    ``ConnectionCertificate.HistoryReadback, ``ConnectionFrame.IndexReadback,
    ``ConnectionStaticRoutes.Local, ``ConnectionStaticRoutes.Delivery,
    ``ConnectionStaticRoutes.LocalMode].any type.isAppOf

private def auditedStructural (state : IO.Ref ReflectionState) (type : Expr) : MetaM Bool := do
  unless ← structural type do return false
  if type.isAppOf ``Eq then
    unless ← reflected state type.getAppArgs[1]! do return false
    return ← reflected state type.getAppArgs[2]!
  return true

/-- Audit the complete closed telescope, including parameters introduced by
closure rather than residual goals. The three indexed owners may be explicit
parameters: they determine which source, routing and earlier library is being
certified. A context is allowed only as the actual placement context. Neither
allowance admits an arbitrary function or a semantic proof premise. -/
def auditFamilyType (type : Expr) : MetaM Unit :=
  forallTelescopeReducing type fun parameters result => do
    unless result.isAppOf ``ConnectionTargetPlacement.CheckedBody do
      throwError "connection-family-result: expected CheckedBody"
    let indices := result.getAppArgs
    let owners := indices.extract 2 5
    let placement := indices.back!
    let context ← whnf (← mkAppM ``ConnectionTargetPlacement.Placement.context #[placement])
    let reflection ← IO.mkRef ({} : ReflectionState)
    for parameter in parameters do
      let type ← whnf (← inferType parameter)
      if (← finiteData type) || (← auditedStructural reflection type) then continue
      if type.isAppOf ``ProtocolContext && context == parameter then continue
      if [``ConnectionLibrary.Entry, ``Original.Routing, ``ConnectionLibrary.Selection].any
          type.isAppOf && owners.contains parameter then continue
      throwError "connection-family-forbidden-parameter: {(← parameter.fvarId!.getDecl).userName} : {type}"

end ZkcTools.ConstructionBindings.Interface
