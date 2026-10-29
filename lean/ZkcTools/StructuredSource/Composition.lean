module

public meta import Lean.Elab.Tactic
public import Zkc.Source.Structured.NormalizedRoot
public import Zkc.Source.Structured.ProtocolPresentation

public meta section

/-! Untrusted factoring of the existing normal-form denotation. Templates are
ordinary typed processes, not rules for a new evaluator. A template matches a
prefix only when every actual helper/callee application and operand unifies.
The resulting presentation must separately be proved with the process bind
laws. Unsupported operations remain in the proposed process for the property
assembler to report. No name, digest or successful search supplies a proof. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.Composition
open Lean Meta Elab Term

private inductive ProcessView where
  | returned (value : Expr)
  | bound (head next : Expr)
  | other (process : Expr)

private partial def viewProcess (atoms : Array Name) (process : Expr) : MetaM ProcessView := do
  let e ← whnfHeadPred process fun e => pure
    (!(e.isAppOf ``PIR.Process.bind || e.isAppOf ``PIR.Process.done ||
       atoms.any e.isAppOf))
  let args := e.getAppArgs
  if e.isAppOf ``PIR.Process.done then return .returned args.back!
  unless e.isAppOf ``PIR.Process.bind do return .other e
  let head := args[args.size - 2]!
  let next := args.back!
  match ← viewProcess atoms head with
  | .returned value => viewProcess atoms (mkApp next value)
  | .other atom => return .bound atom next
  | .bound first rest =>
      let type ← whnf (← inferType rest)
      withLocalDeclD `result type.bindingDomain! fun result => do
        let tail ← mkAppM ``PIR.Process.bind #[mkApp rest result, next]
        let continuation ← mkLambdaFVars #[result] tail
        return .bound first continuation

private partial def compactData (e : Expr) : MetaM Expr := withTransparency .default do
  if (← isType e) || (← isProof e) then return e
  let e ← whnf e
  if !e.isApp then return e
  let info ← getFunInfoNArgs e.getAppFn e.getAppNumArgs
  let mut args := e.getAppArgs
  for i in [:args.size] do
    if i < info.paramInfo.size && !info.paramInfo[i]!.isExplicit then continue
    let type ← whnf (← inferType args[i]!)
    if !type.isForall then
      args := args.set! i (← compactData args[i]!)
  let result := mkAppN e.getAppFn args
  if result == e then return e
  return ← whnf result

private def compactHead (head : Expr) : MetaM Expr := do
  let args ← head.getAppArgs.mapM fun arg => do
    let type ← whnf (← inferType arg)
    if type.isAppOf ``Zkc.Source.Values || type.isAppOf ``Option then
      compactData arg
    else pure arg
  return mkAppN head.getAppFn args

private partial def factor (atoms : Array Name) (patterns : Array Expr) (source : Expr)
    (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then throwError "source composition exceeds structural proposal depth"
  for pattern in patterns do
    let saved ← saveState
    try
      let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType pattern)
      let selected := mkAppN pattern arguments
      let rec matchPrefix (template actual : Expr) (matched : Nat) : MetaM Expr := do
        match ← viewProcess atoms template with
        | .returned value =>
            let value ← instantiateMVars value
            withLocalDeclD `component (← inferType value) fun component => do
              let rest ← factor atoms patterns actual (fuel - 1)
              let rest := (← kabstract rest (← compactData value)).instantiate1 component
              let next ← mkLambdaFVars #[component] rest
              mkAppM ``PIR.Process.bind #[← instantiateMVars selected, next]
        | .bound first rest =>
            let .bound actualFirst actualRest ← viewProcess atoms actual
              | throwError "component template extends beyond the actual process"
            unless ← withTransparency .default <| isDefEq (← compactHead first) (← compactHead actualFirst) do
              throwError "component prefix does not match after {matched} heads"
            let type ← whnf (← inferType rest)
            withLocalDeclD `returned type.bindingDomain! fun returned =>
              matchPrefix (mkApp rest returned) (mkApp actualRest returned) (matched + 1)
        | .other head =>
            let .bound actualHead actualRest ← viewProcess atoms actual
              | throwError "component terminal application has no actual source head"
            unless ← isDefEq (← compactHead head) (← compactHead actualHead) do
              throwError "component terminal application does not match"
            let type ← whnf (← inferType actualRest)
            withLocalDeclD `returned type.bindingDomain! fun returned => do
              let sourceType ← whnf (← inferType head)
              let done ← mkAppOptM ``PIR.Process.done #[some sourceType.getAppArgs[0]!, none, some returned]
              matchPrefix done (mkApp actualRest returned) (matched + 1)
      let result ← matchPrefix selected source 0
      return ← instantiateMVars result
    catch error =>
      -- Formatting a failed match can traverse a whole dependent process.
      -- Keep that work inside the lazy trace so ordinary proposals avoid it.
      trace[Elab.debug] "{error.toMessageData}"
      saved.restore
  match ← viewProcess atoms source with
  | .returned value =>
      let type ← whnf (← inferType source)
      mkAppOptM ``PIR.Process.done #[some type.getAppArgs[0]!, none, some (← compactData value)]
  | .other process => return process
  | .bound head next =>
      let type ← whnf (← inferType next)
      withLocalDeclD `returned type.bindingDomain! fun returned => do
        let rest ← factor atoms patterns (mkApp next returned) (fuel - 1)
        let continuation ← mkLambdaFVars #[returned] rest
        mkAppM ``PIR.Process.bind #[← compactHead head, continuation]

private structure Exposed where
  process : Expr
  proof : Expr
  view : ProcessView

private partial def expose (atoms : Array Name) (source : Expr) : MetaM Exposed := do
  let e ← whnfHeadPred source fun e => pure
    (!(e.isAppOf ``PIR.Process.bind || e.isAppOf ``PIR.Process.done || atoms.any e.isAppOf))
  let args := e.getAppArgs
  if e.isAppOf ``PIR.Process.done then
    return ⟨e, ← mkEqRefl source, .returned args.back!⟩
  unless e.isAppOf ``PIR.Process.bind do
    return ⟨e, ← mkEqRefl source, .other e⟩
  let head := args[args.size - 2]!
  let next := args.back!
  let inner ← expose atoms head
  match inner.view with
  | .returned value => expose atoms (mkApp next value)
  | .other atom => return ⟨e, ← mkEqRefl source, .bound atom next⟩
  | .bound first rest =>
      let type ← whnf (← inferType rest)
      let continuation ← withLocalDeclD `returned type.bindingDomain! fun returned => do
        let tail ← mkAppM ``PIR.Process.bind #[mkApp rest returned, next]
        mkLambdaFVars #[returned] tail
      let rhs ← mkAppM ``PIR.Process.bind #[first, continuation]
      let map ← withLocalDeclD `prior (← inferType head) fun prior => do
        mkLambdaFVars #[prior] (← mkAppM ``PIR.Process.bind #[prior, next])
      let same ← mkAppM ``congrArg #[map, inner.proof]
      let assoc ← mkAppM ``PIR.Process.bind_assoc #[first, rest, next]
      return ⟨rhs, ← mkAppM ``Eq.trans #[same, assoc], .bound first continuation⟩

private partial def presentation (atoms : Array Name) (left right : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then throwError "source presentation exceeds structural proof depth"
  let a ← expose atoms left
  let b ← expose atoms right
  -- Generalize a blocked discriminant, then prove all constructor branches.
  -- This also distributes a bind over a source match without an evaluator.
  let blocked ← (#[a.view, b.view]).findSomeM? fun view => do
    let head := match view with
      | .bound head _ | .other head => head
      | .returned _ => .bvar 0
    return (← matchMatcherApp? head true).bind fun matcher => matcher.discrs.back?
  if let some discr := blocked then
    unless ← isDefEq a.process b.process do
      let target ← mkEq a.process b.process
      let abstracted ← kabstract target discr
      return ← withLocalDeclD `choice (← inferType discr) fun choice => do
        let goal ← mkFreshExprMVar (abstracted.instantiate1 choice)
        for branch in ← goal.mvarId!.cases choice.fvarId! do
          branch.mvarId.withContext do
            let some (_, first, second) := (← branch.mvarId.getType).eq?
              | throwError "source branch is not an equation"
            branch.mvarId.assign (← presentation atoms first second (fuel - 1))
        let proof ← mkLambdaFVars #[choice] (← instantiateMVars goal)
        let middle := mkApp proof discr
        let joined ← mkAppM ``Eq.trans #[a.proof, middle]
        mkAppM ``Eq.trans #[joined, ← mkAppM ``Eq.symm #[b.proof]]
  let middle ← match a.view, b.view with
  | .returned first, .returned second => do
      unless ← isDefEq (← compactData first) (← compactData second) do
        throwError "source presentation returns different complete values"
      mkEqRefl a.process
  | .bound first rest, .bound second tail => do
      unless ← isDefEq (← compactHead first) (← compactHead second) do
        throwError "source presentation has different typed application heads:\n{first}\nand\n{second}"
      let type ← whnf (← inferType rest)
      let pointwise ← withLocalDeclD `returned type.bindingDomain! fun returned => do
        let proof ← presentation atoms (mkApp rest returned) (mkApp tail returned) (fuel - 1)
        mkLambdaFVars #[returned] proof
      let same ← mkAppM ``funext #[pointwise]
      let map ← withLocalDeclD `next (← inferType rest) fun next => do
        mkLambdaFVars #[next] (← mkAppM ``PIR.Process.bind #[first, next])
      mkAppM ``congrArg #[map, same]
  | .bound first _, .other second => do
      unless ← isDefEq (← compactHead first) (← compactHead second) do
        throwError "source presentation has different terminal application heads"
      let proof ← mkAppM ``Zkc.Source.Structured.ProtocolPresentation.bind_single #[first]
      unless ← isDefEq (← inferType proof) (← mkEq a.process b.process) do
        throwError "source presentation has a nonidentity terminal ABI reconstruction"
      pure proof
  | .other first, .bound second _ => do
      unless ← isDefEq (← compactHead first) (← compactHead second) do
        throwError "source presentation has different terminal application heads"
      let proof ← mkAppM ``Zkc.Source.Structured.ProtocolPresentation.bind_single #[second]
      let proof ← mkAppM ``Eq.symm #[proof]
      unless ← isDefEq (← inferType proof) (← mkEq a.process b.process) do
        throwError "source presentation has a nonidentity terminal ABI reconstruction"
      pure proof
  | .other first, .other second => do
      if ← isDefEq first second then mkEqRefl a.process else do
        -- Conditional branches may contain differently associated binds. Use
        -- ordinary congruence and function extensionality under their common
        -- eliminator; every branch is proved by the same process laws.
        match first, second with
        | .lam name type body _, .lam _ otherType otherBody _ =>
            unless ← isDefEq type otherType do
              throwError "source presentation has different branch domains"
            let pointwise ← withLocalDeclD name type fun value => do
              let proof ← presentation atoms (body.instantiate1 value)
                (otherBody.instantiate1 value) (fuel - 1)
              mkLambdaFVars #[value] proof
            mkAppM ``funext #[pointwise]
        | _, _ =>
            let leftArgs := first.getAppArgs
            let rightArgs := second.getAppArgs
            unless leftArgs.size > 0 && leftArgs.size == rightArgs.size &&
                (← isDefEq first.getAppFn second.getAppFn) do
              throwError "source presentation has different terminal applications ({first.getAppFn} / {second.getAppFn}):\n{first}\nand\n{second}"
            let mut args := leftArgs
            let mut proof ← mkEqRefl first
            for i in [:args.size] do
              if ← isDefEq args[i]! rightArgs[i]! then continue
              unless ← isDefEq (← inferType args[i]!) (← inferType rightArgs[i]!) do
                throwError "source presentation has different typed branch arguments"
              let same ← presentation atoms args[i]! rightArgs[i]! (fuel - 1)
              let map ← withLocalDeclD `branch (← inferType args[i]!) fun value =>
                mkLambdaFVars #[value] (mkAppN first.getAppFn (args.set! i value))
              proof ← mkAppM ``Eq.trans #[proof, ← mkAppM ``congrArg #[map, same]]
              args := args.set! i rightArgs[i]!
            pure proof
  | _, _ => throwError "source presentation has different process constructors:\n{a.process}\nand\n{b.process}"
  let joined ← mkAppM ``Eq.trans #[a.proof, middle]
  mkAppM ``Eq.trans #[joined, ← mkAppM ``Eq.symm #[b.proof]]

elab "source_composition_equation " " atoms " "[" atomNames:ident,* "]" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let some (_, left, right) := target.eq? | throwError "expected a source presentation equation"
    let names ← atomNames.getElems.mapM resolveGlobalConstNoOverload
    let proof ← presentation names left right 128
    goal.assign proof
    Lean.Elab.Tactic.replaceMainGoal []

elab "source_composition " "(" source:term ")"
    " components " "[" templates:term,* "]" " atoms " "[" atomNames:ident,* "]" : term => do
  withoutErrToSorry do
    let process ← elabTerm source none
    let patterns ← templates.getElems.mapM (fun template => elabTerm template none)
    let names ← atomNames.getElems.mapM resolveGlobalConstNoOverload
    let result ← factor names patterns process 128
    unless ← isDefEq (← inferType result) (← inferType process) do
      throwError "source composition changed the complete process return type"
    let result ← instantiateMVars result
    if result.hasMVar then throwError "source composition has unassociated template arguments"
    return result

end ZkcTools.StructuredSource.Composition
