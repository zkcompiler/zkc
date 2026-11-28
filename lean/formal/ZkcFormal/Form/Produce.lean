module

public import ZkcFormal.Form.Denotation
public meta import Zkc.Kernel.Normal
public meta import Lean

/-!
The form of a stored definition: its computation, written out, with the one equation that it is
the reading of the definition's meaning.

The library states what the computation of a stored definition is (`Form.storedRole`,
`Form.storedFunction`): the recursion `Form.term` applied to the definition's stored syntax. The
form is that right side reduced: the stored syntax by the kernel's normal form, then head
reduction in which the constants that a form is made of are not unfolded (`formed`): the monad's
operations, a query, the reading of a called definition's meaning, a renamed computation, a
local computation among effects, the model's operations, and a value of a list read by its
place. The library's own functions that decide by cases on a fragment or on an operation are
opened once what they decide on is a constructor.

The equation's proof is one application of the library's theorem, so its size does not grow with
the program, and the kernel decides, when the equation is declared, that the form is the
library's right side. A form that this module computes wrongly is therefore refused; nothing
that it computes is trusted.

Three things about Lean's reduction that the walk respects. A `match` whose discriminant needs a
definition unfolded is not reduced under a restricted unfolding, so a fragment is brought to a
constructor before a function that matches on it is opened. A member of the installed program
that is computed (the member of a called definition among those of the whole program) is
normalized by the kernel and never by head reduction, which would run the core's elaboration
symbolically. A constant of `formed` is not unfolded by head reduction, so the library's
functions among them are unfolded by hand.
-/

public meta section

namespace ZkcFormal.Form.Produce
open Lean Meta Elab

/-- **What a form is made of.** The constants that the walk does not unfold: the monad's
operations and the exception's, a query, a `for`, the reading of a called definition, a renamed
computation, a computation without effects among effects, a partial operation's value or stop,
the model's operations, a list of values read by its place, a choice among alternatives; and the
library's functions that decide by cases, which the walk opens itself. -/
def formed : List Lean.Name := [``Bind.bind, ``Pure.pure, ``MonadExcept.throw, ``throw,
  ``Functor.map, ``ForIn.forIn, ``ite, ``List.range', ``Nat.beq,
  ``ZkcFormal.Reading.ask, ``ZkcFormal.Reading.read, ``Zkc.Core.roleMeaning, ``Zkc.Core.fnMeaning,
  ``ZkcFormal.Form.renamed, ``ZkcFormal.Form.liftEmpty, ``ZkcFormal.Form.optionE,
  ``Zkc.Core.Model.apply, ``ZkcFormal.Form.headV, ``ZkcFormal.Form.tailV,
  ``ZkcFormal.Form.splitPick, ``ZkcFormal.Form.onlyPayload,
  ``ZkcFormal.Form.Fragment.next, ``ZkcFormal.Form.Fragment.eval, ``ZkcFormal.Form.computed,
  ``ZkcFormal.Form.roleFragment, ``ZkcFormal.Form.localFragment, ``ZkcFormal.Form.ownedFragment]

/-- Head reduction that keeps what a form is made of. -/
def head (e : Expr) : MetaM Expr :=
  withCanUnfoldPred (fun _ info => pure (!formed.contains info.name)) (whnf e)

/-- A kept function of the library applied to a constructor: unfolded once, and its cases
decided. -/
def opened (e : Expr) : MetaM Expr := do
  let some unfolded ← unfoldDefinition? e
    | throwError "form: {e.getAppFn} is not a definition that the walk can open"
  whnfCore unfolded

/-- A value: constructors opened to their fields, a place of a list of values that is written
out taken, everything else as head reduction leaves it. -/
partial def value (e : Expr) : MetaM Expr := do
  let e ← head e
  if e.isAppOfArity ``ZkcFormal.Form.headV 5 || e.isAppOfArity ``ZkcFormal.Form.tailV 5 then
    let list ← value e.appArg!
    if list.isAppOfArity ``Zkc.Core.HList.cons 6 then
      return ← value (list.getArg! (if e.isAppOf ``ZkcFormal.Form.headV then 4 else 5))
    return mkApp e.appFn! list
  if ← isConstructorApp e then
    let args ← e.getAppArgs.mapM fun a => do
      if (← isType a) || (← isProof a) then pure a else value a
    return mkAppN e.getAppFn args
  return e

/-- A fragment as a constructor. An operation's fragment is opened on the values of its
operands, so that its cases are decided on constructors. -/
partial def fragment (p : Expr) : MetaM Expr := do
  let p ← head p
  let args := p.getAppArgs
  if p.isAppOf ``ZkcFormal.Form.computed then
    let inner ← fragment args.back!
    return ← fragment (← opened (mkAppN p.getAppFn (args.set! (args.size - 1) inner)))
  if p.isAppOf ``ZkcFormal.Form.roleFragment || p.isAppOf ``ZkcFormal.Form.localFragment ||
      p.isAppOf ``ZkcFormal.Form.ownedFragment then
    let operands ← value args.back!
    return ← fragment (← opened (mkAppN p.getAppFn (args.set! (args.size - 1) operands)))
  unless ← isConstructorApp p do
    throwError "form: an instruction's computation is no fragment that the walk knows:{indentExpr p}"
  return p

/-- The arguments at the given places, each replaced by what `how` makes of it. -/
def at_ (places : List Nat) (how : Expr → MetaM Expr) (args : Array Expr) :
    MetaM (Array Expr) := do
  let mut out := args
  for i in places do
    if h : i < out.size then out := out.set i (← how out[i])
  return out

/-- A member of the installed program that a form names, by the kernel's normal form. -/
def member (e : Expr) : MetaM Expr := do
  Zkc.Kernel.normal e (← inferType e)

/-- **The computation of a form**: the walk. -/
partial def computation (e : Expr) : MetaM Expr := do
  checkSystem "form"
  let e ← head e
  if e.isLambda then
    return ← lambdaTelescope e fun xs body => do mkLambdaFVars xs (← computation body)
  let args := e.getAppArgs
  let n := args.size
  let rebuilt (args : Array Expr) := mkAppN e.getAppFn args
  if e.isAppOfArity ``ZkcFormal.Form.Fragment.eval 4 then
    return ← computation (← opened (rebuilt (args.set! 3 (← fragment args[3]!))))
  if e.isAppOfArity ``ZkcFormal.Form.Fragment.next 6 then
    return ← computation (← opened (rebuilt (args.set! 4 (← fragment args[4]!))))
  if e.isAppOfArity ``Bind.bind 6 then return rebuilt (← at_ [4, 5] computation args)
  if e.isAppOfArity ``Pure.pure 4 then return rebuilt (← at_ [3] value args)
  if e.isAppOfArity ``ite 5 then
    return rebuilt (← at_ [3, 4] computation (← at_ [1] value args))
  if e.isAppOfArity ``Functor.map 6 then return rebuilt (← at_ [5] computation args)
  if e.isAppOf ``ForIn.forIn then
    return rebuilt (← at_ [n - 1] computation (← at_ [n - 3, n - 2] value args))
  if e.isAppOf ``MonadExcept.throw || e.isAppOf ``throw then
    return rebuilt (← at_ [n - 1] value args)
  if e.isAppOf ``ZkcFormal.Reading.ask then return rebuilt (← at_ [n - 1] value args)
  if e.isAppOf ``ZkcFormal.Form.renamed then return rebuilt (← at_ [n - 1] computation args)
  if e.isAppOf ``ZkcFormal.Form.liftEmpty then return rebuilt (← at_ [n - 1] computation args)
  if e.isAppOf ``ZkcFormal.Form.optionE then return rebuilt (← at_ [n - 2] value args)
  if e.isAppOf ``ZkcFormal.Form.splitPick then
    return rebuilt (← at_ [n - 2, n - 1] computation (← at_ [n - 3] value args))
  if e.isAppOf ``ZkcFormal.Reading.read then
    -- a called definition: its member of the program by the kernel, its arguments as values
    let called ← whnfCore args.back!
    let parts := called.getAppArgs
    if called.isAppOfArity ``Zkc.Core.roleMeaning 8 then
      let parts ← at_ [6, 7] value (← at_ [4] member parts)
      return rebuilt (args.set! (n - 1) (mkAppN called.getAppFn parts))
    if called.isAppOfArity ``Zkc.Core.fnMeaning 6 then
      let parts ← at_ [5] value (← at_ [4] member parts)
      return rebuilt (args.set! (n - 1) (mkAppN called.getAppFn parts))
    if called.isLambda || called.getAppFn.isLambda then
      throwError "form: a called definition that the walk does not reach:{indentExpr called}"
    return e
  throwError "form: the walk does not know this computation:{indentExpr e}"

/-- The form of a statement of the library's stored-definition theorem at a definition: the
value of the form, the equation, and its proof, the theorem applied. `stated` is the theorem at
the definition, a statement for every path and every list of inputs. -/
def formOf (theorem_ : Expr) (formName : Lean.Name) : MetaM (Expr × Expr × Expr) := do
  forallTelescope (← inferType theorem_) fun xs equation => do
    let some (_, lhs, rhs) := equation.eq? | throwError "form: expected an equation"
    -- the stored syntax and the names of the inputs in normal form, by the kernel
    let evalArgs := rhs.getAppArgs
    let term := evalArgs.back!
    let parts := term.getAppArgs
    let n := parts.size
    let env := parts[n - 1]!
    let envParts := env.getAppArgs
    let env := mkAppN env.getAppFn (← at_ [envParts.size - 2] member envParts)
    let term := mkAppN term.getAppFn ((← at_ [n - 3] member parts).set! (n - 1) env)
    let form ← computation (mkAppN rhs.getAppFn (evalArgs.set! (evalArgs.size - 1) term))
    let value ← mkLambdaFVars xs form
    return (value, ← mkForallFVars xs (← mkEq lhs (mkAppN (mkConst formName) xs)),
      ← mkLambdaFVars xs (mkAppN theorem_ xs))

/-- Declare the form of a definition and its equation: `<name>.form` and `<name>.reads`. -/
def declare (name : Lean.Name) (theorem_ : Expr) : MetaM Unit := do
  let formName := name ++ `form
  let readsName := name ++ `reads
  let (value, claim, proof) ← formOf theorem_ formName
  let formType ← inferType value
  addDecl (.defnDecl {
    name := formName
    levelParams := []
    type := formType
    value := value
    hints := .regular 0
    safety := .safe })
  addDecl (.thmDecl {
    name := readsName
    levelParams := []
    type := claim
    value := proof })

/-- **The form of a role of a protocol of a program**: `form_of_role N : M, p, x, r` declares
`N.form`, the computation of the role `r` of the protocol `x` of the program `p` in the model
`M`, for every path and every list of the role's inputs, and `N.reads`, that it is the reading
of the role's meaning. -/
elab "form_of_role " name:ident " : " M:term ", " p:term ", " x:term ", " r:term : command =>
    Command.liftTermElabM do
  let M ← Term.elabTermAndSynthesize M none
  let p ← Term.elabTermAndSynthesize p none
  let x ← Term.elabTermAndSynthesize x none
  let r ← Term.elabTermAndSynthesize r (some (mkConst ``Zkc.Core.Role))
  declare name.getId (← mkAppM ``ZkcFormal.Form.storedRole #[M, p, x, r])

/-- **The form of a function of a program**: `form_of_function N : M, p, x` declares `N.form`
and `N.reads` for the function `x` of the program `p` in the model `M`. -/
elab "form_of_function " name:ident " : " M:term ", " p:term ", " x:term : command =>
    Command.liftTermElabM do
  let M ← Term.elabTermAndSynthesize M none
  let p ← Term.elabTermAndSynthesize p none
  let x ← Term.elabTermAndSynthesize x none
  declare name.getId (← mkAppM ``ZkcFormal.Form.storedFunction #[M, p, x])

end ZkcFormal.Form.Produce
