module

public import ZkcFormal.Form.Denotation
public meta import Zkc.Kernel.Normal
public meta import Lean

/-!
The form of a stored definition: its computation, written out, with the one equation that it is
the reading of the definition's meaning.

The library states what the computation of a stored definition is (`Form.storedRole`,
`Form.storedFunction`): the recursion `Form.term` applied to the definition's stored syntax. The
form is that right side written out. The walk reads the stored syntax, in the kernel's normal
form, by its constructors, as the recursion does, and builds what the recursion gives at each;
it keeps the environment itself, so that a name is looked up in a table and a value is reduced
once. What an operation gives is the library's own function at that operation, reduced: a small
term, by head reduction in which the constants that a form is made of are not unfolded
(`formed`: the monad's operations, a query, the reading of a called definition's meaning, a
renamed computation, a local computation among effects, the model's operations, a value of a
list read by its place), the library's functions that decide by cases being opened once what
they decide on is a constructor. A constructor of the stored syntax that the walk does not know
is refused by its name.

The equation's proof is one application of the library's theorem, so its size does not grow with
the program, and the kernel decides, when the equation is declared, that the form is the
library's right side. A form that this module computes wrongly is therefore refused; nothing
that it computes is trusted.

The walk is linear in the stored steps (measured on a family of programs from 29 to 485 steps:
3.7 s at 485, the kernel's check of the equation 1.9 s). What keeps it so: the environment is a
table, a binder is closed once at the end and not at each step, and a conversion of a list of
values between types is reduced by the kernel, not by the unifier, which on these conversions
costs more than the rest of the walk together.

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
the model's operations, the core's own operations on values, a list of values read by its place,
a choice among alternatives; and the library's functions that decide by cases, which the walk
opens itself. -/
def formed : List Lean.Name := [``Bind.bind, ``Pure.pure, ``MonadExcept.throw, ``throw,
  ``Functor.map, ``ForIn.forIn, ``ite, ``List.range',
  ``ZkcFormal.Reading.ask, ``ZkcFormal.Reading.read, ``Zkc.Core.roleMeaning, ``Zkc.Core.fnMeaning,
  ``ZkcFormal.Form.renamed, ``ZkcFormal.Form.liftEmpty, ``ZkcFormal.Form.optionE,
  ``Zkc.Core.Model.apply, ``ZkcFormal.Form.headV, ``ZkcFormal.Form.tailV,
  ``ZkcFormal.Form.splitPick, ``ZkcFormal.Form.onlyPayload,
  ``ZkcFormal.Form.Fragment.next, ``ZkcFormal.Form.Fragment.eval, ``ZkcFormal.Form.computed,
  ``ZkcFormal.Form.roleFragment, ``ZkcFormal.Form.localFragment, ``ZkcFormal.Form.ownedFragment,
  ``Zkc.Core.hide, ``Zkc.Core.reveal, ``Zkc.Core.carry, ``Zkc.Core.enter, ``Zkc.Core.leave,
  ``Zkc.Core.nothing, ``Zkc.Core.collectRV, ``List.reverse,
  -- the operations of the core's own on values: a form names them as the source does
  ``or, ``and, ``not, ``BEq.beq, ``Nat.beq, ``Nat.blt, ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul,
  ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow, ``List.length, ``GetElem?.getElem?,
  -- a path under a frame, and one list after another
  ``HAppend.hAppend]

/-- The operations on values among what a form is made of: an application of one is kept, and
its operands are values in their turn. -/
def operations : List Lean.Name := [``or, ``and, ``not, ``BEq.beq, ``Nat.beq, ``Nat.blt,
  ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow, ``List.length,
  ``GetElem?.getElem?, ``HAppend.hAppend, ``List.reverse, ``List.cons, ``Zkc.Core.collectRV]

/-- Head reduction that keeps what a form is made of. -/
def head (e : Expr) : MetaM Expr :=
  withCanUnfoldPred (fun _ info => pure (!formed.contains info.name)) (whnf e)

/-- A kept function of the library applied to a constructor: unfolded once, and its cases
decided. -/
def opened (e : Expr) : MetaM Expr := do
  let some unfolded ← unfoldDefinition? e
    | throwError "form: {e.getAppFn} is not a definition that the walk can open"
  whnfCore unfolded

/-- **The conversions of a list of values** between what a role has, what is located and what a
local operation takes: each gives, on a list that is written out, the list of the same values
at other types. -/
def conversions : List Lean.Name := [``Zkc.Core.computeArgs, ``Zkc.Core.HList.ofLocated,
  ``Zkc.Core.revealAll, ``Zkc.Core.hideAll, ``Zkc.Core.HList.located, ``Zkc.Core.enterAll,
  ``Zkc.Core.leaveAll, ``Zkc.Core.fitAllRV, ``Zkc.Core.HList.map]

/-- Whether a role holds a value of a located type: the decision on the role and the type's
holders, both written in the stored program, by Lean's own reduction. -/
def held (role located : Expr) : MetaM Bool := do
  let holders ← mkAppM ``Zkc.Core.LTy.holders #[located]
  let decided ← whnfD (← mkAppM ``List.elem #[role, holders])
  if decided.isConstOf ``Bool.true then return true
  if decided.isConstOf ``Bool.false then return false
  throwError "form: whether the role {role} holds a value of{indentExpr located}\nis not decided"

/-- The elements of a list of types that is written out. -/
partial def cells (list : Expr) : MetaM (Array Expr) := do
  if list.isAppOfArity ``List.cons 3 then return #[list.getArg! 1] ++ (← cells (list.getArg! 2))
  if list.isAppOfArity ``List.nil 1 then return #[]
  throwError "form: a list of types of the stored syntax is not written out:{indentExpr list}"

/-- A list of values, written out: `index` is the type of the types, `family` what a value of
a type is, and the values are of the given types. -/
def written (index family : Expr) (types values : Array Expr) : Expr := Id.run do
  let mut list := mkApp2 (mkConst ``Zkc.Core.HList.nil) index family
  let mut rest := mkApp (mkConst ``List.nil [0]) index
  for i in [0:types.size] do
    let k := types.size - 1 - i
    list := mkApp6 (mkConst ``Zkc.Core.HList.cons) index family types[k]! rest values[k]! list
    rest := mkApp3 (mkConst ``List.cons [0]) index types[k]! rest
  return list

/-- The first values of a list of values by their places, and the list after them. -/
def places (list : Expr) (count : Nat) : MetaM (Array Expr × Expr) := do
  let mut found := #[]
  let mut rest := list
  for _ in [0:count] do
    found := found.push (← mkAppM ``ZkcFormal.Form.headV #[rest])
    rest ← mkAppM ``ZkcFormal.Form.tailV #[rest]
  return (found, rest)

/-- A term of the program's data by the kernel's normal form. -/
def data (e : Expr) : MetaM Expr := do
  Zkc.Kernel.normal e (← inferType e)

/-- A value: constructors opened to their fields, a place of a list of values that is written
out taken, what a role has of a value replaced by the value where the role holds it and by
nothing where it does not, everything else as head reduction leaves it. The kernel decides,
with the form's equation, that each replacement is the value that it replaces. -/
partial def value (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).headBeta
  -- a conversion of a list of values that is written out: by the kernel, which decides the
  -- equations of types that the conversion is stated along without the unifier
  if let some name := e.getAppFn.constName? then
    if conversions.contains name && e.getAppNumArgs > 0 then
      let list ← value e.appArg!
      let converted := mkApp e.appFn! list
      unless list.isAppOf ``Zkc.Core.HList.cons || list.isAppOf ``Zkc.Core.HList.nil do
        return converted
      let opened ← Zkc.Kernel.whnf converted
      if opened.getAppFn.constName? == some name then return opened
      return ← value opened
  -- a literal of the stored program: its value by the kernel
  if e.isAppOf ``Zkc.Core.Ty.readLiteral then
    let read ← Zkc.Kernel.whnf e
    return ← if read.isAppOf ``Zkc.Core.Ty.readLiteral then pure read else value read
  -- the results of a call and of a computation, by their places: on the written list of their
  -- types, the written list of what the role has of each
  if e.isAppOfArity ``ZkcFormal.Form.leaveAllV 6 then
    let args := e.getAppArgs
    let (V, M, ρ, r) := (args[0]!, args[1]!, args[2]!, args[3]!)
    let items ← cells (← data args[4]!)
    let (found, _) ← places (← value args[5]!) items.size
    let mut types := #[]
    let mut values := #[]
    for (a, x) in items.zip found do
      values := values.push (← value (← mkAppM ``Zkc.Core.leave #[M, ρ, r, a, x]))
      types := types.push (← data (← mkAppM ``Zkc.Core.LTy.map
        #[← mkAppM ``Zkc.Core.RoleMap.to #[ρ], a]))
    return written (mkApp (mkConst ``Zkc.Core.LTy) V) (mkApp3 (mkConst ``Zkc.Core.RV) V M r)
      types values
  if e.isAppOfArity ``ZkcFormal.Form.hideLocatedV 6 then
    let args := e.getAppArgs
    let (V, M, r, R) := (args[0]!, args[1]!, args[2]!, args[3]!)
    let outs ← cells (← data args[4]!)
    let (found, _) ← places (← value args[5]!) outs.size
    let mut types := #[]
    let mut values := #[]
    for (τ, x) in outs.zip found do
      let located ← data (mkApp3 (mkConst ``Zkc.Core.LTy.mk) V τ R)
      values := values.push (← value (← mkAppM ``Zkc.Core.hide #[M, r, located, x]))
      types := types.push located
    return written (mkApp (mkConst ``Zkc.Core.LTy) V) (mkApp3 (mkConst ``Zkc.Core.RV) V M r)
      types values
  let e ← head e
  let unit := mkConst ``Unit.unit
  if e.isAppOfArity ``Zkc.Core.hide 5 then
    return ← if ← held (e.getArg! 2) (e.getArg! 3) then value e.appArg! else pure unit
  if e.isAppOfArity ``Zkc.Core.reveal 6 || e.isAppOfArity ``Zkc.Core.carry 8 then
    return ← value e.appArg!
  if e.isAppOfArity ``Zkc.Core.nothing 5 then return unit
  if e.isAppOfArity ``Zkc.Core.collectRV 6 then
    unless ← held (e.getArg! 2) (e.getArg! 4) do return unit
    return mkApp e.appFn! (← value e.appArg!)
  if e.isAppOfArity ``Zkc.Core.enter 6 || e.isAppOfArity ``Zkc.Core.leave 6 then
    let callee ← mkAppM ``Zkc.Core.RoleMap.back #[e.getArg! 2, e.getArg! 3]
    return ← if ← held callee (e.getArg! 4) then value e.appArg! else pure unit
  if e.isAppOfArity ``ZkcFormal.Form.headV 5 || e.isAppOfArity ``ZkcFormal.Form.tailV 5 then
    let list ← value e.appArg!
    if list.isAppOfArity ``Zkc.Core.HList.cons 6 then
      return ← value (list.getArg! (if e.isAppOf ``ZkcFormal.Form.headV then 4 else 5))
    return mkApp e.appFn! list
  if let some constructor ← isConstructorApp? e then
    -- the fields only: a parameter of the constructor (the vocabulary, the model) is a name
    -- that the form keeps
    let args := e.getAppArgs
    let mut fields := args
    for i in [constructor.numParams:args.size] do
      let a := args[i]!
      unless (← isType a) || (← isProof a) do fields := fields.set! i (← value a)
    return mkAppN e.getAppFn fields
  -- an operation on values that the form keeps: its operands are values
  if let some name := e.getAppFn.constName? then
    if operations.contains name then
      let args ← e.getAppArgs.mapM fun a => do
        let type ← inferType a
        if (← isType a) || (← isProof a) || (← isClass? type).isSome then pure a else value a
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

/-- A definition that a form calls: a protocol at a role, or a function. -/
structure Called where
  /-- The declared member. -/
  member : Lean.Name
  /-- The key of the definition's header. -/
  key : Nat
  /-- The role, of a protocol. -/
  role : Option Nat
  deriving BEq, Inhabited

/-- How the walk names the definitions that a form calls: the name under which their members
are declared, and the calls met, which the command that runs the walk reads afterwards. The
record is of one command. -/
structure Naming where
  space : Lean.Name
  calls : IO.Ref (Array Called)

/-- **A called definition as a name.** The member of the program that a call names is declared
once, under the naming's space, by its kind and the key of its header, at the type that the
call states for it and with the kernel's normal form as its value. A member that is written out
is a member of a list of headers that is written out, which is the program's list only by
unfolding the program: a tactic would not accept it in the call's place. The name is also what
a contract of the callee is stated at, whoever applies it. Gives the name and the key. -/
def named (space : Lean.Name) (kind : String) (keyOf : Lean.Name) (header called : Expr) :
    MetaM (Expr × Nat) := do
  let type ← inferType called
  let number ← whnfD (← mkAppM ``Zkc.Core.Key.number #[← mkAppM keyOf #[header]])
  let some n := number.rawNatLit? <|> number.nat?
    | throwError "form: the key of a called definition is not a number:{indentExpr number}"
  if type.hasFVar || type.hasMVar then
    throwError "form: the member of a called definition is not of the program alone:{indentExpr type}"
  let name := space ++ Lean.Name.mkSimple s!"{kind}{n}"
  unless (← getEnv).contains name do
    withOptions (·.setBool `Elab.async false) do
      addDecl (.defnDecl {
        name, levelParams := [], type, value := ← member called
        hints := .regular 0, safety := .safe })
  return (mkConst name, n)

/-- A list of values that is written out, with what a value of a type is stated anew. -/
partial def restated (family list : Expr) : Expr :=
  if list.isAppOfArity ``Zkc.Core.HList.cons 6 then
    mkApp6 list.getAppFn (list.getArg! 0) family (list.getArg! 2) (list.getArg! 3)
      (list.getArg! 4) (restated family (list.getArg! 5))
  else if list.isAppOfArity ``Zkc.Core.HList.nil 2 then
    mkApp2 list.getAppFn (list.getArg! 0) family
  else list

/-- A role as its number, where the program decides it. -/
def roleNumber (role : Expr) : MetaM Expr := do
  let reduced ← whnfD role
  match reduced.rawNatLit? <|> reduced.nat? with
  | some n => return mkRawNatLit n
  | none => return role

/-- A term with the role that a role is in a callee written as its number, in every place:
what a role has of a value is a type that a tactic computes at a number, and not at a role map
applied to a role. -/
def calleeRoles (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun part => do
    if part.isAppOf ``Zkc.Core.RoleMap.back && !part.hasLooseBVars then
      let number ← roleNumber part
      if number.isRawNatLit then return .done number
    return .continue)

/-- The computation of one operation, reduced: a small term. A called definition is named under
the naming's space and recorded as called. -/
partial def reduced (naming : Naming) (e : Expr) : MetaM Expr := do
  let small := reduced naming
  let e ← head e
  if e.isLambda then
    return ← lambdaTelescope e fun xs body => do mkLambdaFVars xs (← small body)
  let args := e.getAppArgs
  let n := args.size
  let rebuilt (args : Array Expr) := mkAppN e.getAppFn args
  -- The type arguments of a bind and of a `pure` are read again from their reduced parts: a
  -- result that was a conversion of a list is now the list written out, and its type is the
  -- written one, not the type that the conversion states.
  if e.isAppOfArity ``Bind.bind 6 then
    let first ← small args[4]!
    let gives := (← inferType first).appArg!
    let next ← head args[5]!
    unless next.isLambda do
      return rebuilt ((args.set! 4 first).set! 2 gives)
    return ← withLocalDeclD next.bindingName! gives fun given => do
      let after ← small (next.bindingBody!.instantiate1 given)
      let ends := (← inferType after).appArg!
      return rebuilt #[args[0]!, args[1]!, gives, ends, first, ← mkLambdaFVars #[given] after]
  if e.isAppOfArity ``Pure.pure 4 then
    let given ← value args[3]!
    return rebuilt #[args[0]!, args[1]!, ← inferType given, given]
  if e.isAppOf ``MonadExcept.throw || e.isAppOf ``throw then
    return rebuilt (← at_ [n - 1] value args)
  if e.isAppOf ``ZkcFormal.Reading.ask then return rebuilt (← at_ [n - 1] value args)
  if e.isAppOf ``ZkcFormal.Form.renamed then
    return ← mkAppM ``ZkcFormal.Form.renamed #[args[n - 2]!, ← small args[n - 1]!]
  if e.isAppOf ``ZkcFormal.Form.liftEmpty then
    return ← mkAppM ``ZkcFormal.Form.liftEmpty #[args[n - 3]!, args[n - 2]!, ← small args[n - 1]!]
  if e.isAppOf ``ZkcFormal.Form.optionE then return rebuilt (← at_ [n - 2] value args)
  if e.isAppOf ``ZkcFormal.Reading.read then
    -- a called definition: its member of the program by the kernel, its arguments as values
    let called ← whnfCore args.back!
    let parts := called.getAppArgs
    if called.isAppOfArity ``Zkc.Core.roleMeaning 8 then
      let (callee, key) ← named naming.space "protocol" ``Zkc.Core.ProtocolHeader.key
        parts[3]! parts[4]!
      let parts ← at_ [6, 7] value (← at_ [5] roleNumber (parts.set! 4 callee))
      let some role := parts[5]!.rawNatLit?
        | throwError "form: the role of a called protocol is not decided:{indentExpr parts[5]!}"
      naming.calls.modify (·.push ⟨callee.constName!, key, some role⟩)
      -- the callee's inputs are what its role has of each: stated at the role's number, as
      -- the callee's own meaning states them, and not at the role map applied
      let has := mkApp3 (mkConst ``Zkc.Core.RV) parts[0]! parts[1]! parts[5]!
      let parts := parts.set! 7 (restated has parts[7]!)
      return ← mkAppM ``ZkcFormal.Reading.read #[mkAppN called.getAppFn parts]
    if called.isAppOfArity ``Zkc.Core.fnMeaning 6 then
      let (callee, key) ← named naming.space "function" ``Zkc.Core.FnHeader.key
        parts[3]! parts[4]!
      naming.calls.modify (·.push ⟨callee.constName!, key, none⟩)
      let parts ← at_ [5] value (parts.set! 4 callee)
      return ← mkAppM ``ZkcFormal.Reading.read #[mkAppN called.getAppFn parts]
    if called.isLambda || called.getAppFn.isLambda then
      throwError "form: a called definition that the walk does not reach:{indentExpr called}"
    return e
  throwError "form: the walk does not know this computation of an operation:{indentExpr e}"

/-- The computation of one operation, reduced, with the roles of its callees as numbers. -/
def small (naming : Naming) (e : Expr) : MetaM Expr := do
  calleeRoles (← reduced naming e)

/-! ## The walk

The walk reads the stored syntax by its constructors, as `Form.term` does, and builds what
`Form.term` gives there. It keeps the environment itself: a value is reduced once, when it is
bound, and a name is looked up in a table. It reduces only small terms: an operation's fragment
on the values of its operands, a condition, a count. -/

/-- What the walk is given once: the semantics, its operations, the monad of the computation,
the type of a stop, and the values of a type. -/
structure Setting where
  /-- How the called definitions are named, and where the calls met are recorded. -/
  naming : Naming
  semantics : Expr
  operations : Expr
  monad : Expr
  stop : Expr
  values : Expr
  /-- The type of the types of values. -/
  index : Expr
  /-- The monad's bind and its `pure`, at the monad, with their instances: what follows is
  applied to the two types, and to the computation and its continuation, or to the value. -/
  bind : Expr
  pure_ : Expr

/-- A list of types that is written out, with the type of its elements spelled as the setting
spells it: the stored syntax spells it through the dialect. -/
partial def Setting.types (setting : Setting) (list : Expr) : Expr :=
  if list.isAppOfArity ``List.cons 3 then
    mkApp3 list.getAppFn setting.index (list.getArg! 1) (setting.types (list.getArg! 2))
  else if list.isAppOfArity ``List.nil 1 then mkApp list.getAppFn setting.index
  else list

/-- A list of values, written out, at the setting's type of types. -/
def Setting.written (setting : Setting) (family : Expr) (types values : Array Expr) : Expr :=
  ZkcFormal.Form.Produce.written setting.index family types values

/-- The type of a list of values of the given types. -/
def Setting.list (setting : Setting) (types : Expr) : Expr :=
  mkApp3 (mkConst ``Zkc.Core.HList) setting.index setting.values (setting.types types)

/-! A binder of a continuation is made without abstracting its variable in the continuation: the
lambda's body still mentions the variable, and is marked with it. `closed` replaces every such
variable by its bound variable in one pass at the end. Abstracting at every binder would walk,
at each, everything after it. -/

private def markKey : Lean.Name := `zkcFormBinder

/-- A lambda over a variable in scope, whose body mentions the variable free. -/
def marked (v body : Expr) : MetaM Expr := do
  let decl ← v.fvarId!.getDecl
  return .lam decl.userName decl.type
    (.mdata (KVMap.empty.insert markKey (.ofName v.fvarId!.name)) body) .default

/-- A term with its marked binders closed. A result is kept by term and depth, which is right
while every marked variable is bound at one depth; if one is met at another, the table is no
longer read. -/
partial def closed (e : Expr) : MetaM Expr := do
  let table ← IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap (Expr × Nat) Expr)
  let depths ← IO.mkRef ({} : Std.HashMap FVarId Nat)
  let read ← IO.mkRef true
  let rec go (e : Expr) (depth : Nat) (bound : Std.HashMap FVarId Nat) : MetaM Expr := do
    if !e.hasFVar then return e
    if ← read.get then
      if let some done := (← table.get)[(e, depth)]? then return done
    let done ← match e with
      | .fvar id => pure (match bound[id]? with
        | some at_ => .bvar (depth - at_ - 1)
        | none => e)
      | .lam n t b bi =>
        match b with
        | .mdata d inner =>
          match d.find markKey with
          | some (.ofName y) =>
            match (← depths.get)[(⟨y⟩ : FVarId)]? with
            | some at_ => if at_ != depth then read.set false
            | none => depths.modify (·.insert ⟨y⟩ depth)
            pure (.lam n (← go t depth bound) (← go inner (depth + 1) (bound.insert ⟨y⟩ depth)) bi)
          | _ => pure (.lam n (← go t depth bound) (← go b (depth + 1) bound) bi)
        | _ => pure (.lam n (← go t depth bound) (← go b (depth + 1) bound) bi)
      | .forallE n t b bi => pure (.forallE n (← go t depth bound) (← go b (depth + 1) bound) bi)
      | .letE n t v b nd =>
        pure (.letE n (← go t depth bound) (← go v depth bound) (← go b (depth + 1) bound) nd)
      | .app f a => pure (.app (← go f depth bound) (← go a depth bound))
      | .mdata d b => pure (.mdata d (← go b depth bound))
      | .proj s i b => pure (.proj s i (← go b depth bound))
      | e => pure e
    table.modify (·.insert (e, depth) done)
    return done
  go e 0 {}

/-- What an instruction gives, as `Form.Fragment` has it. -/
inductive Piece where
  | ready (x : Expr)
  | value (a : Expr)
  /-- A computation of a reply of the type `reply`, and what is made of the reply. -/
  | action (x reply f : Expr)

/-- The values in scope, by name. -/
abbrev Scope := Lean.PersistentHashMap Nat Expr

/-- A name of the stored syntax, as a number. -/
def nameOf (e : Expr) : MetaM Nat := do
  let e ← whnfR e
  match e.rawNatLit? <|> e.nat? with
  | some n => return n
  | none => throwError "form: a name of the stored syntax is no numeral:{indentExpr e}"

/-- The elements of a list of values that is written out. -/
partial def elements (list : Expr) : MetaM (Array Expr) := do
  if list.isAppOfArity ``Zkc.Core.HList.cons 6 then
    return #[list.getArg! 4] ++ (← elements (list.getArg! 5))
  if list.isAppOfArity ``Zkc.Core.HList.nil 2 then return #[]
  throwError "form: a list of the stored syntax is not written out:{indentExpr list}"

/-- The value of a variable. -/
def lookup (scope : Scope) (var : Expr) : MetaM Expr := do
  unless var.isAppOfArity ``Zkc.Core.Var.mk 5 do
    throwError "form: a variable of the stored syntax is not written out:{indentExpr var}"
  let name ← nameOf (var.getArg! 3)
  let some found := scope.find? name | throwError "form: the name {name} is not in scope"
  return found

/-- The values of a list of variables, as a list of values of the given types. The type of the
types is spelled as the setting spells it: the generator of conditions compares the types of a
computation and of its continuation without unfolding a dialect. -/
partial def lookups (setting : Setting) (scope : Scope) (vars : Expr) : MetaM Expr := do
  if vars.isAppOfArity ``Zkc.Core.HList.cons 6 then
    let rest ← lookups setting scope (vars.getArg! 5)
    return mkApp6 (mkConst ``Zkc.Core.HList.cons) setting.index setting.values
      (vars.getArg! 2) (setting.types (vars.getArg! 3)) (← lookup scope (vars.getArg! 4)) rest
  if vars.isAppOfArity ``Zkc.Core.HList.nil 2 then
    return mkApp2 (mkConst ``Zkc.Core.HList.nil) setting.index setting.values
  throwError "form: a list of variables is not written out:{indentExpr vars}"

/-- The scope with a list of names bound to a list of values: to its elements where the list is
written out, and to its places otherwise. -/
partial def bound (scope : Scope) (names values : Expr) : MetaM Scope := do
  let names ← elements names
  let mut scope := scope
  let mut values := values
  for name in names do
    let name ← nameOf name
    if values.isAppOfArity ``Zkc.Core.HList.cons 6 then
      scope := scope.insert name (values.getArg! 4)
      values := values.getArg! 5
    else
      scope := scope.insert name (← mkAppM ``ZkcFormal.Form.headV #[values])
      values ← mkAppM ``ZkcFormal.Form.tailV #[values]
  return scope

/-- A value of a type, in the monad. -/
def returned (setting : Setting) (type a : Expr) : Expr :=
  mkApp2 setting.pure_ type a

/-- A computation of values of one type, followed by a computation of values of another. -/
def followed (setting : Setting) (first second x k : Expr) : Expr :=
  mkApp4 setting.bind first second x k

/-- What a computation returns, as its own type spells it. A binder of a continuation has this
type as it stands: the generator of conditions compares the types of a computation and of its
continuation without evaluating them. -/
def returns (x : Expr) : MetaM Expr := do
  return (← whnfR (← inferType x)).appArg!

/-- The computation of a piece, of values of the given type. -/
def computationOf (setting : Setting) (type : Expr) : Piece → MetaM Expr
  | .ready x => pure x
  | .value a => pure (returned setting type a)
  | .action x reply f => do
    withLocalDeclD `v reply fun v => do
      return followed setting reply type x (← marked v (returned setting type (f.beta #[v])))

/-- `if` on a Boolean, of the given type: the condition is that the Boolean is true, decided as
equality of Booleans is. The Boolean may be spelled at a type that is `Bool` only after a
decision (what a role has of a Boolean that it holds), so the equation is stated at `Bool`. -/
def whether (type condition yes no : Expr) : MetaM Expr := do
  let truth := mkConst ``Bool.true
  let equation := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) condition truth
  let decision := mkApp2 (mkConst ``instDecidableEqBool) condition truth
  mkAppOptM ``ite #[some type, some equation, some decision, some yes, some no]

/-- A path with one frame more. -/
def deeper (path frame : Expr) : MetaM Expr := do
  mkAppM ``HAppend.hAppend #[path, ← mkListLit (mkConst ``Zkc.Core.Frame) [frame]]

mutual

/-- The piece of a term, as `Form.term` gives it. -/
partial def term (setting : Setting) (t path : Expr) (scope : Scope) : MetaM Piece := do
  checkSystem "form"
  if t.isAppOfArity ``Zkc.Core.Term.ret 4 then
    return .value (← lookups setting scope t.appArg!)
  if t.isAppOfArity ``Zkc.Core.Term.step 8 then
    let outs := setting.list (t.getArg! 2)
    let key := t.getArg! 4
    let results := t.getArg! 6
    let rest := t.getArg! 7
    let after (values : Expr) : MetaM Expr := do
      computationOf setting outs (← term setting rest path (← bound scope results values))
    match ← instr setting key (t.getArg! 5) (t.getArg! 3) path scope with
    | .value a => return .ready (← after a)
    | .ready x =>
      let given ← returns x
      return ← withLocalDeclD `vs given fun vs => do
        return .ready (followed setting given outs x (← marked vs (← after vs)))
    | .action x reply f =>
      return ← withLocalDeclD `v reply fun v => do
        return .ready (followed setting reply outs x (← marked v (← after (← value (f.beta #[v])))))
  throwError "form: the walk does not know this term of the stored syntax:{indentExpr t.getAppFn}"

/-- The computation of a term, of the values that the term returns. -/
partial def termComputation (setting : Setting) (t path : Expr) (scope : Scope) : MetaM Expr := do
  computationOf setting (setting.list (t.getArg! 2)) (← term setting t path scope)

/-- The piece of an instruction at its key, as `Form.instr` gives it. `mid` is the types of what
the instruction returns. -/
partial def instr (setting : Setting) (key i mid path : Expr) (scope : Scope) : MetaM Piece := do
  let s := setting.semantics
  if i.isAppOfArity ``Zkc.Core.Instr.op 6 then
    -- the operations at this operation, on the values of its operands: a small term
    let operands ← lookups setting scope (i.getArg! 5)
    let piece ← fragment (mkAppN setting.operations
      #[i.getArg! 2, i.getArg! 3, key, i.getArg! 4, path, operands])
    if piece.isAppOfArity ``ZkcFormal.Form.Fragment.ready 4 then return .ready (← small setting.naming piece.appArg!)
    if piece.isAppOfArity ``ZkcFormal.Form.Fragment.value 4 then return .value (← value piece.appArg!)
    if piece.isAppOfArity ``ZkcFormal.Form.Fragment.action 6 then
      -- the reply's type as the reduced query spells it, not as the fragment states it: the
      -- fragment states it over operands that are not yet values
      let query ← small setting.naming (piece.getArg! 4)
      return .action query (← returns query) (piece.getArg! 5)
    throwError "form: an operation's computation is no fragment:{indentExpr piece}"
  if i.isAppOfArity ``Zkc.Core.Instr.guard 7 then
    let holds ← value (← mkAppM ``Zkc.Core.Semantics.holds #[s, i.getArg! 5, ← lookup scope (i.getArg! 4)])
    let at_ ← mkAppM ``Zkc.Core.Occurrence.mk #[path, key]
    let stop ← value (← mkAppM ``Zkc.Core.Semantics.stop #[s, i.getArg! 3, i.getArg! 6, at_])
    let none_ := mkApp2 (mkConst ``Zkc.Core.HList.nil) setting.index setting.values
    let nothing ← inferType none_
    let passed := returned setting nothing none_
    let stopped ← mkAppOptM ``throw #[some setting.stop, some setting.monad, none, some nothing, some stop]
    return .ready (← whether (mkApp setting.monad nothing) holds passed stopped)
  if i.isAppOfArity ``Zkc.Core.Instr.choose 10 then
    let holds ← value (← mkAppM ``Zkc.Core.Semantics.holds #[s, i.getArg! 6, ← lookup scope (i.getArg! 5)])
    let onTrue ← termComputation setting (i.getArg! 8) path scope
    let onFalse ← termComputation setting (i.getArg! 9) path scope
    return .ready (← whether (mkApp setting.monad (setting.list mid)) holds onTrue onFalse)
  if i.isAppOfArity ``Zkc.Core.Instr.block 5 then
    let frame ← mkAppM ``Zkc.Core.Frame.iteration #[key, i.getArg! 3]
    return ← term setting (i.getArg! 4) (← deeper path frame) scope
  if i.isAppOfArity ``Zkc.Core.Instr.loop 10 then
    let w := i.getArg! 4
    let times := i.getArg! 5
    let carried := i.getArg! 2
    let each := i.getArg! 3
    -- the count: written, or read from a value in scope
    let count ← if times.isAppOf ``Zkc.Core.Times.fixed then pure times.appArg! else
      if times.isAppOf ``Zkc.Core.Times.value then
        value (← mkAppM ``Zkc.Core.Semantics.count #[s, times.appArg!, ← lookup scope (times.getArg! 4)])
      else throwError "form: the count of a loop is not written out:{indentExpr times}"
    let size ← value (← mkAppM ``Zkc.Core.Times.size #[times])
    -- The state of the loop is the carried values and what was collected of each type. A list
    -- that is a variable (the body's result, the state) is read by its places, as the
    -- library's recursion reads it, so every list of the form is written out.
    let carriedTypes ← cells carried
    let eachTypes ← cells each
    let lists ← withLocalDeclD `a setting.index fun a => do
      mkLambdaFVars #[a] (← mkAppM ``List #[(mkApp setting.values a).headBeta])
    let empty ← eachTypes.mapM fun a => mkAppOptM ``List.nil #[some (mkApp setting.values a).headBeta]
    let initial ← lookups setting scope (i.getArg! 7)
    let start ← mkAppM ``Prod.mk #[initial, setting.written lists eachTypes empty]
    let state ← inferType start
    let range := mkApp3 (mkConst ``List.range') (mkNatLit 0) count (mkNatLit 1)
    let body ← withLocalDeclD `j (mkConst ``Nat) fun j => withLocalDeclD `state state fun st => do
      let index ← value (← mkAppM ``Zkc.Core.Semantics.index #[s, w, j])
      let before ← mkAppM ``Prod.fst #[st]
      -- the iteration number and the carried values, at the types of the loop's input names
      let names := i.getArg! 8
      let inputs := mkApp6 (mkConst ``Zkc.Core.HList.cons) setting.index setting.values
        (names.getArg! 2) (names.getArg! 3) index before
      let frame ← mkAppM ``Zkc.Core.Frame.iteration #[key, j]
      let inner ← termComputation setting (i.getArg! 9) (← deeper path frame)
        (← bound scope (i.getArg! 8) inputs)
      let outs := setting.list ((i.getArg! 9).getArg! 2)
      let step ← withLocalDeclD `out outs fun out => do
        let (kept, after) ← places out carriedTypes.size
        let (added, _) ← places after eachTypes.size
        let (held, _) ← places (← mkAppM ``Prod.snd #[st]) eachTypes.size
        let longer ← (added.zip held).mapM fun (x, xs) => mkAppM ``List.cons #[x, xs]
        let next ← mkAppM ``Prod.mk #[setting.written setting.values carriedTypes kept,
          setting.written lists eachTypes longer]
        marked out (returned setting state next)
      let iteration := followed setting outs state inner step
      let yield ← mkAppOptM ``ForInStep.yield #[some state]
      let stepped ← mkAppOptM ``Functor.map
        #[some setting.monad, none, some state, none, some yield, some iteration]
      marked j (← marked st stepped)
    let looped ← mkAppOptM ``forIn
      #[some setting.monad, none, none, none, some state, some range, some start, some body]
    let finish ← withLocalDeclD `state state fun st => do
      let (kept, _) ← places (← mkAppM ``Prod.fst #[st]) carriedTypes.size
      let (held, _) ← places (← mkAppM ``Prod.snd #[st]) eachTypes.size
      let collected ← (eachTypes.zip held).mapM fun (a, xs) => do
        value (← mkAppM ``Zkc.Core.Semantics.collect #[s, size, a, ← mkAppM ``List.reverse #[xs]])
      let all := setting.written setting.values (← cells (setting.types mid)) (kept ++ collected)
      marked st (returned setting (setting.list mid) all)
    return .ready (followed setting state (setting.list mid) looped finish)
  -- Not read yet, and refused by name. A choice among the alternatives of a variant: the
  -- semantics gives the alternative as a `Pick` made from the variant's own value, which is a
  -- conversion stuck on a variable, as a loop's state was; the library's recursion has to read
  -- the value by its alternatives first. An attempt: the source language has no construct that
  -- the frontend lowers to one, so a form of it could not be checked on an issued subject.
  if i.isAppOfArity ``Zkc.Core.Instr.cases 10 then
    throwError "form: the walk does not read a choice among the alternatives of a variant \
      (`Instr.cases`) yet"
  if i.isAppOfArity ``Zkc.Core.Instr.attempt 7 then
    throwError "form: the walk does not read an attempt (`Instr.attempt`) yet"
  throwError "form: the walk does not know this instruction of the stored syntax:{indentExpr i.getAppFn}"

end

/-- The form of a definition from the library's stored-definition theorem at it: the value of
the form with its type, the equation, and its proof, the theorem applied. `theorem_` is the
theorem at the definition: a statement for every model, every path and every list of inputs. -/
def formOf (naming : Naming) (theorem_ : Expr) (formName : Lean.Name) :
    MetaM (Expr × Expr × Expr × Expr) := do
  forallTelescope (← inferType theorem_) fun xs equation => do
    let some (_, lhs, rhs) := equation.eq? | throwError "form: expected an equation"
    -- the right side is the library's recursion at the semantics, the operations, the stored
    -- syntax, a path and an environment of the inputs under their names
    let recursion := rhs.getAppArgs.back!
    unless recursion.isAppOf ``ZkcFormal.Form.term do
      throwError "form: expected the library's recursion, got{indentExpr recursion}"
    let parts := recursion.getAppArgs
    let n := parts.size
    let semantics := parts[1]!
    let operations := parts[2]!
    -- the stored syntax and the names of the inputs in normal form, by the kernel
    let syntax_ ← member parts[n - 3]!
    let path := parts[n - 2]!
    let extended := parts[n - 1]!
    unless extended.isAppOf ``ZkcFormal.Form.extend do
      throwError "form: expected the inputs under their names, got{indentExpr extended}"
    let names ← member (extended.getArg! (extended.getAppNumArgs - 2))
    let type ← whnfR (← inferType lhs)
    let monad := type.appFn!
    -- the values of a type as the semantics names them (`RV M r`, `M.Val`): the field of the
    -- semantics' record, read once and not unfolded further
    let some record ← unfoldDefinition? semantics
      | throwError "form: the semantics is not a definition:{indentExpr semantics}"
    let values ← whnfCore (.proj ``Zkc.Core.Semantics 0 (← whnfCore record))
    let setting : Setting := {
      naming
      semantics, operations, monad, values
      stop := monad.getArg! 0
      index := (← whnfR (← inferType values)).bindingDomain!
      bind := ← mkAppOptM ``Bind.bind #[some monad, none]
      pure_ := ← mkAppOptM ``Pure.pure #[some monad, none] }
    let form ← closed (← termComputation setting syntax_ path (← bound {} names extended.appArg!))
    -- The form's type is spelled as its body spells types: the lists of the types of the inputs
    -- and of the results written out, as the stored syntax holds them, and not as fields of the
    -- definition's header. The generator of conditions compares the type of a computation with
    -- the type of what follows it without unfolding a header, so the two spellings must be one;
    -- the kernel decides, with the equation, that the written lists are the header's.
    let inputs := xs.back!
    let inputTypes := if names.isAppOfArity ``Zkc.Core.HList.cons 6
      then mkApp3 (mkConst ``List.cons [0]) setting.index (names.getArg! 2)
        (setting.types (names.getArg! 3))
      else mkApp (mkConst ``List.nil [0]) setting.index
    let resultType := mkApp setting.monad (setting.list (syntax_.getArg! 2))
    return ← withLocalDeclD `ins (setting.list inputTypes) fun written => do
      let before := xs.pop
      let stated := before.push written
      return (← mkLambdaFVars stated (form.replaceFVar inputs written),
        ← mkForallFVars stated resultType,
        ← mkForallFVars xs (← mkEq lhs (mkAppN (mkConst formName) xs)),
        ← mkLambdaFVars xs (mkAppN theorem_ xs))

/-- A term with every proof in it replaced by an unproved one of the same statement. -/
def withoutProofs (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun part => do
    -- an unproved statement that is not marked as made by an error: Lean does not show a
    -- message that holds one that is
    if ← isProof part then return .done (← mkSorry (← inferType part) false)
    return .continue)

/-- Declare the form of a definition and its equation: `<name>.form` and `<name>.reads`. The
form's type is the type of the reading that it equals, with the lists of types written out. -/
def declare (naming : Naming) (name : Lean.Name) (theorem_ : Expr) : MetaM Unit := do
  let formName := name ++ `form
  let readsName := name ++ `reads
  let (value, formType, claim, proof) ← formOf naming theorem_ formName
  -- A numeral of the form is written as Lean's elaborator writes one, as the stored program's
  -- are: the generator of conditions matches a rule that an author gives against the form's
  -- term as the two are written, and a value that the walk computed may hold a bare literal.
  let (value, formType, claim) := (Zkc.Kernel.numerals value, Zkc.Kernel.numerals formType,
    Zkc.Kernel.numerals claim)
  -- A form is for tactics, and `simp` and `rw` compare types without unfolding a definition
  -- that is not reducible. The kernel would accept a form whose values fit their places only
  -- by such unfolding; a tactic would not rewrite in it. So the form is checked as a tactic
  -- checks a term, before the kernel sees it. A proof that the stored program holds (that the
  -- roles of a call are distinct) is by evaluation, and no tactic reads inside it.
  try Meta.check (← withoutProofs value) .instances
  catch refusal =>
    throwError "form: the form of {name} is not type-correct as a tactic compares types \
      (without unfolding a definition that is not reducible):{indentD refusal.toMessageData}"
  -- the kernel checks the two declarations here, so that a refusal is this command's
  withOptions (·.setBool `Elab.async false) do
  addDecl (.defnDecl {
    name := formName
    levelParams := []
    type := formType
    value := value
    hints := .regular 0
    safety := .safe })
  -- the form's own equation (`<name>.form.eq_1`) can then be made where a tactic unfolds it
  enableRealizationsForConst formName
  addDecl (.thmDecl {
    name := readsName
    levelParams := []
    type := claim
    value := proof })

/-- The vocabulary of a program, from its type. -/
def vocabularyOf (p : Expr) : MetaM Expr := do
  let type ← whnf (← inferType p)
  unless type.isAppOfArity ``Zkc.Core.Typed 1 do
    throwError "form: expected a typed program, got a term of type{indentExpr type}"
  return type.appArg!

/-- **The form of a role of a protocol of a program**: `form_of_role N : p, x, r` declares
`N.form`, the computation of the role `r` of the protocol `x` of the program `p`, for every
model, every path and every list of the role's inputs, and `N.reads`, that it is the reading of
the role's meaning. -/
elab "form_of_role " name:ident " : " p:term ", " x:term ", " r:term : command =>
    Command.liftTermElabM do
  let p ← Term.elabTermAndSynthesize p none
  let x ← Term.elabTermAndSynthesize x none
  let r ← Term.elabTermAndSynthesize r (some (mkConst ``Zkc.Core.Role))
  let model ← mkAppM ``Zkc.Core.Model #[← vocabularyOf p]
  withLocalDeclD `M model fun M => do
    declare ⟨name.getId, ← IO.mkRef #[]⟩ name.getId
      (← mkLambdaFVars #[M] (← mkAppM ``ZkcFormal.Form.storedRole #[M, p, x, r]))

/-- **The form of a function of a program**: `form_of_function N : p, x` declares `N.form` and
`N.reads` for the function `x` of the program `p`, for every model. -/
elab "form_of_function " name:ident " : " p:term ", " x:term : command =>
    Command.liftTermElabM do
  let p ← Term.elabTermAndSynthesize p none
  let x ← Term.elabTermAndSynthesize x none
  let model ← mkAppM ``Zkc.Core.Model #[← vocabularyOf p]
  withLocalDeclD `M model fun M => do
    declare ⟨name.getId, ← IO.mkRef #[]⟩ name.getId
      (← mkLambdaFVars #[M] (← mkAppM ``ZkcFormal.Form.storedFunction #[M, p, x]))

end ZkcFormal.Form.Produce
