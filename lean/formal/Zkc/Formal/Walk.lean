module

public import Zkc.Formal.ProcessJudgment
public import Zkc.Formal.RoleRules
public import Zkc.Core.Meaning.Role
public import Zkc.Core.Meaning.Program
public meta import Lean

public meta section

/-!
The walk of a role's program under a judgment, one step at a time.

A goal is a judgment of a process: `Process.interpret J done halt P …`, where `P` is the
denotation of a term in an environment, or what is left of an instruction after an effect.
`walk_step` asks the kernel for the head normal form of what the next instruction denotes, and
states the goal that follows:

- for values, the rest of the term in the environment extended by them. A value that is a
  variable, a literal or a truth value is used as it is; any other gets a local variable with
  the equation that says what it is, in a form to read;
- for a stop, what the judgment asks of a stop;
- for an effect, the judgment at the effect, with the rest after its reply;
- where the step waits on a value (the element of a sequence at a position, the condition of a
  guard), a goal for each form of that value, with the equation that says which form it is; each
  of these goals then takes the step that its form makes possible.

`walk_step at h` takes the same step on a hypothesis that judges a process: what a judgment of
the process gives, as the walk of a goal says what a judgment of it needs.

Nothing is unified. A step passes from the goal to the next along an equation of processes:
the term is its first instruction and then the rest (`Term.denote_step`), what the instruction
denotes is its head normal form, and values, a stop or an effect followed by the rest are the
rest on the values, the stop, or the effect with the rest after its reply (`Process.done_bind`,
`Process.halt_bind`, `Process.call_bind_sealed`). The kernel checks each equation where it is
stated, on one instruction: it computes what the instruction denotes and compares the values.
It is never asked whether the goal before a step and the goal after it are one. The two judge
the processes of two points of the program. Left with that question on the first step of a
program whose rest is a loop with effects, under the judgment with fees, the kernel did not end
within its limit (`Zkc/Tests/Formal/WalkLoop.lean` keeps that walk).

Lean's own reduction is not asked to evaluate an environment, whose cost on a long region grows
with every instruction. For the same reason a goal that the walk states judges a sealed process
(`Process.sealed`): a tactic that normalizes its goal, to take a hypothesis apart or to close
it, stops at the name and does not run what is left of the program. The judgment at an effect
is stated open, so that it can be met, and what follows the reply is sealed.

Two instructions are taken by a rule and not by what they denote. The goal passes to the rule
along the equation between the term and the step that the rule is about:

- `walk_compute value` takes a computation of a role by its law. The law, that the operation
  gives `value` on the operands, is left as the goal `law`; the body of a function that the
  operation calls is not read, and the law of a call is stated of the meaning of the function
  in its program (`fnMeaning`). `walk_compute value at h` does the same on a hypothesis.
- `walk_loop invariant` takes a loop by an invariant (`Term.interpret_loop_invariant`). The
  invariant is a function of the iteration number, of each carried value, of what was collected
  so far for each collected type, latest first, and of what the judgment carries along a path.
  It leaves the goals `first` (the invariant before the first iteration), `step` (the body at
  any iteration, from the invariant to the invariant at the next) and `after` (the rest, from
  the invariant after the last). In `step` and `after` the carried values and what was
  collected are variables, `x<name>` and `collected<name>` after the names that the loop binds.

`walk_step` on a computation that calls a function reads the function's body; on a loop it has
no step. A block and an application wait for their first subject.

The module gives the tactic and nothing else: how a goal is read and how a term is taken apart
are private to it.
-/

open Lean Elab Tactic Meta

namespace Zkc.Formal.Walk
open Zkc.Core

/-- The kernel's head normal form. -/
private def kernelWhnf (e : Expr) : MetaM Expr := do
  ofExceptKernelException (Lean.Kernel.whnf (← getEnv) (← getLCtx) (← instantiateMVars e))

/-- Whether a term mentions an environment: it reads one somewhere. -/
private def readsEnvironment (e : Expr) : Bool :=
  (e.find? fun s => s.isConstOf ``Zkc.Core.Env.extend || s.isConstOf ``Zkc.Core.Env.empty ||
    s.isConstOf ``Zkc.Core.Env.insert).isSome

/-- What a role holds of a value, when it holds it, is the value: `hide` and `reveal` are casts
between the type of a role's part and the type of the value, and the kernel finds the two sides
definitionally equal. -/
private def unwrapped (e : Expr) : MetaM Expr := do
  unless e.isAppOf ``Zkc.Core.hide || e.isAppOf ``Zkc.Core.reveal do return e
  let inner := e.appArg!
  let same ← ofExceptKernelException (Lean.Kernel.isDefEq (← getEnv) (← getLCtx) e inner)
  return if same then inner else e

/-- A value that a step uses as it is: a variable, a literal, or a truth value. -/
private def isPlain (e : Expr) : Bool :=
  e.isFVar || e.isLit || e.isConstOf ``Bool.true || e.isConstOf ``Bool.false

/-- Whether a term is a field of a semantics that says how a loop names or collects a value. -/
private def ofSemantics (e : Expr) : Bool :=
  e.isAppOf ``Zkc.Core.Semantics.collect || e.isAppOf ``Zkc.Core.Semantics.index

/-- A value in a form to read. Its reads of an environment are replaced by what they read: a
subterm that mentions an environment and that the kernel reduces to a local variable, to a
literal or to a truth value is replaced by it. What a role holds of a value is the value. A
function applied to its argument is its body there. Everything else stays as the semantics
wrote it: the operations of the model are not unfolded, since the kernel's normal form of an
operation on a variable is its recursor. The result is definitionally the term given. -/
private partial def settle (e : Expr) : MetaM Expr := do
  match e with
  | .app .. | .proj .. =>
    if readsEnvironment e then
      let type ← inferType e
      unless (← isProp type) || (← Meta.isType e) || (← whnf type).isForall do
        let read ← kernelWhnf e
        if isPlain read then return read
    match e with
    | .proj typeName idx struct => return .proj typeName idx (← settle struct)
    | _ =>
      let applied := (mkAppN (← settle e.getAppFn) (← e.getAppArgs.mapM settle)).headBeta
      if applied != e && applied.isApp && applied.getAppFn.isLambda then settle applied
      else if ofSemantics applied then
        -- a field of a semantics, at a semantics that is written out, is what the field says
        let read ← whnfR applied
        if read != applied && !ofSemantics read then settle read else unwrapped applied
      else unwrapped applied
  | .mdata _ inner => settle inner
  | _ => return e

/-- A judgment of a process: the judgment applied to all but the process, the process as the
goal states it, the process in the form that the walk reads (the denotation of a term, or what
is left of an instruction and then the rest), the proof that the two are one
(`stated = process`), and what follows the process (a budget). It is the goal, or a hypothesis
from which the goal concludes `conclusion`. -/
private structure Judged where
  fn : Expr
  stated : Expr
  process : Expr
  opened : Expr
  extra : Array Expr
  conclusion : Option Expr := none

private def readJudged (target : Expr) : MetaM Judged := do
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Zkc.Core.Process.interpret && args.size ≥ 8 do
    throwError "walk: the goal does not judge a process{indentExpr target}"
  return {
    fn := mkAppN target.getAppFn (args.extract 0 7)
    stated := args[7]!
    process := args[7]!
    opened := ← mkEqRefl args[7]!
    extra := args.extract 8 args.size }

/-- The goal that states a judgment: the judgment, or what is concluded from it. -/
private def Judged.goal (j : Judged) (judgment : Expr) : Expr :=
  match j.conclusion with
  | some conclusion => mkForall `judged .default judgment conclusion
  | none => judgment

/-- A process under the name that Lean's own reduction does not unfold. -/
private def Judged.seal (j : Judged) (p : Expr) : Expr :=
  let a := j.fn.getAppArgs
  mkApp4 (mkConst ``Zkc.Core.Process.sealed) a[0]! a[1]! a[2]! p

/-- The goal that judges a process as it is: the judgment at an effect, to be met. -/
private def Judged.atEffect (j : Judged) (p : Expr) : Expr := j.goal (mkAppN (mkApp j.fn p) j.extra)

/-- The goal that judges what is left of a program: the judgment of the sealed process. -/
private def Judged.of (j : Judged) (p : Expr) : Expr := j.atEffect (j.seal p)

/-- The type of the processes that the judgment judges. -/
private def Judged.processType (j : Judged) : Expr :=
  let a := j.fn.getAppArgs
  mkApp3 (mkConst ``Zkc.Core.Process) a[0]! a[1]! a[2]!

/-- An equation that the kernel checks by computing its two sides. The walk states it between
two forms of one instruction, of one list of values or of one name: either one side is the head
normal form of the other, or the two share their head and differ in arguments of that kind. It
is never stated between the processes of two points of a program, which the kernel would
compare by running both. -/
private def byComputation (lhs rhs : Expr) : MetaM Expr := do
  if lhs == rhs then mkEqRefl lhs else mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)

/-- Close a goal by a proof of the judgment of another process, given the equation between the
process that the walk read and that process: the judgment passes along the equation. -/
private def Judged.pass (j : Judged) (goal : MVarId) (next equation proof : Expr) : MetaM Unit := do
  let whole ← mkEqTrans j.opened equation
  let motive ← withLocalDeclD `p j.processType fun p => mkLambdaFVars #[p] (j.atEffect p)
  goal.assign (mkApp4 (mkConst ``Eq.mpr [Level.zero]) (j.atEffect j.stated) (j.atEffect next)
    (← mkCongrArg motive whole) proof)

/-- Close a goal by a proof of the judgment of what is left of the program, sealed. -/
private def Judged.passSealed (j : Judged) (goal : MVarId) (next equation proof : Expr) :
    MetaM Unit := do
  let a := j.fn.getAppArgs
  let sealing ← mkEqSymm (mkApp4 (mkConst ``Zkc.Core.Process.sealed_eq) a[0]! a[1]! a[2]! next)
  j.pass goal (j.seal next) (← mkEqTrans equation sealing) proof

/-- The cells of a list of values: the implicit arguments of each `cons`, and its element. -/
private partial def spine (e : Expr) (acc : Array (Array Expr × Expr) := #[]) :
    MetaM (Array (Array Expr × Expr) × Expr) := do
  let w ← kernelWhnf e
  if w.isAppOfArity ``Zkc.Core.HList.cons 6 then
    let a := w.getAppArgs
    spine a[5]! (acc.push (a.extract 0 4, a[4]!))
  else if w.isAppOfArity ``Zkc.Core.HList.nil 2 then return (acc, w)
  else throwError "walk: the values of a step are not a list{indentExpr w}"

private def rebuild (cells : Array (Array Expr × Expr)) (nil : Expr) (elems : Array Expr) : Expr :=
  (cells.zip elems).foldr
    (fun ((implicits, _), x) tail => mkAppN (mkConst ``Zkc.Core.HList.cons) (implicits ++ #[x, tail])) nil

/-- The type of a variable that a step introduces, computed: the carrier of a type of the
vocabulary, and for a sequence the list of the carrier of its items. -/
private partial def readType (type : Expr) : MetaM Expr := do
  let computed ← whnfD type
  if computed.isAppOfArity ``List 1 then return mkApp computed.appFn! (← readType computed.appArg!)
  else return computed

/-- Whether a term mentions the type of the values of a type of the vocabulary. -/
private def mentionsValues (e : Expr) : Bool :=
  (e.find? fun s => s.isConstOf ``Zkc.Core.Model.Val || s.isConstOf ``Zkc.Core.Ty.Val ||
    s.isConstOf ``Zkc.Core.Tys.Val || s.isConstOf ``Zkc.Core.Tys.Choice ||
    s.isConstOf ``Zkc.Core.Semantics.Val || s.isConstOf ``Zkc.Core.RV ||
    s.isConstOf ``Zkc.Core.LVal).isSome

/-- A statement with the types in it computed: a type that is written as the values of a type of
the vocabulary is replaced by its carrier, also where it is an implicit argument, so that the
statement is about the same terms as a lemma about the carrier. The result is definitionally
the statement given. -/
private def computedTypes (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun sub => do
    if sub.hasLooseBVars || !mentionsValues sub then return .continue
    if !(← Meta.isType sub) then return .continue
    let computed ← whnfD sub
    return if computed == sub then .continue else .visit computed)

/-- A value in a form to read, as a step states it: what it settles to, and the variable, the
literal or the truth value that it is when the kernel finds one. -/
private def readValue (value : Expr) : MetaM Expr := do
  let read ← settle value
  let head ← kernelWhnf read
  return if isPlain head then head else read

/-- A function of values one at a time (`HList.uncurry`), applied to a list of them and to what
follows it, is the function at the values: the form in which the invariant of a loop is read.
The values are in a form to read. The result is definitionally the term given. -/
private partial def applied (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  let args := e.getAppArgs
  if e.getAppFn.isConstOf ``Zkc.Core.HList.uncurry && args.size ≥ 6 then
    let f ← applied args[4]!
    let (cells, _) ← spine args[5]!
    let values ← cells.mapM fun (_, value) => readValue value
    applied (mkAppN (mkAppN f values) (args.extract 6 args.size))
  else computedTypes e

/-- What the judgment asks at the end, of `done` or of `halt` (argument 5 or 6). -/
private def Judged.ask (j : Judged) (position : Nat) (value : Expr) : MetaM Expr :=
  return j.goal (← applied (mkAppN (mkApp (j.fn.getAppArgs[position]!) value) j.extra))

/-- Close a goal whose process has ended, by the goal that states what the judgment asks of the
end: of the values returned, or of the payload of a stop. `equation` is between the process that
the walk read and `ended`, the end on `value`. -/
private def Judged.ending (j : Judged) (goal : MVarId) (ended equation : Expr) (returned : Bool)
    (value : Expr) : MetaM MVarId := do
  let a := j.fn.getAppArgs
  let position := if returned then 5 else 6
  let rule := mkAppN
    (mkConst (if returned then ``Zkc.Core.Process.interpret_done else ``Zkc.Core.Process.interpret_halt))
    (a.push value)
  let judged := mkApp j.fn ended
  let asked := mkApp a[position]! value
  let asks ← mkExpectedTypeHint rule (← mkEq judged asked)
  let motive ← withLocalDeclD `judged a[3]! fun l => mkLambdaFVars #[l] (j.goal (mkAppN l j.extra))
  let next ← mkFreshExprSyntheticOpaqueMVar (← j.ask position value)
  j.pass goal ended equation (mkApp4 (mkConst ``Eq.mpr [Level.zero]) (j.goal (mkAppN judged j.extra))
    (j.goal (mkAppN asked j.extra)) (← mkCongrArg motive asks) next)
  return next.mvarId!

/-- The numbers of a list of names, when they are written. -/
private partial def nameNumbers (names : Expr) : MetaM (Array Nat) := do
  let (cells, _) ← spine names
  cells.mapM fun (_, n) => do
    let n ← kernelWhnf n
    return (n.rawNatLit?.orElse fun _ => n.nat?).getD 0

/-- The goal after values. Each value is settled. A value that settles to a local variable, a
literal or a truth value is used as it is; any other gets a new local variable `x<name>`, at
its computed type, with the equation `h<name>` that says what it is. The goal is then the rest
on these. The result is the list of the settled values, the proof of the judgment of the rest on
that list, sealed, which is the new goal at the values themselves, and the new goal. -/
private def bindValues (goal : MVarId) (j : Judged) (values : Expr) (rest : Expr) (numbers : Array Nat) :
    MetaM (Expr × Expr × MVarId) := goal.withContext do
  let (cells, nil) ← spine values
  -- a value that is what was read, under what a role holds of it, is that variable
  let settled ← cells.mapM fun (_, value) => readValue value
  let named := (List.range cells.size).toArray.filter fun i => !isPlain settled[i]!
  let mut decls := #[]
  for i in named do
    decls := decls.push (Name.mkSimple s!"x{numbers.getD i i}", ← readType (← inferType settled[i]!))
  let newType ← withLocalDeclsDND decls fun xs => do
    let mut elems := settled
    for k in [0:named.size] do
      elems := elems.set! named[k]! xs[k]!
    let mut body := j.of (mkApp rest (rebuild cells nil elems)).headBeta
    for k in (List.range named.size).reverse do
      let i := named[k]!
      body := mkForall (Name.mkSimple s!"h{numbers.getD i i}") .default
        (← computedTypes (← mkEq xs[k]! settled[i]!)) body
    mkForallFVars xs body
  let next ← mkFreshExprSyntheticOpaqueMVar newType
  let mut proof := mkAppN next (named.map (settled[·]!))
  for i in named do
    proof := mkApp proof (← mkEqRefl settled[i]!)
  let names := (named.map fun i => Name.mkSimple s!"x{numbers.getD i i}").toList ++
    (named.map fun i => Name.mkSimple s!"h{numbers.getD i i}").toList
  let (_, introduced) ← next.mvarId!.introN (2 * named.size) names
  return (rebuild cells nil settled, proof, introduced)

/-- Where a stuck term waits: the first major premise, going inwards, that is not itself a
process, and the term again as a function of what stands there. Definitions on the way are
unfolded once, so the result is definitionally the term given. -/
private partial def waitsOn (e : Expr) : MetaM (Expr × (Expr → Expr)) := do
  let e := e.headBeta
  let inner (major : Expr) (put : Expr → Expr) : MetaM (Expr × (Expr → Expr)) := do
    let type ← whnf (← inferType major)
    -- a process, or the pair that structural recursion on a process builds, is on the way;
    -- anything else is a value that the step waits on
    if type.isAppOf ``Zkc.Core.Process || type.isAppOf ``PProd then
      let (waited, rebuild) ← waitsOn (← kernelWhnf major)
      return (waited, fun x => put (rebuild x))
    else return (major, put)
  match e with
  | .proj typeName idx struct => inner struct fun x => .proj typeName idx x
  | _ =>
    let args := e.getAppArgs
    let .const name _ := e.getAppFn
      | throwError "walk: the step is stuck at a term that is not an application of a constant{indentExpr e}"
    let position ← do
      if let some (.recInfo info) := (← getEnv).find? name then pure (some info.getMajorIdx)
      else if let some info ← getMatcherInfo? name then pure (some info.getFirstDiscrPos)
      else pure none
    match position with
    | some at_ =>
      unless at_ < args.size do throwError "walk: a stuck recursor without its major premise{indentExpr e}"
      inner args[at_]! fun x => mkAppN e.getAppFn (args.set! at_ x)
    | none =>
      match ← unfoldDefinition? e with
      | some unfolded => waitsOn unfolded
      | none => throwError "walk: the step is stuck at{indentExpr e}"

/-- What is left of an instruction, then the rest, with what is left in another form: the
process, and the equation between `bound` and it. The kernel computes what is left. -/
private def withLeft (bound form : Expr) : MetaM (Expr × Expr) := do
  let b := bound.getAppArgs
  let leftType := mkApp3 (mkConst ``Zkc.Core.Process) b[0]! b[1]! b[2]!
  let motive ← withLocalDeclD `left leftType fun x =>
    mkLambdaFVars #[x] (mkAppN bound.getAppFn (b.set! 4 x))
  return (mkAppN bound.getAppFn (b.set! 4 form), ← mkCongrArg motive (← byComputation b[4]! form))

/-- A step that waits on a value: a goal for every form of the value. Each has the equation
`at<key>` between what the step waits on, in a form to read, and the form; a part of the form
is a variable at its computed type, named `x<name>` after what the step binds when the form has
as many parts as the step has results. `bound` is what is left of the instruction and then the
rest, `why` the equation between the process of the goal and it, and `stuck` the head normal
form of what is left. -/
private def splitStuck (goal : MVarId) (j : Judged) (bound why stuck : Expr) (key : Option Nat)
    (numbers : Array Nat) : MetaM (List MVarId) := goal.withContext do
  let b := bound.getAppArgs
  let (waited, put) ← waitsOn stuck
  let waited ← settle waited
  let waitedType ← kernelWhnf (← inferType waited)
  let equation := Name.mkSimple (match key with | some k => s!"at{k}" | none => "at_")
  let newType ← withLocalDeclD `waited waitedType fun form => do
    let body := j.of (mkAppN bound.getAppFn (b.set! 4 (put form)))
    mkForallFVars #[form] (mkForall equation .default (← computedTypes (← mkEq waited form)) body)
  let next ← mkFreshExprSyntheticOpaqueMVar newType
  let (waiting, toWaiting) ← withLeft bound (put waited)
  j.passSealed goal waiting (← mkEqTrans why toWaiting) (mkApp2 next waited (← mkEqRefl waited))
  let (form, afterForm) ← next.mvarId!.intro `waited
  let (_, afterEquation) ← afterForm.intro equation
  let cases ← afterEquation.cases form
  cases.toList.mapM fun case => case.mvarId.withContext do
    let mut current := case.mvarId
    let parts := case.fields.filterMap fun field => if field.isFVar then some field.fvarId! else none
    for part in parts, i in [0:parts.size] do
      let type ← current.withContext do readType (← inferType (.fvar part))
      current ← current.replaceLocalDeclDefEq part type
      if parts.size == numbers.size then
        current ← current.rename part (Name.mkSimple s!"x{numbers[i]!}")
    return current

/-- One step on what is left of an instruction and then the rest: `bound` is that process,
`left.bind rest`, and `why` is the equation between the process of the goal and it. -/
private def advance (goal : MVarId) (j : Judged) (bound why : Expr) (key : Option Nat)
    (numbers : Array Nat) : MetaM (List MVarId) := goal.withContext do
  let b := bound.getAppArgs
  let rest := b[5]!
  let w ← kernelWhnf b[4]!
  if w.isAppOfArity ``Zkc.Core.Process.done 4 then
    let (list, proof, introduced) ← bindValues goal j (w.getArg! 3) rest numbers
    let (returned, toReturned) ← withLeft bound
      (mkApp4 (mkConst ``Zkc.Core.Process.done) b[0]! b[1]! b[2]! list)
    let after := (mkApp rest list).headBeta
    let toAfter ← mkExpectedTypeHint
      (mkAppN (mkConst ``Zkc.Core.Process.done_bind) #[b[0]!, b[1]!, b[2]!, b[3]!, list, rest])
      (← mkEq returned after)
    j.passSealed goal after (← mkEqTrans why (← mkEqTrans toReturned toAfter)) proof
    return [introduced]
  else if w.isAppOfArity ``Zkc.Core.Process.halt 4 then
    let payload := w.getArg! 3
    let (_, toHalted) ← withLeft bound
      (mkApp4 (mkConst ``Zkc.Core.Process.halt) b[0]! b[1]! b[2]! payload)
    let rule := mkAppN (mkConst ``Zkc.Core.Process.halt_bind)
      #[b[0]!, b[1]!, b[2]!, b[3]!, payload, rest]
    let stopped := (← inferType rule).appArg!
    return [← j.ending goal stopped (← mkEqTrans why (← mkEqTrans toHalted rule)) false payload]
  else if w.isAppOfArity ``Zkc.Core.Process.call 5 then
    -- the judgment at the effect, with the rest after its reply
    let op := w.getArg! 3
    let k := w.getArg! 4
    let (called, toCalled) ← withLeft bound
      (mkApp5 (mkConst ``Zkc.Core.Process.call) b[0]! b[1]! b[2]! op k)
    let replyType := (← whnf (← inferType k)).bindingDomain!
    let afterReply ← withLocalDeclD `reply replyType fun x => do
      mkLambdaFVars #[x] (mkApp4 (mkConst ``Zkc.Core.Process.sealed) b[0]! b[1]! b[3]!
        (mkAppN bound.getAppFn (b.set! 4 (mkApp k x).headBeta)))
    let effect := mkApp5 (mkConst ``Zkc.Core.Process.call) b[0]! b[1]! b[3]! op afterReply
    let toEffect ← mkExpectedTypeHint
      (mkAppN (mkConst ``Zkc.Core.Process.call_bind_sealed) #[b[0]!, b[1]!, b[2]!, b[3]!, op, k, rest])
      (← mkEq called effect)
    let next ← mkFreshExprSyntheticOpaqueMVar (j.atEffect effect)
    j.pass goal effect (← mkEqTrans why (← mkEqTrans toCalled toEffect)) next
    return [next.mvarId!]
  else splitStuck goal j bound why w key numbers

/-- Where a walk starts: an equation between the meaning of a role or of a function in a program
and the sealed denotation of its body. A module that states such equations for its program gives
them this label, and a walk on a goal that judges such a meaning passes along the one that
fits, so that no text names the equation. -/
register_label_attr walk_entry

/-- A process that is the meaning of a role or of a function in a program, entered: the right
side of the labelled equation whose left side it is, with the equation so far extended to it.
What the equation fixes (the program, the member, the role) is compared as it is written, under
reducible names only. Lean is asked to unify only what the equation leaves open (the model, the
path, the inputs), whose types it compares by unfolding the header of the member. A process
that no labelled equation fits is returned as it is. -/
private def entered (at_ : Expr × Expr) : MetaM (Expr × Expr) := do
  let p := at_.1
  let .const head _ := p.getAppFn | return at_
  let given := p.getAppArgs
  for name in ← Lean.labelled `walk_entry do
    let found ← withNewMCtxDepth do
      let entry ← mkConstWithFreshMVarLevels name
      let (args, _, statement) ← forallMetaTelescope (← inferType entry)
      let some (_, lhs, rhs) := statement.eq? | return none
      let stated := lhs.getAppArgs
      unless lhs.getAppFn.isConstOf head && stated.size == given.size do return none
      let fixed ← (stated.zip given).allM fun (s, g) => do
        if s.hasExprMVar then pure true else withReducible (isDefEq s g)
      unless fixed do return none
      unless ← isDefEq lhs p do return none
      return some (← instantiateMVars rhs, ← instantiateMVars (mkAppN entry args))
    if let some (form, equation) := found then
      return (form, ← mkEqTrans at_.2 equation)
  return at_

/-- The judgment that a goal is, or, with `hypothesis`, the judgment from which it concludes. -/
private def readGoal (goal : MVarId) (hypothesis : Bool) : MetaM Judged := goal.withContext do
  -- a goal is read through the annotations that `have` and `show` leave on it
  let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let (judgment, conclusion) ← do
    if hypothesis then
      let .forallE _ judgment conclusion _ := target
        | throwError "walk: the goal concludes from no judgment{indentExpr target}"
      if conclusion.hasLooseBVars then
        throwError "walk: what the goal concludes depends on the judgment{indentExpr target}"
      pure (judgment.consumeMData.headBeta, some conclusion)
    else pure (target, none)
  let j ← readJudged judgment
  let known (p : Expr) := p.isAppOfArity ``Zkc.Core.Process.bind 6 || p.isAppOfArity ``Zkc.Core.Term.denote 7
  -- the process in another form, with the equation so far extended to it
  let reduced (at_ : Expr × Expr) (form : Expr) : MetaM (Expr × Expr) := do
    if form == at_.1 then return at_
    else return (form, ← mkEqTrans at_.2 (← byComputation at_.1 form))
  let throughSeal (at_ : Expr × Expr) : MetaM (Expr × Expr) := do
    if at_.1.isAppOfArity ``Zkc.Core.Process.sealed 4 then
      return (at_.1.appArg!, ← mkEqTrans at_.2
        (mkAppN (mkConst ``Zkc.Core.Process.sealed_eq) at_.1.getAppArgs))
    else return at_
  let mut read := (j.stated, j.opened)
  read ← reduced read read.1.headBeta
  read ← throughSeal read
  read ← reduced read read.1.headBeta
  -- a process under a reducible name is the process
  unless known read.1 do
    read ← reduced read (← whnfR read.1)
    read ← throughSeal read
  -- the meaning of a role or of a function in a program is the denotation of its body
  unless known read.1 do
    read ← entered read
    read ← throughSeal read
  return { j with process := read.1, opened := read.2, conclusion }

/-- The number of a key, for the names of what a step states; a key that is no literal gives
none. -/
private def keyNumber (key : Expr) : MetaM (Option Nat) := do
  let key ← kernelWhnf key
  if key.isAppOfArity ``Zkc.Core.Key.mk 1 then
    let number ← kernelWhnf key.appArg!
    return number.rawNatLit?.orElse fun _ => number.nat?
  else return none

/-- The rest of a term after a step, as a function of the values of the step. -/
private def restAfter (a : Array Expr) (names rest : Expr) : MetaM Expr := do
  let (D, sem, path, env) := (a[0]!, a[1]!, a[5]!, a[6]!)
  let restType ← inferType rest
  let mid ← do
    let namesType ← whnfR (← inferType names)
    pure namesType.appArg!
  let valuesType ← mkAppM ``Zkc.Core.HList #[← mkAppM ``Zkc.Core.Semantics.Val #[sem], mid]
  withLocalDeclD `values valuesType fun vs => do
    let extended ← mkAppM ``Zkc.Core.Env.extend #[env, names, vs]
    let newΓ := restType.getAppArgs[1]!
    mkLambdaFVars #[vs] (mkAppN (mkConst ``Zkc.Core.Term.denote) #[D, sem, newΓ, a[3]!, rest, path, extended])

/-- One step of the walk on a goal: on the judgment that the goal is, or, with `hypothesis`, on
the judgment from which the goal concludes. -/
private def step (goal : MVarId) (hypothesis := false) : MetaM (List MVarId) := goal.withContext do
  let j ← readGoal goal hypothesis
  let p := j.process
  if p.isAppOfArity ``Zkc.Core.Process.bind 6 then
    -- what is left of an instruction after an effect or a split
    advance goal j p (← mkEqRefl p) none #[]
  else if p.isAppOfArity ``Zkc.Core.Term.denote 7 then
    let a := p.getAppArgs
    let (D, sem, Γ, outs, path, env) := (a[0]!, a[1]!, a[2]!, a[3]!, a[5]!, a[6]!)
    let term ← kernelWhnf a[4]!
    if term.isAppOfArity ``Zkc.Core.Term.step 8 then
      let t := term.getAppArgs
      let (mid, key, i, names, rest) := (t[3]!, t[4]!, t[5]!, t[6]!, t[7]!)
      -- the term is its first instruction, then the rest on the values
      let rule := mkAppN (mkConst ``Zkc.Core.Term.denote_step)
        #[D, sem, Γ, outs, mid, key, i, names, rest, path, env]
      let stated := (← inferType rule).appArg!
      let bound := mkAppN stated.getAppFn (stated.getAppArgs.set! 5 (← restAfter a names rest))
      let why ← mkExpectedTypeHint rule (← mkEq p bound)
      advance goal j bound why (← keyNumber key) (← nameNumbers names)
    else if term.isAppOfArity ``Zkc.Core.Term.ret 4 then
      -- the term returns the values of its names
      let exit := term.getArg! 3
      let rule := mkAppN (mkConst ``Zkc.Core.Term.denote_ret) #[D, sem, Γ, outs, exit, path, env]
      let returned := (← inferType rule).appArg!
      let (cells, nil) ← spine returned.appArg!
      let elems ← cells.mapM fun (_, e) => kernelWhnf e
      let list := rebuild cells nil elems
      let ended := mkApp returned.appFn! list
      return [← j.ending goal ended (← mkExpectedTypeHint rule (← mkEq p ended)) true list]
    else throwError "walk: the term is neither a step nor a return{indentExpr term}"
  else throwError "walk: the process is not a term in an environment{indentExpr p}"

/-- A goal whose process is a term in an environment that begins with a step: the judgment, the
arguments of the denotation (dialect, semantics, context, outputs, term, path, environment) and
those of the step (the same three, the types of what it returns, key, instruction, names,
rest). -/
private def readTermStep (goal : MVarId) (hypothesis : Bool) :
    MetaM (Judged × Array Expr × Array Expr) := goal.withContext do
  let j ← readGoal goal hypothesis
  let p := j.process
  unless p.isAppOfArity ``Zkc.Core.Term.denote 7 do
    throwError "walk: the process is what is left of an instruction; take it with `walk_step`{indentExpr p}"
  let a := p.getAppArgs
  let term ← kernelWhnf a[4]!
  unless term.isAppOfArity ``Zkc.Core.Term.step 8 do
    throwError "walk: the term does not begin with a step{indentExpr term}"
  return (j, a, term.getAppArgs)

/-- A computation of a role, taken by its law: the goal `law`, that the operation gives the
value on the operands in a form to read, and the rest on the value. For a call of a function of
a program the law is about the meaning of the function there. -/
private def compute (goal : MVarId) (value : Syntax) (hypothesis := false) :
    TacticM (List MVarId) := goal.withContext do
  let (j, a, t) ← readTermStep goal hypothesis
  let (sem, Γ, outs, path, env) := (a[1]!, a[2]!, a[3]!, a[5]!, a[6]!)
  let (key, names, rest) := (t[4]!, t[6]!, t[7]!)
  let instr ← kernelWhnf t[5]!
  unless instr.isAppOfArity ``Zkc.Core.Instr.op 6 do
    throwError "walk: the next instruction is no operation{indentExpr instr}"
  let op ← kernelWhnf (instr.getArg! 4)
  unless op.isAppOfArity ``Zkc.Core.RoleOp.compute 11 do
    throwError "walk: the next instruction is no computation of a role{indentExpr op}"
  unless sem.isAppOfArity ``Zkc.Core.roleSem 6 do
    throwError "walk: the semantics is not written as that of a role{indentExpr sem}"
  let s := sem.getAppArgs
  let o := op.getAppArgs
  let rule := mkAppN (mkConst ``Zkc.Core.Term.denote_compute_role) #[s[0]!, s[1]!, s[2]!, s[3]!,
    s[4]!, s[5]!, Γ, outs, o[3]!, o[4]!, key, o[5]!, o[6]!, o[7]!, o[8]!, o[9]!, o[10]!,
    instr.getArg! 5, names, rest, path, env]
  let valueType := (← inferType rule).bindingDomain!
  let value ← instantiateMVars (← Tactic.elabTermEnsuringType value valueType)
  let withValue := mkApp rule value
  -- the law, with the operands in a form to read
  let lawType := (← inferType withValue).bindingDomain!
  let sides := lawType.getAppArgs
  let (cells, nil) ← spine sides[1]!.appArg!
  let operands ← cells.mapM fun (_, operand) => readValue operand
  -- a call of a function of a program is stated as the meaning of the function there, which is
  -- the form that a law of the function has
  let read := rebuild cells nil operands
  let operation ← kernelWhnf o[6]!
  let table := s[4]!
  let computed :=
    if operation.isAppOfArity ``Zkc.Core.LocalOp.call 4 && table.isAppOfArity ``Zkc.Core.Defs.fnTable 4
        && (table.getArg! 3).isAppOfArity ``Zkc.Core.Typed.defs 2 then
      mkAppN (mkConst ``Zkc.Core.fnMeaning) #[s[0]!, s[1]!, (table.getArg! 3).appArg!,
        operation.getArg! 2, operation.getArg! 3, read]
    else mkApp sides[1]!.appFn! read
  let law ← mkFreshExprSyntheticOpaqueMVar (tag := `law)
    (mkAppN lawType.getAppFn #[sides[0]!, computed, sides[2]!])
  -- the step is the rest on the value: the term is the step of the rule, and the rule gives
  -- the rest on what the role holds of the value
  let equation := mkApp withValue law
  let equationType ← inferType equation
  let (computing, given) := (equationType.appFn!.appArg!, equationType.appArg!)
  let restOn ← restAfter a names rest
  let (list, proof, introduced) ← bindValues goal j given.appArg!.appArg! restOn (← nameNumbers names)
  let after := (mkApp restOn list).headBeta
  j.passSealed goal after (← mkEqTrans (← byComputation j.process computing)
    (← mkEqTrans equation (← byComputation given after))) proof
  return [law.mvarId!, introduced]

/-- A statement that concludes a judgment, with the process of the judgment sealed. -/
private partial def sealConclusion (type : Expr) : Expr :=
  match type with
  | .forallE name domain body info => .forallE name domain (sealConclusion body) info
  | _ =>
    let args := type.getAppArgs
    if type.getAppFn.isConstOf ``Zkc.Core.Process.interpret && args.size ≥ 8 then
      mkAppN type.getAppFn (args.set! 7
        (mkApp4 (mkConst ``Zkc.Core.Process.sealed) args[0]! args[1]! args[2]! args[7]!))
    else type

/-- A goal for a hypothesis of a rule that concludes a judgment, stated with the process of the
judgment sealed, and the proof of the hypothesis from that goal. -/
private def sealedGoal (type : Expr) (tag : Lean.Name) : MetaM (Expr × MVarId) := do
  let goal ← mkFreshExprSyntheticOpaqueMVar (sealConclusion type) (tag := tag)
  let proof ← forallTelescope type fun xs judgment => do
    let args := judgment.getAppArgs
    unless judgment.getAppFn.isConstOf ``Zkc.Core.Process.interpret && args.size ≥ 8 do
      throwError "walk: a hypothesis of the rule concludes no judgment{indentExpr judgment}"
    let (S, H, A) := (args[0]!, args[1]!, args[2]!)
    let motive ← withLocalDeclD `p (mkApp3 (mkConst ``Zkc.Core.Process) S H A) fun p =>
      mkLambdaFVars #[p] (mkAppN judgment.getAppFn (args.set! 7 p))
    let sealedJudgment := mkAppN judgment.getAppFn
      (args.set! 7 (mkApp4 (mkConst ``Zkc.Core.Process.sealed) S H A args[7]!))
    let sealing := mkApp4 (mkConst ``Zkc.Core.Process.sealed_eq) S H A args[7]!
    mkLambdaFVars xs (mkApp4 (mkConst ``Eq.mp [Level.zero]) sealedJudgment judgment
      (← mkCongrArg motive sealing) (mkAppN goal xs))
  return (proof, goal.mvarId!)

/-- A variable that is a list of values, opened: a variable for each value. The other variables
are followed through the substitutions. -/
private partial def openList (goal : MVarId) (list : FVarId) (others : Array FVarId)
    (values : Array FVarId := #[]) : MetaM (MVarId × Array FVarId × Array FVarId) := do
  let #[case] ← goal.cases list
    | throwError "walk: a list of values that has not one form"
  let follow (x : FVarId) : FVarId := (case.subst.get x).fvarId!
  let parts := case.fields.filterMap fun field => if field.isFVar then some field.fvarId! else none
  match parts with
  | #[] => return (case.mvarId, values.map follow, others.map follow)
  | #[head, tail] => openList case.mvarId tail (others.map follow) ((values.map follow).push head)
  | _ => throwError "walk: a list of values with a cell of {parts.size} parts"

/-- The state of a loop, opened: a variable for each carried value and for what was collected of
each collected type, named and at its computed type. -/
private def openState (goal : MVarId) (state : FVarId) (carried collected : Array Lean.Name) :
    MetaM (MVarId × Array FVarId × Array FVarId) := do
  let #[pair] ← goal.cases state
    | throwError "walk: the state of a loop is not a pair"
  let (first, second) := (pair.fields[0]!.fvarId!, pair.fields[1]!.fvarId!)
  let (goal, values, others) ← openList pair.mvarId first #[second]
  let (goal, lists, values) ← openList goal others[0]! values
  let mut goal := goal
  for x in values ++ lists, name in carried ++ collected do
    let type ← goal.withContext do readType (← inferType (.fvar x))
    goal ← goal.replaceLocalDeclDefEq x type
    goal ← goal.rename x name
  return (goal, values, lists)

/-- A loop, taken by an invariant: the goals `first`, `step` and `after`. -/
private def loop (goal : MVarId) (invariant : Syntax) (monotone? : Option Syntax) :
    TacticM (List MVarId) := goal.withContext do
  let (j, a, t) ← readTermStep goal false
  let #[carriedAlong] := j.extra
    | throwError "walk: the rule of a loop is for a judgment that carries one value along a path"
  let (D, sem, Γ, outs, path, env) := (a[0]!, a[1]!, a[2]!, a[3]!, a[5]!, a[6]!)
  let (key, names, rest) := (t[4]!, t[6]!, t[7]!)
  let instr ← kernelWhnf t[5]!
  unless instr.isAppOfArity ``Zkc.Core.Instr.loop 10 do
    throwError "walk: the next instruction is no loop{indentExpr instr}"
  let l := instr.getAppArgs
  let judged := j.fn.getAppArgs
  let (judgment, done, halt) := (judged[4]!, judged[5]!, judged[6]!)
  let along ← inferType carriedAlong
  let monotone ← match monotone? with
    | some proof => do
      let expected ← mkAppM ``Zkc.Core.ProcessJudgment.Monotone #[judgment]
      instantiateMVars (← Tactic.elabTermEnsuringType proof expected)
    | none =>
      if judgment.isAppOf ``Zkc.Core.ProcessJudgment.silent then
        pure (mkConst ``Zkc.Core.ProcessJudgment.silent_monotone)
      else if judgment.isAppOf `Zkc.Core.ProcessJudgment.charged then
        pure (mkAppN (mkConst `Zkc.Core.ProcessJudgment.charged_mono) judgment.getAppArgs)
      else throwError "walk: say why the judgment is monotone, `walk_loop … using …`{indentExpr judgment}"
  let rule := mkAppN (mkConst ``Zkc.Core.Term.interpret_loop_invariant) #[D, sem, along, Γ, outs,
    l[2]!, l[3]!, key, l[4]!, l[5]!, l[6]!, l[7]!, l[8]!, l[9]!, names, rest, path, env, judgment,
    monotone, done, halt, carriedAlong]
  let invariantType := (← inferType rule).bindingDomain!
  let invariant ← instantiateMVars (← Tactic.elabTermEnsuringType invariant invariantType)
  let withInvariant := mkApp rule invariant
  let hypotheses ← inferType withInvariant
  let (firstType, stepType, afterType) := (hypotheses.bindingDomain!,
    hypotheses.bindingBody!.bindingDomain!, hypotheses.bindingBody!.bindingBody!.bindingDomain!)
  let first ← mkFreshExprSyntheticOpaqueMVar firstType (tag := `first)
  let (stepProof, step) ← sealedGoal stepType `step
  let (afterProof, after) ← sealedGoal afterType `after
  -- the term is the loop of the rule
  let looping := hypotheses.bindingBody!.bindingBody!.bindingBody!.getAppArgs[7]!
  j.pass goal looping (← byComputation j.process looping)
    (mkAppN withInvariant #[first, stepProof, afterProof])
  -- the names: after the key of the loop, and after the names that the loop binds
  let suffix := ((← keyNumber key).map toString).getD ""
  let named (base : String) : Lean.Name := Name.mkSimple (base ++ suffix)
  let inputs ← nameNumbers l[8]!
  let results ← nameNumbers names
  let carried := (inputs.extract 1 inputs.size).map fun n => Name.mkSimple s!"x{n}"
  let collected := (results.extract carried.size results.size).map fun n => Name.mkSimple s!"collected{n}"
  -- how often the loop runs, in a form to read
  let count := stepType.bindingBody!.bindingBody!.bindingBody!.bindingDomain!.appArg!
  let countRead ← do
    let read ← readValue count
    -- a number that the kernel computed is written as a numeral
    pure ((read.rawNatLit?.map mkNatLit).getD read)
  let atCount (e : Expr) : Expr := e.replace fun s => if s == count then some countRead else none
  -- before the first iteration
  let firstGoal ← first.mvarId!.replaceTargetDefEq (← applied firstType)
  -- the body, at any iteration
  let (_, stepGoal) ← step.intro (named "i")
  let (state, stepGoal) ← stepGoal.intro `state
  let (stepGoal, _, _) ← openState stepGoal state carried collected
  let (_, stepGoal) ← stepGoal.intro (named "t")
  let (early, stepGoal) ← stepGoal.intro (named "early")
  let (holds, stepGoal) ← stepGoal.intro (named "invariant")
  let stepGoal ← stepGoal.withContext do
    let earlyType ← inferType (.fvar early)
    let stepGoal ← stepGoal.replaceLocalDeclDefEq early (atCount earlyType)
    stepGoal.replaceLocalDeclDefEq holds (← applied (← inferType (.fvar holds)))
  -- the rest, after the last iteration
  let (state, afterGoal) ← after.intro `state
  let (afterGoal, _, _) ← openState afterGoal state carried collected
  let (_, afterGoal) ← afterGoal.intro (named "t")
  let (holds, afterGoal) ← afterGoal.intro (named "invariant")
  let afterGoal ← afterGoal.withContext do
    afterGoal.replaceLocalDeclDefEq holds (← applied (atCount (← inferType (.fvar holds))))
  let afterGoal ← afterGoal.withContext do
    let judgedAfter ← readGoal afterGoal false
    let restOn ← restAfter a names rest
    let (list, proof, introduced) ←
      bindValues afterGoal judgedAfter judgedAfter.process.appArg!.appArg! restOn results
    let next := (mkApp restOn list).headBeta
    judgedAfter.passSealed afterGoal next (← byComputation judgedAfter.process next) proof
    pure introduced
  firstGoal.setTag `first
  stepGoal.setTag `step
  afterGoal.setTag `after
  return [firstGoal, stepGoal, afterGoal]

/-- One step of the walk on the main goal, or, with `at h`, on a hypothesis that judges a
process. Where the step waits on a value, the goal is split by the forms of the value, and each
case takes the step that its form makes possible. -/
syntax "walk_step" (" at " ident)? : tactic

elab_rules : tactic
  | `(tactic| walk_step) => do
    let next ← step (← getMainGoal)
    let next ← if next.length ≤ 1 then pure next else next.flatMapM fun case => step case
    replaceMainGoal next
  | `(tactic| walk_step at $h:ident) => withMainContext do
    let hypothesis ← getFVarId h
    let name ← hypothesis.getUserName
    let (reverted, goal) ← (← getMainGoal).revert #[hypothesis]
    unless reverted.size == 1 do
      throwError "walk: other hypotheses depend on {h}"
    let next ← step goal true
    let next ← if next.length ≤ 1 then pure next else next.flatMapM fun case => step case true
    replaceMainGoal (← next.mapM fun case => return (← case.intro name).2)

/-- Take the computation of a role that is the next instruction by its law: the operation gives
`value` on the operands. The law is left as the goal `law`, with the operands in a form to
read; the main goal is the rest on the value. With `at h`, on a hypothesis that judges a
process. -/
syntax "walk_compute " term (" at " ident)? : tactic

/-- Take the loop that is the next instruction by an invariant: a function of the iteration
number, of each carried value, of what was collected so far for each collected type, latest
first, and of what the judgment carries along a path. The goals are `first`, `step` and
`after`. The judgment must be monotone; for one that the walk does not know, `using` gives the
proof. -/
syntax "walk_loop " term (" using " term)? : tactic

elab_rules : tactic
  | `(tactic| walk_compute $value:term) => do
    replaceMainGoal (← compute (← getMainGoal) value)
  | `(tactic| walk_compute $value:term at $h:ident) => withMainContext do
    let hypothesis ← getFVarId h
    let name ← hypothesis.getUserName
    let (reverted, goal) ← (← getMainGoal).revert #[hypothesis]
    unless reverted.size == 1 do
      throwError "walk: other hypotheses depend on {h}"
    let next ← compute goal value true
    replaceMainGoal [next[0]!, (← next[1]!.intro name).2]
  | `(tactic| walk_loop $invariant:term) => do
    replaceMainGoal (← loop (← getMainGoal) invariant none)
  | `(tactic| walk_loop $invariant:term using $monotone:term) => do
    replaceMainGoal (← loop (← getMainGoal) invariant (some monotone))

end Zkc.Formal.Walk
