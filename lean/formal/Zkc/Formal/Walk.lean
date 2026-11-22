module

public import Zkc.Formal.ProcessJudgment
public import Zkc.Formal.RoleRules
public import Zkc.Formal.Application
public import Zkc.Core.Meaning.Role
public import Zkc.Core.Meaning.Program
public import Zkc.Formal.WalkLabels
public meta import Lean

public meta section

/-!
The walk of a role's program under a judgment.

A goal is a judgment of a process: `Process.interpret J done halt P …`, where `P` is the
denotation of a term in an environment, or what is left of an instruction after an effect.

## What a text writes

`walk` goes to the next place where a text has something to say: an effect, where the text says
what the judgment asks of it (for the judgment with fees, `walk_free` and `walk_pay` of
`Zkc/Formal/Written/WalkFees.lean`); a loop, which the text takes by an invariant
(`walk_loop`); a call of a function, which it takes by the function's law (`walk_law`); or the
end of the program, where what is left is what the judgment asks of the end. `walk … at h`
walks a hypothesis that judges a process: what a judgment of the process gives, as the walk of
a goal says what a judgment of it needs.

Where the program applies a protocol, the walk goes into the callee (`enterApplication`): under
a judgment that reads no peer of an effect, the application and then the rest is judged as the
callee's program of the role, whose condition at the end is the judgment of the rest on the
results. The text writes nothing there; the next place that it meets is in the callee.

A text follows the mathematics of a program, not its instructions.

- **Nothing that an instruction binds has a name.** A value of a step that is no variable, no
  literal and no truth value gets a variable and the equation that says what it is, both under
  names that a text cannot write. While the process goes on, the variable stands for the value
  in it, so that the kernel computes on the value only what the program does. Where the walk
  stops with the process going on, the hypotheses are restated of the values. Where no process
  goes on (the end, and a goal that a rule leaves beside the walk), the variables are replaced
  by the values, and the operations of a model are read as the library says they are
  (`walk_value`: the addition of the arithmetic model over a field is the field's). What a
  text has left to prove at the end is stated in the inputs, the replies and its own names.
- **A text names what it speaks of.** A reply has the name that the text gives it at the
  effect. Where a step waits on a value (the condition of a guard, an element of a sequence
  whose position is not known to be in it), there is a goal for each form of the value; a side
  that is closed as it stands is closed, and the walk goes on in every other. `walk as h`
  names the hypothesis that says which form the value is, `walk as ⟨x, h⟩` also the parts of
  the form, and `walk as ⟨x, h⟩, g` the forks on the way in order. A name for which no fork is
  met is an error. The arguments of an invariant have the names that the text gave them.
- **A read that the context decides is no fork.** Where a step waits on a read of a sequence
  and the context decides what the read finds, the step goes on with it. The context decides a
  read by a hypothesis that says what it finds, by a law of reads (a theorem with the label
  `walk_read`, as the entry of the list of a function at a position below its size) whose
  premises are hypotheses or follow from them by arithmetic, or by the length of the list and
  a bound of the position. A text that reads a sequence in another order, or once more, says
  nothing new.

## One step

`walk_step` is one step of the walk. It asks the kernel for the head normal form of what the
next instruction denotes, and states the goal that follows:

- for values, the rest of the term in the environment extended by them;
- for a stop, what the judgment asks of a stop;
- for an effect, the judgment at the effect, with the rest after its reply;
- where the step waits on a value, a goal for each form of that value, with the equation that
  says which form it is; each of these goals then takes the step that its form makes possible.

`walk_step at h` takes the same step on a hypothesis that judges a process.

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

- `walk_law law` takes a computation of a role by a law that the text gives, as a theorem of
  what a function of the program computes: the value is what the law says. The law may be
  stated in the table of another program that has the function than the one that the call
  reads (a protocol that is applied reads the table of the definitions before it): the call
  is the call there, by the entries of the function in the two tables (`fnMeaning_entry`).
- `walk_compute value` takes a computation of a role by its law. The law, that the operation
  gives `value` on the operands, is left as the goal `law`; the body of a function that the
  operation calls is not read, and the law of a call is stated of the meaning of the function
  in its program (`fnMeaning`). `walk_compute value at h` does the same on a hypothesis.
- `walk_loop invariant` takes a loop by an invariant (`Term.interpret_loop_invariant`). The
  invariant is a function of the iteration number, of each carried value, of what was collected
  so far for each collected type, latest first, and of what the judgment carries along a path.
  It leaves the goals `first` (the invariant before the first iteration), `step` (the body at
  any iteration, from the invariant to the invariant at the next) and `after` (the rest, from
  the invariant after the last). In `step` and `after` the iteration number, the carried
  values, what was collected and what the judgment carries are variables with the names that
  the text gave the arguments of the invariant; the invariant is the hypothesis
  `invariant_<index>`, and that the iteration is one of the loop's is `early_<index>`.

A region is walked as a program is. An instruction that runs a region (a choice, which runs
the arm that its condition chooses; a block, which runs its body under its frame) is not
computed as one instruction: the goal passes to the judgment of the region, whose condition at
the end is the judgment of what follows it (`Process.interpret_bind`). Inside the region every
rule is as outside, so the values of an arm have variables, its effects, loops and calls are
met, and a fork inside it is named; at its end the goal is the judgment of the rest. Where the
kernel computes the condition of a choice, the walk goes into the arm chosen; where the
condition is not known, the choice is a fork on the condition, which a text names, and each
side goes into its arm. A case analysis on a variant and an attempt are still computed as one
instruction: the values inside them have no variables, and no check walks one.

`walk_step` on a computation that calls a function reads the function's body; on a loop it has
no step. An application waits for its first subject.

A walk enters by itself. The meaning of a role or of a function in a program (`roleMeaning`,
`fnMeaning`) is closed to Lean's own reduction, and the equation between it and the sealed
denotation of the body is stated once, where the program is, and checked by the kernel there.
Such an equation has the label `walk_entry`. On a goal that judges such a meaning, every tactic
of the walk first passes along the labelled equation that fits; a text names no equation.

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
between the type of a role's part and the type of the value, and so are the passages of a
value into an application and out of it (`coverRV`, `enter`, `leave`) for a role that holds it
on both sides. The kernel finds the two sides definitionally equal. -/
private def unwrapped (e : Expr) : MetaM Expr := do
  unless e.isAppOf ``Zkc.Core.hide || e.isAppOf ``Zkc.Core.reveal ||
      e.isAppOf ``Zkc.Core.coverRV || e.isAppOf ``Zkc.Core.enter || e.isAppOf ``Zkc.Core.leave do
    return e
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
the statement given. A reply and an input of a statement are read with it: a part of a tuple,
an item of a sequence and an alternative of a variant are then values of the field, the group
or the natural numbers, and not of a type that only computation makes one of those. -/
def computedTypes (e : Expr) : MetaM Expr :=
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

/-- What the judgment asks at the end, of `done` or of `halt` (argument 5 or 6). Where that is
the judgment of a process (the end of a region, after which the program goes on, sealed since
the walk went into the region), it is stated as it is; where it is a statement of the values,
it is in a form to read. -/
private def Judged.ask (j : Judged) (position : Nat) (value : Expr) : MetaM Expr := do
  let asked := (mkAppN (mkApp (j.fn.getAppArgs[position]!) value) j.extra).headBeta
  if asked.getAppFn.isConstOf ``Zkc.Core.Process.interpret && asked.getAppNumArgs ≥ 8 then
    return j.goal asked
  return j.goal (← applied asked)

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

/-- The name of the equations by which the walk says what the values of its steps are. A walk
gives such an equation, and the variable that it is about, a name that a text cannot write: a
text names what it gave a name (a reply, a fork, the arguments of an invariant), and nothing
that the program's instructions bind. -/
private def equationBase : Lean.Name := `walked

/-- Whether a hypothesis is an equation by which the walk says what a value of a step is. -/
private def isWalkEquation (decl : LocalDecl) : Bool :=
  decl.userName.hasMacroScopes && decl.userName.eraseMacroScopes == equationBase

/-- The goal after values. Each value is settled. A value that settles to a local variable, a
literal or a truth value is used as it is; any other gets a new local variable, at its computed
type, with the equation that says what it is, both under names that a text cannot write. The
variable stands for the value in the process that goes on, where the kernel computes on it only
what the program does; the equation is used where the walk stops (`readThrough`,
`useEquations`). The result is the list of the settled values, the proof of the judgment of the
rest on that list, sealed, which is the new goal at the values themselves, and the new goal. -/
private def bindValues (goal : MVarId) (j : Judged) (values : Expr) (rest : Expr) :
    MetaM (Expr × Expr × MVarId) := goal.withContext do
  let (cells, nil) ← spine values
  -- a value that is what was read, under what a role holds of it, is that variable
  let settled ← cells.mapM fun (_, value) => readValue value
  let named := (List.range cells.size).toArray.filter fun i => !isPlain settled[i]!
  let variables ← named.mapM fun _ => Lean.Core.mkFreshUserName `value
  let equations ← named.mapM fun _ => Lean.Core.mkFreshUserName equationBase
  let mut decls := #[]
  for k in [0:named.size] do
    decls := decls.push (variables[k]!, ← readType (← inferType settled[named[k]!]!))
  let newType ← withLocalDeclsDND decls fun xs => do
    let mut elems := settled
    for k in [0:named.size] do
      elems := elems.set! named[k]! xs[k]!
    let mut body := j.of (mkApp rest (rebuild cells nil elems)).headBeta
    for k in (List.range named.size).reverse do
      let i := named[k]!
      body := mkForall equations[k]! .default (← computedTypes (← mkEq xs[k]! settled[i]!)) body
    mkForallFVars xs body
  let next ← mkFreshExprSyntheticOpaqueMVar newType
  let mut proof := mkAppN next (named.map (settled[·]!))
  for i in named do
    proof := mkApp proof (← mkEqRefl settled[i]!)
  let (_, introduced) ← next.mvarId!.introN (2 * named.size) (variables.toList ++ equations.toList)
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
    -- a part of the pair that structural recursion builds, applied: what is left of a region
    -- that the kernel computes as one instruction (an arm of a case analysis, the body of an
    -- attempt) after an effect inside it; the step waits inside the pair. A choice and a
    -- block are not met here: the walk goes into them.
    if let .proj typeName idx struct := e.getAppFn then
      if (← whnf (← inferType struct)).isAppOf ``PProd then
        return ← inner struct fun x => mkAppN (.proj typeName idx x) args
    let .const name _ := e.getAppFn
      | throwError "walk: the step is stuck at a term that is not an application of a constant{indentExpr e}"
    let position ← do
      if let some (.recInfo info) := (← getEnv).find? name then pure (some info.getMajorIdx)
      else if let some info ← getMatcherInfo? name then pure (some info.getFirstDiscrPos)
      else pure none
    match position with
    | some at_ =>
      unless at_ < args.size do throwError "walk: a stuck recursor without its major premise{indentExpr e}"
      -- an argument after the major premise whose type is stated of it (the equation that a
      -- match on an indexed family carries) is not an argument at another value: the term at
      -- a variable in place of the major premise is then no term, and no step is built
      let major := args[at_]!
      if at_ + 1 < args.size then
        let fits ← withLocalDeclD `waited (← inferType major) fun x => withNewMCtxDepth do
          let mut type ← inferType (mkAppN e.getAppFn ((args.extract 0 at_).push x))
          for later in args.extract (at_ + 1) args.size do
            let .forallE _ domain body _ ← whnf type | return false
            unless ← isDefEq domain (← inferType later) do return false
            type := body.instantiate1 later
          return true
        unless fits do
          throwError "walk: the step waits on a case analysis whose later arguments are stated \
            of what it analyses (a match on a variant), which has no step yet{indentExpr major}"
      inner major fun x => mkAppN e.getAppFn (args.set! at_ x)
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

/-- A premise of a law of a read, proved: by a hypothesis that states it, or by arithmetic on
the hypotheses (the position below a bound, the length of the sequence). -/
private def readPremise : Simp.Discharge := fun premise => do
  if let some hypothesis ← findLocalDeclWithType? premise then return some (mkFVar hypothesis)
  let goal ← mkFreshExprSyntheticOpaqueMVar premise
  try
    let (left, _) ← Lean.Elab.runTactic goal.mvarId! (← `(tactic| omega))
    if left.isEmpty then return some (← instantiateMVars goal) else return none
  catch _ => return none

/-- A read of a sequence that the context decides: the value that the read is (`some value`, or
`none`), with the proof that the read is it. The read is rewritten by the hypotheses that say
what a variable is or what a read finds and by the laws of reads (`walk_read`), then, where
those do not decide it, by the entry of a list at a position below its length. A term that is
no read, and a read that is not decided, give nothing. -/
private def knownRead (waited : Expr) : MetaM (Option (Expr × Expr)) := do
  let read ← computedTypes waited
  unless read.isAppOf ``GetElem?.getElem? do return none
  let mut laws : SimpTheorems := {}
  for name in ← Lean.labelled `walk_read do
    laws ← laws.addConst name
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let some (_, lhs, _) := (← instantiateMVars decl.type).eq? | continue
    if lhs.isFVar || lhs.isAppOf ``GetElem?.getElem? then
      laws ← laws.add (.fvar decl.fvarId) #[] decl.toExpr
  let attempt (laws : SimpTheorems) : MetaM (Option (Expr × Expr)) := do
    -- a search that does not end within its bound, or that fails in any way, decides nothing:
    -- the read is then a fork, as before
    let found ← tryCatchRuntimeEx
      (do
        let context ← Simp.mkContext (config := { maxSteps := 2000 }) (simpTheorems := #[laws])
          (congrTheorems := ← getSimpCongrTheorems)
        let (result, _) ← Meta.simp read context (discharge? := some readPremise)
        pure (some result))
      (fun _ => pure none)
    let some result := found | return none
    let some proof := result.proof? | return none
    unless result.expr.isAppOf ``Option.some || result.expr.isAppOf ``Option.none do return none
    return some (result.expr, ← mkExpectedTypeHint proof (← mkEq waited result.expr))
  if let some known ← attempt laws then return some known
  attempt (← laws.addConst ``List.getElem?_eq_getElem)

/-- A step that waits on a value: a goal for every form of the value. Each has the equation
between what the step waits on, in a form to read, and the form, under the name `fork` that the
text gave or under one that a text cannot write; a part of the form is a variable at its
computed type, under the name that the text gave it (`named`) or one that it cannot write.
`bound` is what is left of the instruction and then the rest, `why` the equation between the
process of the goal and it, and `stuck` the head normal form of what is left. -/
private def splitStuck (goal : MVarId) (j : Judged) (bound why stuck : Expr)
    (fork : Option Lean.Name := none) (named : Array Lean.Name := #[]) :
    MetaM (List MVarId × Bool) := goal.withContext do
  let b := bound.getAppArgs
  let (waited, put) ← waitsOn stuck
  let waited ← settle waited
  let waitedType ← kernelWhnf (← inferType waited)
  -- a read that the context decides is no fork: the step goes on with what it finds
  if let some (found, isFound) ← knownRead waited then
    let motive ← withLocalDeclD `waited waitedType fun form =>
      mkLambdaFVars #[form] (j.of (mkAppN bound.getAppFn (b.set! 4 (put form))))
    let next ← mkFreshExprSyntheticOpaqueMVar (mkApp motive found).headBeta
    let (waiting, toWaiting) ← withLeft bound (put waited)
    j.passSealed goal waiting (← mkEqTrans why toWaiting)
      (← mkEqMPR (← mkCongrArg motive isFound) next)
    return ([next.mvarId!], false)
  let equation ← match fork with
    | some name => pure name
    | none => Lean.Core.mkFreshUserName `fork
  let newType ← withLocalDeclD `waited waitedType fun form => do
    let body := j.of (mkAppN bound.getAppFn (b.set! 4 (put form)))
    mkForallFVars #[form] (mkForall equation .default (← computedTypes (← mkEq waited form)) body)
  let next ← mkFreshExprSyntheticOpaqueMVar newType
  let (waiting, toWaiting) ← withLeft bound (put waited)
  j.passSealed goal waiting (← mkEqTrans why toWaiting) (mkApp2 next waited (← mkEqRefl waited))
  let (form, afterForm) ← next.mvarId!.intro `waited
  let (_, afterEquation) ← afterForm.intro equation
  let cases ← afterEquation.cases form
  let sides ← cases.toList.mapM fun case => case.mvarId.withContext do
    let mut current := case.mvarId
    let parts := case.fields.filterMap fun field => if field.isFVar then some field.fvarId! else none
    for part in parts, i in [0:parts.size] do
      let type ← current.withContext do readType (← inferType (.fvar part))
      current ← current.replaceLocalDeclDefEq part type
      current ← current.rename part (← match named[i]? with
        | some name => pure name
        | none => Lean.Core.mkFreshUserName `part)
    return current
  return (sides, true)

/-- **A region is walked as a program is.** `bound` is a region and then the rest: the term of
an arm of a choice or of a block in its environment, bound to what follows it. The judgment of
such a process is the judgment of the region whose condition at the end is the judgment of the
rest on what the region returns (`Process.interpret_bind`). The goal passes to that judgment,
so every rule of the walk is the same inside a region as outside: its values have variables,
its effects, loops and calls are met as any other, and at its end the goal is the judgment of
what follows. `why` is the equation between the process of the goal and `bound`, and `isRegion`
the equation between what is left in `bound` and the region. -/
private def enterRegion (goal : MVarId) (j : Judged) (bound why region isRegion : Expr) :
    MetaM MVarId := goal.withContext do
  let b := bound.getAppArgs
  let rest := b[5]!
  let a := j.fn.getAppArgs
  let (judgment, done, halt) := (a[4]!, a[5]!, a[6]!)
  -- the process of the goal is the region, then the rest
  let motive ← withLocalDeclD `left (← inferType b[4]!) fun left =>
    mkLambdaFVars #[left] (mkAppN bound.getAppFn (b.set! 4 left))
  let regionThenRest := mkAppN bound.getAppFn (b.set! 4 region)
  let toRegion ← mkEqTrans why (← mkCongrArg motive isRegion)
  -- the judgment of the region: at its end, the judgment of the rest, which stays sealed, as
  -- every process that a goal of the walk judges: a tactic of the text that reduces its goal
  -- does not run what follows the region
  let valuesType := (← whnf (← inferType rest)).bindingDomain!
  let after ← withLocalDeclD `values valuesType fun values =>
    mkLambdaFVars #[values] (mkApp j.fn (j.seal (mkApp rest values).headBeta))
  let inside := { j with fn := ← mkAppM ``Zkc.Core.Process.interpret #[judgment, after, halt] }
  let next ← mkFreshExprSyntheticOpaqueMVar (inside.of region)
  -- `interpret (region.bind rest) = interpret region` with that condition, at what follows
  let bind ← mkAppM ``Zkc.Core.Process.interpret_bind #[judgment, done, halt, rest, region]
  let mut judged ← mkExpectedTypeHint bind
    (← mkEq (mkApp j.fn regionThenRest) (mkApp inside.fn region))
  for extra in j.extra do
    judged ← mkCongrFun judged extra
  let ia := inside.fn.getAppArgs
  let sealing ← mkEqSymm (mkApp4 (mkConst ``Zkc.Core.Process.sealed_eq) ia[0]! ia[1]! ia[2]! region)
  let sealedMotive ← withLocalDeclD `p (← inferType region) fun p =>
    mkLambdaFVars #[p] (mkAppN (mkApp inside.fn p) j.extra)
  let toInside ← mkEqTrans judged (← mkCongrArg sealedMotive sealing)
  -- the goal, or the hypothesis that it concludes from, passes along the equation
  let stated ← withLocalDeclD `judged (mkSort Level.zero) fun x => mkLambdaFVars #[x] (j.goal x)
  j.pass goal regionThenRest toRegion (← mkEqMPR (← mkCongrArg stated toInside) next)
  return next.mvarId!

/-- What an instruction denotes, where it runs a region: a block is its body under its frame,
and a choice is the region that its condition chooses. The result is the process in that form
and the equation between what the instruction denotes (`left`) and it. For a choice whose
condition the kernel computes, the form is the region chosen; for one whose condition is not
known, it is the choice written on its condition, on which the step then waits. -/
private def regionOf (left instr sem key path env : Expr) : MetaM (Option (Expr × Expr)) := do
  let ia := instr.getAppArgs
  let n := ia.size
  if instr.isAppOf ``Zkc.Core.Instr.block && n ≥ 2 then
    let rule ← mkAppM ``Zkc.Core.Instr.denote_block #[sem, key, ia[n - 2]!, ia[n - 1]!, path, env]
    let region := (← inferType rule).appArg!
    return some (region, ← mkExpectedTypeHint rule (← mkEq left region))
  if instr.isAppOf ``Zkc.Core.Instr.choose && n ≥ 6 then
    let rule ← mkAppM ``Zkc.Core.Instr.denote_choose
      #[sem, key, ia[n - 6]!, ia[n - 5]!, ia[n - 4]!, ia[n - 3]!, ia[n - 2]!, ia[n - 1]!, path, env]
    let chosen := (← inferType rule).appArg!
    let toChosen ← mkExpectedTypeHint rule (← mkEq left chosen)
    unless chosen.isAppOfArity ``cond 4 do return some (chosen, toChosen)
    let c := chosen.getAppArgs
    let value ← kernelWhnf c[1]!
    let decided (literal : Bool) : MetaM (Option (Expr × Expr)) := do
      let (lemma, region) :=
        if literal then (``Bool.cond_true, c[2]!) else (``Bool.cond_false, c[3]!)
      let motive ← withLocalDeclD `condition (mkConst ``Bool) fun condition =>
        mkLambdaFVars #[condition] (mkAppN chosen.getAppFn (c.set! 1 condition))
      let toLiteral ← mkCongrArg motive (← byComputation c[1]! value)
      let toRegion ← mkAppOptM lemma #[c[0]!, c[2]!, c[3]!]
      return some (region, ← mkEqTrans toChosen (← mkEqTrans toLiteral toRegion))
    if value.isConstOf ``Bool.true then return ← decided true
    if value.isConstOf ``Bool.false then return ← decided false
    return some (chosen, toChosen)
  return none

/-- One step on what is left of an instruction and then the rest: `bound` is that process,
`left.bind rest`, and `why` is the equation between the process of the goal and it. -/
private def advance (goal : MVarId) (j : Judged) (bound why : Expr)
    (fork : Option Lean.Name := none) (named : Array Lean.Name := #[]) :
    MetaM (List MVarId × Bool) := goal.withContext do
  let b := bound.getAppArgs
  let rest := b[5]!
  let w ← kernelWhnf b[4]!
  if w.isAppOfArity ``Zkc.Core.Process.done 4 then
    let (list, proof, introduced) ← bindValues goal j (w.getArg! 3) rest
    let (returned, toReturned) ← withLeft bound
      (mkApp4 (mkConst ``Zkc.Core.Process.done) b[0]! b[1]! b[2]! list)
    let after := (mkApp rest list).headBeta
    let toAfter ← mkExpectedTypeHint
      (mkAppN (mkConst ``Zkc.Core.Process.done_bind) #[b[0]!, b[1]!, b[2]!, b[3]!, list, rest])
      (← mkEq returned after)
    j.passSealed goal after (← mkEqTrans why (← mkEqTrans toReturned toAfter)) proof
    return ([introduced], false)
  else if w.isAppOfArity ``Zkc.Core.Process.halt 4 then
    let payload := w.getArg! 3
    let (_, toHalted) ← withLeft bound
      (mkApp4 (mkConst ``Zkc.Core.Process.halt) b[0]! b[1]! b[2]! payload)
    let rule := mkAppN (mkConst ``Zkc.Core.Process.halt_bind)
      #[b[0]!, b[1]!, b[2]!, b[3]!, payload, rest]
    let stopped := (← inferType rule).appArg!
    return ([← j.ending goal stopped (← mkEqTrans why (← mkEqTrans toHalted rule)) false payload],
      false)
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
    return ([next.mvarId!], false)
  else splitStuck goal j bound why w fork named

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
      -- an equation with a binder that its left side does not fix is not one to pass along
      let equation ← instantiateMVars (mkAppN entry args)
      if equation.hasExprMVar then return none
      return some (← instantiateMVars rhs, equation)
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

/-- The proof that a judgment reads no peer of an effect under a renaming of roles
(`Zkc.Core.Blind`): from a hypothesis of the goal that says so (a theorem about every judgment
of a kind states it as a hypothesis), or from a theorem with the label `walk_blind` that says
so of the judgment as the goal states it. -/
private def blindUnder (roleMap judgment : Expr) : MetaM (Option Expr) := do
  let wanted ← mkAppM ``Zkc.Core.Blind #[roleMap, judgment]
  let from_ (source : Expr) : MetaM (Option Expr) := withNewMCtxDepth do
    let (args, _, stated) ← forallMetaTelescope (← instantiateMVars (← inferType source))
    unless stated.isAppOf ``Zkc.Core.Blind do return none
    unless ← isDefEq stated wanted do return none
    let proof ← instantiateMVars (mkAppN source args)
    if proof.hasExprMVar then return none
    return some proof
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if let some proof ← from_ decl.toExpr then return some proof
  for name in ← Lean.labelled `walk_blind do
    if let some proof ← from_ (← mkConstWithFreshMVarLevels name) then return some proof
  return none

/-- Whether the kernel finds two terms definitionally equal. -/
private def kernelSame (a b : Expr) : MetaM Bool := do
  ofExceptKernelException (Lean.Kernel.isDefEq (← getEnv) (← getLCtx)
    (← instantiateMVars a) (← instantiateMVars b))

/-- The process of a role in a table of role programs (`table header member role path inputs`,
with `table` the role programs of a program), stated as the meaning of that role in the
program, in the words of the labelled entry equation that is about it: the left side of the
equation at this path and these inputs. The program is compared as it is written, under
reducible names; the header, the member and the role are small closed terms, which the kernel
compares. No equation is passed along here: the next step of the walk enters the meaning by it.
Nothing is returned where no labelled equation is about this role of this protocol in this
program. -/
private def statedByEntry (program model header member role path inputs : Expr) :
    MetaM (Option Expr) := do
  for name in ← Lean.labelled `walk_entry do
    let found ← withNewMCtxDepth do
      let entry ← mkConstWithFreshMVarLevels name
      let (_, _, statement) ← forallMetaTelescope (← inferType entry)
      let some (_, lhs, _) := statement.eq? | return none
      let stated := lhs.getAppArgs
      -- `roleMeaning M p member role path inputs`, after the vocabulary and the header
      unless lhs.getAppFn.isConstOf ``Zkc.Core.roleMeaning && stated.size == 8 do return none
      let (statedModel, statedProgram, statedHeader, statedMember, statedRole, statedPath,
        statedInputs) := (stated[1]!, stated[2]!, stated[3]!, stated[4]!, stated[5]!, stated[6]!,
          stated[7]!)
      -- the equation is for every model, path and inputs, and for one program, member and role
      unless statedModel.isMVar && statedPath.isMVar && statedInputs.isMVar do return none
      if statedProgram.hasExprMVar || statedMember.hasExprMVar || statedRole.hasExprMVar then
        return none
      unless ← withReducible (isDefEq statedProgram program) do return none
      statedModel.mvarId!.assign model
      unless ← kernelSame statedHeader header do return none
      unless ← kernelSame statedMember member do return none
      unless ← kernelSame statedRole role do return none
      statedPath.mvarId!.assign path
      statedInputs.mvarId!.assign inputs
      let lhs ← instantiateMVars lhs
      if lhs.hasExprMVar then return none
      return some lhs
    if found.isSome then return found
  return none

/-- **An application is entered as a region is.** `bound` is an instruction that applies a
protocol and then the rest, under the semantics of a role. What the instruction denotes for the
role is the callee's program of the role that it plays there, at the path of the application,
with the peers of its effects renamed to the caller's roles and its results carried back
(`Instr.denote_apply_role`). Under a judgment that reads no peer (`blindUnder`), that process
and then the rest is judged as the callee's program, as it stands, whose condition at the end
is the judgment of the rest on the results carried (`Process.interpret_applied`). The goal
passes to that judgment, with the callee's program stated as the meaning of its role in the
program whose table the application reads, sealed, the role computed and each input in a form
to read; the next step enters it by the labelled equation of that meaning, and from there every
rule of the walk is the same in the callee as in the root.

Nothing is returned, and the instruction is then computed as any other, where the instruction
applies no protocol, where the semantics is not that of a role over the tables of a program,
where the role plays no role of the callee (its program there has no effect), or where no
theorem or hypothesis says that the judgment reads no peer. Under a judgment that reads no
peer, an application in which the role takes part and whose callee has no labelled entry
equation is an error: the module of statements is then not the module of this program. -/
private def enterApplication (goal : MVarId) (j : Judged) (bound why instr sem key path env : Expr) :
    MetaM (Option MVarId) := goal.withContext do
  -- the instruction: an operation that applies a protocol to operands
  let ia := instr.getAppArgs
  unless instr.isAppOf ``Zkc.Core.Instr.op && ia.size ≥ 2 do return none
  let operation ← kernelWhnf ia[ia.size - 2]!
  let oa := operation.getAppArgs
  unless operation.isAppOf ``Zkc.Core.RoleOp.apply && oa.size ≥ 6 do return none
  let n := oa.size
  let (callee, roles, distinct, covers, operands, fits) :=
    (oa[n - 6]!, oa[n - 5]!, oa[n - 4]!, oa[n - 3]!, oa[n - 2]!, oa[n - 1]!)
  -- the semantics: of a role, over the tables of a program
  let sa := sem.getAppArgs
  unless sem.isAppOf ``Zkc.Core.roleSem && sa.size ≥ 3 do return none
  let (role, fnTable, rTable) := (sa[sa.size - 3]!, sa[sa.size - 2]!, sa[sa.size - 1]!)
  unless rTable.isAppOf ``Zkc.Core.Defs.rTable && rTable.getAppNumArgs ≥ 2 do return none
  let definitions := rTable.appArg!
  let some program := (match definitions with
      | .proj ``Zkc.Core.Typed 1 p => some p
      | _ => if definitions.isAppOf ``Zkc.Core.Typed.defs then some definitions.appArg! else none)
    | return none
  -- what the instruction denotes: `(mapR M ρ (rTable _ callee r' path' inputs')).map leave`
  let rule ← mkAppM ``Zkc.Core.Instr.denote_apply_role
    #[role, fnTable, rTable, key, callee, roles, distinct, covers, operands, fits,
      ia[ia.size - 1]!, path, env]
  -- the rule is `@Instr.denote_apply_role V M …`
  let model := rule.getAppArgs[1]!
  let some (_, _, applied) := (← inferType rule).eq? | return none
  unless applied.isAppOf ``Zkc.Core.Process.map && applied.getAppNumArgs ≥ 2 do return none
  let leave := applied.appFn!.appArg!
  let renamed := applied.appArg!
  -- `mapR M ρ (B := _) p`
  unless renamed.isAppOf ``Zkc.Core.mapR && renamed.getAppNumArgs ≥ 3 do return none
  let roleMap := renamed.appFn!.appFn!.appArg!
  let calleeProcess := renamed.appArg!
  let ca := calleeProcess.getAppArgs
  unless ca.size ≥ 5 do return none
  let m := ca.size
  let (header, member, played, calleePath, given) :=
    (ca[m - 5]!, ca[m - 4]!, ca[m - 3]!, ca[m - 2]!, ca[m - 1]!)
  -- a role that plays no role of the callee takes no part in the application: its program
  -- there has no effect, and the instruction is computed as any other
  let plays ← kernelWhnf (← mkAppM ``List.elem #[role, roles])
  unless plays.isConstOf ``Bool.true do return none
  -- the judgment reads no peer
  let a := j.fn.getAppArgs
  let (judgment, done, halt) := (a[4]!, a[5]!, a[6]!)
  let some blind ← blindUnder roleMap judgment | return none
  -- the callee's program as the meaning of its role, on inputs in a form to read
  let (cells, nil) ← spine given
  let inputs := rebuild cells nil (← cells.mapM fun (_, value) => readValue value)
  let some stated ← statedByEntry program model header member (← kernelWhnf played) calleePath inputs
    | throwError "walk: the judgment reads no peer, and no equation with the label `walk_entry` \
        is about the role of the protocol that is applied here: a module of statements states \
        one for each role that its deciding role plays through applications{indentExpr calleeProcess}"
  -- the process of the goal is the application, then the rest
  let b := bound.getAppArgs
  let rest := b[5]!
  let motive ← withLocalDeclD `left (← inferType b[4]!) fun left =>
    mkLambdaFVars #[left] (mkAppN bound.getAppFn (b.set! 4 left))
  let appliedThenRest := mkAppN bound.getAppFn (b.set! 4 applied)
  let toApplied ← mkEqTrans why
    (← mkCongrArg motive (← mkExpectedTypeHint rule (← mkEq b[4]! applied)))
  -- the judgment of the callee: at its end, the judgment of the rest on the results carried,
  -- which stays sealed
  let resultsType := (← whnf (← inferType leave)).bindingDomain!
  let after ← withLocalDeclD `results resultsType fun results =>
    mkLambdaFVars #[results]
      (mkApp j.fn (j.seal (mkApp rest (mkApp leave results).headBeta).headBeta))
  let inside := { j with fn := ← mkAppM ``Zkc.Core.Process.interpret #[judgment, after, halt] }
  let next ← mkFreshExprSyntheticOpaqueMVar (inside.of stated)
  let passage ← mkAppM ``Zkc.Core.Process.interpret_applied
    #[roleMap, judgment, blind, done, halt, leave, rest, calleeProcess]
  let mut judged ← mkExpectedTypeHint passage
    (← mkEq (mkApp j.fn appliedThenRest) (mkApp inside.fn calleeProcess))
  for extra in j.extra do
    judged ← mkCongrFun judged extra
  -- the callee's program is the meaning as stated, which is sealed
  let ia' := inside.fn.getAppArgs
  let sealing ← mkEqSymm (mkApp4 (mkConst ``Zkc.Core.Process.sealed_eq) ia'[0]! ia'[1]! ia'[2]! stated)
  let toStated ← mkEqTrans (← byComputation calleeProcess stated) sealing
  let sealedMotive ← withLocalDeclD `p (← inferType calleeProcess) fun p =>
    mkLambdaFVars #[p] (mkAppN (mkApp inside.fn p) j.extra)
  let toInside ← mkEqTrans judged (← mkCongrArg sealedMotive toStated)
  let statedGoal ← withLocalDeclD `judged (mkSort Level.zero) fun x => mkLambdaFVars #[x] (j.goal x)
  j.pass goal appliedThenRest toApplied (← mkEqMPR (← mkCongrArg statedGoal toInside) next)
  return some next.mvarId!

/-- What an instruction is, in the words of an error: its constructor and, for an operation,
the constructor of the operation. -/
private def instructionKind (i : Expr) : String :=
  let last (e : Expr) : String := match e.getAppFn with
    | .const name _ => name.components.getLast?.map toString |>.getD "?"
    | _ => "?"
  let args := i.getAppArgs
  if i.isAppOf ``Zkc.Core.Instr.op && args.size ≥ 2 then
    let op := args[args.size - 2]!
    let inner := op.getAppArgs.find? fun a => a.getAppFn.isConst &&
      (a.isAppOf ``Zkc.Core.LocalOp.call || a.isAppOf ``Zkc.Core.LocalOp.row ||
        a.isAppOf ``Zkc.Core.LocalOp.owned)
    match inner with
    | some local_ => s!"{last op} of {last local_}"
    | none => last op
  else last i

/-- A step that begins an instruction and fails says which instruction it was at: the number
of its key in the stored program and what it is. A failure of Lean itself (an interruption, a
limit of time or of depth) is passed on as it is. -/
private def atInstruction {α : Type} (key i : Expr) (step : MetaM α) : MetaM α := do
  try step
  catch failure =>
    if failure.isRuntime || failure matches .internal .. then throw failure
    let number : MessageData := match key.getAppArgs with
      | #[n] => match n.nat? <|> n.rawNatLit? with
        | some n => m!"{n}"
        | none => m!"{key}"
      | _ => m!"{key}"
    throwError "walk: at instruction {number} ({instructionKind i}):{indentD failure.toMessageData}"

/-- One step of the walk on a goal: on the judgment that the goal is, or, with `hypothesis`, on
the judgment from which the goal concludes. -/
private def stepOrFork (goal : MVarId) (hypothesis := false) (fork : Option Lean.Name := none)
    (named : Array Lean.Name := #[]) : MetaM (List MVarId × Bool) := goal.withContext do
  let j ← readGoal goal hypothesis
  let p := j.process
  if p.isAppOfArity ``Zkc.Core.Process.bind 6 then
    -- what is left is a region (the side of a choice whose condition is now known): the walk
    -- goes into it. Lean's core reduction finds it: the choice on a known condition is one of
    -- its arms, and the arm is not unfolded. The kernel checks the equation, which costs it at
    -- most the first instruction of the arm.
    let left := p.getAppArgs[4]!
    let reduced ← whnfCore left
    if reduced.isAppOfArity ``Zkc.Core.Term.denote 7 then
      return ([← enterRegion goal j p (← mkEqRefl p) reduced (← byComputation left reduced)], false)
    -- what is left of an instruction after an effect or a split
    advance goal j p (← mkEqRefl p) fork named
  else if p.isAppOfArity ``Zkc.Core.Term.denote 7 then
    let a := p.getAppArgs
    let (D, sem, Γ, outs, path, env) := (a[0]!, a[1]!, a[2]!, a[3]!, a[5]!, a[6]!)
    let term ← kernelWhnf a[4]!
    if term.isAppOfArity ``Zkc.Core.Term.step 8 then
      let t := term.getAppArgs
      let (mid, key, i, names, rest) := (t[3]!, t[4]!, t[5]!, t[6]!, t[7]!)
      let instruction ← kernelWhnf i
      atInstruction key instruction do
        -- the term is its first instruction, then the rest on the values
        let rule := mkAppN (mkConst ``Zkc.Core.Term.denote_step)
          #[D, sem, Γ, outs, mid, key, i, names, rest, path, env]
        let stated := (← inferType rule).appArg!
        let bound := mkAppN stated.getAppFn (stated.getAppArgs.set! 5 (← restAfter a names rest))
        let why ← mkExpectedTypeHint rule (← mkEq p bound)
        -- an instruction that applies a protocol: the walk goes into the callee
        if let some inside ← enterApplication goal j bound why instruction sem key path env then
          return ([inside], false)
        -- an instruction that runs a region: the walk goes into the region
        let left := bound.getAppArgs[4]!
        if let some (form, isForm) ← regionOf left instruction sem key path env then
          if form.isAppOfArity ``Zkc.Core.Term.denote 7 then
            return ([← enterRegion goal j bound why form isForm], false)
          -- a choice on a condition that is not known: the step waits on the condition
          let motive ← withLocalDeclD `left (← inferType left) fun x =>
            mkLambdaFVars #[x] (mkAppN bound.getAppFn (bound.getAppArgs.set! 4 x))
          return ← splitStuck goal j (mkAppN bound.getAppFn (bound.getAppArgs.set! 4 form))
            (← mkEqTrans why (← mkCongrArg motive isForm)) form fork named
        advance goal j bound why fork named
    else if term.isAppOfArity ``Zkc.Core.Term.ret 4 then
      -- the term returns the values of its names
      let exit := term.getArg! 3
      let rule := mkAppN (mkConst ``Zkc.Core.Term.denote_ret) #[D, sem, Γ, outs, exit, path, env]
      let returned := (← inferType rule).appArg!
      let (cells, nil) ← spine returned.appArg!
      let elems ← cells.mapM fun (_, e) => kernelWhnf e
      let list := rebuild cells nil elems
      let ended := mkApp returned.appFn! list
      return ([← j.ending goal ended (← mkExpectedTypeHint rule (← mkEq p ended)) true list], false)
    else throwError "walk: the term is neither a step nor a return{indentExpr term}"
  else throwError "walk: the process is not a term in an environment{indentExpr p}"

/-- One step of the walk on a goal: the goals that follow. -/
private def step (goal : MVarId) (hypothesis := false) : MetaM (List MVarId) :=
  return (← stepOrFork goal hypothesis).1

/-- What stands next at a goal of the walk. -/
private inductive Ahead where
  /-- The goal judges no process: the program has ended, and the goal is what the judgment asks
  of the end. -/
  | ended
  /-- The goal is the judgment at an effect, stated open. -/
  | effect
  /-- The next instruction is a loop, which is taken by an invariant. -/
  | loop
  /-- The next instruction is a computation of a role that calls a function, which a text may
  take by the function's law. -/
  | call
  /-- Anything else: a step that the kernel computes. -/
  | step

/-- Whether an operation is a computation of a role that calls a function of the program: the
call that a text can take by the function's law. A call inside the body of a function is no
such computation; the rule of a law has no form for it yet, and a walk reads the body of the
function that it calls. -/
private def callsFunction (op : Expr) : MetaM Bool := do
  let op ← kernelWhnf op
  if op.isAppOfArity ``Zkc.Core.RoleOp.compute 11 then
    return (← kernelWhnf (op.getArg! 6)).isAppOfArity ``Zkc.Core.LocalOp.call 4
  return false

/-- What stands next at a goal. -/
private def ahead (goal : MVarId) (hypothesis : Bool) : MetaM Ahead := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let judgment ← do
    if hypothesis then
      let .forallE _ judgment _ _ := target | return .ended
      pure judgment.consumeMData.headBeta
    else pure target
  unless judgment.getAppFn.isConstOf ``Zkc.Core.Process.interpret && judgment.getAppNumArgs ≥ 8 do
    return .ended
  let j ← readGoal goal hypothesis
  let p := j.process
  if p.isAppOfArity ``Zkc.Core.Process.call 5 then return .effect
  unless p.isAppOfArity ``Zkc.Core.Term.denote 7 do return .step
  let term ← kernelWhnf p.getAppArgs[4]!
  unless term.isAppOfArity ``Zkc.Core.Term.step 8 do return .step
  let instr ← kernelWhnf (term.getArg! 5)
  if instr.isAppOfArity ``Zkc.Core.Instr.loop 10 then return .loop
  if instr.isAppOfArity ``Zkc.Core.Instr.op 6 then
    if ← callsFunction (instr.getArg! 4) then return .call
  return .step

/-- The equations of the walk, used where no process goes on: every variable that stands for a
value of a step is replaced by the value, so that what is left is stated in the replies, the
inputs and the names of the text, and nothing in it is the walk's. This is for a goal that
judges no process: the end of a program, and a goal that a rule leaves beside the walk (the
weight of an excluded set, the law of a computation, the invariant before a loop). In a process
that goes on the variables stay, since the kernel would compute on a value put in their place
what the program does not ask. -/
partial def useEquations (goal : MVarId) : MetaM MVarId := goal.withContext do
  for decl in ← getLCtx do
    unless isWalkEquation decl do continue
    if let some next ← observing? (subst goal decl.fvarId) then
      return ← useEquations next
  return goal

/-- The values of a goal that judges no process, in the terms of the mathematics: the goal and
its hypotheses are rewritten by the equations that say what the operations of a model are
(`walk_value`). A goal that this makes true as it stands is closed. -/
def readValues (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let names ← Lean.labelled `walk_value
  if names.isEmpty then return some goal
  let mut laws : SimpTheorems := {}
  for name in names do
    laws ← laws.addConst name
  let context ← Simp.mkContext (config := { failIfUnchanged := false, instances := true })
    (simpTheorems := #[laws]) (congrTheorems := ← getSimpCongrTheorems)
  let hypotheses ← (← getLCtx).foldlM (init := #[]) fun found decl => do
    if decl.isImplementationDetail then return found
    if ← isProp (← instantiateMVars decl.type) then return found.push decl.fvarId
    return found
  -- the equations that hold by definition are read everywhere, also in an instance that a
  -- statement carries: a decision about `x + y` is then one that a lemma about the field finds
  let (result, _) ← dsimpGoal goal context (fvarIdsToSimp := hypotheses)
  let some goal := result | return none
  -- the others (what a literal is) are read as rewriting reads them
  goal.withContext do
    let hypotheses ← (← getLCtx).foldlM (init := #[]) fun found decl => do
      if decl.isImplementationDetail then return found
      if ← isProp (← instantiateMVars decl.type) then return found.push decl.fvarId
      return found
    let (result, _) ← simpGoal goal context (fvarIdsToSimp := hypotheses)
    return result.map (·.2)

/-- What a walk leaves where no process goes on, stated for the text: the equations of the walk
are used, an equation between two lists of one returned value is the equation between the two
values at the type of the mathematics, and the operations of a model are read
(`readValues`). -/
def stateForText (goal : MVarId) : MetaM (Option MVarId) := do
  let goal ← useEquations goal
  let goal ← goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    let some (_, lhs, rhs) := target.eq? | return goal
    unless lhs.isAppOfArity ``Zkc.Core.HList.cons 6 && rhs.isAppOfArity ``Zkc.Core.HList.cons 6 do
      return goal
    let (l, r) := (lhs.getAppArgs, rhs.getAppArgs)
    unless l[5]!.isAppOf ``Zkc.Core.HList.nil && r[5]!.isAppOf ``Zkc.Core.HList.nil do return goal
    unless ← isDefEq l[5]! r[5]! do return goal
    let elementType ← readType (← inferType l[4]!)
    let level ← getLevel elementType
    let values ← mkFreshExprSyntheticOpaqueMVar
      (← computedTypes (mkApp3 (mkConst ``Eq [level]) elementType l[4]! r[4]!)) (← goal.getTag)
    let motive ← withLocalDeclD `value (← inferType l[4]!) fun value =>
      mkLambdaFVars #[value] (mkAppN lhs.getAppFn (l.set! 4 value))
    goal.assign (← mkCongrArg motive values)
    return values.mvarId!
  readValues goal

/-- The equations of the walk, read into the hypotheses of a goal whose process goes on: a
hypothesis that speaks of a variable of the walk (a guard that passed, what a read found) is
restated of the value. Left as they are: the equations; a hypothesis that judges a process
(the one that a walk of a hypothesis goes on with), since the variables stay in a process; a
hypothesis that something else depends on (another hypothesis or the goal names its proof),
which cannot be replaced; and one whose statement is not a statement any more with the value
in the variable's place. One hypothesis is restated at a time, and the context is read again
after each, since restating a hypothesis gives those after it other identities; a hypothesis
that is still there after it was restated is not restated again. -/
private partial def readThrough (goal : MVarId) (kept : Array FVarId := #[]) : MetaM MVarId :=
  goal.withContext do
    let context ← getLCtx
    let target ← instantiateMVars (← goal.getType)
    for equation in context do
      unless isWalkEquation equation do continue
      let some (_, .fvar standing, value) := (← instantiateMVars equation.type).eq? | continue
      for decl in context do
        if decl.isImplementationDetail || isWalkEquation decl || decl.fvarId == standing then continue
        if kept.contains decl.fvarId then continue
        let type ← instantiateMVars decl.type
        if type.consumeMData.getAppFn.isConstOf ``Zkc.Core.Process.interpret then continue
        unless type.containsFVar standing && (← isProp type) do continue
        -- its proof is named elsewhere: it stays
        let named ← context.anyM fun other => do
          if other.fvarId == decl.fvarId then return false
          return (← instantiateMVars other.type).containsFVar decl.fvarId
        if named || target.containsFVar decl.fvarId then continue
        let motive ← mkLambdaFVars #[.fvar standing] type
        unless ← Meta.isTypeCorrect motive do continue
        let result ← goal.replaceLocalDecl decl.fvarId (type.replaceFVar (.fvar standing) value)
          (← mkCongrArg motive equation.toExpr)
        let stays ← result.mvarId.withContext do return (← getLCtx).contains decl.fvarId
        return ← readThrough result.mvarId (if stays then kept.push decl.fvarId else kept)
    return goal

/-- A goal that holds as it stands: it is `True`, a hypothesis, an equation of a term with
itself, or its hypotheses contradict one another (`contradiction`, which also decides a
hypothesis that has no variable). The goal itself is not decided or computed.
With `hypothesis`, the goal concludes from a judgment, which is introduced under that name
first. -/
private def closes (goal : MVarId) (hypothesis : Option Lean.Name := none) : TacticM Bool := do
  let saved ← saveState
  let goals ← getGoals
  try
    let goal ← match hypothesis with
      | some name => pure (← goal.intro name).2
      | none => pure goal
    setGoals [goal]
    evalTactic (← `(tactic| first | exact True.intro | assumption | contradiction | with_reducible rfl))
    if (← getGoals).isEmpty then
      setGoals goals
      return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

/-- The walk from a goal to the next places where a text has something to say: an effect, a
loop, a call of a function (unless `calls`, which reads the function's body as a step does), or
the end. At a fork each side takes the step that its form makes possible; a side that is closed
as it stands is closed, and the walk goes on in every other, so that a fork of which several
sides are open leaves a goal for each. `names` are the names that the text gave the forks on
the way, in order: for each, the parts of the form that an open side is, and the hypothesis
that says which form it is. Along every path that is left open each name has to name a fork,
so that a text does not name what the program no longer does. The result is the open goals,
each with whether the program has ended there, and whether along some path every name named a
fork (a path that is closed needs none of the names that are left for it). -/
private partial def walkFrom (goal : MVarId) (calls : Bool)
    (names : List (Array Lean.Name × Lean.Name)) (hypothesis : Option Lean.Name) :
    TacticM (List (MVarId × Bool) × Bool) := do
  -- a place where the walk stops with the goal open: every name has to have named a fork
  let stop (stopped : String) (ended : Bool) : TacticM (List (MVarId × Bool) × Bool) := do
    if let (_, name) :: _ := names then
      throwError "walk: {stopped} before a value that the run waits on, and `{name}` names nothing"
    return ([(goal, ended)], true)
  let take : TacticM (List (MVarId × Bool) × Bool) := do
    let (parts, name) ← match names with
      | head :: _ => pure (head.1, some head.2)
      | [] => pure (#[], none)
    let (next, forked) ← stepOrFork goal hypothesis.isSome (fork := name) (named := parts)
    -- a fork takes the first name, whatever the number of its sides; each side goes on with
    -- the names that are left
    let left := if forked then names.tail else names
    -- a fork of a value that has no form leaves nothing to walk and nothing to name
    if next.isEmpty then return ([], left.isEmpty)
    let reached ← next.mapM fun side => walkFrom side calls left hypothesis
    return (reached.flatMap (·.1), reached.any (·.2))
  match ← ahead goal hypothesis.isSome with
  | .step => take
  | .call => if calls then take else stop "the walk stops at a call" false
  | .ended =>
    -- a side that is closed as it stands is closed, with or without names left for it
    if ← closes goal hypothesis then return ([], names.isEmpty)
    stop "the program ends" true
  | .effect => stop "the walk stops at an effect" false
  | .loop => stop "the walk stops at a loop" false

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
a program the law is about the meaning of the function there. With `byLaw` the text gave the
proof of the law and not the value: the value is what the law says, and no goal is left for the
law. -/
private def compute (goal : MVarId) (written : Syntax) (hypothesis := false) (byLaw := false) :
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
  -- a call of a function of a program: the program whose table the semantics reads, the header
  -- of the function and its member there
  let operation ← kernelWhnf o[6]!
  let table := s[4]!
  let called : Option (Expr × Expr × Expr) :=
    if operation.isAppOfArity ``Zkc.Core.LocalOp.call 4 && table.isAppOfArity ``Zkc.Core.Defs.fnTable 4
        && (table.getArg! 3).isAppOfArity ``Zkc.Core.Typed.defs 2 then
      some ((table.getArg! 3).appArg!, operation.getArg! 2, operation.getArg! 3)
    else none
  -- the law at a value, with the operands in a form to read, and the operands. A call of a
  -- function of a program is stated as the meaning of the function there, which is the form
  -- that a law of the function has; with `place`, as its meaning in another program
  let lawAt (value : Expr) (place : Option (Expr × Expr) := none) : MetaM (Expr × Expr) := do
    let lawType := (← inferType (mkApp rule value)).bindingDomain!
    let sides := lawType.getAppArgs
    let (cells, nil) ← spine sides[1]!.appArg!
    let operands ← cells.mapM fun (_, operand) => readValue operand
    let read := rebuild cells nil operands
    let computed := match called with
      | some (program, header, member) =>
        let (program, member) := place.getD (program, member)
        mkAppN (mkConst ``Zkc.Core.fnMeaning) #[s[0]!, s[1]!, program, header, member, read]
      | none => mkApp sides[1]!.appFn! read
    return (mkAppN lawType.getAppFn #[sides[0]!, computed, sides[2]!], read)
  let (value, law, lawGoals) ← do
    if byLaw then
      -- the value is what the law that the text gave says of the operands. The text states its
      -- law of what the operands are, and not of the variables that stand for them in the
      -- process: the law is elaborated at the values, and carried back along the equations.
      let stated ← mkFreshExprMVar valueType
      -- a law of a function is stated in the table of whichever program the text chose: of the
      -- definitions before the root, also for a call inside a protocol that the root applies,
      -- which reads the table of the definitions before that protocol
      let place ← match called with
        | some (_, header, _) => do
          let program ← mkFreshExprMVar (mkApp (mkConst ``Zkc.Core.Typed) s[0]!)
          let functions ← mkAppM ``Zkc.Core.Headers.fns #[← mkAppM ``Zkc.Core.Typed.headers #[program]]
          let member ← mkFreshExprMVar (← mkAppM ``Zkc.Core.Member #[functions, header])
          pure (some (program, member))
        | none => pure none
      let (law, read) ← lawAt stated place
      let equations := (← getLCtx).foldl (init := #[]) fun found decl =>
        if isWalkEquation decl then found.push decl else found
      -- `forms[k]` is the law with the variables of the equations from `k` on replaced
      let mut latestFirst := #[law]
      for equation in equations.reverse do
        let some (_, .fvar standing, value) := (← instantiateMVars equation.type).eq?
          | throwError "walk: an equation of the walk is not of a variable{indentExpr equation.type}"
        latestFirst := latestFirst.push (latestFirst.back!.replaceFVar (.fvar standing) value)
      let forms := latestFirst.reverse
      let mut proof ← Tactic.elabTermEnsuringType written forms[0]!
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars stated
      if value.hasExprMVar then
        throwError "walk_law: the law does not say what the computation gives{indentExpr (← inferType proof)}"
      for equation in equations, k in [0:equations.size] do
        let some (_, .fvar standing, _) := (← instantiateMVars equation.type).eq? | continue
        let motive ← mkLambdaFVars #[.fvar standing] (← instantiateMVars forms[k + 1]!)
        proof ← mkEqMPR (← mkCongrArg motive equation.toExpr) proof
      -- the call here is the call where the law is stated: both are the body of the function,
      -- by the entries of the function in the two tables
      if let (some (program, _, member), some (lawProgram, lawMember)) := (called, place) then
        let lawProgram ← instantiateMVars lawProgram
        let lawMember ← instantiateMVars lawMember
        if lawProgram.hasExprMVar || lawMember.hasExprMVar then
          throwError "walk_law: the law is about no function of a program{indentExpr (← inferType proof)}"
        let here ← (withReducible (isDefEq lawProgram program)) <&&> kernelSame lawMember member
        unless here do
          let entryHere ← mkAppM ``Zkc.Core.fnMeaning_entry #[s[1]!, program, member, read]
          let entryThere ← mkAppM ``Zkc.Core.fnMeaning_entry #[s[1]!, lawProgram, lawMember, read]
          proof ← mkEqTrans (← mkEqTrans entryHere (← mkEqSymm entryThere)) proof
      pure (value, ← instantiateMVars proof, [])
    else
      let value ← instantiateMVars (← Tactic.elabTermEnsuringType written valueType)
      let law ← mkFreshExprSyntheticOpaqueMVar (tag := `law) (← lawAt value).1
      pure (value, law, (← readValues (← useEquations law.mvarId!)).toList)
  let withValue := mkApp rule value
  -- the step is the rest on the value: the term is the step of the rule, and the rule gives
  -- the rest on what the role holds of the value
  let equation := mkApp withValue law
  let equationType ← inferType equation
  let (computing, held) := (equationType.appFn!.appArg!, equationType.appArg!)
  let restOn ← restAfter a names rest
  let (list, proof, introduced) ← bindValues goal j held.appArg!.appArg! restOn
  let after := (mkApp restOn list).headBeta
  j.passSealed goal after (← mkEqTrans (← byComputation j.process computing)
    (← mkEqTrans equation (← byComputation held after))) proof
  return lawGoals ++ [introduced]

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
  let hidden (base : Lean.Name) : MetaM Lean.Name := Lean.Core.mkFreshUserName base
  let inputs := (← spine l[8]!).1
  let results := (← spine names).1
  -- where the text wrote the invariant as a function with a name for each of its arguments,
  -- the goals of the loop have those names: the iteration number, each carried value, what was
  -- collected for each collected type, and what the judgment carries along a path. What the
  -- text left without a name (`_`) has one that a text cannot write, as all have for an
  -- invariant that is not written as such a function.
  let rec binders (e : Expr) (found : Array Lean.Name) : Array Lean.Name :=
    match e with
    | .lam name _ body _ => binders body (found.push name)
    | .mdata _ inner => binders inner found
    | _ => found
  let written := binders invariant #[]
  let carriedCount := inputs.size - 1
  let collectedCount := results.size - carriedCount
  let arguments := carriedCount + collectedCount + 2
  let chosen (position : Nat) : Option Lean.Name :=
    if written.size == arguments then
      (written[position]?).filter fun name => !name.hasMacroScopes && !name.isAnonymous
    else none
  let named (position : Nat) (base : Lean.Name) : MetaM Lean.Name :=
    match chosen position with
    | some name => pure name
    | none => hidden base
  let carried ← (List.range carriedCount).toArray.mapM fun k => named (1 + k) `carried
  let collected ← (List.range collectedCount).toArray.mapM fun k =>
    named (1 + carriedCount + k) `collected
  let index ← named 0 `index
  let along ← named (arguments - 1) `along
  let earlyName ← match chosen 0 with
    | some name => pure (Name.mkSimple s!"early_{name}")
    | none => hidden `early
  let holdsName ← match chosen 0 with
    | some name => pure (Name.mkSimple s!"invariant_{name}")
    | none => hidden `invariant
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
  let (_, stepGoal) ← step.intro index
  let (state, stepGoal) ← stepGoal.intro `state
  let (stepGoal, _, _) ← openState stepGoal state carried collected
  let (_, stepGoal) ← stepGoal.intro along
  let (early, stepGoal) ← stepGoal.intro earlyName
  let (holds, stepGoal) ← stepGoal.intro holdsName
  let stepGoal ← stepGoal.withContext do
    let earlyType ← inferType (.fvar early)
    let stepGoal ← stepGoal.replaceLocalDeclDefEq early (atCount earlyType)
    stepGoal.replaceLocalDeclDefEq holds (← applied (← inferType (.fvar holds)))
  -- the rest, after the last iteration
  let (state, afterGoal) ← after.intro `state
  let (afterGoal, _, _) ← openState afterGoal state carried collected
  let (_, afterGoal) ← afterGoal.intro along
  let (holds, afterGoal) ← afterGoal.intro holdsName
  let afterGoal ← afterGoal.withContext do
    afterGoal.replaceLocalDeclDefEq holds (← applied (atCount (← inferType (.fvar holds))))
  let afterGoal ← afterGoal.withContext do
    let judgedAfter ← readGoal afterGoal false
    let restOn ← restAfter a names rest
    let (list, proof, introduced) ←
      bindValues afterGoal judgedAfter judgedAfter.process.appArg!.appArg! restOn
    let next := (mkApp restOn list).headBeta
    judgedAfter.passSealed afterGoal next (← byComputation judgedAfter.process next) proof
    pure introduced
  -- before the first iteration no process goes on: the goal is stated as an end is
  let firstGoal ← readValues (← useEquations firstGoal)
  if let some firstGoal := firstGoal then firstGoal.setTag `first
  stepGoal.setTag `step
  afterGoal.setTag `after
  return firstGoal.toList ++ [stepGoal, afterGoal]

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

/-- Walk to where the text has something to say. Steps are taken as `walk_step` takes them,
until the goal is the judgment at an effect, the next instruction is a loop or calls a function,
or the program has ended. At a fork a side that is closed as it stands is closed, and the walk
goes on in every other: a fork of which several sides are open leaves a goal for each, in the
order of the forms. What the judgment asks of an end is closed where it holds as it stands. The
equations by which the steps named their values are then used: what is left is stated in the
replies, the inputs and the variables of the text.

`walk!` reads the body of a function that a role calls as a step does, and does not stop at the
call. `walk as h` names the hypothesis of the first fork on the way (a guard that passed, a
value in one of its forms) `h`; `walk as ⟨x, h⟩` also names the parts of the form that the open
side is (the entry that a read of a sequence found); `walk as ⟨x, h⟩, g` names the forks on the
way in order. `walk … at h` walks a hypothesis that judges a process: what a judgment of the
process gives. A goal that judges no process is not walked. -/
syntax (name := walkTo) "walk" (" as " (ident <|> ("⟨" ident,+ "⟩")),+)? (" at " ident)? : tactic

@[inherit_doc walkTo]
syntax (name := walkThroughCalls)
  "walk!" (" as " (ident <|> ("⟨" ident,+ "⟩")),+)? (" at " ident)? : tactic

/-- The names in a piece of syntax, in the order written. -/
private partial def writtenNames (name : Syntax) : Array Lean.Name :=
  if name.isIdent then #[name.getId] else name.getArgs.flatMap writtenNames

/-- The walk of the main goal, or of a hypothesis of it. `names` are, for each fork that the
text names, the parts of its form and then its hypothesis. -/
private def walkTactic (calls : Bool) (names : List (Array Lean.Name × Lean.Name))
    (at_ : Option (TSyntax `ident)) : TacticM Unit := withMainContext do
  let main ← getMainGoal
  let walked (goal : MVarId) (hypothesis : Option Lean.Name) : TacticM (List (MVarId × Bool)) := do
    if (← ahead goal hypothesis.isSome) matches .ended then
      throwError "walk: the goal judges no process{indentExpr (← goal.getType)}"
    let (reached, named) ← walkFrom goal calls names hypothesis
    unless named do
      throwError "walk: every side was closed before each name had named a value that the run waits on"
    return reached
  match at_ with
  | none =>
    let reached ← walked main none
    replaceMainGoal (← reached.filterMapM fun (goal, ended) => do
      if ended then stateForText goal else return some (← readThrough goal))
  | some h =>
    let hypothesis ← getFVarId h
    let name ← hypothesis.getUserName
    let (reverted, goal) ← main.revert #[hypothesis]
    unless reverted.size == 1 do
      throwError "walk: other hypotheses depend on {h}"
    let reached ← walked goal (some name)
    replaceMainGoal (← reached.filterMapM fun (goal, ended) => do
      let (_, goal) ← goal.intro name
      if ended then stateForText goal else return some (← readThrough goal))

/-- The names that a text gave the forks of a walk: for each, the parts and then the name. -/
private def forkNames (names : Array Syntax) : List (Array Lean.Name × Lean.Name) :=
  (names.map fun name =>
    let parts := writtenNames name
    (parts.pop, parts.back!)).toList

elab_rules : tactic
  | `(tactic| walk $[as $names,*]? $[at $h:ident]?) =>
    walkTactic false (forkNames (((names.map (·.getElems)).getD #[]).map (·.raw))) h
  | `(tactic| walk! $[as $names,*]? $[at $h:ident]?) =>
    walkTactic true (forkNames (((names.map (·.getElems)).getD #[]).map (·.raw))) h

/-- Take the computation of a role that is the next instruction by its law: the operation gives
`value` on the operands. The law is left as the goal `law`, with the operands in a form to
read; the main goal is the rest on the value. With `at h`, on a hypothesis that judges a
process. -/
syntax "walk_compute " term (" at " ident)? : tactic

/-- Take the computation of a role that is the next instruction by a law that the text gives:
a proof that the operation gives a value on the operands, as a theorem of what a function of
the program computes. The value is what the law says; the main goal is the rest on it. A hole
in the law (`_`) for an operand is the operand of the computation. With `at h`, on a hypothesis
that judges a process. -/
syntax "walk_law " term (" at " ident)? : tactic

/-- Take the loop that is the next instruction by an invariant: a function of the iteration
number, of each carried value, of what was collected so far for each collected type, latest
first, and of what the judgment carries along a path. The goals are `first`, `step` and
`after`. The judgment must be monotone; for one that the walk does not know, `using` gives the
proof. -/
syntax "walk_loop " term (" using " term)? : tactic

/-- A computation taken by its law on the main goal or on a hypothesis of it. -/
private def computeTactic (written : Syntax) (byLaw : Bool) (at_ : Option (TSyntax `ident)) :
    TacticM Unit := withMainContext do
  let main ← getMainGoal
  match at_ with
  | none => replaceMainGoal (← compute main written false byLaw)
  | some h =>
    let hypothesis ← getFVarId h
    let name ← hypothesis.getUserName
    let (reverted, goal) ← main.revert #[hypothesis]
    unless reverted.size == 1 do
      throwError "walk: other hypotheses depend on {h}"
    let next ← compute goal written true byLaw
    replaceMainGoal (next.dropLast ++ [(← next.getLast!.intro name).2])

elab_rules : tactic
  | `(tactic| walk_compute $value:term $[at $h:ident]?) => computeTactic value false h
  | `(tactic| walk_law $law:term $[at $h:ident]?) => computeTactic law true h
  | `(tactic| walk_loop $invariant:term) => do
    replaceMainGoal (← loop (← getMainGoal) invariant none)
  | `(tactic| walk_loop $invariant:term using $monotone:term) => do
    replaceMainGoal (← loop (← getMainGoal) invariant (some monotone))

end Zkc.Formal.Walk
