module

public import Zkc.Formal.ProcessJudgment
public import Zkc.Core.Meaning.Role
public meta import Lean

public meta section

/-!
The walk of a role's program under a judgment, one step at a time.

A goal is a judgment of a process: `Process.interpret J done halt P …`, where `P` is the
denotation of a term in an environment, or what is left of an instruction after an effect.
`walk_step` asks the kernel for the head normal form of what the next instruction denotes, and
states the goal that follows:

- for values, the rest of the term in the environment extended by them. A value that is a
  variable or a literal is used as it is; any other gets a local variable with the equation
  that says what it is, in a form to read;
- for a stop, what the judgment asks of a stop;
- for an effect, the judgment at the effect, with the rest after its reply;
- where the step waits on a value (the element of a sequence at a position, the condition of a
  guard), a goal for each form of that value, with the equation that says which form it is; each
  of these goals then takes the step that its form makes possible.

`walk_step at h` takes the same step on a hypothesis that judges a process: what a judgment of
the process gives, as the walk of a goal says what a judgment of it needs.

Nothing is unified and no lemma about an instruction is applied: each new goal is definitionally
the old one at the values themselves, and the kernel checks that when the proof is closed. Lean's
own reduction is not asked to evaluate an environment, whose cost on a long region grows with
every instruction.

The driver takes the steps that a region without a loop, a block, an application or a call of a
function takes. Those wait for their first subject.

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

/-- A value in a form to read. Its reads of an environment are replaced by what they read: a
subterm that mentions an environment and that the kernel reduces to a local variable or to a
literal is replaced by it. What a role holds of a value is the value. A function applied to its
argument is its body there. Everything else stays as the semantics wrote it: the operations of
the model are not unfolded, since the kernel's normal form of an operation on a variable is its
recursor. The result is definitionally the term given. -/
private partial def settle (e : Expr) : MetaM Expr := do
  match e with
  | .app .. | .proj .. =>
    if readsEnvironment e then
      let type ← inferType e
      unless (← isProp type) || (← Meta.isType e) || (← whnf type).isForall do
        let read ← kernelWhnf e
        if read.isFVar || read.isLit then return read
    match e with
    | .proj typeName idx struct => return .proj typeName idx (← settle struct)
    | _ =>
      let applied := (mkAppN (← settle e.getAppFn) (← e.getAppArgs.mapM settle)).headBeta
      if applied != e && applied.isApp && applied.getAppFn.isLambda then settle applied
      else unwrapped applied
  | .mdata _ inner => settle inner
  | _ => return e

/-- A judgment of a process: the judgment applied to all but the process, the process, and what
follows it (a budget). It is the goal, or a hypothesis from which the goal concludes
`conclusion`. -/
private structure Judged where
  fn : Expr
  process : Expr
  extra : Array Expr
  conclusion : Option Expr := none

private def readJudged (target : Expr) : MetaM Judged := do
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Zkc.Core.Process.interpret && args.size ≥ 8 do
    throwError "walk: the goal does not judge a process{indentExpr target}"
  return {
    fn := mkAppN target.getAppFn (args.extract 0 7)
    process := args[7]!
    extra := args.extract 8 args.size }

/-- The goal that states a judgment: the judgment, or what is concluded from it. -/
private def Judged.goal (j : Judged) (judgment : Expr) : Expr :=
  match j.conclusion with
  | some conclusion => mkForall `judged .default judgment conclusion
  | none => judgment

private def Judged.of (j : Judged) (p : Expr) : Expr := j.goal (mkAppN (mkApp j.fn p) j.extra)

/-- What the judgment asks at the end, of `done` or of `halt` (argument 5 or 6). -/
private def Judged.ask (j : Judged) (position : Nat) (value : Expr) : Expr :=
  j.goal (mkAppN (mkApp (j.fn.getAppArgs[position]!) value) j.extra).headBeta

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

/-- The numbers of a list of names, when they are written. -/
private partial def nameNumbers (names : Expr) : MetaM (Array Nat) := do
  let (cells, _) ← spine names
  cells.mapM fun (_, n) => do
    let n ← kernelWhnf n
    return (n.rawNatLit?.orElse fun _ => n.nat?).getD 0

/-- The goal after values. Each value is settled. A value that settles to a local variable or a
literal is used as it is; any other gets a new local variable `x<name>`, at its computed type,
with the equation `h<name>` that says what it is. The goal is then the rest on these. The old
goal is closed by the new one at the values themselves. -/
private def bindValues (goal : MVarId) (j : Judged) (values : Expr) (rest : Expr) (numbers : Array Nat) :
    MetaM MVarId := goal.withContext do
  let (cells, nil) ← spine values
  let settled ← cells.mapM fun (_, value) => do
    let read ← settle value
    -- a value that is what was read, under what a role holds of it, is that variable
    let head ← kernelWhnf read
    return if head.isFVar || head.isLit then head else read
  let named := (List.range cells.size).toArray.filter fun i =>
    !(settled[i]!.isFVar || settled[i]!.isLit)
  let mut decls := #[]
  for i in named do
    decls := decls.push (Name.mkSimple s!"x{numbers.getD i i}", ← kernelWhnf (← inferType settled[i]!))
  let newType ← withLocalDeclsDND decls fun xs => do
    let mut elems := settled
    for k in [0:named.size] do
      elems := elems.set! named[k]! xs[k]!
    let mut body := j.of (mkApp rest (rebuild cells nil elems)).headBeta
    for k in (List.range named.size).reverse do
      let i := named[k]!
      body := mkForall (Name.mkSimple s!"h{numbers.getD i i}") .default (← mkEq xs[k]! settled[i]!) body
    mkForallFVars xs body
  let next ← mkFreshExprSyntheticOpaqueMVar newType
  let mut proof := mkAppN next (named.map (settled[·]!))
  for i in named do
    proof := mkApp proof (← mkEqRefl settled[i]!)
  goal.assign proof
  let names := (named.map fun i => Name.mkSimple s!"x{numbers.getD i i}").toList ++
    (named.map fun i => Name.mkSimple s!"h{numbers.getD i i}").toList
  let (_, introduced) ← next.mvarId!.introN (2 * named.size) names
  return introduced

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

/-- A step that waits on a value: a goal for every form of the value. Each has the equation
`at<key>` between what the step waits on, in a form to read, and the form; a part of the form
is a variable at its computed type, named `x<name>` after what the step binds when the form has
as many parts as the step has results. -/
private def splitStuck (goal : MVarId) (j : Judged) (stuck rest : Expr) (key : Option Nat)
    (numbers : Array Nat) : MetaM (List MVarId) := goal.withContext do
  let (waited, put) ← waitsOn stuck
  let waited ← settle waited
  let waitedType ← kernelWhnf (← inferType waited)
  let equation := Name.mkSimple (match key with | some k => s!"at{k}" | none => "at_")
  let newType ← withLocalDeclD `waited waitedType fun form => do
    let body := j.of (← mkAppM ``Zkc.Core.Process.bind #[put form, rest])
    mkForallFVars #[form] (mkForall equation .default (← mkEq waited form) body)
  let next ← mkFreshExprSyntheticOpaqueMVar newType
  goal.assign (mkApp2 next waited (← mkEqRefl waited))
  let (form, afterForm) ← next.mvarId!.intro `waited
  let (_, afterEquation) ← afterForm.intro equation
  let cases ← afterEquation.cases form
  cases.toList.mapM fun case => case.mvarId.withContext do
    let mut current := case.mvarId
    let parts := case.fields.filterMap fun field => if field.isFVar then some field.fvarId! else none
    for part in parts, i in [0:parts.size] do
      let type ← current.withContext do kernelWhnf (← inferType (.fvar part))
      current ← current.replaceLocalDeclDefEq part type
      if parts.size == numbers.size then
        current ← current.rename part (Name.mkSimple s!"x{numbers[i]!}")
    return current

/-- One step on what is left of an instruction: a process and the rest on its values. -/
private def advance (goal : MVarId) (j : Judged) (p rest : Expr) (key : Option Nat) (numbers : Array Nat) :
    MetaM (List MVarId) := goal.withContext do
  let w ← kernelWhnf p
  if w.isAppOfArity ``Zkc.Core.Process.done 4 then
    return [← bindValues goal j (w.getArg! 3) rest numbers]
  else if w.isAppOfArity ``Zkc.Core.Process.halt 4 then
    let next ← mkFreshExprSyntheticOpaqueMVar (j.ask 6 (w.getArg! 3))
    goal.assign next
    return [next.mvarId!]
  else if w.isAppOfArity ``Zkc.Core.Process.call 5 then
    -- the judgment at the effect, with the rest after its reply
    let op := w.getArg! 3
    let k := w.getArg! 4
    let replyType := (← whnf (← inferType k)).bindingDomain!
    let after ← withLocalDeclD `reply replyType fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Zkc.Core.Process.bind #[(mkApp k x).headBeta, rest])
    let args := (← inferType j.process).getAppArgs
    let call := mkAppN (mkConst ``Zkc.Core.Process.call) #[args[0]!, args[1]!, args[2]!, op, after]
    let next ← mkFreshExprSyntheticOpaqueMVar (j.of call)
    goal.assign next
    return [next.mvarId!]
  else splitStuck goal j w rest key numbers

/-- One step of the walk on a goal: on the judgment that the goal is, or, with `hypothesis`, on
the judgment from which the goal concludes. -/
private def step (goal : MVarId) (hypothesis := false) : MetaM (List MVarId) := goal.withContext do
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
  -- a process under a reducible name is the process
  let known (p : Expr) := p.isAppOfArity ``Zkc.Core.Process.bind 6 || p.isAppOfArity ``Zkc.Core.Term.denote 7
  let p := j.process.headBeta
  let p ← if known p then pure p else whnfR p
  let j := { j with process := p, conclusion }
  if p.isAppOfArity ``Zkc.Core.Process.bind 6 then
    -- what is left of an instruction after an effect or a split
    advance goal j (p.getArg! 4) (p.getArg! 5) none #[]
  else if p.isAppOfArity ``Zkc.Core.Term.denote 7 then
    let a := p.getAppArgs
    let (D, sem, Γ, path, env) := (a[0]!, a[1]!, a[2]!, a[5]!, a[6]!)
    let term ← kernelWhnf a[4]!
    if term.isAppOfArity ``Zkc.Core.Term.step 8 then
      let t := term.getAppArgs
      let (mid, key, i, names, rest) := (t[3]!, t[4]!, t[5]!, t[6]!, t[7]!)
      let stepExpr := mkAppN (mkConst ``Zkc.Core.Instr.denote) #[D, sem, key, Γ, mid, i, path, env]
      let valuesType := (← inferType stepExpr).getAppArgs[2]!
      let after ← withLocalDeclD `values valuesType fun vs => do
        let extended ← mkAppM ``Zkc.Core.Env.extend #[env, names, vs]
        let newΓ := (← inferType rest).getAppArgs[1]!
        mkLambdaFVars #[vs] (mkAppN (mkConst ``Zkc.Core.Term.denote) #[D, sem, newΓ, a[3]!, rest, path, extended])
      -- the number of the key, for the names of what the step states; a key that is no
      -- literal gives none
      let keyNumber ← do
        let key ← kernelWhnf key
        if key.isAppOfArity ``Zkc.Core.Key.mk 1 then
          let number ← kernelWhnf key.appArg!
          pure (number.rawNatLit?.orElse fun _ => number.nat?)
        else pure none
      advance goal j stepExpr after keyNumber (← nameNumbers names)
    else if term.isAppOfArity ``Zkc.Core.Term.ret 4 then
      let exit := term.getArg! 3
      let all ← mkAppM ``Zkc.Core.Env.all #[env, exit]
      let (cells, nil) ← spine all
      let elems ← cells.mapM fun (_, e) => kernelWhnf e
      let next ← mkFreshExprSyntheticOpaqueMVar (j.ask 5 (rebuild cells nil elems))
      goal.assign next
      return [next.mvarId!]
    else throwError "walk: the term is neither a step nor a return{indentExpr term}"
  else throwError "walk: the process is not a term in an environment{indentExpr p}"

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

end Zkc.Formal.Walk
