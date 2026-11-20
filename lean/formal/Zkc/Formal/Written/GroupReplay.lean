module

public import Zkc.Formal.Written.Tactics
public import Zkc.Formal.Written.FunctionMeaning
public meta import Zkc.Formal.Written.Source
public meta import Zkc.Frontend.Written.LeanTerms
public meta import Lean.Elab.Eval

public meta section
namespace Zkc.Formal.Written
open Zkc.Core Lean Elab Tactic Meta

private inductive ReplayStep where
  | instruction (script : String)
  | guard (script : String)

/-- Hints for kernel-checked instruction rules and the guards encountered along the trace. -/
private structure ReplayPlan where
  steps : Array ReplayStep := #[]
  guards : Array String := #[]

open Zkc.Frontend.Written (numbers consList component)

private def typeTerm (t : Standard.Ty) : Except String String :=
  pure (Zkc.Frontend.Written.ty (b := Zkc.Frontend.Emit.Bindings.mk [] (by decide)) t)

private def valueStep (role : Nat) (who : List Role) (types : List Standard.Ty) (values : List String) (proof := "rfl") :
    Except String String := do
  let mid ← types.mapM fun t => do return s!"⟨{← typeTerm t}, {numbers who}⟩"
  return s!"refine afterValue (D := roleDialect V ⟨[],[]⟩ {role}) (sem := sem) (mid := [{", ".intercalate mid}]) {consList values} (by {proof}) ?_"

private def replyStep (role : Nat) (who : List Role) (ty op reply : String) :=
  s!"refine afterReply (D := roleDialect V ⟨[],[]⟩ {role}) (sem := sem) (mid := [⟨{ty}, {numbers who}⟩]) (show ROp M from {op}) {reply} (fun x => .cons x .nil) (by rfl) ?_"

/-- Read only the admitted program's erasure. Every hinted value, including every tuple
projection, is checked by conversion against the corresponding projected typed instruction. -/
private def plan (program : NamedProgram Standard) (role : Role) (replies : List String) : Except String ReplayPlan := do
  let [.protocol _ _ ports [] (.mk inputs steps [])] := program.definitions | throw "expected a closed straight-line verifier"
  let publicInputs := (inputs.zip ports).filter (fun (_, p) => p.holders.contains role)
  let mut env := publicInputs.zipIdx.map fun ((n,_),i) => (n, component "s" i (i+1 == publicInputs.length))
  let mut plan : ReplayPlan := {}
  let mut remaining := replies
  for instr in steps do
    let lookup (n : Nat) : Except String String := match env.lookup n with
      | some x => .ok x | none => .error s!"unavailable verifier operand {n}"
    let atKey (k : Key) := s!"⟨path, ⟨{k.number}⟩⟩"
    match instr with
    | .op _ outs (.compute who raw) args =>
      let proof := if who.contains role && (raw matches .row _) then
        "exact (pure_instruction M).trans (by rfl)" else "rfl"
      let (types, values) ← match raw with
        | .row k => do
          let some sig := Standard.row k | throw "unknown row"
          if !who.contains role then pure (sig.outs, List.replicate outs.length "()")
          else
            let .pure := sig.kind | throw "restricted row needs a domain proof"
            let .inl standardKey := k | throw "unbound primitive row"
            let key := s!"(.inl ({reprStr (show Zkc.Vocabulary.RowKey from standardKey)}))"
            let ins ← sig.ins.mapM typeTerm
            let res ← sig.outs.mapM typeTerm
            let inputs := consList (← args.mapM lookup)
            let vals := s!"(rowValues (ins := [{", ".intercalate ins}]) (outs := [{", ".intercalate res}]) M {key} rfl {inputs})"
            let mut tail := vals
            let mut results := #[]
            for _ in sig.outs do
              results := results.push s!"(firstValue (F := M.Val) {tail})"
              tail := s!"(otherValues (F := M.Val) {tail})"
            pure (sig.outs, results.toList)
        | .owned name ts indices => do
          let some sig := OwnedOp.resolve (V := Standard) name ts indices | throw "unknown owned operation"
          if !who.contains role then pure (sig.2.1, List.replicate outs.length "()")
          else
            let xs ← args.mapM lookup
            let values ← match name, ts, indices, xs with
              | .take, [.tuple items], [], [x] => pure ((List.range items.toList.length).map (component x ·))
              | .get, [.tuple _], [i], [x] => pure [component x i]
              | .make, [.tuple _], [], values => pure [values.foldr (fun x rest => s!"({x}, {rest})") "()"]
              | _, _, _, _ => throw "uninterpreted verifier operation"
            pure (sig.2.1, values)
        | .literal t _ =>
          if who.contains role then throw "uninterpreted verifier literal"
          pure ([t], ["()"])
        | _ => throw "uninterpreted local computation"
      unless types.length == outs.length && values.length == outs.length do throw "unexpected result arity"
      plan := {plan with steps := plan.steps.push (.instruction (← valueStep role who types values proof))}
      env := outs.zip values ++ env
    | .op k [out] (.event (.flow .message prover [peer]) t) _ =>
      unless role == peer do throw "unexpected message recipient"
      let x :: rest := remaining | throw "missing trace reply"
      remaining := rest
      let ty ← typeTerm t
      let step := replyStep role ([prover,peer].mergeSort) ty s!".get .message {prover} {atKey k} {ty}" x
      plan := {plan with steps := plan.steps.push (.instruction step)}
      env := (out,x) :: env
    | .op k [out] (.event (.given (.coin law) owner peers) t) [] =>
      let step ← if owner != role && !peers.contains role then valueStep role [owner] [t] ["()"]
        else do
          unless owner == role do throw "expected the verifier to own the observed draw"
          let x :: _ := remaining | throw "missing trace reply"
          let kind := s!"(.coin {Zkc.Frontend.Written.lawKey law})"
          let ty ← typeTerm t
          pure (replyStep role ((owner :: peers).mergeSort) ty s!".own {kind} {numbers peers} {atKey k} [] .nil {ty}" x)
      plan := {plan with steps := plan.steps.push (.instruction step)}
      if owner == role then
        let x :: rest := remaining | throw "missing trace reply"
        remaining := rest
        env := (out,x) :: env
    | .guard _ who cond .reject =>
      unless who.contains role do
        plan := {plan with steps := plan.steps.push (.guard "refine projectedGuardElsewhere (by decide) ?_")}
        continue
      let test ← lookup cond
      let step := s!"refine projectedGuard (sem := sem) (by decide) {test} (by rfl) ?_"
      plan := ⟨plan.steps.push (.guard step), plan.guards.push test⟩
    | .choose _ who .. | .loop _ who .. =>
      if who.contains role then throw "expected private control outside the verifier"
      plan := {plan with steps := plan.steps.push (.instruction "refine afterValue (sem := sem) _ (by rfl) ?_")}
    | _ => throw "uninterpreted verifier instruction"
  unless remaining.isEmpty do throw "unused trace replies"
  return plan

private unsafe def readPlan (stored : Syntax) (role : Nat) (replies : Array (TSyntax `term)) : TacticM ReplayPlan := do
  let ty ← mkAppM ``NamedProgram #[mkConst ``Standard]
  let program ← Term.evalTerm (NamedProgram Standard) ty stored
  let rendered ← replies.toList.mapM fun x => do
    let some source := x.raw.reprint | throwErrorAt x "expected a printable reply term"
    return "(" ++ source ++ ")"
  ofExcept (plan program role rendered)

private def runStep (step : String) : TacticM Unit := do
  evalTactic (← ofExcept (Parser.runParserCategory (← getEnv) `tactic step))

syntax (name := writtenGuards) "written_guards " term:max num " replies " "[" term,* "]" : tactic
@[tactic writtenGuards] unsafe def guardsTac : Tactic := fun stx => withMainContext do
  let result ← readPlan stx[1] stx[2].isNatLit?.get! (stx[5].getSepArgs.map (⟨·⟩))
  let prop := result.guards.foldr (fun test tail => s!"{test} = true ∧ {tail}") "True"
  runStep s!"exact ({prop})"

syntax (name := writtenSteps) "written_steps " term:max num " replies " "[" term,* "]" : tactic
@[tactic writtenSteps] unsafe def stepsTac : Tactic := fun stx => withMainContext do
  let result ← readPlan stx[1] stx[2].isNatLit?.get! (stx[5].getSepArgs.map (⟨·⟩))
  for step in result.steps do
    match step with
    | .instruction script =>
      runStep "expose_cursor"
      runStep script
    | .guard script => runStep script
  runStep "expose_cursor"
  runStep "finish_guard_replay"

private def simplifyUsing (condition : Expr) (rules : Array Expr) (heads : Array Lean.Name) : MetaM Simp.Result := do
  let post : Simp.Simproc := fun e => do
    if heads.contains (e.getAppFn.constName?.getD .anonymous) then
      for rule in rules do
        let some result ← liftM (m := MetaM) (observing? (do
          let (args, _, eq) ← forallMetaTelescopeReducing (← inferType rule)
          let some (_, lhs, rhs) := eq.eq? | failure
          unless ← withTransparency .default (isDefEq lhs e) do failure
          return (← instantiateMVars rhs, ← instantiateMVars (mkAppN rule args)) : MetaM _)) | continue
        return .done {expr := result.1, proof? := some result.2}
    return .done {expr := e}
  let ctx ← Simp.mkContext (simpTheorems := #[{}])
  return (← Simp.main condition ctx (methods := {post})).1

/-- Interpret the model values using precisely the equations supplied by a record of row
laws. Rows without an equation retain their typed model value. -/
private def interpret (condition model laws : Expr) : MetaM Simp.Result := do
  let mut rules := #[]
  let lawType ← whnf (← inferType laws)
  for field in getStructureFields (← getEnv) lawType.getAppFn.constName! do
    let fact ← mkProjection laws field
    let rule ← forallTelescopeReducing (← inferType fact) fun xs _ => do
      mkLambdaFVars xs (← instantiateMVars (← mkAppM ``firstValue_of_apply #[model, mkAppN fact xs]))
    rules := rules.push rule
  let concrete ← simplifyUsing (← whnf condition) rules #[``firstValue]
  let mut logic : SimpTheorems := {}
  for name in #[``decide_eq_true_eq, ``and_true] do logic ← logic.addConst name
  let (result, _) ← simp concrete.expr (← Simp.mkContext (simpTheorems := #[logic]))
  return ← concrete.mkEqTrans result

elab "interpreted_guards% " condition:term:max " with " model:term:max laws:term:max : term => do
  return (← interpret (← Term.elabTerm condition none) (← Term.elabTerm model none)
    (← Term.elabTerm laws none)).expr

elab "interpret_guards " equivalent:term:max " with " model:term:max laws:term:max : tactic =>
  withMainContext do
    let eqv ← elabTerm equivalent none
    let type ← whnf (← inferType eqv)
    unless type.isAppOfArity ``Iff 2 do throwError "expected a verifier equivalence, got {type}"
    let result ← interpret type.getAppArgs[1]! (← elabTerm model none) (← elabTerm laws none)
    let proof ← match result.proof? with
      | none => pure eqv
      | some eq => mkAppM ``Iff.trans #[eqv, ← mkAppM ``Iff.of_eq #[eq]]
    (← getMainGoal).assign proof
    replaceMainGoal []

/-- Reduce the dependent Core environment while preserving the mathematical operations
and propositions that a companion and its row equations use. -/
private partial def compactValue (value : Expr) : MetaM Expr :=
  let rec visit (e : Expr) : MonadCacheT Expr Expr MetaM Expr := checkCache e fun _ => do
    if ← isProof e then return e
    let e ← whnfHeadPred e fun head => do
      let n := head.getAppFn.constName?.getD .anonymous
      return !((``Operations).isPrefixOf n || (``FunctionRows).isPrefixOf n ||
        #[``decide, ``Not, ``Ne, ``Eq, ``Bool.and, ``Bool.not, ``Ty.readLiteral].contains n)
    if e.isAppOfArity ``decide 2 then
      let args := e.getAppArgs
      return mkAppN e.getAppFn #[← visit args[0]!, args[1]!]
    if e.isApp then
      let f := e.getAppFn
      let mut args := e.getAppArgs
      let info ← getFunInfoNArgs f args.size
      for i in [:args.size] do
        if info.paramInfo[i]?.any (·.isExplicit) then
          args ← args.modifyM i visit
      return mkAppN f args
    return e
  visit value |>.run

elab "compact_return" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← instantiateMVars (← goal.getType)).eq? | throwError "expected a function equation"
  let target ← mkEq (← compactValue lhs) rhs
  replaceMainGoal [← goal.replaceTargetDefEq target]

/-- An application of a constructor, by the head normal form when the term is not one. -/
private def exposed (e : Expr) (constructor : Lean.Name) : MetaM Expr := do
  if e.isAppOf constructor then return e
  whnf e

/-- The values of a binding, each under `mark`. `none` for values that are not written out as a
list. -/
private partial def markedValues (mark values : Expr) : MetaM (Option Expr) := do
  let values ← exposed values ``HList.cons
  if values.isAppOf ``HList.nil then return some values
  unless values.isAppOf ``HList.cons do return none
  let parts := values.getAppArgs
  let some rest ← markedValues mark parts.back! | return none
  let value := parts[parts.size - 2]!
  let marked := mkApp2 mark (← inferType value) value
  return some (mkAppN values.getAppFn ((parts.set! (parts.size - 2) marked).set! (parts.size - 1) rest))

/-- An environment with the values of each of its bindings under `mark`. What is under the
first binding stays as it is. -/
private partial def markedEnvironment (mark env : Expr) : MetaM (Option Expr) := do
  unless env.isAppOf ``Env.extend do return some env
  let args := env.getAppArgs
  let some parent ← markedEnvironment mark args[args.size - 4]! | return none
  let some bound ← markedValues mark args.back! | return none
  return some (mkAppN env.getAppFn ((args.set! (args.size - 4) parent).set! (args.size - 1) bound))

/-- The operands of a step with each read replaced by the value bound: the kernel's head normal
form of the read in the marked environment is that value under `mark`. `none` when a read does
not end at a marked value. -/
private partial def readMarked (mark original marked : Expr) : MetaM (Option Expr) := do
  let original ← exposed original ``HList.cons
  if original.isAppOf ``HList.nil then return some original
  let marked ← exposed marked ``HList.cons
  unless original.isAppOf ``HList.cons && marked.isAppOf ``HList.cons do return none
  let args := original.getAppArgs
  let markedArgs := marked.getAppArgs
  let read ← ofExceptKernelException
    (Lean.Kernel.whnf (← getEnv) (← getLCtx) markedArgs[markedArgs.size - 2]!)
  unless read.getAppFn == mark && read.getAppNumArgs == 2 do return none
  let some rest ← readMarked mark args.back! markedArgs.back! | return none
  return some (mkAppN original.getAppFn
    ((args.set! (args.size - 2) read.getAppArgs.back!).set! (args.size - 1) rest))

/-- The operands of a step, read by the Core's own lookup from an environment whose bound values
the kernel does not look into. Each bound value is put under a local function without a
definition, the kernel reduces each read to its head normal form, which is one of those
applications, and its argument is the operand. Which binding a name reads, and shadowing, are
decided by `Env.all` as it is; the values, however large, are not evaluated again at each read.
`none` for operands that are not such reads, which the general reduction then handles. The
result is used under a definitional equality that the kernel checks, so a wrong read cannot
pass. -/
private def protectedOperands (operands : Expr) : MetaM (Option Expr) := do
  unless operands.isAppOf ``Env.all do return none
  withLocalDeclD `bound (← inferType (mkConst ``id [.succ .zero])) fun mark => do
    let args := operands.getAppArgs
    let some env ← markedEnvironment mark args[args.size - 3]! | return none
    let some read ← readMarked mark operands (mkAppN operands.getAppFn (args.set! (args.size - 3) env))
      | return none
    if read.containsFVar mark.fvarId! then return none
    return some read

/-- Compute operand lookup once at each instruction before it enters any later environment. -/
elab "compact_operands" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? | failure
  unless lhs.isAppOf ``localOp do failure
  let operands := lhs.getAppArgs.back!
  let value ← compactValue ((← protectedOperands operands).getD operands)
  replaceMainGoal [← g.replaceTargetDefEq (← mkEq (mkApp lhs.appFn! value) rhs)]

elab "compact_guard " h:ident : tactic => withMainContext do
  let g ← getMainGoal
  let f ← getFVarId h
  let some (_, lhs, rhs) := (← inferType (mkFVar f)).eq? | throwError "expected a boolean guard"
  replaceMainGoal [← g.changeLocalDecl f (← mkEq (← compactValue lhs) rhs)]

/-- Use one supplied primitive interpretation at an actual Core call. Dependent
environment lookups and the types of the registered row may agree by conversion. -/
elab "function_row_law " group:term:max scalar:term:max : tactic => withMainContext do
  let g ← getMainGoal
  let field ← elabTerm scalar none
  let mut rules := #[← mkAppM ``FunctionRows.refine_of_ne #[field]]
  for record in #[← elabTerm group none, field] do
    let t ← whnf (← inferType record)
    for name in getStructureFields (← getEnv) t.getAppFn.constName! do
      rules := rules.push (← mkProjection record name)
  for rule in rules do
    if let some goals ← observing? (g.apply rule) then
      replaceMainGoal goals
      evalTactic (← `(tactic| all_goals try assumption))
      return
  throwError "missing primitive interpretation"

elab "local_instruction " group:term:max scalar:term:max : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq? | failure
  unless lhs.isAppOf ``functionResult do failure
  let process := lhs.getAppArgs.back!
  unless process.isAppOfArity ``Zkc.Core.Term.denote 7 do failure
  let term ← whnf process.getAppArgs[4]!
  unless term.isAppOfArity ``Zkc.Core.Term.step 8 do failure
  let instr ← whnf term.getAppArgs[5]!
  if instr.isAppOf ``Zkc.Core.Instr.op then
    evalTactic (← `(tactic| (apply function_op; compact_operands; (first | rfl | apply function_row; function_row_law $group $scalar))))
  else if instr.isAppOf ``Zkc.Core.Instr.guard then
    evalTactic (← `(tactic| (apply function_guard <;> (intro branch; compact_guard branch; try simp at branch))))
  else throwError "unsupported local control instruction"

/-- Prove the value-level calculation against the execution of the emitted Core function. -/
macro "check_function " written:Lean.Parser.Tactic.simpLemma " with " group:term:max scalar:term:max : tactic => `(tactic|
  (repeat' local_instruction $group $scalar
   all_goals compact_return
   all_goals simp (config := {zetaDelta := true}) [$written, require, divide, Bool.and_eq_true,
     FunctionRows.inverseScalar $scalar, FunctionRows.roundTrip $scalar, FunctionRows.zero $scalar, *] <;> first | rfl | (split <;> simp_all <;> rfl)))

/-- Collect one witness equation per matching pair of verifier equations. An unrelated
guard is allowed; only facts justified by the group lemma enter the extractor proof. -/
private partial def witnessFacts (ops laws left right apart : Expr) : MetaM (List Expr) := do
  let t ← whnf (← inferType left)
  if t.isAppOf ``And then
    let lhs ← witnessFacts ops laws (← mkAppM ``And.left #[left]) (← mkAppM ``And.left #[right]) apart
    let rhs ← witnessFacts ops laws (← mkAppM ``And.right #[left]) (← mkAppM ``And.right #[right]) apart
    return lhs ++ rhs
  observing? (mkAppM ``extract_difference #[ops,laws,left,right,apart]) >>= fun x => pure x.toList

elab "fork_witnesses " ops:term:max laws:term:max left:term:max right:term:max apart:term:max : tactic =>
  withMainContext do
    let terms ← #[ops,laws,left,right,apart].mapM (elabTerm · none)
    let facts ← witnessFacts terms[0]! terms[1]! terms[2]! terms[3]! terms[4]!
    let mut goal ← getMainGoal
    for fact in facts do
      let (_, next) ← (← goal.assert (← mkFreshUserName `extracted) (← inferType fact) fact).intro1P
      goal := next
    replaceMainGoal [goal]

/-- Discharge the written extractor and relation using the equations of the actual verifier.
The same witness must satisfy every verification condition for the returned value. -/
macro "certify_group_fork " equations:term:max " with " ops:term:max laws:term:max
    " for " extractor:ident relation:Lean.Parser.Tactic.simpLemma : tactic => `(tactic| (
  intro s a l r hl hr apart
  have one := ($equations s a l).mp hl
  have two := ($equations s a r).mp hr
  fork_witnesses $ops $laws one two apart
  have gap : Operations.sub $ops l.challenge r.challenge ≠ Operations.zero $ops :=
    fun h => apart ((ActionLaws.sub_zero $laws ..).mp h)
  apply returned_of_triple
  unfold $extractor
  vcgen
  all_goals simp (config := {zetaDelta := true}) [$relation, *] <;> rfl))

end Zkc.Formal.Written
