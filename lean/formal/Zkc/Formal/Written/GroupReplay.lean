module

public import Zkc.Formal.Written.Tactics
public meta import Zkc.Formal.Written.Source
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

private def natList (ns : List Nat) := "[" ++ ", ".intercalate (ns.map toString) ++ "]"

private def consList (items : List String) :=
  items.foldr (fun x tail => s!"(.cons {x} {tail})") ".nil"

private partial def typeTerm : Standard.Ty → Except String String
  | .bool => pure ".bool"
  | .nominal (.inl (.group .g1)) => pure "pointTy"
  | .nominal (.inl (.field .bls12381Fr)) => pure "scalarTy"
  | .tuple ts => do return s!"(.tuple {consList (← ts.toList.mapM typeTerm)})"
  | _ => throw "uninterpreted verifier type"

private def projection (base : String) (i : Nat) (last := false) :=
  base ++ String.join (List.replicate i ".2") ++ (if last then "" else ".1")

private def valueStep (role : Nat) (who : List Role) (types : List Standard.Ty) (values : List String) :
    Except String String := do
  let mid ← types.mapM fun t => do return s!"⟨{← typeTerm t}, {natList who}⟩"
  return s!"refine afterValue (D := roleDialect V ⟨[],[]⟩ {role}) (sem := sem) (mid := [{", ".intercalate mid}]) {consList values} (by rfl) ?_"

private def replyStep (role : Nat) (who : List Role) (ty op reply : String) :=
  s!"refine afterReply (D := roleDialect V ⟨[],[]⟩ {role}) (sem := sem) (mid := [⟨{ty}, {natList who}⟩]) (show ROp N from {op}) {reply} (fun x => .cons x .nil) (by rfl) ?_"

/-- Read only the admitted program's erasure. Every hinted value, including every tuple
projection, is checked by conversion against the corresponding projected typed instruction. -/
private def plan (program : NamedProgram Standard) (role : Role) : Except String ReplayPlan := do
  let [.protocol _ _ ports [] (.mk inputs steps [])] := program.definitions | throw "expected a closed straight-line verifier"
  let publicInputs := (inputs.zip ports).filter (fun (_, p) => p.holders.contains role)
  let mut env := publicInputs.zipIdx.map fun ((n,_),i) => (n, projection "s" i (i+1 == publicInputs.length))
  let mut plan : ReplayPlan := {}
  let mut messages := 0
  for instr in steps do
    let lookup (n : Nat) : Except String String := match env.lookup n with
      | some x => .ok x | none => .error s!"unavailable verifier operand {n}"
    let atKey (k : Key) := s!"⟨path, ⟨{k.number}⟩⟩"
    match instr with
    | .op _ outs (.compute who raw) args =>
      let (types, values) ← match raw with
        | .row k => do
          let some sig := Standard.row k | throw "unknown row"
          if !who.contains role then pure (sig.outs, List.replicate outs.length "()")
          else
            let [x,y] ← args.mapM lookup | throw "expected a binary group row"
            let result ← match k with
              | .inl (.group .add (.group .g1)) => pure s!"(ops.add {x} {y})"
              | .inl (.group .scale (.group .g1)) => pure s!"(ops.scale {x} {y})"
              | .inl (.group .equal (.group .g1)) => pure s!"(decide ({x} = {y}))"
              | _ => throw "uninterpreted verifier row"
            pure (sig.outs, [result])
        | .owned name ts indices => do
          let some sig := OwnedOp.resolve (V := Standard) name ts indices | throw "unknown owned operation"
          if !who.contains role then pure (sig.2.1, List.replicate outs.length "()")
          else
            let xs ← args.mapM lookup
            let values ← match name, ts, indices, xs with
              | .take, [.tuple items], [], [x] => pure ((List.range items.toList.length).map (projection x ·))
              | .get, [.tuple _], [i], [x] => pure [projection x i]
              | .make, [.tuple _], [], values => pure [values.foldr (fun x rest => s!"({x}, {rest})") "()"]
              | _, _, _, _ => throw "uninterpreted verifier operation"
            pure (sig.2.1, values)
        | _ => throw "uninterpreted local computation"
      unless types.length == outs.length && values.length == outs.length do throw "unexpected result arity"
      plan := {plan with steps := plan.steps.push (.instruction (← valueStep role who types values))}
      env := outs.zip values ++ env
    | .op k [out] (.event (.flow .message prover [peer]) t) _ =>
      unless role == peer && messages < 2 do throw "unexpected message"
      let x := if messages == 0 then "a" else "b.suffix"
      let ty ← typeTerm t
      let step := replyStep role ([prover,peer].mergeSort) ty s!".get .message {prover} {atKey k} {ty}" x
      plan := {plan with steps := plan.steps.push (.instruction step)}
      env := (out,x) :: env
      messages := messages+1
    | .op k [out] (.event (.given (.coin _) owner peers) t) [] =>
      let step ← if owner != role && !peers.contains role then valueStep role [owner] [t] ["()"]
        else do
          let ty ← typeTerm t
          pure (replyStep role ((owner :: peers).mergeSort) ty s!".own (.coin challengeLaw) {natList peers} {atKey k} [] .nil {ty}" "b.challenge")
      plan := {plan with steps := plan.steps.push (.instruction step)}
      if owner == role then env := (out,"b.challenge") :: env
    | .guard _ who cond .reject =>
      unless who == [role] do throw "expected a verifier guard"
      let test ← lookup cond
      let step := s!"refine projectedGuard (sem := sem) (by decide) {test} (by rfl) ?_"
      plan := ⟨plan.steps.push (.guard step), plan.guards.push test⟩
    | _ => throw "uninterpreted verifier instruction"
  return plan

private unsafe def readPlan (stored : Syntax) (role : Nat) : TacticM ReplayPlan := do
  let ty ← mkAppM ``NamedProgram #[mkConst ``Standard]
  let program ← Term.evalTerm (NamedProgram Standard) ty stored
  ofExcept (plan program role)

private def runStep (step : String) : TacticM Unit := do
  evalTactic (← ofExcept (Parser.runParserCategory (← getEnv) `tactic step))

syntax (name := writtenGuards) "written_guards " term:max num : tactic
@[tactic writtenGuards] unsafe def guardsTac : Tactic := fun stx => withMainContext do
  let result ← readPlan stx[1] stx[2].isNatLit?.get!
  let prop := result.guards.foldr (fun test tail => s!"{test} = true ∧ {tail}") "True"
  runStep s!"exact ({prop})"

syntax (name := writtenSteps) "written_steps " term:max num : tactic
@[tactic writtenSteps] unsafe def stepsTac : Tactic := fun stx => withMainContext do
  let result ← readPlan stx[1] stx[2].isNatLit?.get!
  for step in result.steps do
    match step with
    | .instruction script =>
      runStep "expose_cursor"
      runStep script
    | .guard script => runStep script
  runStep "expose_cursor"
  runStep "finish_guard_replay"

/-- Expose the mathematical equations to users of the generated verifier theorem.
The proof of equivalence uses the ordinary Boolean decision and conjunction lemmas. -/
private partial def guardFormula (e : Expr) : MetaM Expr := do
  if e.isAppOfArity ``And 2 then
    let l ← guardFormula e.getAppArgs[0]!
    let r ← guardFormula e.getAppArgs[1]!
    return if r.isConstOf ``True then l else mkApp2 (mkConst ``And) l r
  if e.isAppOfArity ``Eq 3 && e.getAppArgs[2]!.isConstOf ``Bool.true then
    let test := e.getAppArgs[1]!
    if test.isAppOfArity ``Decidable.decide 2 then return test.getAppArgs[0]!
  return e

elab "guard_formula% " guard:term:max : term => do
  let e ← Term.elabTermEnsuringType guard (mkSort .zero)
  guardFormula (← whnf e)

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
