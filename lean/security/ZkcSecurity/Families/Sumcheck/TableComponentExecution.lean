module

public import ZkcSecurity.FiatShamir.HonestReadbackLoops
public import ZkcSecurity.Families.Sumcheck.TableComponentReadbackLoop
public import Zkc.Construction.DomainCalculations
public import Mathlib.Tactic.FailIfNoProgress
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Structural execution for installed table components. The elaborator reads
selected generated View definitions; it neither selects a protocol by name nor
evaluates source helpers independently. Every resulting rewrite and capture
definition is checked by the kernel. Loop bodies remain opaque component slots.
-/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent.Execution
open Zkc.Source.Structured Zkc.Construction

theorem booleanAnd {F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (left right : Bool) :
    Domain.calculate (ringModel F G) .booleanAnd
      [.data (.boolean left), .data (.boolean right)] =
      .returned [.data (.boolean (left && right))] := rfl

meta section
open Lean Meta Elab Tactic

partial def collectSpine (scope : Name) (expression : Expr) :
    StateT (NameSet × Array Name) MetaM Unit := do
  if expression.isAppOf ``Domain.View.loop then return
  match expression with
  | .const name _ =>
      if scope.isPrefixOf name && !(← get).1.contains name then
        modify fun (seen, names) => (seen.insert name, names.push name)
        if let .defnInfo definition ← getConstInfo name then
          collectSpine scope definition.value
  | .app function argument =>
      collectSpine scope function
      collectSpine scope argument
  | .lam _ _ body _ | .forallE _ _ body _ => collectSpine scope body
  | .letE _ _ value body _ => collectSpine scope value; collectSpine scope body
  | .mdata _ body => collectSpine scope body
  | .proj _ _ body => collectSpine scope body
  | _ => pure ()

/-- Unfold the selected View sequence spines without enumerating generated
step names or opening a loop's installed component body. -/
elab "unfold_component_bodies " "[" bodies:ident,* "]" : tactic => withMainContext do
  let mut names : Array Name := #[]
  for body in bodies.getElems do
    let expression ← Elab.Term.elabTerm body none
    let some name := expression.getAppFn.constName?
      | throwErrorAt body "expected a selected generated View body"
    let (_, (_, found)) ← (collectSpine name.getPrefix expression).run ({}, #[])
    names := names ++ found
  let lemmas ← (names.push ``Domain.View.sequence).mapM fun name =>
    `(Parser.Tactic.simpLemma| $(mkIdent name):term)
  evalTactic (← `(tactic| simp only [$lemmas,*]))

partial def firstIteration (expression : Expr) : Option Expr :=
  if expression.isAppOfArity ``Domain.iterate 7 then
    some expression
  else if expression.isAppOf ``PIR.Process.bind then
    let arguments := expression.getAppArgs
    firstIteration arguments[arguments.size - 2]!
  else
    match expression with
    | .mdata _ body => firstIteration body
    | _ => none

def firstCapture (expression : Expr) : Option Expr :=
  (firstIteration expression).map (fun iteration => iteration.getAppArgs[2]!)

/-- Read the nominal field from the reached producer's carried table, then
kernel-check that it is the installed generated plan's field. -/
elab "component_field " name:ident " from " plan:term : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``FiatShamir.Readback do throwError "expected a Readback goal"
  let arguments := target.getAppArgs
  let some iteration := firstIteration arguments[arguments.size - 2]!
    | throwError "producer has not reached a loop"
  let carried := iteration.getAppArgs[6]!
  unless carried.isAppOf ``List.cons do throwError "expected the actual carried table"
  let values := carried.getAppArgs
  let value := values[values.size - 2]!
  unless value.isAppOf ``Domain.Value.data do throwError "expected a carried data value"
  let payload := value.getAppArgs.back!
  unless payload.isAppOf ``Domain.Payload.vector do throwError "expected a carried vector"
  let components := payload.getAppArgs
  let field ← PrettyPrinter.delab components[components.size - 2]!
  evalTactic (← `(tactic| have $name : ReadbackRound.Plan.field $plan = $field := by rfl))

/-- Recover both immutable frames from the actual reached loop applications.
No authored capture vector, source slot number or helper result is supplied. -/
elab "component_captures " left:ident right:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``FiatShamir.Readback do
    throwError "component_captures expects a Readback goal at two reached loops; found {target.getAppFn}"
  let arguments := target.getAppArgs
  let some leftValue := firstCapture arguments[arguments.size - 2]!
    | throwError "producer has not reached an actual iterate application"
  let some rightValue := firstCapture arguments[arguments.size - 1]!
    | throwError "validator has not reached an actual iterate application"
  let mut goal ← getMainGoal
  for (name, value) in [(left.getId, leftValue), (right.getId, rightValue)] do
    goal ← goal.define name (← inferType value) value
    let (_, introduced) ← goal.intro1P
    goal := introduced
  replaceMainGoal [goal]

syntax "component_rewrite " "[" term,* "]" : tactic
macro_rules
  | `(tactic| component_rewrite []) => `(tactic| fail "no component equation applies")
  | `(tactic| component_rewrite [$law:term]) =>
      `(tactic| fail_if_no_progress (with_reducible rw [($law)]))
  | `(tactic| component_rewrite [$law:term, $rest:term,*]) =>
      `(tactic| first
        | fail_if_no_progress (with_reducible rw [($law)])
        | component_rewrite [$rest,*])

syntax "component_apply " "[" term,* "]" : tactic
macro_rules
  | `(tactic| component_apply []) => `(tactic| fail "no component rule applies")
  | `(tactic| component_apply [$rule:term]) =>
      `(tactic| with_reducible apply ($rule))
  | `(tactic| component_apply [$rule:term, $rest:term,*]) =>
      `(tactic| first
        | with_reducible apply ($rule)
        | component_apply [$rest,*])

/-- Execute pure/checkpoint structure using only supplied checked helper laws.
An installed loop or unresolved effect remains as an explicit proof obligation. -/
macro "normalize_component_process " "[" checkpoints:term,* "]" "[" laws:term,* "]"
    " unfolding " "[" definitions:term,* "]" : tactic => do
  let definitions ← definitions.getElems.mapM fun declaration =>
    `(Parser.Tactic.simpLemma| $declaration:term)
  `(tactic| repeat first
    | component_apply [$checkpoints,*]
    | component_rewrite [$laws,*]
    | component_rewrite [Domain.Calculations.indexConstant, Domain.Calculations.indexEqual,
        Domain.Calculations.booleanConstant, Domain.Calculations.booleanEqual, booleanAnd]
    | fail_if_no_progress (simp only [$definitions,*, Domain.View.participant, Domain.View.sequence, Domain.View.calculation,
        Domain.View.helper, Domain.View.guard, Domain.View.loop, Domain.View.append,
        Domain.View.empty, Domain.read, List.mapM_cons, List.mapM_nil, Bind.bind,
        Option.bind, Option.pure_def, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.cons_append, List.nil_append, Domain.sortsMatch, Domain.Value.sort,
        Domain.Payload.ty, List.map_cons, List.map_nil, Nat.lt_irrefl, PIR.Process.bind,
        beq_self_eq_true, ite_true, decide_true, decide_false, Bool.false_beq,
        Nat.zero_le, and_true, true_and, and_self])
    | fail_if_no_progress (dsimp only [Bind.bind, Pure.pure, instMonadOption,
        Option.bind, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal]))

macro "normalize_table_readback " "[" laws:term,* "]"
    " unfolding " "[" definitions:term,* "]" : tactic =>
  `(tactic| normalize_component_process
    [FiatShamir.Readback.checkpointLeft, FiatShamir.Readback.checkpointRight]
    [$laws,*] unfolding [$definitions,*])

/-- Install the reached actual loop through a generated round namespace. The
same elaboration handles every sequential occurrence. Only table mathematics
(shape, capacity and the initial honest sum) is supplied by the caller. -/
macro "readback_table_loop " round:ident " [" program:term ", " helpers:term ", "
    context:term ", " suite:term ", " sites:term ", " raw:term ", " count:term ", "
    countSmall:term ", " shape:term ", " bounded:term ", " history:term "]" " as "
    left:ident ", " right:ident ", " state:ident ", " original:ident ", " honest:ident : tactic => do
  let member (name : String) := mkIdent (round.getId ++ Name.mkSimple name)
  let plan := member "plan"
  let producerCapture := member "producerCapture"
  let validatorCapture := member "validatorCapture"
  let descriptor := member "descriptor"
  let producerBlock := member "producer_block"
  let validatorBlock := member "validator_block"
  `(tactic| (
    component_field componentField from $plan
    component_captures $left $right
    have componentLeftSize : ($left).length = $producerCapture := by
      first | rfl | simp (config := {zetaDelta := true})
        [ReadbackRound.producerCarried, ReadbackRound.validatorCarried, $producerCapture:term, $descriptor:term]
    have componentRightSize : ($right).length = $validatorCapture := by
      first | rfl | simp (config := {zetaDelta := true})
        [ReadbackRound.producerCarried, ReadbackRound.validatorCarried, $validatorCapture:term, $descriptor:term]
    have componentLoops := ReadbackRound.initial_loop_readback $plan $program $helpers
      $context $sites $left $right $raw $count $countSmall $shape $bounded $history
    simp only [componentLeftSize, componentRightSize] at componentLoops
    rw [← $producerBlock _ _ $program $context $suite,
      ← $validatorBlock _ _ $program $context $suite] at componentLoops
    dsimp only [$producerCapture:term, $validatorCapture:term, $descriptor:term] at componentLoops
    simp only [componentField, Nat.reduceAdd, $suite:term] at componentLoops
    simp only [PIR.Process.bind_assoc]
    set_option backward.isDefEq.respectTransparency false in
      apply componentLoops.bind
    intro componentLeft componentRight componentInvariant
    obtain ⟨$state, $original, _componentRemaining, $honest,
      componentLeftEq, componentRightEq⟩ := componentInvariant
    subst componentLeft componentRight))

end
end ZkcSecurity.Families.Sumcheck.TableComponent.Execution
