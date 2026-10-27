module

public import Zkc.Construction.DomainView
public meta import Zkc.Construction.ArtifactBindingTactic
public meta import Lean.Elab.Tactic

@[expose] public meta section

/-! Inspect selected generated Process views without a protocol registry.
Loops remain opaque component slots. Every unfolding produces an ordinary
kernel-checked equality in the caller's actual Process goal. -/
set_option autoImplicit false
namespace Zkc.Construction.ProcessViewTactic
open Zkc.Source.Structured Zkc.Construction Lean Meta Elab Tactic

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
  evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [$lemmas,*]))

/-- Normalize public View equations while retaining helper and loop slots.
Their source certificates are applied before any closed helper evaluation. -/
macro "normalize_component_operations " "[" laws:Parser.Tactic.simpLemma,* "]"
    " unfolding " "[" definitions:term,* "]" : tactic => do
  let definitions ← definitions.getElems.mapM fun term =>
    `(Parser.Tactic.simpLemma| $term:term)
  let lemmas := definitions ++ laws.getElems
  `(tactic| simp (config := { failIfUnchanged := false }) only [↓Original.stopAtCall, $lemmas,*,
    Domain.View.participant, Domain.View.sequence, Domain.View.calculation,
    Domain.View.guard, Domain.View.append, Domain.View.empty,
    Domain.View.receive, Domain.View.send, Domain.View.indicesEmpty,
    Domain.View.indicesAppend, Domain.View.observe, Domain.View.challenge,
    Domain.read, List.mapM_cons, List.mapM_nil, Bind.bind, Option.bind, Option.pure_def,
    Option.map_some, Option.map_none,
    Option.getD_some, Option.getD_none, List.getD_cons_zero, List.getD_cons_succ,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.cons_append, List.nil_append, Domain.sortsMatch, Domain.Value.sort,
    Domain.Payload.ty, Domain.Value.encode, Domain.Payload.ofValue, Domain.dataType,
    ↓reduceTransport,
    List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    List.filter_cons, List.filter_nil, List.all_cons, List.all_nil,
    List.length_cons, List.length_nil, List.length_append,
    Function.comp_apply, id_eq, PIR.Process.bind, PIR.Process.bind_assoc,
    Domain.Calculations.fieldAdd, Domain.Calculations.fieldSubtract,
    Domain.Calculations.fieldMultiply, Domain.Calculations.fieldEqual,
    Domain.Calculations.fieldConstant, Domain.Calculations.indexConstant,
    Domain.Calculations.indexEqual, Domain.Calculations.booleanConstant,
    Domain.Calculations.booleanEqual,
    String.reduceEq, String.reduceBEq, String.reduceAppend,
    Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
    Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
    beq_self_eq_true, ite_true, ite_false, ↓reduceDIte,
    decide_true, decide_false, Bool.false_beq, Bool.true_eq_false,
    Nat.zero_le, and_true, true_and, and_self,
    not_false_eq_true, decide_eq_true_eq, decide_eq_false_iff_not])


end Zkc.Construction.ProcessViewTactic
