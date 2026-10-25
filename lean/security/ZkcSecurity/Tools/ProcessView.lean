module

public import Zkc.Construction.DomainView
public meta import Lean.Elab.Tactic

@[expose] public meta section

/-! Inspect selected generated Process views without a protocol registry.
Loops remain opaque component slots. Every unfolding produces an ordinary
kernel-checked equality in the caller's actual Process goal. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.ProcessView
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
  evalTactic (← `(tactic| simp only [$lemmas,*]))

end ZkcSecurity.Tools.ProcessView
