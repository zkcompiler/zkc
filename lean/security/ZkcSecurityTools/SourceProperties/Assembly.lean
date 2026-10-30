module

public meta import ZkcTools.Companions.Report

public meta section

/-! Security property attempts use the common companion resolver and report.
Identity and navigation are supplied by the source owner. An open result is
returned as authoring data; the term form can only return a discharged proof.
It does not create declarations, assumptions, registrations or receipts. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.SourceProperties
open Lean Meta Elab Term ZkcTools.Companions

structure Request where
  identity : String
  source : Option SourceSpan := none
  selections : Array Selection := #[]
  responsibility : String := "source property mathematics"

def attempt (request : Request) (expected : Expr) (methods : Array DefaultMethod) :
    TermElabM (Assembly × Json) := do
  let result ← assemble request.selections expected methods
  let row ← report ⟨request.identity, request.source, request.responsibility, expected, none⟩ result
  return (result, row)

syntax (name := sourceProperty) "source_property " str
  " companions " "[" companionSelection,* "]" " via " term : term

elab_rules : term <= expected
  | `(source_property $identity:str companions [$choices:companionSelection,*] via $method:term) => do
      let selections ← choices.getElems.mapM fun choice => do
        let `(companionSelection| $key:str [$arguments:term,*]) := choice
          | throwError "invalid source property companion selection"
        return (⟨key.getString, arguments.getElems⟩ : Selection)
      let (result, row) ← attempt { identity := identity.getString, selections := selections } expected
        #[⟨"source-normal-form", method⟩]
      match result with
      | .discharged value _ _ => return value
      | .openObligation _ _ => throwError "open source property obligation: {row.compress}"
      | .refused _ _ => throwError "refused source property obligation: {row.compress}"

end ZkcSecurity.Tools.SourceProperties
