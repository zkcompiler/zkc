module

public import Zkc.Source.Structured.CommonCoordinateExecution

@[expose] public section

/-! Root observations read the actual optional inputs. A missing input stays missing.
The generated contract requests value observations of named source ports; equal host
carriers, tags, or extents cannot substitute for those observations. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm

variable {model : DomainModel}

def inputObservations : {types : List Ty} →
    Values (Component (ProtocolValue model.toCarriers)) types →
    Observations model (types.map Slot.value)
  | _, .nil => .nil
  | _, .cons head tail => .cons (head.bind ProtocolValue.toConcrete) (inputObservations tail)

theorem input_readback {types : List Ty}
    (values : Values (Component (ProtocolValue model.toCarriers)) types) :
    Matches (inputSymbols.inputTerms types) (inputObservations values) values := by
  induction values with
  | nil => intro ty position; cases position
  | @cons ty types value values ih =>
    intro type position term known
    cases position with
    | here =>
      cases ty <;> simp only [inputSymbols.inputTerms, Values.get, Option.some.injEq] at known
      all_goals first
        | contradiction
        | (subst term; rfl)
    | there position =>
      simp only [inputSymbols.inputTerms, Values.get, get_map] at known
      cases original : (inputSymbols.inputTerms types).get position with
      | none =>
        simp only [original, Option.map_none] at known
        contradiction
      | some originalTerm =>
        have same : term = originalTerm.rename (fun position ↦ .there position) := by
          simpa only [original, Option.map_some, Option.some.injEq] using known.symm
        subst term
        exact (ih position originalTerm original).trans
          (observe_rename (model := model) (fun position ↦ .there position) originalTerm
            (inputObservations values) (inputObservations (.cons value values))
              (fun _ ↦ rfl)).symm

theorem masked_input_readback (pair : Pair) (self : Nat) (member : pair.includes self)
    (context : ProtocolContext) {types : List Ty} (scopes : List (List Nat))
    (values : Values (Component (ProtocolValue model.toCarriers)) types) :
    Matches (inputSymbols pair context.roles types scopes) (inputObservations values)
      (maskValues self (context.mapScopes scopes) values) :=
  matches_mask pair self member context scopes _ _ _ (input_readback values)

/-- Only source input ports generate external requirements. Counter bindings instead
require a matching reached structural application/repeat prefix. -/
def externalRequirements (certificate : List (Pair × Selection)) : List (Pair × Binding) :=
  certificate.flatMap fun (pair, selection) ↦
    selection.requirements.filterMap fun binding ↦ match binding with
      | .input .. => some (pair, binding)
      | .counter .. => none

end Zkc.Source.Structured.CommonCoordinate
