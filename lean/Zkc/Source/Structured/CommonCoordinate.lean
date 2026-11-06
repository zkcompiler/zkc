module

public import Zkc.Source.Structured.NormalForm.Normalize
public import Zkc.Source.Structured.OracleProtocol

@[expose] public section

/-! Ordinary coordinate provenance, after import. Terms are the existing typed normal-form
terms, with no helper laws. Optional binder observations never fill an absent source value.
The conservative scalar profile deliberately excludes Local, receive, service and carried
state leaves. Agreement does not imply availability, lookup success or table consistency. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm

abbrev Expression (scope : Scope) := Term [] scope
abbrev Symbols (scope : Scope) := Values (fun ty ↦ Option (Expression scope ty))
abbrev Observations (model : DomainModel) (scope : Scope) :=
  Values (fun slot ↦ Option (Slot.Value model slot)) scope

mutual
  def observe (model : DomainModel) {scope : Scope} {ty : Ty} :
      Expression scope ty → Observations model scope → Option (model.Value ty)
    | .var position, values => values.get position
    | .result position field, values => (values.get position).map (·.get field)
    | .capability _ handle, _ => some handle
    | .index value, _ => some value
    | .bool value, _ => some value
    | .field domain value, _ => some (fieldLiteral model.toFieldModel domain value)
    | .groupZero _, _ => some 0
    | .calc op total args position, values =>
      (observeTerms model args values).map (fun args ↦ (op.evalTotal model total args).get position)
    | .law entry _ _, _ => Fin.elim0 entry

  def observeTerms (model : DomainModel) {scope : Scope} {types : List Ty} :
      Terms [] scope types → Observations model scope → Option (Values model.Value types)
    | .nil, _ => some .nil
    | .cons head tail, values => do
      let head ← observe model head values
      let tail ← observeTerms model tail values
      return .cons head tail
end

mutual
  def demanded {scope : Scope} {ty : Ty} : Expression scope ty → List Nat
    | .var position => [position.index]
    | .result position _ => [position.index]
    | .calc _ _ args _ => demandedTerms args
    | .law entry _ _ => Fin.elim0 entry
    | _ => []

  def demandedTerms {scope : Scope} {types : List Ty} : Terms [] scope types → List Nat
    | .nil => []
    | .cons head tail => demanded head ++ demandedTerms tail
end

/-- Agreement of exactly the typed observations demanded by a term. Neither a matching
nominal carrier nor equality of extent or tag discharges a value observation. -/
def AgreeOn (model : DomainModel) {scope : Scope} (positions : List Nat)
    (left right : Observations model scope) : Prop :=
  ∀ {slot} (position : Var scope slot), position.index ∈ positions →
    left.get position = right.get position

mutual
  theorem observe_agreement (model : DomainModel) {scope : Scope} {ty : Ty}
      (term : Expression scope ty) (left right : Observations model scope)
      (agree : AgreeOn model (demanded term) left right) :
      observe model term left = observe model term right := by
    cases term with
    | var position => exact agree position (by simp [demanded])
    | result position field =>
      simp only [observe, agree position (by simp [demanded])]
    | capability | index | bool | field | groupZero => rfl
    | law entry => exact Fin.elim0 entry
    | «calc» op total args position =>
      exact congrArg (Option.map (fun args ↦ (op.evalTotal model total args).get position))
        (observeTerms_agreement model args left right agree)

  theorem observeTerms_agreement (model : DomainModel) {scope : Scope} {types : List Ty}
      (terms : Terms [] scope types) (left right : Observations model scope)
      (agree : AgreeOn model (demandedTerms terms) left right) :
      observeTerms model terms left = observeTerms model terms right := by
    cases terms with
    | nil => rfl
    | cons head tail =>
      have first := observe_agreement model head left right
        (fun position member ↦ agree position (List.mem_append_left _ member))
      have rest := observeTerms_agreement model tail left right
        (fun position member ↦ agree position (List.mem_append_right _ member))
      simp only [observeTerms, first, rest]
end

/-- The scalar operations with a proved optional-value readback. Word operations use
exactly the existing modulo-2^64 semantics, without a natural-successor assumption. -/
def scalar : Op → Bool
  | .indexConstant _ | .indexWrappingAdd | .indexWrappingSubtract | .indexBitAnd |
    .indexLogicalShiftRight | .indexPowerOfTwo => true
  | _ => false

theorem scalar_total {op : Op} (allowed : scalar op = true) : op.total = true := by
  cases op <;> simp_all [scalar, Op.total]

def collect {scope : Scope} : {types : List Ty} → Symbols scope types →
    Option (Terms [] scope types)
  | _, .nil => some .nil
  | _, .cons head tail => do
    let head ← head
    let tail ← collect tail
    return .cons head tail

def unknown (scope : Scope) (types : List Ty) : Symbols scope types :=
  Values.absent (Expression scope) types

def calculated {scope : Scope} (op : Op) (allowed : scalar op = true)
    (terms : Terms [] scope op.arguments) : Symbols scope op.results :=
  mapValues (fun position ↦ some (.calc op (scalar_total allowed) terms position))
    (Operands.identity op.results)

end Zkc.Source.Structured.CommonCoordinate
