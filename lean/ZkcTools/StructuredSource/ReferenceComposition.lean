module

public import Zkc.Source.Structured.CollectionReference
public meta import ZkcTools.StructuredSource.HelperPresentation

@[expose] public section

/-! Propose existing library compositions from an actual typed source tree.
Only forwarding calls, silent markers and complete collection returns are
accepted. Exact body equality is checked after construction; identifiers never
select a mathematical law. -/

set_option autoImplicit false
namespace ZkcTools.StructuredSource.ReferenceComposition
open Zkc.Source Zkc.Source.Structured

public meta section
open Lean Meta Elab Term

/-- Normalize only structural argument/return conversions, then transport the
complete named outcome through its explicit return encoding. -/
macro "reference_encoding" " [" definitions:Lean.Parser.Tactic.simpArg,* "]" : tactic => do
  let definitions : Syntax.TSepArray
    [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] "," :=
      ⟨definitions.elemsAndSeps⟩
  `(tactic| {
    simp only [$definitions,*, ReferenceLibrary.indexedCollection, Values.get_head,
      Values.get_tail, Var.weakenPrefix, Operands.eval, Values.append, Collection.pack]
    split <;> rename_i admission <;> simp only [admission] <;> rfl })

def operation (body : Expr) : MetaM (Expr × Expr × Expr) := do
  let body ← whnf body
  unless body.isAppOf ``Region.letOp do
    throwError "reference composition expects a forwarding operation with a complete return"
  let args := body.getAppArgs
  return (args[args.size - 4]!, args[args.size - 3]!, args[args.size - 1]!)

elab "collection_spec% " body:term : term => do
  withoutErrToSorry do
    let (op, _, _) ← operation (← elabTerm body none)
    let op ← whnf op
    unless op.isAppOf ``Op.collect do
      throwError "collection_spec% requires an actual collection"
    return op.getAppArgs.back!

def checkBody (law body : Expr) : TermElabM Expr := do
  let proposed ← mkAppM ``ReferenceLaw.body #[law]
  unless ← isDefEq proposed body do
    throwError "reference composition does not preserve the complete actual body"
  return law

partial def forwarding (body dependency model : Expr) : TermElabM Expr := do
  let (op, arguments, next) ← operation body
  let op ← whnf op
  if op.isAppOf ``Op.mark then
    let law ← forwarding next dependency model
    checkBody (← mkAppM ``ReferenceLibrary.marked #[model, op.getAppArgs.back!, law]) body
  else if op.isAppOf ``Op.invoke then
    let reference ← mkAppM ``ReferenceLaw.reference #[dependency]
    let law ← mkAppM ``ReferenceLibrary.forward
      #[model, op.getAppArgs.back!, arguments, reference]
    checkBody law body
  else throwError "reference composition expects an actual helper call or source marker"

elab "forward_reference% " body:term " using " dependency:term : term => do
  withoutErrToSorry do
    let body ← elabTerm body none
    let dependency ← elabTerm dependency none
    synthesizeSyntheticMVarsNoPostponing
    let type ← whnf (← inferType dependency)
    unless type.isAppOf ``ReferenceLaw do
      throwError "forward_reference% requires an explicit ReferenceLaw"
    forwarding body dependency type.getAppArgs[0]!

def curried (model types result : Expr) (term : Syntax) : TermElabM Expr := do
  let value ← mkAppM ``Carriers.Value #[← mkAppM ``FieldModel.toCarriers #[← mkAppM ``DomainModel.toFieldModel #[model]]]
  let expected ← withTransparency .all <| reduceAll (← mkAppM ``Values.Curried #[value, types, result])
  let function ← elabTermEnsuringType term expected
  let argumentsType ← mkAppM ``Values #[value, types]
  withLocalDeclD `arguments argumentsType fun arguments => do
    let mut remaining := types
    let mut precedingTypes : Array Expr := #[]
    let mut applied := function
    repeat
      remaining ← whnf remaining
      if remaining.isAppOf ``List.nil then break
      unless remaining.isAppOf ``List.cons do
        throwError "reference composition requires a concrete complete input schema"
      let head := remaining.getAppArgs[1]!
      let tail := remaining.getAppArgs[2]!
      let here ← mkAppOptM ``Var.here #[none, some tail, some head]
      let selected ← mkAppM ``Var.weakenPrefix #[← mkListLit (mkConst ``Ty) precedingTypes.toList, here]
      applied := mkApp applied (← mkAppM ``Values.get #[arguments, selected])
      precedingTypes := precedingTypes.push head
      remaining := tail
    mkLambdaFVars #[arguments] applied

elab "collection_reference% " body:term " with_model " model:term
    " with_shape " shape:term " with_items " items:term " with_formula " formula:term : term => do
  withoutErrToSorry do
    let body ← elabTerm body none
    let model ← elabTermEnsuringType model (mkConst ``DomainModel)
    let type ← whnf (← inferType body)
    unless type.isAppOf ``Region do
      throwError "collection_reference% requires an actual typed helper body"
    let inputTypes := type.getAppArgs[1]!
    let (op, arguments, _) ← operation body
    let op ← whnf op
    unless op.isAppOf ``Op.collect do
      throwError "collection_reference% requires an actual collection"
    let spec := op.getAppArgs.back!
    let shape ← curried model inputTypes (← mkAppM ``PIR.Outcome #[mkConst ``Nat]) shape
    let domain ← mkAppM ``CollectSpec.domain #[spec]
    let itemTypes ← mkAppM ``DomainSpec.items #[domain]
    let itemType ← mkAppM ``Values #[← mkAppM ``Carriers.Value #[← mkAppM ``FieldModel.toCarriers #[← mkAppM ``DomainModel.toFieldModel #[model]]], itemTypes]
    let items ← curried model inputTypes (← mkArrow (mkConst ``Nat) itemType) items
    let helper ← mkAppM ``CollectSpec.bodyHelper #[spec]
    let helperInputs ← mkAppM ``Helper.inputs #[helper]
    let collection ← mkAppM ``CollectSpec.collection #[spec]
    let element ← mkAppM ``Collection.element #[collection]
    let formula ← curried model helperInputs (← mkAppM ``Carriers.Value #[← mkAppM ``FieldModel.toCarriers #[← mkAppM ``DomainModel.toFieldModel #[model]], element]) formula
    let predicate ← mkAppM ``CollectSpec.predicate #[spec]
    let absentType ← mkEq (← mkAppM ``String.isEmpty #[predicate]) (mkConst ``Bool.true)
    unless ← isDefEq (← mkAppM ``String.isEmpty #[predicate]) (mkConst ``Bool.true) do
      throwError "collection_reference% requires an unfiltered collection"
    let absent ← elabTermEnsuringType (← `(by rfl)) absentType
    let law ← mkAppM ``ReferenceLibrary.indexedCollection
      #[model, spec, arguments, shape, items, formula, absent]
    checkBody law body

end
end ZkcTools.StructuredSource.ReferenceComposition
