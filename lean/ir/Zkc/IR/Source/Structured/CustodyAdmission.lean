module

public import Zkc.IR.Source.Structured.Checked

@[expose] public section

/-! Static custody admission.

A custody value (`Ty.resourceUnit`) is a nominal, role-local affine permission
without payload. Admission keeps every custody value to one use and every
custody transfer inside a checked custody frame:

* a Local helper that mentions custody is a straight-line custody frame
  (`Region.custodyFrame`): custody transfers, site marks, calls of custody-free
  helpers on data and callback-free calculations, each custody variable used at
  most once;
* a Math helper never mentions custody;
* a protocol body uses each custody value at most once (`RawRegion.custodyAffine`)
  and never captures one in a repeated callback.

`Zkc.Source.Structured.CustodySoundness` proves what an admitted custody frame
guarantees against the custody ledger. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

def Op.isCustody : Op → Bool
  | .createUnit _ | .passUnit _ | .consumeUnit _ => true
  | _ => false

/-! ## Admission: custody frames -/

/-- The context positions of the custody operands, in operand order. -/
def Operands.custodyIndices {Γ : List Ty} : {args : List Ty} → Operands Γ args → List Nat
  | [], .nil => []
  | ty :: _, .cons v rest => (if ty.isCustody then [v.index] else []) ++ custodyIndices rest

/-- An operation that neither transfers nor carries custody, and calls only
named custody-free helpers. -/
def Op.custodyFreeStep (custodyFree : String → Bool) (op : Op) : Bool :=
  !op.isCustody && !(op.arguments ++ op.results).any Ty.isCustody &&
    op.helpers.all fun helper => custodyFree helper.name

/-- An operation of a custody frame: a custody transfer, a site mark, a call of
a named custody-free helper on data, or a helper-free operation whose ports are
data. Callbacks of the latter are custody-free (`Region.custodyFrame`). -/
def Op.custodyStep (custodyFree : String → Bool) : Op → Bool
  | .createUnit _ | .passUnit _ | .consumeUnit _ | .mark _ => true
  | .invoke helper => custodyFree helper.name && !(helper.inputs ++ helper.outputs).any Ty.isCustody
  | op => op.helpers.isEmpty && !(op.arguments ++ op.results).any Ty.isCustody

/-- A custody frame: its custody transfers and custody values stay on the
straight-line spine, no custody variable is used twice, and every callback is
custody-free. `spent` lists the context positions already used. -/
def _root_.Zkc.Source.Region.custodyFrame (custodyFree : String → Bool) : {Γ out : List Ty} →
    List Nat → Region dialect Γ out → Bool
  | _, _, spent, .ret values =>
    let used := Operands.custodyIndices values
    used.Nodup && used.all (fun index => !spent.contains index)
  | _, _, _, .stop _ => true
  | _, _, spent, .letOp op arguments bodies next =>
    let used := Operands.custodyIndices arguments
    op.custodyStep custodyFree && bodies.erase.operations.all (Op.custodyFreeStep custodyFree) &&
      used.Nodup && used.all (fun index => !spent.contains index) &&
      next.custodyFrame custodyFree ((spent ++ used).map (· + op.results.length))
  | _, _, _, .bind .. => false

theorem Operands.custodyIndices_mem {Γ : List Ty} : {args : List Ty} → (operands : Operands Γ args) →
    {slot : String} → (position : Var args (.resourceUnit slot)) →
    (operands.get position).index ∈ Operands.custodyIndices operands
  | _ :: _, .cons _ _, _, .here => by
    simp only [Operands.custodyIndices, Ty.isCustody, ↓reduceIte, Values.get, List.singleton_append,
      List.mem_cons, true_or]
  | _ :: _, .cons _ rest, _, .there position => by
    simp only [Operands.custodyIndices, Values.get, List.mem_append]
    exact .inr (custodyIndices_mem rest position)

theorem Operands.custodyIndices_inj {Γ : List Ty} : {args : List Ty} → (operands : Operands Γ args) →
    (Operands.custodyIndices operands).Nodup → {first second : String} →
    (left : Var args (.resourceUnit first)) → (right : Var args (.resourceUnit second)) →
    (operands.get left).index = (operands.get right).index → left.index = right.index
  | _ :: _, .cons _ _, _, _, _, .here, .here, _ => rfl
  | _ :: _, .cons value rest, unique, _, _, .here, .there right, same => by
    simp only [Operands.custodyIndices, Ty.isCustody, ↓reduceIte, List.singleton_append,
      List.nodup_cons] at unique
    simp only [Values.get] at same
    exact absurd (same ▸ custodyIndices_mem rest right) unique.1
  | _ :: _, .cons value rest, unique, _, _, .there left, .here, same => by
    simp only [Operands.custodyIndices, Ty.isCustody, ↓reduceIte, List.singleton_append,
      List.nodup_cons] at unique
    simp only [Values.get] at same
    exact absurd (same.symm ▸ custodyIndices_mem rest left) unique.1
  | _ :: _, .cons value rest, unique, _, _, .there left, .there right, same => by
    have tail : (Operands.custodyIndices rest).Nodup := by
      simp only [Operands.custodyIndices] at unique
      exact (List.nodup_append.mp unique).2.1
    simp only [Values.get] at same
    simp only [Var.index]
    exact congrArg (· + 1) (custodyIndices_inj rest tail left right same)

/-! ## Helper tables -/

/-- A definition without custody: no custody port, no custody transfer and no
custody operand or result anywhere in its body, and calls of custody-free
helpers only. -/
def CheckedDefinition.custodyFree (free : String → Bool) (definition : CheckedDefinition) : Bool :=
  !(definition.inputs ++ definition.outputs).any Ty.isCustody &&
    definition.raw.operations.all (Op.custodyFreeStep free)

/-- The names of the custody-free definitions of an ordered helper list, each
judged against the custody-free names before it. -/
def custodyFreeNames : List CheckedDefinition → List String → List String
  | [], names => names
  | definition :: rest, names =>
    custodyFreeNames rest
      (if definition.custodyFree names.contains then definition.name :: names else names)

/-- Every definition of an ordered helper list is custody-free, or is a Local
custody frame over the custody-free helpers before it. -/
def checkCustodyFrames : List CheckedDefinition → List String → Except String Unit
  | [], _ => pure ()
  | definition :: rest, names => do
    if definition.custodyFree names.contains then
      checkCustodyFrames rest (definition.name :: names)
    else
      if definition.kind != .local then throw "structured-custody-math"
      if !definition.body.custodyFrame names.contains [] then throw "structured-custody-frame"
      checkCustodyFrames rest names

/-! ## Protocol bodies -/

mutual
  /-- Each custody value of a body is used at most once. Callbacks are checked in
  their own contexts; their operations' admission decides which operands they
  may carry (a repeat carries custody only as state). -/
  def _root_.Zkc.Source.RawRegion.custodyAffine {Op : Type} : RawRegion Ty Op → List Ty → List Nat → Bool
    | .ret indices, context, spent =>
      let used := indices.filter fun index => (context[index]?).any Ty.isCustody
      used.Nodup && used.all (fun index => !spent.contains index)
    | .stop _, _, _ => true
    | .letOp _ arguments results bodies next, context, spent =>
      let used := arguments.filter fun index => (context[index]?).any Ty.isCustody
      used.Nodup && used.all (fun index => !spent.contains index) &&
        bodies.custodyAffine &&
        next.custodyAffine (results ++ context) ((spent ++ used).map (· + results.length))
    | .bind .., _, _ => false

  def _root_.Zkc.Source.RawRegions.custodyAffine {Op : Type} : RawRegions Ty Op → Bool
    | .nil => true
    | .cons inputs _ body rest => body.custodyAffine inputs [] && rest.custodyAffine
end

end Zkc.Source.Structured
