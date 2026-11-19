module

public import Zkc.Formal.Relation.Region

@[expose] public section

/-! Two models related: local code.

The local operations whose two meanings are related, and what each asks:

- a pure or restricted row: that the row is respected as a row of its kind (`RowRespected`):
  on related inputs a pure row gives related outputs, and a restricted row has a value in both
  models or in neither. A law is respected when the replies of its output type are covered;
  no local operation applies a law, and the protocol operations that draw and sample ask for
  it;
- a call: that the function is related, which the functions before it give;
- `if` and `guard`: nothing: a condition is a `bool`, and related `bool`s are equal;
- a literal of a type whose values the core fixes: nothing.

A `match`, a `loop`, an operation that the core owns and a literal of a nominal type are not
among them yet: a region that has one does not pass the test `LocalOp.relatable`, and the
theorem says nothing of it.

`functions_related`: the functions of a program whose bodies pass the test have related
meanings, when the rows that the test names are respected.
-/

set_option autoImplicit false

namespace Zkc.Formal

open Zkc.Source Zkc.Core PIR

variable {M N : Model}

/-- Two options are related: both have related values, or neither has one. -/
def OptionRelated {α β : Type} (related : α → β → Prop) : Option α → Option β → Prop
  | some value, some image => related value image
  | none, none => True
  | _, _ => False

/-- A row is respected by a relation of two models, as a row of its kind: on related inputs a
pure row gives related outputs, and a restricted row has related outputs in both models or a
value in neither; a law has outputs whose replies are covered. -/
def RowRespected (R : Carriers M N) (row : OperationRow) : OperationKind → Prop
  | .pure =>
      ∀ (populated : Ty.allPopulated row.outputs = true) (values : Values M.Value row.inputs)
        (images : Values N.Value row.inputs), ValuesRelated (Related R) values images →
          ValuesRelated (Related R) (M.pure row populated values) (N.pure row populated images)
  | .restricted _ =>
      ∀ (values : Values M.Value row.inputs) (images : Values N.Value row.inputs),
        ValuesRelated (Related R) values images →
          OptionRelated (ValuesRelated (Related R)) (M.restricted row values)
            (N.restricted row images)
  | .sampling => ∀ output, output ∈ row.outputs → Covered R output

/-- The rows of an operation table with the given numbers are respected. -/
def RowsRespected (R : Carriers M N) (operations : List OperationSignature) (rows : List Nat) : Prop :=
  ∀ {inputs outputs : List Ty} {kind : OperationKind} (row : Var operations ⟨inputs, outputs, kind⟩),
    row.index ∈ rows → RowRespected R (.of row) kind

/-- Two tables of functions are related: every function gives related processes on related
inputs. -/
def FunctionsRelated (R : Carriers M N) {functions : List FunctionHeader}
    (first : FunctionTable M functions) (second : FunctionTable N functions) : Prop :=
  ∀ {header : FunctionHeader} (callee : Var functions header) (values : Values M.Value header.inputs)
    (images : Values N.Value header.inputs), ValuesRelated (Related R) values images →
      ProcessRelated R (ValuesRelated (Related R)) (first.get callee values) (second.get callee images)

section Operations

variable {operations : List OperationSignature} {functions : List FunctionHeader} {deployed : Bool}

/-- The local operations that the relation of two models covers, with the rows it may use. -/
def LocalOp.relatable (rows : List Nat) : LocalOp operations functions deployed → Bool
  | .op row _ => rows.contains row.index
  | .call .. => true
  | .conditional .. => true
  | .guard _ => true
  | .literal (.nominal ..) => false
  | .literal _ => true
  | .match .. => false
  | .loop .. => false
  | .builtin _ => false

theorem ListRelated.refl {α : Type} {related : α → α → Prop} (reflexive : ∀ value, related value value) :
    ∀ values : List α, ListRelated related values values
  | [] => trivial
  | value :: rest => ⟨reflexive value, ListRelated.refl reflexive rest⟩

/-- A literal of a type whose values the core fixes is the same value in two models. -/
theorem literal_related (R : Carriers M N) :
    ∀ value : Literal, (match value with | .nominal .. => false | _ => true) = true →
      Related R value.type (value.value M) (value.value N)
  | .nat _, _ => by simp only [Related, Literal.value]
  | .bool _, _ => by simp only [Related, Literal.value]
  | .fin _ _, _ => by simp only [Related, Literal.value]
  | .bytes data, _ => by
    simp only [Related, Literal.value]
    exact ListRelated.refl (fun _ => rfl) data
  | .nominal _ _, within => Bool.noConfusion within

variable {R : Carriers M N} {rows : List Nat}
  {first : FunctionTable M functions} {second : FunctionTable N functions}

/-- A local operation that passes the test has related meanings in two models whose rows are
respected and whose functions are related. -/
theorem local_compatible (respected : RowsRespected R operations rows)
    (tables : FunctionsRelated R first second) :
    ∀ op : LocalOp operations functions deployed, LocalOp.relatable rows op = true →
      CompatibleAt R (localMeaning M first) (localMeaning N second) (Related R) op
  | .op (kind := kind) row applies, within => by
    intro values images same _ _ _
    have respects : RowRespected R (.of row) kind :=
      respected row (List.contains_iff_mem.mp within)
    show ProcessRelated R _ (rowProcess M (.of row) kind applies values)
      (rowProcess N (.of row) kind applies images)
    cases kind with
    | pure => exact .done (respects applies values images same)
    | restricted domain =>
      have defined := respects values images same
      show ProcessRelated R _ (definedProcess M (M.restricted (.of row) values))
        (definedProcess N (N.restricted (.of row) images))
      cases left : M.restricted (.of row) values with
      | none =>
        cases right : N.restricted (.of row) images with
        | none => exact .halt _
        | some _ => rw [left, right] at defined; exact defined.elim
      | some outputs =>
        cases right : N.restricted (.of row) images with
        | none => rw [left, right] at defined; exact defined.elim
        | some outputs' => rw [left, right] at defined; exact .done defined
    | sampling => exact absurd applies Bool.false_ne_true
  | .call callee _, _ => fun values images same _ _ _ => tables callee values images same
  | .conditional captures outputs, _ => by
    intro values images same bodies bodies' regions
    have flag : values.get Var.here = images.get Var.here := by
      simpa only [Related] using same Ty.bool Var.here
    show ProcessRelated R _
      (cond (values.get Var.here) ((bodies.get Var.here) values.tail)
        ((bodies.get (Var.there Var.here)) values.tail))
      (cond (images.get Var.here) ((bodies'.get Var.here) images.tail)
        ((bodies'.get (Var.there Var.here)) images.tail))
    rw [flag]
    cases images.get (ty := Ty.bool) Var.here with
    | true => exact regions _ Var.here _ _ same.tail
    | false => exact regions _ (Var.there Var.here) _ _ same.tail
  | .guard reason, _ => by
    intro values images same _ _ _
    have flag : values.get Var.here = images.get Var.here := by
      simpa only [Related] using same Ty.bool Var.here
    show ProcessRelated R _
      (cond (values.get Var.here) (Process.done Values.nil) (Process.halt reason.stop))
      (cond (images.get Var.here) (Process.done Values.nil) (Process.halt reason.stop))
    rw [flag]
    cases images.get (ty := Ty.bool) Var.here with
    | true => exact .done ValuesRelated.nil
    | false => exact .halt _
  | .literal value, within => by
    intro _ _ _ _ _ _
    refine .done (ValuesRelated.cons (literal_related R value ?_) ValuesRelated.nil)
    cases value <;> first | rfl | exact Bool.noConfusion within
  | .match .., within => Bool.noConfusion within
  | .loop .., within => Bool.noConfusion within
  | .builtin _, within => Bool.noConfusion within

end Operations

/-! ## The functions of a program -/

section Functions

variable {typeTable : TypeTable} {operations : List OperationSignature}

/-- Every function of a program is written in the core language, and its body passes the
test. -/
def _root_.Zkc.Core.Functions.relatable (rows : List Nat) :
    {functions : List FunctionHeader} → Functions typeTable operations functions → Bool
  | _, .nil => true
  | _, .snoc earlier definition _ =>
      earlier.relatable rows && definition.body.all (LocalOp.relatable rows)
  | _, .opaque .. => false

variable {R : Carriers M N} {rows : List Nat}

/-- The functions of a program that pass the test have related meanings in two models whose
rows are respected. -/
theorem functions_related (respected : RowsRespected R operations rows) :
    {functions : List FunctionHeader} → (program : Functions typeTable operations functions) →
      program.relatable rows = true → FunctionsRelated R (program.table M) (program.table N)
  | _, .nil, _ => fun callee => callee.elimNil
  | _, .snoc earlier definition _, within => by
    simp only [Functions.relatable, Bool.and_eq_true] at within
    have before : FunctionsRelated R (earlier.table M) (earlier.table N) :=
      functions_related respected earlier within.1
    intro callee values images same
    cases callee with
    | here =>
      exact region_related (local_compatible respected before) definition.body within.2 _ _
        (EnvironmentRelated.ofValues same)
    | there callee => exact before callee values images same
  | _, .opaque .., within => Bool.noConfusion within

end Functions

end Zkc.Formal
