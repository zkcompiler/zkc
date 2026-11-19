module

public import Zkc.Core.Meaning

@[expose] public section

/-! Two models related: values.

A relation between two models is a relation between their carriers, for each nominal type.
It is lifted to the values of every type: at `bool`, `nat` and `index<n>` the core fixes the
values for every model and control reads them, so related values there are equal; a
collection, a tuple, a record and a variant are related part by part. It need not be one to
one: several values of one model may stand for one value of the other.

Tuples of values and environments are related position by position, for any family of values
over any index (`ValuesRelated`, `EnvironmentRelated`): the typed values of local code, and the
held values of a side.
-/

set_option autoImplicit false

namespace Zkc.Formal

open Zkc.Source Zkc.Core

/-- A relation between the carriers of two models, per nominal type. -/
abbrev Carriers (M N : Model) := (row : Nat) → M.Carrier row → N.Carrier row → Prop

/-- Two lists related element by element; they have one length. -/
def ListRelated {α β : Type} (related : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | first :: rest, second :: others => related first second ∧ ListRelated related rest others
  | _, _ => False

theorem ListRelated.length_eq {α β : Type} {related : α → β → Prop} :
    ∀ {first : List α} {second : List β}, ListRelated related first second →
      first.length = second.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, same => congrArg (· + 1) (ListRelated.length_eq same.2)
  | [], _ :: _, same => same.elim
  | _ :: _, [], same => same.elim

/-- Related lists, each mapped by functions that keep the relation, are related. -/
theorem ListRelated.map {α β γ δ : Type} {related : α → β → Prop} {image : γ → δ → Prop}
    {change : α → γ} {other : β → δ}
    (keeps : ∀ value datum, related value datum → image (change value) (other datum)) :
    ∀ {first : List α} {second : List β}, ListRelated related first second →
      ListRelated image (first.map change) (second.map other)
  | [], [], _ => True.intro
  | _ :: _, _ :: _, same => ⟨keeps _ _ same.1, ListRelated.map keeps same.2⟩
  | [], _ :: _, same => same.elim
  | _ :: _, [], same => same.elim

/-- Two pairs of related lists, combined element by element by functions that keep the
relation, are related. -/
theorem ListRelated.zipWith {α β γ δ : Type} {related : α → β → Prop} {image : γ → δ → Prop}
    {combine : α → α → γ} {other : β → β → δ}
    (keeps : ∀ value datum later after, related value datum → related later after →
      image (combine value later) (other datum after)) :
    ∀ {first left : List α} {second right : List β}, ListRelated related first second →
      ListRelated related left right →
        ListRelated image (List.zipWith combine first left)
          ((second.zip right).map fun (datum, after) => other datum after)
  | [], _, [], _, _, _ => True.intro
  | _ :: _, [], _ :: _, [], _, _ => True.intro
  | _ :: _, _ :: _, _ :: _, _ :: _, same, others =>
      ⟨keeps _ _ _ _ same.1 others.1, ListRelated.zipWith keeps same.2 others.2⟩
  | [], _, _ :: _, _, same, _ => same.elim
  | _ :: _, _, [], _, same, _ => same.elim
  | _ :: _, [], _ :: _, _ :: _, _, others => others.elim
  | _ :: _, _ :: _, _ :: _, [], _, others => others.elim

section Lifted

variable {M N : Model}

mutual
  /-- The relation of two models at the values of a type. -/
  def Related (R : Carriers M N) : (type : Ty) → M.Value type → N.Value type → Prop
    | .bool, first, second => first = second
    | .nat, first, second => first = second
    | .fin _, first, second => first = second
    | .nominal row, first, second => R row first second
    | .seq element none, first, second => ListRelated (Related R element) first second
    | .seq element (some _), first, second =>
        ListRelated (Related R element) first.val second.val
    | .tuple components, first, second => RelatedTuple R components first second
    | .record _ _ fields, first, second => RelatedTuple R fields first second
    | .variant _ alternatives, first, second => RelatedVariant R alternatives first second

  def RelatedTuple (R : Carriers M N) :
      (components : List Ty) → Ty.Tuple M.Carrier components → Ty.Tuple N.Carrier components → Prop
    | [], _, _ => True
    | component :: rest, first, second =>
        Related R component first.1 second.1 ∧ RelatedTuple R rest first.2 second.2

  def RelatedVariant (R : Carriers M N) :
      (alternatives : List Ty) → Ty.Variant M.Carrier alternatives →
        Ty.Variant N.Carrier alternatives → Prop
    | [], first, _ => nomatch first
    | alternative :: _, .inl first, .inl second => Related R alternative first second
    | _ :: rest, .inr first, .inr second => RelatedVariant R rest first second
    | _ :: _, .inl _, .inr _ => False
    | _ :: _, .inr _, .inl _ => False
end

end Lifted

/-! ## Tuples of values and environments, over any index -/

section Families

variable {T : Type} {V W : T → Type}

/-- Two tuples of values are related position by position. -/
def ValuesRelated (related : ∀ index, V index → W index → Prop) {indices : List T}
    (first : Values V indices) (second : Values W indices) : Prop :=
  ∀ (index : T) (position : Var indices index), related index (first.get position) (second.get position)

/-- Two environments are related at every reference. -/
def EnvironmentRelated (related : ∀ index, V index → W index → Prop) {Γ : List T}
    (first : Environment V Γ) (second : Environment W Γ) : Prop :=
  ∀ (index : T) (reference : Var Γ index), related index (first reference) (second reference)

variable {related : ∀ index, V index → W index → Prop}

theorem ValuesRelated.nil : ValuesRelated related (Values.nil : Values V []) Values.nil :=
  fun _ position => position.elimNil

theorem ValuesRelated.cons {index : T} {indices : List T} {value : V index} {other : W index}
    {values : Values V indices} {others : Values W indices} (head : related index value other)
    (tail : ValuesRelated related values others) :
    ValuesRelated related (.cons value values) (.cons other others) := by
  intro index position
  cases position with
  | here => exact head
  | there position => exact tail _ position

theorem ValuesRelated.head {index : T} {indices : List T} {values : Values V (index :: indices)}
    {others : Values W (index :: indices)} (same : ValuesRelated related values others) :
    related index (values.get .here) (others.get .here) :=
  same _ .here

theorem ValuesRelated.tail {index : T} {indices : List T} {values : Values V (index :: indices)}
    {others : Values W (index :: indices)} (same : ValuesRelated related values others) :
    ValuesRelated related values.tail others.tail := by
  intro index position
  cases values with
  | cons value values =>
    cases others with
    | cons other others => exact same _ position.there

theorem EnvironmentRelated.push {Γ : List T} {env : Environment V Γ} {other : Environment W Γ}
    (same : EnvironmentRelated related env other) {index : T} {value : V index} {image : W index}
    (head : related index value image) :
    EnvironmentRelated related (env.push value) (other.push image) := by
  intro index reference
  cases reference with
  | here => exact head
  | there reference => exact same _ reference

theorem EnvironmentRelated.bindAll {Γ : List T} :
    ∀ {added : List T} (env : Environment V Γ) (other : Environment W Γ) (values : Values V added)
      (others : Values W added), EnvironmentRelated related env other →
      ValuesRelated related values others →
        EnvironmentRelated related (env.bindAll values) (other.bindAll others) := by
  intro added
  induction added generalizing Γ with
  | nil => exact fun _ _ _ _ same _ => same
  | cons index rest ih =>
    intro env other values others same parts
    cases values with
    | cons value values =>
      cases others with
      | cons image others =>
        exact ih (env.push value) (other.push image) values others
          (same.push (parts _ .here)) (fun _ position => parts _ position.there)

theorem ValuesRelated.operands {Γ indices : List T} {env : Environment V Γ}
    {other : Environment W Γ} (same : EnvironmentRelated related env other)
    (operands : Operands Γ indices) :
    ValuesRelated related (operands.eval env) (operands.eval other) := by
  intro index position
  simp only [Operands.get_eval]
  exact same _ (operands.get position)

theorem EnvironmentRelated.ofValues {indices : List T} {values : Values V indices}
    {others : Values W indices} (same : ValuesRelated related values others) :
    EnvironmentRelated related (Environment.ofValues values) (Environment.ofValues others) :=
  EnvironmentRelated.bindAll _ _ _ _ (fun _ reference => reference.elimNil) same

end Families

end Zkc.Formal
