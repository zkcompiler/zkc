module

public import Zkc.Formal.Relation.Values
public import Zkc.Core.EveryRun

@[expose] public section

/-! Two models related: processes.

Two processes over the effects of two models are related when they have one shape: they stop
with one reason; they perform the same effect at the same site, with related values sent and
related inputs of a law; and on related replies they go on related. A value that one returns is
related to the value that the other returns by a relation given for the results. A law that
they draw or sample has covered replies: every reply that the second model can give has a
related reply of the first (`Covered`).

- `ProcessRelated.bind`: sequencing keeps the relation.
- `everyRun_related`: when every run of the first process returns a value of which a condition
  holds, so does every run of the second.

The relation is about the replies that can be given, not about how likely each is: it carries
a statement about every run, and no statement about a probability.
-/

set_option autoImplicit false

namespace Zkc.Formal

open Zkc.Source Zkc.Core PIR

variable {M N : Model}

/-- Every value of a type in the second model has a related value in the first. -/
def Covered (R : Carriers M N) (type : Ty) : Prop :=
  ∀ image : N.Value type, ∃ value : M.Value type, Related R type value image

/-- Two processes over the effects of two models are related: they perform the same effects at
the same sites with related values, stop alike and return related values. A draw and a sample
are of a law whose replies are covered: every reply of the second model has a related reply of
the first. -/
inductive ProcessRelated (R : Carriers M N) {A B : Type} (post : A → B → Prop) :
    Process (Effects M) A → Process (Effects N) B → Prop where
  | done {value : A} {image : B} : post value image → ProcessRelated R post (.done value) (.done image)
  | halt (reason : Stop) : ProcessRelated R post (.halt reason) (.halt reason)
  | send (site : Site) (type : Ty) {value : M.Value type} {image : N.Value type}
      {next : PUnit → Process (Effects M) A} {next' : PUnit → Process (Effects N) B} :
      Related R type value image → ProcessRelated R post (next ⟨⟩) (next' ⟨⟩) →
        ProcessRelated R post (.call (.send site type value) next) (.call (.send site type image) next')
  | receive (site : Site) (type : Ty)
      {next : M.Value type → Process (Effects M) A} {next' : N.Value type → Process (Effects N) B} :
      (∀ reply image, Related R type reply image → ProcessRelated R post (next reply) (next' image)) →
        ProcessRelated R post (.call (.receive site type) next) (.call (.receive site type) next')
  | draw (site : Site) (law : SamplingRow) {inputs : Values M.Value law.inputs}
      {inputs' : Values N.Value law.inputs}
      {next : M.Value law.output → Process (Effects M) A}
      {next' : N.Value law.output → Process (Effects N) B} :
      Covered R law.output → ValuesRelated (Related R) inputs inputs' →
      (∀ reply image, Related R law.output reply image →
        ProcessRelated R post (next reply) (next' image)) →
        ProcessRelated R post (.call (.draw site law inputs) next) (.call (.draw site law inputs') next')
  | sample (site : Site) (law : SamplingRow) {inputs : Values M.Value law.inputs}
      {inputs' : Values N.Value law.inputs}
      {next : M.Value law.output → Process (Effects M) A}
      {next' : N.Value law.output → Process (Effects N) B} :
      Covered R law.output → ValuesRelated (Related R) inputs inputs' →
      (∀ reply image, Related R law.output reply image →
        ProcessRelated R post (next reply) (next' image)) →
        ProcessRelated R post (.call (.sample site law inputs) next)
          (.call (.sample site law inputs') next')

namespace ProcessRelated

variable {R : Carriers M N} {A B C D : Type}

/-- Sequencing keeps the relation. -/
theorem bind {middle : A → B → Prop} {post : C → D → Prop}
    {first : Process (Effects M) A} {second : Process (Effects N) B}
    (same : ProcessRelated R middle first second)
    (next : A → Process (Effects M) C) (next' : B → Process (Effects N) D)
    (continues : ∀ value image, middle value image → ProcessRelated R post (next value) (next' image)) :
    ProcessRelated R post (first.bind next) (second.bind next') := by
  induction same with
  | done holds => exact continues _ _ holds
  | halt reason => exact .halt reason
  | send site type sent _ ih => exact .send site type sent ih
  | receive site type _ ih => exact .receive site type fun reply image same => ih reply image same
  | draw site law covered inputs _ ih =>
    exact .draw site law covered inputs fun reply image same => ih reply image same
  | sample site law covered inputs _ ih =>
    exact .sample site law covered inputs fun reply image same => ih reply image same

/-- A weaker relation of the results. -/
theorem mono {post weaker : A → B → Prop} (weakens : ∀ value image, post value image → weaker value image)
    {first : Process (Effects M) A} {second : Process (Effects N) B}
    (same : ProcessRelated R post first second) : ProcessRelated R weaker first second := by
  induction same with
  | done holds => exact .done (weakens _ _ holds)
  | halt reason => exact .halt reason
  | send site type sent _ ih => exact .send site type sent ih
  | receive site type _ ih => exact .receive site type ih
  | draw site law covered inputs _ ih => exact .draw site law covered inputs ih
  | sample site law covered inputs _ ih => exact .sample site law covered inputs ih

end ProcessRelated

/-! ## Every run -/

/-- Every run of the first of two related processes returns a value of which a condition
holds, and related results carry the condition. Then every run of the second returns a value
of which the second condition holds: a reply of the second model to a draw or a sample has a
related reply of the first, on which the first process returns. -/
theorem everyRun_related {R : Carriers M N} {A B : Type} {post : A → B → Prop}
    {holds : A → Prop} {holds' : B → Prop} (carries : ∀ value image, post value image → holds value → holds' image)
    {first : Process (Effects M) A} {second : Process (Effects N) B}
    (same : ProcessRelated R post first second) :
    EveryRun holds first → EveryRun holds' second := by
  induction same with
  | done related => exact fun every => carries _ _ related every
  | halt reason => exact fun every => every
  | send site type _ _ _ => exact fun every => every
  | receive site type _ _ => exact fun every => every
  | draw site law covered _ _ ih =>
    intro every image
    obtain ⟨reply, related⟩ := covered image
    exact ih reply image related (every reply)
  | sample site law covered _ _ ih =>
    intro every image
    obtain ⟨reply, related⟩ := covered image
    exact ih reply image related (every reply)

end Zkc.Formal
