module

public import Zkc.Source.Structured.SumReference

@[expose] public section

/-! Complete-signature installation of the nominal finite-sum library.
No whole-table reduction or source-name dispatch supplies a dependency law. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.ReferenceLibrary.Sum
open Zkc.Source Multilinear

structure Bodies (model : DomainModel) (definitions : List CheckedDefinition)
    (field : String) (b : Bindings) : Prop where
  add : BodyIn definitions (addHelper field b) (add model field).body
  step : BodyIn definitions (foldSpec field b).stepHelper (step model field b).body
  total : BodyIn definitions (totalHelper field b) (total model field b).body

/-- The source target fixes which sum chain is installed. A second, unrelated
sum implementation in the same library cannot satisfy this anchor. -/
structure ScalarBodies (model : DomainModel) (definitions : List CheckedDefinition)
    (field name : String) (b : Bindings) : Prop extends Bodies model definitions field b where
  relation : BodyIn definitions ⟨name, .math, [.vector field, .field field], [.boolean]⟩
    (scalarRelation model field b).body

/-- A pair relation selects its actual common sum dependency, without choosing
helper names or a finite-domain identifier by hand. -/
structure PairBodies (model : DomainModel) (definitions : List CheckedDefinition)
    (field name : String) (b : Bindings) : Prop extends Bodies model definitions field b where
  relation : BodyIn definitions
    ⟨name, .math, [.vector field, .vector field, .field field, .field field], [.boolean]⟩
    (pairRelation model field b).body

variable (model : DomainModel) {definitions : List CheckedDefinition} {field : String} {b : Bindings}
  (linked : DeclarationsLinked [] definitions) (bodies : Bodies model definitions field b)
include linked bodies

attribute [local implicit_reducible] addHelper totalHelper foldSpec

theorem add_eq (a c : model.Field field) :
    invoke (closed model (definitions := definitions)) (addHelper field b)
      (.cons a (.cons c .nil)) = .done (.cons (a+c) .nil) :=
  ReferenceLaw.invoke (model := model) (helper := addHelper field b) (add model field) definitions linked bodies.add _ trivial

set_option backward.isDefEq.respectTransparency false in
theorem step_eq (xs : List (model.Field field)) (a value : model.Field field) :
    invoke (closed model (definitions := definitions)) (foldSpec field b).stepHelper
      (.cons a (.cons value (.cons xs .nil))) = .done (.cons (a+value) .nil) := by
  apply ReferenceLaw.invoke (model := model) (helper := (foldSpec field b).stepHelper) (step model field b) definitions linked bodies.step
  exact add_eq model linked bodies a value

theorem total_eq (xs : List (model.Field field)) :
    invoke (closed model (definitions := definitions)) (totalHelper field b) (.cons xs .nil) =
      primitiveOutcome (totalOutcome model field xs) := by
  apply ReferenceLaw.invoke (model := model) (helper := totalHelper field b) (total model field b) definitions linked bodies.total
  exact step_eq model linked bodies xs

/-- Bounded adequacy computes false as well as true claims. -/
theorem scalar_eq (name : String)
    (associated : BodyIn definitions ⟨name, .math, [.vector field, .field field], [.boolean]⟩
      (scalarRelation model field b).body)
    (xs : List (model.Field field)) (scalar : model.Field field) :
    invoke (closed model (definitions := definitions))
      ⟨name, .math, [.vector field, .field field], [.boolean]⟩ (.cons xs (.cons scalar .nil)) =
      primitiveOutcome ((scalarRelation model field b).reference (.cons xs (.cons scalar .nil))) := by
  apply ReferenceLaw.invoke (model := model)
    (helper := ⟨name, .math, [.vector field, .field field], [.boolean]⟩) (scalarRelation model field b) definitions linked associated
  exact total_eq model linked bodies xs


set_option backward.isDefEq.respectTransparency false in
theorem pending_eq (name : String) {metadata : MultilinearBodies.Bindings}
    (metadataBodies : Multilinear.Bodies definitions field metadata)
    (associated : BodyIn definitions
      ⟨name, .math, [.vector field, .index, .index, .vector field, .field field], [.boolean]⟩
      (pendingRelation model field b metadata.values).body)
    (xs point : List (model.Field field)) (n w : Nat) (scalar : model.Field field) :
    invoke (closed model (definitions := definitions))
      ⟨name, .math, [.vector field, .index, .index, .vector field, .field field], [.boolean]⟩
      (.cons xs (.cons n (.cons w (.cons point (.cons scalar .nil))))) =
      primitiveOutcome ((pendingRelation model field b metadata.values).reference
        (.cons xs (.cons n (.cons w (.cons point (.cons scalar .nil)))))) := by
  apply ReferenceLaw.invoke (model := model)
    (helper := ⟨name, .math, [.vector field, .index, .index, .vector field, .field field], [.boolean]⟩)
    (pendingRelation model field b metadata.values) definitions linked associated
  exact ⟨Multilinear.values_eq model linked metadataBodies xs n w,
    total_eq model linked bodies (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point)⟩

theorem pair_eq (name : String)
    (associated : BodyIn definitions
      ⟨name, .math, [.vector field, .vector field, .field field, .field field], [.boolean]⟩
      (pairRelation model field b).body)
    (xs ys : List (model.Field field)) (a c : model.Field field) :
    invoke (closed model (definitions := definitions))
      ⟨name, .math, [.vector field, .vector field, .field field, .field field], [.boolean]⟩
      (.cons xs (.cons ys (.cons a (.cons c .nil)))) =
      primitiveOutcome ((pairRelation model field b).reference (.cons xs (.cons ys (.cons a (.cons c .nil))))) := by
  apply ReferenceLaw.invoke (model := model)
    (helper := ⟨name, .math, [.vector field, .vector field, .field field, .field field], [.boolean]⟩)
    (pairRelation model field b) definitions linked associated
  exact ⟨total_eq model linked bodies xs, total_eq model linked bodies ys⟩

omit bodies in
set_option backward.isDefEq.respectTransparency false in
theorem tableShape_eq (name : String) {metadata : MultilinearBodies.Bindings}
    (metadataBodies : Multilinear.Bodies definitions field metadata)
    (associated : BodyIn definitions ⟨name, .math, [.vector field, .index, .index], [.boolean]⟩
      (tableShape model field metadata).body)
    (xs : List (model.Field field)) (n w : Nat) :
    invoke (closed model (definitions := definitions))
      ⟨name, .math, [.vector field, .index, .index], [.boolean]⟩ (.cons xs (.cons n (.cons w .nil))) =
      .done (.cons (decide (w = 1 ∧ xs.length = 2 ^ n)) .nil) := by
  apply ReferenceLaw.invoke (model := model)
    (helper := ⟨name, .math, [.vector field, .index, .index], [.boolean]⟩)
    (tableShape model field metadata) definitions linked associated
  exact ⟨Multilinear.width_eq model linked metadataBodies xs n w,
    Multilinear.values_eq model linked metadataBodies xs n w,
    Multilinear.dimension_eq model linked metadataBodies xs n w⟩

end Zkc.Source.Structured.ReferenceLibrary.Sum
