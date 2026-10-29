module

public import Zkc.Source.Structured.MultilinearAdmissionReference
public import Zkc.Source.Structured.MultilinearReferenceInstallation

@[expose] public section

/-! The admission and terminal helpers extend the same complete library binding.
The selected bodies supply all dependency equations. Claims remain arbitrary. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Zkc.Source.Structured.ReferenceLibrary.Multilinear.Admission
open Zkc.Source MultilinearBodies Zkc.Polynomial.Multilinear

structure Bodies (definitions : List CheckedDefinition) (domain : String) (bindings : Bindings)
    (checker : String) : Prop extends Multilinear.Bodies definitions domain bindings where
  rows : BodyIn definitions (rowsHelper bindings) (rowsBody domain bindings)
  shape : BodyIn definitions (shapeHelper domain bindings) (shapeBody domain bindings)
  table : BodyIn definitions (tableHelper domain bindings) (tableBody domain bindings)
  checkTable : BodyIn definitions (checkTableHelper domain bindings) (checkTableBody domain bindings)
  check : BodyIn definitions ⟨checker, .local,
    [.vector domain, .vector domain, .field domain], [.boolean]⟩ (checkBody domain bindings)

variable {definitions : List CheckedDefinition} {domain : String} {bindings : Bindings} {checker : String}
  (model : DomainModel) (linked : DeclarationsLinked [] definitions)
  (bodies : Bodies definitions domain bindings checker)
include linked bodies

theorem rows_eq (n : Nat) (small : n < 64) :
    invoke (closed model (definitions := definitions)) (rowsHelper bindings) (indexResult model n) =
      .done (indexResult model (2^n)) := by
  apply ReferenceLaw.invoke (model := model) (helper := rowsHelper bindings)
    (rows model domain bindings) definitions linked bodies.rows
  refine ⟨small, ?_⟩
  have comparison := less_eq model linked bodies.toBodies n 64
  simpa [less, Values.get, Nat.lt_trans small (show 64 < indexLimit by decide +kernel),
    show 64 < indexLimit by decide +kernel, small, primitiveOutcome, boolResult, indexResult] using comparison

set_option backward.isDefEq.respectTransparency false in
theorem shape_eq (xs : List (model.Field domain)) (n w : Nat)
    (lengthBound : xs.length < indexLimit) (nBound : n < indexLimit) (wBound : w < indexLimit) :
    invoke (closed model (definitions := definitions)) (shapeHelper domain bindings)
      (tableValues model domain xs n w) = .done (boolResult model (decide (HasShape xs n w))) := by
  apply ReferenceLaw.invoke (model := model) (helper := shapeHelper domain bindings)
    (shape model domain bindings) definitions linked bodies.shape
  change (shape model domain bindings).Requires (closed model (definitions := definitions))
    (tableValues model domain xs n w)
  dsimp only [shape, tableValues, Values.get]
  refine ⟨lengthBound, nBound, wBound, ?_, ?_, fun small => rows_eq model linked bodies n small⟩
  · simpa [less, Values.get, wBound, show 0 < indexLimit by decide +kernel,
      primitiveOutcome, boolResult] using less_eq model linked bodies.toBodies 0 w
  · simpa [less, Values.get, nBound, show 64 < indexLimit by decide +kernel,
      primitiveOutcome, boolResult] using less_eq model linked bodies.toBodies n 64

theorem table_eq (xs : List (model.Field domain)) (n w : Nat)
    (lengthBound : xs.length < indexLimit) (nBound : n < indexLimit) (wBound : w < indexLimit) :
    invoke (closed model (definitions := definitions)) (tableHelper domain bindings)
      (tableValues model domain xs n w) = primitiveOutcome (tableOutcome model domain xs n w) := by
  apply ReferenceLaw.invoke (model := model) (helper := tableHelper domain bindings)
    (table model domain bindings) definitions linked bodies.table
  exact shape_eq model linked bodies xs n w lengthBound nBound wBound

theorem checkTable_eq (xs point : List (model.Field domain)) (claim : model.Field domain)
    (lengthBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    invoke (closed model (definitions := definitions)) (checkTableHelper domain bindings)
      (checkInputs model domain xs point claim) = primitiveOutcome (checkTableOutcome model domain xs point claim) := by
  apply ReferenceLaw.invoke (model := model) (helper := checkTableHelper domain bindings)
    (checkTable model domain bindings) definitions linked bodies.checkTable
  change (checkTable model domain bindings).Requires (closed model (definitions := definitions))
    (checkInputs model domain xs point claim)
  dsimp only [checkTable, checkInputs, Values.get]
  refine ⟨pointBound, table_eq model linked bodies xs point.length 1 lengthBound pointBound (by decide +kernel), ?_, ?_⟩
  · intro valid
    have restriction := prefix_eq model linked bodies.toBodies xs point point.length 1
      lengthBound valid.2.1 (by decide +kernel) (by simpa using valid.length)
    simpa [prefixOutcome, pointBound, tableValues, primitiveOutcome] using restriction
  · intro _
    exact valuesRealization_eq model linked bodies.toBodies (restrictPrefixValues xs point) 0 1

theorem check_eq (xs point : List (model.Field domain)) (claim : model.Field domain)
    (lengthBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    invoke (closed model (definitions := definitions))
      ⟨checker, .local, [.vector domain, .vector domain, .field domain], [.boolean]⟩
      (checkInputs model domain xs point claim) = .done (boolResult model
        (decide (HasShape xs point.length 1 ∧ (restrictPrefixValues xs point).sum = claim))) := by
  apply ReferenceLaw.invoke (model := model)
    (helper := ⟨checker, .local, [.vector domain, .vector domain, .field domain], [.boolean]⟩)
    (check model domain bindings) definitions linked bodies.check
  change (check model domain bindings).Requires (closed model (definitions := definitions))
    (checkInputs model domain xs point claim)
  dsimp only [check, checkInputs, Values.get]
  exact ⟨pointBound, shape_eq model linked bodies xs point.length 1 lengthBound pointBound (by decide +kernel),
    fun _ => checkTable_eq model linked bodies xs point claim lengthBound pointBound⟩

end Zkc.Source.Structured.ReferenceLibrary.Multilinear.Admission
