module

public import ZkcSecurityExamples.RootProperties.SmallSumcheck.Soundness

/-! Checked boundary controls for the actual shared checker and optional Math
helper. Raw lists have no shape or length premise in the large-dimension case.
These are source-body equations, separate from the cryptographic claims. -/
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.SumcheckSourceAdmissionControls
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Multilinear Multilinear.Admission MultilinearBodies
open ZkcExamples.Structured SumcheckSourceSelections
attribute [local implicit_reducible] Op.arguments Op.results Op.regions
variable (model : DomainModel) (domain : String) (bindings : Bindings)
private theorem get_cons_here {types : List Ty} {ty : Ty} (value : model.Value ty)
    (rest : Values model.Value types) : (Values.cons value rest).get .here = value := rfl
private theorem get_cons_there {types : List Ty} {ty head : Ty} (value : model.Value head)
    (rest : Values model.Value types) (position : Var types ty) :
    (Values.cons value rest).get (.there position) = rest.get position := rfl

def pointOverflow : ReferenceLaw model [.vector domain, .vector domain, .field domain] [.boolean] where
  body := checkBody domain bindings
  Requires _ args := ¬ (args.get (.there .here)).length < indexLimit
  reference _ := .stopped .exhausted
  valid table args overflow := by
    cases args with
    | cons xs rest => cases rest with
      | cons point rest => cases rest with
        | cons claim rest =>
          cases rest
          change ¬ point.length < indexLimit at overflow
          simp [checkBody, Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
            Operands.eval, Regions.denote, Values.get_cons, get_cons_here, get_cons_there,
            Values.get, Environment.prepend, Environment.push, SiteObservations.closed,
            SiteObservations.silent, PIR.Process.bind, Primitive.evaluateOn, primitiveOutcome, overflow]

def largeShape : ReferenceLaw model (triple domain) [.boolean] where
  body := MultilinearBodies.shapeBody domain bindings
  Requires table args :=
    args.get (.there (.there .here)) = 1 ∧ ¬ args.get (.there .here) < 64 ∧
    invoke table (lessHelper bindings) (.cons 0 (.cons 1 .nil)) = .done (boolResult model true) ∧
    invoke table (lessHelper bindings) (.cons (args.get (.there .here)) (.cons 64 .nil)) =
      .done (boolResult model false)
  reference _ := .returned (boolResult model false)
  valid table args premises := by
    cases args with
    | cons xs rest => cases rest with
      | cons n rest => cases rest with
        | cons w rest =>
          cases rest
          obtain ⟨rfl, large, first, second⟩ := premises
          change ¬ n < 64 at large
          change invoke table (lessHelper bindings) (.cons n (.cons 64 .nil)) = .done (boolResult model false) at second
          simp only [MultilinearBodies.shapeBody, tableValues, Region.denote, Evaluation.meaningOn,
            Evaluation.operationOn, Operands.eval, Regions.denote, Values.get_cons,
            get_cons_here, get_cons_there, Values.get, Environment.prepend, Environment.push,
            SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
            Evaluation.invokeCallbackOn, Values.split]
          simp [Primitive.evaluateOn, primitiveOutcome, first, second, boolResult,
            show 0 < indexLimit by decide +kernel, show 64 < indexLimit by decide +kernel,
            PIR.Process.bind, Values.get_cons, get_cons_here, get_cons_there,
            Values.get, Environment.prepend, Environment.push, Values.split]

def largeCheck : ReferenceLaw model [.vector domain, .vector domain, .field domain] [.boolean] where
  body := checkBody domain bindings
  Requires table args := (args.get (.there .here)).length < indexLimit ∧
    invoke table (shapeHelper domain bindings)
      (tableValues model domain (args.get .here) (args.get (.there .here)).length 1) =
        .done (boolResult model false)
  reference _ := .returned (boolResult model false)
  valid table args premises := by
    cases args with
    | cons xs rest => cases rest with
      | cons point rest => cases rest with
        | cons claim rest =>
          cases rest
          obtain ⟨pointBound, shape⟩ := premises
          change point.length < indexLimit at pointBound
          change invoke table (shapeHelper domain bindings) (tableValues model domain xs point.length 1) = .done (boolResult model false) at shape
          simp only [checkBody, checkTrueBody, checkFalseBody, checkInputs, Region.denote,
            Evaluation.meaningOn, Evaluation.operationOn, Operands.eval, Regions.denote,
            Values.get_cons, get_cons_here, get_cons_there, Values.get, Environment.prepend,
            Environment.push, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
            Evaluation.invokeCallbackOn, Values.split]
          simp only [Primitive.evaluateOn, pointBound, show 1 < indexLimit by decide +kernel,
            ↓reduceIte, primitiveOutcome, PIR.Process.bind, Values.get_cons, get_cons_here,
            get_cons_there, Values.get, Environment.prepend, Environment.push]
          change (invoke table (shapeHelper domain bindings)
            (tableValues model domain xs point.length 1)).bind _ = _
          rw [shape]
          rfl

variable (selection : Selection)
theorem point_overflow (raw point : List (model.Field field)) (scalar : model.Field field)
    (overflow : ¬ point.length < indexLimit) :
    invoke (SumcheckReferenceInstallation.tables model (source selection).payload.definitions).closed
      Generated.Bindings.SmallSumcheckInputs.helper33Helper
      (checkInputs model field raw point scalar) = .halt .exhausted := by
  rw [Evaluation.closed_invoke_componentTablesOn]
  rw [ReferenceLaw.invoke (model := model)
    (helper := Generated.Bindings.SmallSumcheckInputs.helper33Helper)
    (pointOverflow model field SumcheckSourceSelections.bindings)
    (source selection).payload.definitions (source selection).payload.linked (admissionBodies selection).check
    (checkInputs model field raw point scalar) overflow]
  rfl

/-- A representable large dimension returns false before any raw-length guard. -/
theorem large_dimension (raw point : List (model.Field field)) (scalar : model.Field field)
    (finite : point.length < indexLimit) (large : ¬ point.length < 64) :
    invoke (SumcheckReferenceInstallation.tables model (source selection).payload.definitions).closed
      Generated.Bindings.SmallSumcheckInputs.helper33Helper
      (checkInputs model field raw point scalar) = .done (boolResult model false) := by
  have shape : invoke (closed model (definitions := (source selection).payload.definitions))
      (shapeHelper field SumcheckSourceSelections.bindings)
      (tableValues model field raw point.length 1) = .done (boolResult model false) := by
    apply ReferenceLaw.invoke (model := model)
      (helper := shapeHelper field SumcheckSourceSelections.bindings)
      (largeShape model field SumcheckSourceSelections.bindings)
      (source selection).payload.definitions (source selection).payload.linked (admissionBodies selection).shape
    refine ⟨rfl, large, ?_, ?_⟩
    · simpa [tableValues, less, Values.get, primitiveOutcome, boolResult, show 0 < indexLimit by decide +kernel,
        show 1 < indexLimit by decide +kernel] using
        less_eq model (source selection).payload.linked (admissionBodies selection).toBodies 0 1
    · simpa [tableValues, less, Values.get, primitiveOutcome, boolResult, large, finite,
        show 64 < indexLimit by decide +kernel] using
        less_eq model (source selection).payload.linked (admissionBodies selection).toBodies point.length 64
  rw [Evaluation.closed_invoke_componentTablesOn]
  rw [ReferenceLaw.invoke (model := model)
    (helper := Generated.Bindings.SmallSumcheckInputs.helper33Helper)
    (largeCheck model field SumcheckSourceSelections.bindings)
    (source selection).payload.definitions (source selection).payload.linked (admissionBodies selection).check
    (checkInputs model field raw point scalar) ⟨finite, shape⟩]
  rfl

/-- The actual optional mathematical helper preserves an absent Boolean. -/
example (right : Option Bool) :
    invoke (SumcheckReferenceInstallation.tables model (source .twoSums).payload.definitions).components
      Generated.Bindings.TwoSumsInputs.helper25Helper (.cons none (.cons right .nil)) =
      .done (.cons none .nil) := by
  kernel_rfl

#print axioms point_overflow
#print axioms large_dimension
end TestsSecurity.SumcheckSourceAdmissionControls
