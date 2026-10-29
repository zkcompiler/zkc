module

public import Zkc.Source.Structured.MultilinearAdmissionInstallation

@[expose] public section

/-! Overflow rejection laws for the same source admission/checker templates.
The finite mathematical equations remain unchanged. These local laws cover the
unbounded nominal input model used by the fixed soundness experiment.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Families.Sumcheck.SourceAdmission
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Multilinear Multilinear.Admission
open MultilinearBodies
attribute [local implicit_reducible] Op.arguments Op.results Op.regions

variable (model : DomainModel) (domain : String) (bindings : Bindings)

private theorem get_cons_here {types : List Ty} {ty : Ty} (value : model.Value ty)
    (rest : Values model.Value types) : (Values.cons value rest).get .here = value := rfl
private theorem get_cons_there {types : List Ty} {ty head : Ty} (value : model.Value head)
    (rest : Values model.Value types) (position : Var types ty) :
    (Values.cons value rest).get (.there position) = rest.get position := rfl

def shapeOverflow : ReferenceLaw model (triple domain) [.boolean] where
  body := shapeBody domain bindings
  Requires table args :=
    ¬ (args.get .here).length < indexLimit ∧ args.get (.there (.there .here)) = 1 ∧
    invoke table (lessHelper bindings) (.cons 0 (.cons 1 .nil)) = .done (boolResult model true) ∧
    invoke table (lessHelper bindings) (.cons (args.get (.there .here)) (.cons 64 .nil)) =
      .done (boolResult model true)
  reference _ := .stopped .exhausted
  valid table args premises := by
    cases args with
    | cons xs rest => cases rest with
      | cons n rest => cases rest with
        | cons w rest =>
          cases rest
          obtain ⟨overflow, rfl, first, second⟩ := premises
          change ¬ xs.length < indexLimit at overflow
          change invoke table (lessHelper bindings) (.cons n (.cons 64 .nil)) = .done (boolResult model true) at second
          simp only [shapeBody, tableValues, Region.denote, Evaluation.meaningOn,
            Evaluation.operationOn, Operands.eval, Regions.denote, Values.get_cons,
            get_cons_here, get_cons_there, Values.get, Environment.prepend, Environment.push,
            SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
            Evaluation.invokeCallbackOn, Values.split]
          simp only [Primitive.evaluateOn, primitiveOutcome, first, second, boolResult,
            show 0 < indexLimit by decide +kernel, show 64 < indexLimit by decide +kernel,
            overflow, ↓reduceIte, PIR.Process.bind, Values.get_cons, get_cons_here, get_cons_there,
            Values.get, Environment.prepend, Environment.push, Values.split]

def checkOverflow : ReferenceLaw model [.vector domain, .vector domain, .field domain] [.boolean] where
  body := checkBody domain bindings
  Requires table args := (args.get (.there .here)).length < indexLimit ∧
    invoke table (shapeHelper domain bindings)
      (tableValues model domain (args.get .here) (args.get (.there .here)).length 1) = .halt .exhausted
  reference _ := .stopped .exhausted
  valid table args premises := by
    cases args with
    | cons xs rest => cases rest with
      | cons point rest => cases rest with
        | cons claim rest =>
          cases rest
          obtain ⟨pointBound, shape⟩ := premises
          change point.length < indexLimit at pointBound
          change invoke table (shapeHelper domain bindings) (tableValues model domain xs point.length 1) = .halt .exhausted at shape
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

variable {definitions : List CheckedDefinition} {checker : String}
  (linked : DeclarationsLinked [] definitions)
  (bodies : Multilinear.Admission.Bodies definitions domain bindings checker)
include linked bodies

theorem shape_overflow (xs : List (model.Field domain)) (n : Nat)
    (overflow : ¬ xs.length < indexLimit) (small : n < 64) :
    invoke (closed model (definitions := definitions)) (shapeHelper domain bindings)
      (tableValues model domain xs n 1) = .halt .exhausted := by
  apply ReferenceLaw.invoke (model := model) (helper := shapeHelper domain bindings)
    (shapeOverflow model domain bindings) definitions linked bodies.shape
  change ¬ xs.length < indexLimit ∧ (1 : Nat) = 1 ∧
    invoke _ (lessHelper bindings) (.cons 0 (.cons 1 .nil)) = .done (boolResult model true) ∧
    invoke _ (lessHelper bindings) (.cons n (.cons 64 .nil)) = .done (boolResult model true)
  refine ⟨overflow, rfl, ?_, ?_⟩
  · simpa [less, Values.get, primitiveOutcome, boolResult, show 0 < indexLimit by decide +kernel, show 1 < indexLimit by decide +kernel] using less_eq model linked bodies.toBodies 0 1
  · simpa [less, Values.get, primitiveOutcome, boolResult, small,
      Nat.lt_trans small (show 64 < indexLimit by decide +kernel), show 64 < indexLimit by decide +kernel]
      using less_eq model linked bodies.toBodies n 64

theorem check_overflow (xs point : List (model.Field domain)) (claim : model.Field domain)
    (overflow : ¬ xs.length < indexLimit) (small : point.length < 64) :
    invoke (closed model (definitions := definitions))
      ⟨checker, .local, [.vector domain, .vector domain, .field domain], [.boolean]⟩
      (checkInputs model domain xs point claim) = .halt .exhausted := by
  apply ReferenceLaw.invoke (model := model)
    (helper := ⟨checker, .local, [.vector domain, .vector domain, .field domain], [.boolean]⟩)
    (checkOverflow model domain bindings) definitions linked bodies.check
  exact ⟨Nat.lt_trans small (by decide +kernel), shape_overflow model domain bindings linked bodies xs point.length overflow small⟩

#print axioms check_overflow
end ZkcSecurity.Families.Sumcheck.SourceAdmission
