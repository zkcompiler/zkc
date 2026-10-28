module

public import Zkc.Source.Structured.ReferenceLaws

@[expose] public section

/-! Mathematical rules for typed vector helper bodies. Domain identities and
source markers are parameters, not dispatch keys. Application to a declaration
still requires exact body association. Native allocation limits and execution
resources remain outside the logical list model. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.ReferenceLibrary
open Zkc.Source

attribute [local implicit_reducible] Op.arguments Op.results Op.regions

variable (model : DomainModel) (domain site : String)

def emptyVector : ReferenceLaw model [] [.vector domain] where
  body := .letOp (.mark site) .nil .nil <|
    .letOp (.exec (.vectorEmpty domain)) .nil .nil (.ret (.cons .here .nil))
  Requires _ _ := True
  reference _ := .returned (.cons [] .nil)
  valid _ args _ := by cases args; rfl

def appendVector : ReferenceLaw model [.vector domain, .field domain] [.vector domain] where
  body := .letOp (.mark site) .nil .nil <|
    .letOp (.exec (.vectorAppend domain)) (.cons .here (.cons (.there .here) .nil)) .nil
      (.ret (.cons .here .nil))
  Requires _ _ := True
  reference args := .returned (.cons (args.get .here ++ [args.get (.there .here)]) .nil)
  valid _ args _ := by
    cases args with
    | cons values rest => cases rest with
      | cons value rest => cases rest; rfl

/-- The implementation uses a left fold; the reference is the mathematical sum. -/
def sumVector : ReferenceLaw model [.vector domain] [.field domain] where
  body := .letOp (.mark site) .nil .nil <|
    .letOp (.exec (.vectorSum domain)) (.cons .here .nil) .nil (.ret (.cons .here .nil))
  Requires _ _ := True
  reference args := .returned (.cons (args.get .here).sum .nil)
  valid _ args _ := by
    cases args with
    | cons values rest =>
      cases rest
      change PIR.Process.done (show Values model.Value [.field domain] from
          .cons (values.foldl (· + ·) 0) .nil) =
        PIR.Process.done (show Values model.Value [.field domain] from .cons values.sum .nil)
      rw [List.sum_eq_foldl]

/-- Splitting refuses empty or odd tables; these executions are part of the law. -/
def splitVector : ReferenceLaw model [.vector domain] [.vector domain, .vector domain] where
  body := .letOp (.mark site) .nil .nil <|
    .letOp (.exec (.vectorSplit domain)) (.cons .here .nil) .nil
      (.ret (.cons .here (.cons (.there .here) .nil)))
  Requires _ _ := True
  reference args :=
    let values := args.get .here
    if values.length > 0 ∧ values.length % 2 = 0 then
      .returned (.cons (values.take (values.length / 2)) (.cons (values.drop (values.length / 2)) .nil))
    else .stopped .refused
  valid _ args _ := by
    cases args with
    | cons values rest =>
      cases rest
      simp only [Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
        Regions.denote, Operands.eval, Values.get, SiteObservations.closed, SiteObservations.silent,
        PIR.Process.bind, Environment.prepend, Primitive.evaluateOn, primitiveOutcome]
      by_cases shape : values.length > 0 ∧ values.length % 2 = 0 <;>
        simp only [shape] <;> rfl

/-- An exact projection does not introduce mathematical or shape premises. -/
def projection {inputs outputs : List Ty} (selected : Operands inputs outputs) :
    ReferenceLaw model inputs outputs where
  body := .ret selected
  Requires _ _ := True
  reference args := .returned (Operands.eval args.get selected)
  valid _ _ _ := rfl

/-- Reusable affine interpolation, retaining the source arithmetic order. -/
def interpolate : ReferenceLaw model [.field domain, .field domain, .field domain] [.field domain] where
  body :=
    .letOp (.fieldSubtract domain) (.cons (.there .here) (.cons .here .nil)) .nil <|
    .letOp (.fieldMultiply domain) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
    .letOp (.fieldAdd domain) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
    .ret (.cons .here .nil)
  Requires _ _ := True
  reference args := .returned (.cons (args.get .here +
    (args.get (.there .here) - args.get .here) * args.get (.there (.there .here))) .nil)
  valid _ args _ := by
    cases args with
    | cons left rest => cases rest with
      | cons right rest => cases rest with
        | cons challenge rest => cases rest; rfl

/-- A dependency is identified by its complete signature and its exact outcome
law. The caller may select returned values or retain caller inputs; stopping is
preserved. The premise must be proved in the actual linked table. -/
def call {inputs outputs : List Ty} (helper : Helper)
    (arguments : Operands inputs helper.inputs)
    (selected : Operands (helper.outputs ++ inputs) outputs)
    (reference : Values model.Value helper.inputs → PIR.Outcome (Values model.Value helper.outputs)) :
    ReferenceLaw model inputs outputs where
  body := .letOp (.invoke helper) arguments .nil (.ret selected)
  Requires table args := invoke table helper (Operands.eval args.get arguments) =
    primitiveOutcome (reference (Operands.eval args.get arguments))
  reference args := match reference (Operands.eval args.get arguments) with
    | .returned values => .returned (Operands.eval (Environment.prepend args.get values) selected)
    | .stopped reason => .stopped reason
  valid table args dependency := by
    simp only [Region.denote, Evaluation.meaningOn, Evaluation.operationOn, Regions.denote]
    rw [dependency]
    cases reference (Operands.eval args.get arguments) <;> rfl

/-- Select every result in declaration order, retaining an arbitrary caller suffix. -/
def resultOperands (outputs inputs : List Ty) : Operands (outputs ++ inputs) outputs :=
  match outputs with
  | [] => .nil
  | _ :: rest => .cons .here ((resultOperands rest inputs).rename (fun ref => .there ref))

theorem eval_resultOperands {inputs outputs : List Ty}
    (env : Environment model.Value inputs) (values : Values model.Value outputs) :
    Operands.eval (Environment.prepend env values) (resultOperands outputs inputs) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [resultOperands, Operands.eval, Operands.eval_rename, Environment.prepend]
    change Values.cons value (Operands.eval (Environment.prepend env rest)
      (resultOperands _ inputs)) = _
    rw [ih]

/-- A caller which forwards the complete result ABI preserves every outcome.
This is the ordinary call law with a proved ordered result projection. -/
def forward {inputs : List Ty} (helper : Helper)
    (arguments : Operands inputs helper.inputs)
    (reference : Values model.Value helper.inputs → PIR.Outcome (Values model.Value helper.outputs)) :
    ReferenceLaw model inputs helper.outputs where
  body := (call model helper arguments (resultOperands helper.outputs inputs) reference).body
  Requires := (call model helper arguments (resultOperands helper.outputs inputs) reference).Requires
  reference args := reference (Operands.eval args.get arguments)
  valid table args dependency := by
    have actual := (call model helper arguments (resultOperands helper.outputs inputs) reference).valid
      table args dependency
    refine actual.trans (congrArg primitiveOutcome ?_)
    dsimp only [call]
    cases reference (Operands.eval args.get arguments) with
    | stopped reason => rfl
    | returned values => exact congrArg PIR.Outcome.returned (eval_resultOperands model args.get values)

/-- Source markers remain in the associated body. They are silent only under
this closed mathematical interpretation, not under the occurrence connection. -/
def marked {inputs outputs : List Ty} (law : ReferenceLaw model inputs outputs) :
    ReferenceLaw model inputs outputs where
  body := .letOp (.mark site) .nil .nil law.body
  Requires := law.Requires
  reference := law.reference
  valid table args premise := law.valid table args premise

end Zkc.Source.Structured.ReferenceLibrary
