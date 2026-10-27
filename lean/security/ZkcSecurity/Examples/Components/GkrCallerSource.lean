module

public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsCaller
public import ZkcSecurity.Examples.Components.GkrCallerRealization
public import Zkc.Source.Structured.Interpretation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false

/-! Full-process finite setup equations for the admitted caller's helpers.
The intermediate arithmetic is checked against the actual source by the kernel;
ring simplification is separate from selection and source execution. -/
namespace ZkcSecurity.Examples.Components.GkrCallerSource
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.Generated.Bindings.GkrRounds (payload)
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCaller
open GkrCallerRealization

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev table : Meanings F G := closedMeanings payload.definitions

def addBlock : List F := [0, 0, 0, 0, 0, 0, 0, 1]
def mulBlock : List F := [0, 1, 0, 0, 0, 0, 0, 0]

theorem select_add : invoke (table (F := F) (G := G)) selectBlockHelper
    (.cons stackedAdd (.cons 0 (.cons 1 .nil))) = .done (.cons addBlock .nil) := by
  kernel_rfl

theorem select_mul : invoke (table (F := F) (G := G)) selectBlockHelper
    (.cons stackedMul (.cons 0 (.cons 1 .nil))) = .done (.cons mulBlock .nil) := by
  kernel_rfl

theorem values_below : invoke (table (F := F) (G := G)) valuesBelowHelper
    (.cons stackedAdd (.cons stackedMul (.cons inputs
      (.cons 2 (.cons 1 (.cons 1 (.cons 0 .nil))))))) = .done (.cons [8, 15] .nil) := by
  have equation : invoke (table (F := F) (G := G)) valuesBelowHelper
      (.cons stackedAdd (.cons stackedMul (.cons inputs
        (.cons 2 (.cons 1 (.cons 1 (.cons 0 .nil))))))) =
      .done (.cons [
        (((0 + (0 * (3 + 3) + 0 * 3 * 3)) + (1 * (3 + 5) + 0 * 3 * 5)) +
          (0 * (5 + 3) + 0 * 5 * 3)) + (0 * (5 + 5) + 0 * 5 * 5),
        (((0 + (0 * (3 + 3) + 0 * 3 * 3)) + (0 * (3 + 5) + 1 * 3 * 5)) +
          (0 * (5 + 3) + 0 * 5 * 3)) + (0 * (5 + 5) + 0 * 5 * 5)] .nil) := by
    kernel_rfl
  norm_num at equation
  exact equation

theorem layer_gates (rho : F) : invoke (table (G := G)) layerGatesHelper
    (.cons addBlock (.cons mulBlock (.cons [rho] (.cons [8, 15] (.cons 1 .nil))))) =
      .done (raw rho).values := by
  have equation : invoke (table (G := G)) layerGatesHelper
      (.cons addBlock (.cons mulBlock (.cons [rho] (.cons [8, 15] (.cons 1 .nil))))) =
      .done (.cons [0 + (0 - 0) * rho, 0 + (0 - 0) * rho,
        0 + (0 - 0) * rho, 0 + (1 - 0) * rho]
        (.cons [0 + (0 - 0) * rho, 1 + (0 - 1) * rho,
          0 + (0 - 0) * rho, 0 + (0 - 0) * rho]
          (.cons [8, 8, 15, 15] (.cons [8, 15, 8, 15] .nil)))) := by
    kernel_rfl
  simpa [raw, GkrRoundsRealization.RawState.values, sub_mul, sub_eq_add_neg] using equation

theorem evaluate_pair (a b rho : F) : invoke (table (G := G)) evaluateHelper
    (.cons [a, b] (.cons [rho] .nil)) =
      .done (.cons ((1 - rho) * a + rho * b) .nil) := by
  have equation : invoke (table (G := G)) evaluateHelper
      (.cons [a, b] (.cons [rho] .nil)) =
      .done (.cons (0 + (a + (b - a) * rho)) .nil) := by
    kernel_rfl
  have arithmetic : 0 + (a + (b - a) * rho) = (1 - rho) * a + rho * b := by ring
  exact equation.trans (congrArg (fun value => PIR.Process.done (I := closedInterface) (Values.cons value .nil)) arithmetic)

/-- The actual root's LayerClaim constructor. Its association with the
emitted prefix is checked by the whole-prefix equation in GkrCallerPrefix. -/
def layerClaimHelper : Helper :=
  ⟨"zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", .local,
    [.vector "bls12-381.fr", .field "bls12-381.fr"],
    [.vector "bls12-381.fr", .field "bls12-381.fr"]⟩

theorem layer_claim (point : List F) (claim : F) :
    invoke (table (G := G)) layerClaimHelper (.cons point (.cons claim .nil)) =
      .done (.cons point (.cons claim .nil)) := by
  kernel_rfl

/-- Closed setup equations lift to the exact silent participant helper table;
there is no hypothesis about adversarial runtime tables or coefficients. -/
theorem lift_equation (helper : Helper) (args : Values (assignment F G) helper.inputs)
    (result : Values (assignment F G) helper.outputs)
    (equation : invoke (table (F := F) (G := G)) helper args = .done result) :
    invoke (helpers payload).closed helper args = .done result := by
  rw [Evaluation.ComponentTables.closed_fold]
  rw [← Evaluation.foldMeanings_closedLift payload.definitions helper args, equation]
  rfl

/-- A generic present-input lifting rule for closed source setup only. -/
theorem owned_equation (self : Nat) (helper : Helper)
    (args : Values (assignment F G) helper.inputs)
    (result : Values (assignment F G) helper.outputs)
    (equation : invoke (table (F := F) (G := G)) helper args = .done result) :
    Participant.owned self self (invoke (helpers payload).toOn.closed helper) args.present =
      .done result.present := by
  rw [Participant.owned_present]
  erw [lift_equation helper args result equation]
  rfl

theorem owned_evaluate_pair (self : Nat) (a b rho : F) :
    Participant.owned self self (invoke (helpers (F := F) (G := G) payload).toOn.closed evaluateHelper)
      (.cons (some [a, b]) (.cons (some [rho]) .nil)) =
      .done (.cons (some ((1 - rho) * a + rho * b)) .nil) := by
  change Participant.owned self self (invoke (helpers payload).closed evaluateHelper) _ = _
  simp only [Participant.owned, ite_true]
  change (invoke (helpers payload).closed evaluateHelper (.cons [a, b] (.cons [rho] .nil))).bind _ = _
  rw [lift_equation evaluateHelper _ _ (evaluate_pair (G := G) a b rho)]
  rfl

theorem owned_layer_claim (self : Nat) (point : List F) (claim : F) :
    Participant.owned self self (invoke (helpers (F := F) (G := G) payload).toOn.closed layerClaimHelper)
      (.cons (some point) (.cons (some claim) .nil)) =
      .done (.cons (some point) (.cons (some claim) .nil)) := by
  exact owned_equation self layerClaimHelper _ _ (layer_claim (G := G) point claim)

/-- The source setup's selected block/restriction/replicate/tile pipeline,
using the actual finite circuit. This describes source construction only. -/
theorem construction (rho : F) :
    ((invoke (table (G := G)) valuesBelowHelper
      (.cons stackedAdd (.cons stackedMul (.cons inputs
        (.cons 2 (.cons 1 (.cons 1 (.cons 0 .nil)))))))).bind fun below =>
      (invoke table selectBlockHelper (.cons stackedAdd (.cons 0 (.cons 1 .nil)))).bind fun add =>
      (invoke table selectBlockHelper (.cons stackedMul (.cons 0 (.cons 1 .nil)))).bind fun mul =>
      invoke table layerGatesHelper (.cons (add.get .here) (.cons (mul.get .here)
        (.cons [rho] (.cons (below.get .here) (.cons 1 .nil)))))) =
        .done (raw rho).values := by
  rw [values_below]
  simp only [PIR.Process.bind]
  rw [select_add]
  rw [select_mul]
  exact layer_gates rho

end ZkcSecurity.Examples.Components.GkrCallerSource
