module

public import ZkcExamples.NativePrograms.Sumcheck
public import ZkcSecurity.Examples.NativePrograms.Sumcheck
public import ZkcExamples.NativePrograms.SumcheckHelpers
public import ZkcExamples.NativePrograms.SumcheckHorner

@[expose] public section

/-! Several native source forms share one semantic contract and its property theorems. -/

set_option autoImplicit false
noncomputable section

namespace ZkcExamples.NativePrograms.SumcheckVariants
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

inductive Form where
  | original | helpers | horner

variable {F : Type} [Field F] [DecidableEq F]
abbrev helpers := SumcheckHelpers.verifier (F := F)
abbrev horner := SumcheckHorner.verifier (F := F)

set_option maxRecDepth 20000 in
def verifier (form : Form) : Zkc.Protocols.Sumcheck.Common.Verifier F :=
  match form with
  | .original => Sumcheck.verifier
  | .helpers => helpers
  | .horner => horner

open Zkc.Protocols.Sumcheck.Common

theorem helpers_correspondence (coefficients : Coefficients F) (claim : F) (service : Nat) :
    helpers coefficients claim service = Sumcheck.experiment coefficients claim service :=
  (SumcheckHelpers.process_view_eq coefficients claim service).trans
    (SumcheckHelpers.correspondence coefficients claim service)

def hornerValue (m : Zkc.Protocols.AlgebraicRounds.Message F) (x : F) : F :=
  m.constant + x * (m.linear + x * m.quadratic)

def hornerArithmetic : VerifierArithmetic F where
  boundary m := m.quadratic + m.linear + (m.constant + m.constant)
  message := hornerValue
  statement p x y := hornerValue p.constant y + x * (hornerValue p.linear y + x * hornerValue p.quadratic y)

omit [DecidableEq F] in
theorem horner_arithmetic : hornerArithmetic (F := F) = standardArithmetic := by
  apply VerifierArithmetic.standard_eq
  · intro m
    dsimp [hornerArithmetic, wireBoundary]
    ring
  · intro m x
    dsimp [hornerArithmetic, hornerValue, wireEvaluate]
    ring
  · intro p x y
    dsimp [hornerArithmetic, hornerValue, evaluate, wireEvaluate]
    ring

theorem horner_correspondence (coefficients : Coefficients F) (claim : F) (service : Nat) :
    horner coefficients claim service = Sumcheck.experiment coefficients claim service :=
  (SumcheckHorner.process_view_eq coefficients claim service).trans
    (SumcheckHorner.correspondence coefficients claim service)

theorem contract (form : Form) : Zkc.Protocols.Sumcheck.Common.VerifierContract Sumcheck.wiring (verifier (F := F) form) := by
  cases form with
  | original => exact Sumcheck.contract
  | helpers => exact ⟨fun coefficients claim service => ⟨helpers_correspondence coefficients claim service⟩⟩
  | horner => exact ⟨fun coefficients claim service => ⟨horner_correspondence coefficients claim service⟩⟩

abbrev run (form : Form) := Zkc.Protocols.Sumcheck.Common.run (verifier (F := F) form)

noncomputable abbrev acceptance [Fintype F] (form : Form) := Zkc.Protocols.Sumcheck.Common.acceptance (verifier (F := F) form)

open Sumcheck

theorem completeness (form : Form) (coefficients : Coefficients F) (service : Nat) (first second : F) :
    (run form coefficients (polynomial coefficients).booleanSum service
      (honestStrategy coefficients) first second).outcome = .returned (some true) := by
  exact (contract form).completeness coefficients service first second

theorem perfect_completeness [Fintype F] (form : Form) (coefficients : Coefficients F) (service : Nat) :
    acceptance form coefficients (polynomial coefficients).booleanSum service (honestStrategy coefficients) = 1 := by
  exact (contract form).perfect_completeness coefficients service

theorem soundness [Fintype F] (form : Form) (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Strategy F)
    (falseClaim : claim ≠ (polynomial coefficients).booleanSum) :
    acceptance form coefficients claim service prover ≤ 4 / (Fintype.card F : ℚ) := by
  exact (contract form).soundness coefficients claim service prover falseClaim

end ZkcExamples.NativePrograms.SumcheckVariants

end
