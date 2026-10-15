module

public import ZkcExamples.NativePrograms.Sumcheck
public import ZkcExamples.NativePrograms.Variants.SumcheckHelpersData

public import ZkcExamples.NativePrograms.Variants.SumcheckHornerData

@[expose] public section

/-! Several native source forms share one semantic contract and its property theorems. -/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace ZkcExamples.NativePrograms.SumcheckVariants
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

inductive Form where
  | original | helpers | horner

def helpersImport : Imported := Variants.SumcheckHelpersData.snapshot.check.toOption.get (by decide +kernel)

def hornerImport : Imported := Variants.SumcheckHornerData.snapshot.check.toOption.get (by decide +kernel)

variable {F : Type} [Field F] [DecidableEq F]

def helpers (coefficients : Zkc.Protocols.Sumcheck.Common.Coefficients F) (claim : F) (service : Nat) : PIR.Proc (Zkc.Protocols.Sumcheck.Common.actions (F := F)) (Option Bool) :=
  helpersImport.denote (scalarMeaning F F) id 1 (Sumcheck.verifierInputs coefficients claim service)

def horner (coefficients : Zkc.Protocols.Sumcheck.Common.Coefficients F) (claim : F) (service : Nat) : PIR.Proc (Zkc.Protocols.Sumcheck.Common.actions (F := F)) (Option Bool) :=
  hornerImport.denote (scalarMeaning F F) id 1 (Sumcheck.verifierInputs coefficients claim service)

def verifier (form : Form) : Zkc.Protocols.Sumcheck.Common.Verifier F :=
  match form with
  | .original => Sumcheck.verifier
  | .helpers => helpers
  | .horner => horner

theorem helpers_correspondence (coefficients : Zkc.Protocols.Sumcheck.Common.Coefficients F) (claim : F) (service : Nat) :
    helpers coefficients claim service = Sumcheck.experiment coefficients claim service := by
  change (helpersImport.program.denote (scalarMeaning F F) id 1
    (Sumcheck.verifierInputs coefficients claim service).get).bind PIR.Proc.done = _
  rw [PIR.Proc.bind_done]
  repeat' first
    | (apply PIR.Proc.call_congr; intro reply)
    | (change (if _ then _ else _ : PIR.Proc _ _).bind _ = _
       rw [PIR.Proc.bind_ite]
       simp only [↓reduceIte])
    | rfl
    | fail_if_no_progress congr 1

open Zkc.Protocols.Sumcheck.Common

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
    horner coefficients claim service = Sumcheck.experiment coefficients claim service := by
  have source : horner coefficients claim service =
      experimentWith Sumcheck.wiring hornerArithmetic coefficients claim service := by
    change (hornerImport.program.denote (scalarMeaning F F) id 1
      (Sumcheck.verifierInputs coefficients claim service).get).bind PIR.Proc.done = _
    rw [PIR.Proc.bind_done]
    repeat' first
      | (apply PIR.Proc.call_congr; intro reply)
      | (change (if _ then _ else _ : PIR.Proc _ _).bind _ = _
         rw [PIR.Proc.bind_ite]
         simp only [↓reduceIte])
      | rfl
      | fail_if_no_progress congr 1
  rw [source, horner_arithmetic]
  rfl

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
