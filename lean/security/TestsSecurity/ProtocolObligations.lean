import Zkc.Obligations.TokenRules
import ZkcSecurity.Algebra.Polynomial
import ZkcSecurity.Obligations.Derivation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Heterogeneous mathematical clients of the obligation boundary. These are
checked architectural controls, not source-to-native FRI or folding endpoints.
The promise-gap client uses a concrete code and Hamming distance; the folding
client retains an actual relaxed quadratic residual and caller-private frame.
-/

set_option autoImplicit false

namespace TestsSecurity.ProtocolObligations
open Zkc.Obligations Zkc.Transcript
open OracleComp OracleSpec

namespace Proximity

abbrev Word := Fin 4 → Bool

def distance (left right : Word) : Nat :=
  (Finset.univ.filter fun i => left i ≠ right i).card

def zero : Word := fun _ => false
def oneError : Word := fun i => decide (i.val = 0)

/-- This code has one codeword. Distance one is a genuine promise gap. -/
def token : Token Word where
  Yes word := word = zero
  No word := 1 < distance word zero
  disjoint word same far := by
    subst word
    simp [distance] at far

theorem gap : ¬ token.Yes oneError ∧ ¬ token.No oneError := by
  constructor
  · intro same
    have first := congrFun same 0
    simp [oneError, zero] at first
  · change ¬ 1 < distance oneError zero
    decide +kernel

theorem gap_is_safe : token.Safe oneError := gap.2

theorem equality_ledger_is_stronger :
    (Token.exact token.Yes).No oneError ∧ ¬ token.No oneError := gap

/-- A caller can preserve a proximity token without identifying Safe with Yes. -/
theorem identity_frame : Bundle.Backward [token] [token]
    (fun old new => new = old) := by
  intro old new same safe
  subst new
  exact safe

/-- An actual query checks one coordinate. A gap word is intentionally outside
the soundness promise; the contract must not silently strengthen No to not Yes. -/
abbrev signature : PIR.Signature := ⟨Unit, fun _ => Fin 4⟩
def interface : Interface signature Unit Unit (fun _ => Fin 4) :=
  fun _ => .query () some
def checkWord (word : Word) : PIR.Process signature Bool :=
  .call () fun index => .done (!word index)

theorem far_agreement_count (word : Word) (far : token.No word) :
    (Finset.univ.filter fun index => word index = false).card ≤ 2 := by
  have finiteLaw : ∀ word : Word, 1 < distance word zero →
      (Finset.univ.filter fun index => word index = false).card ≤ 2 := by
    decide +kernel
  exact finiteLaw word far

theorem far_acceptance (word : Word) (far : token.No word) :
    Pr{let index ← $ᵗ (Fin 4)}[word index = false] ≤ 2 / 4 := by
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
  exact ENNReal.div_le_div_right (by exact_mod_cast far_agreement_count word far) _

noncomputable def far_derivation (word : Word) (far : token.No word) (history : List Unit) :
    Derivation interface (ZkcSecurity.Obligations.boundedEscape (fun _ _ => 2 / 4))
      (fun reached accepted => reached = history ++ [()] ∧ accepted = false)
      history (checkWord word) := by
  refine .query rfl (fun index => word index = false) (far_acceptance word far) ?_
  intro index value decoded outside
  cases decoded
  exact .done ⟨rfl, by simpa using outside⟩

/-- The promise gap really matters for the sampled check, not just its token. -/
theorem gap_exceeds_far_bound :
    ¬ Pr{let index ← $ᵗ (Fin 4)}[oneError index = false] ≤ 2 / 4 := by
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
  have count : (Finset.univ.filter fun index => oneError index = false).card = 3 := by
    decide +kernel
  rw [count]
  norm_num
  exact (ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num)).mpr (by norm_num)

end Proximity

namespace Folding

variable {F : Type} [Field F]

structure Instance (F : Type) where
  left : F
  right : F
  scale : F
  output : F
  error : F

def residual (x : Instance F) : F :=
  x.left * x.right - x.scale * x.output - x.error

def crossTerm (x y : Instance F) : F :=
  x.left * y.right + y.left * x.right - x.scale * y.output - y.scale * x.output

/-- The cross term is a protocol input. Its correctness is a separate proof
obligation; an adversarial cross term cannot be replaced with the honest one. -/
def fold (x y : Instance F) (cross challenge : F) : Instance F where
  left := x.left + challenge * y.left
  right := x.right + challenge * y.right
  scale := x.scale + challenge * y.scale
  output := x.output + challenge * y.output
  error := x.error + challenge * cross + challenge ^ 2 * y.error

theorem residual_fold (x y : Instance F) (cross challenge : F) :
    residual (fold x y cross challenge) =
      residual x + challenge * (crossTerm x y - cross) + challenge ^ 2 * residual y := by
  dsimp [residual, fold, crossTerm]
  ring

theorem honest_fold (x y : Instance F) (challenge : F)
    (left : residual x = 0) (right : residual y = 0) :
    residual (fold x y (crossTerm x y) challenge) = 0 := by
  rw [residual_fold, left, right]
  ring

noncomputable def residualPolynomial (x y : Instance F) (cross : F) : Polynomial F :=
  Polynomial.C (residual x) + Polynomial.C (crossTerm x y - cross) * Polynomial.X +
    Polynomial.C (residual y) * Polynomial.X ^ 2

theorem residualPolynomial_eval (x y : Instance F) (cross challenge : F) :
    (residualPolynomial x y cross).eval challenge = residual (fold x y cross challenge) := by
  rw [residual_fold]
  simp only [residualPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem degree_le (x y : Instance F) (cross : F) :
    (residualPolynomial x y cross).natDegree ≤ 2 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

theorem false_left_nonzero (x y : Instance F) (cross : F) (bad : residual x ≠ 0) :
    residualPolynomial x y cross ≠ 0 := by
  intro zero
  have atZero := congrArg (Polynomial.eval (0 : F)) zero
  simp [residualPolynomial] at atZero
  exact bad atZero

theorem false_input_nonzero (x y : Instance F) (cross : F)
    (bad : residual x ≠ 0 ∨ residual y ≠ 0) : residualPolynomial x y cross ≠ 0 := by
  rcases bad with left | right
  · exact false_left_nonzero x y cross left
  · intro zero
    have coefficient := congrArg (fun p : Polynomial F => p.coeff 2) zero
    simp [residualPolynomial] at coefficient
    exact right coefficient

/-- The same polynomial bound library applies to a folding residual. Choosing
the cross term after seeing this challenge would violate this fixed-polynomial
premise and needs a different analysis. -/
theorem false_left_probability [Fintype F] [DecidableEq F] [SampleableType F]
    (x y : Instance F) (cross : F) (bad : residual x ≠ 0) :
    Pr{let challenge ← $ᵗ F}[residual (fold x y cross challenge) = 0] ≤
      (2 : ENNReal) / Fintype.card F := by
  have bound := ZkcSecurity.Algebra.Polynomial.root_uniform_le
    (residualPolynomial x y cross) (false_left_nonzero x y cross bad) (degree_le x y cross)
  simpa only [residualPolynomial_eval, Nat.cast_ofNat] using bound

theorem false_input_probability [Fintype F] [DecidableEq F] [SampleableType F]
    (x y : Instance F) (cross : F) (bad : residual x ≠ 0 ∨ residual y ≠ 0) :
    Pr{let challenge ← $ᵗ F}[residual (fold x y cross challenge) = 0] ≤
      (2 : ENNReal) / Fintype.card F := by
  have bound := ZkcSecurity.Algebra.Polynomial.root_uniform_le
    (residualPolynomial x y cross) (false_input_nonzero x y cross bad) (degree_le x y cross)
  simpa only [residualPolynomial_eval, Nat.cast_ofNat] using bound

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- A fold can erase two false residuals at a particular challenge. The
deterministic backward-safety rule therefore cannot replace the escape bound. -/
theorem false_inputs_can_escape :
    let left : Instance (ZMod 7) := ⟨0, 0, 0, 0, -1⟩
    let right : Instance (ZMod 7) := ⟨0, 0, 0, 0, 1⟩
    residual left ≠ 0 ∧ residual right ≠ 0 ∧
      residual (fold left right 0 1) = 0 := by
  norm_num [residual, fold]

/-- Private returned data and the caller frame remain in the contract even
when a public Boolean acceptance projection would discard them. -/
structure Result (F : Type) where
  residual : F
  privateWitness : List F
  callerFrame : Nat

abbrev silent : PIR.Signature := ⟨Empty, Empty.elim⟩
def silentInterface : Interface silent Unit Unit (fun _ => Unit) := fun operation => operation.elim
def noEscape : EscapeJudgment Unit (fun _ => Unit) := fun _ _ bad => ∀ value, ¬ bad value

def returnResidual (value : F) (witness : List F) (frame : Nat) : PIR.Process silent (Result F) :=
  .done ⟨value, witness, frame⟩

def private_residual_preserved (value : F) (witness : List F) (frame : Nat) :
    Derivation silentInterface noEscape
      (fun _ result => result.residual = value ∧ result.privateWitness = witness ∧ result.callerFrame = frame)
      [] (returnResidual value witness frame) := .done ⟨rfl, rfl, rfl⟩

/-- A sampled fold returns the residual and the caller's private data. The
reduction proves a residual contract; acceptance belongs to the later decider. -/
abbrev signature (F : Type) : PIR.Signature := ⟨Unit, fun _ => F⟩
def interface : Interface (signature F) Unit Unit (fun _ => F) := fun _ => .query () some
def sampleFold (x y : Instance F) (cross : F) (witness : List F) (frame : Nat) :
    PIR.Process (signature F) (Result F) :=
  .call () fun challenge => .done ⟨residual (fold x y cross challenge), witness, frame⟩

noncomputable def sampled_residual [Fintype F] [DecidableEq F] [SampleableType F]
    (x y : Instance F) (cross : F) (bad : residual x ≠ 0 ∨ residual y ≠ 0)
    (witness : List F) (frame : Nat) (history : List Unit) :
    Derivation interface
      (ZkcSecurity.Obligations.boundedEscape (fun _ _ => (2 : ENNReal) / Fintype.card F))
      (fun reached result => result.residual ≠ 0 ∧ result.privateWitness = witness ∧
        result.callerFrame = frame ∧ reached = history ++ [()])
      history (sampleFold x y cross witness frame) := by
  refine .query rfl (fun challenge => residual (fold x y cross challenge) = 0)
    (false_input_probability x y cross bad) ?_
  intro challenge value decoded outside
  cases decoded
  exact .done ⟨outside, rfl, rfl, rfl⟩

/-- The caller consumes the actual residual; no accepting Boolean is invented
by forgetting the private return. This is a local fresh-query reduction, not a
commitment, knowledge or Fiat–Shamir security theorem. -/
noncomputable def final_decider [Fintype F] [DecidableEq F] [SampleableType F]
    (x y : Instance F) (cross : F) (bad : residual x ≠ 0 ∨ residual y ≠ 0)
    (witness : List F) (frame : Nat) (history : List Unit) :
    Derivation interface
      (ZkcSecurity.Obligations.boundedEscape (fun _ _ => (2 : ENNReal) / Fintype.card F))
      (fun reached accepted => reached = history ++ [()] ∧ accepted = false)
      history ((sampleFold x y cross witness frame).bind fun result =>
        .done (decide (result.residual = 0))) := by
  apply (sampled_residual x y cross bad witness frame history).bind
  intro reached result preserved
  exact .done ⟨preserved.2.2.2, by simp [preserved.1]⟩

#print axioms sampled_residual
#print axioms final_decider

end Folding
end TestsSecurity.ProtocolObligations
