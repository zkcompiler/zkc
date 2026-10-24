module

public import ZkcExamples.Structured.PolynomialRestrictionBinding
public import ZkcSecurity.Families.Sumcheck.TableReference
public import ZkcSecurity.Families.Sumcheck.Round
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! A bounded coefficient-storage adapter to the existing Sumcheck reference.
The mathematical family law is reused unchanged. This is a source-bound pure
helper and caller, not another Sumcheck root or a native security endpoint. -/

set_option autoImplicit false
namespace ZkcSecurity.Examples.PolynomialRestriction
open ZkcExamples.Structured.PolynomialRestrictionMath
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Families.Sumcheck

variable {F : Type} [Field F]

/-- Only dimensions 0, 1 and 2 are inhabited. Fixed coefficients avoid
duplicate supports and dynamic growth. Dimensions above two are refused by
the type, not interpreted by truncating or padding an input table. -/
def Storage (F : Type) : Nat → Type
  | 0 => F
  | 1 => Affine F
  | 2 => Bilinear F
  | _ + 3 => Empty

def restrictStorage : {n : Nat} → Storage F (n + 1) → F → Storage F n
  | 0, p, r => p.evaluate r
  | 1, p, r => restrictFirst p r
  | _ + 2, impossible, _ => nomatch impossible

def interpret : {n : Nat} → Storage F n → Table F n
  | 0, value => fun _ => value
  | 1, p => fun bits => p.evaluate (if bits 0 then 1 else 0)
  | 2, p => fun bits => p.evaluate (if bits 0 then 1 else 0) (if bits 1 then 1 else 0)
  | _ + 3, impossible => nomatch impossible

/-- Identify the initial interpretation with the original coefficient
polynomial at arbitrary field points, not only at Boolean vertices. -/
theorem bilinear_extension (p : Bilinear F) (point : Fin 2 → F) :
    extension 2 (interpret (n := 2) p) point = p.evaluate (point 0) (point 1) := by
  simp only [extension, interpret, Bilinear.evaluate, Function.comp_def,
    Fin.cons_zero, Fin.cons_one, Bool.false_eq_true, ↓reduceIte]
  change (1 - point 0) * ((1 - point 1) * p.evaluate 0 0 + point 1 * p.evaluate 0 1) +
    point 0 * ((1 - point 1) * p.evaluate 1 0 + point 1 * p.evaluate 1 1) = _
  simp only [Bilinear.evaluate]
  ring

theorem affine_extension (p : Affine F) (point : Fin 1 → F) :
    extension 1 (interpret (n := 1) p) point = p.evaluate (point 0) := by
  simp only [extension, interpret, Affine.evaluate,
    Fin.cons_zero, Bool.false_eq_true, ↓reduceIte]
  ring

def coefficients : {n : Nat} → Storage F n → List F
  | 0, value => [value]
  | 1, p => p.slots
  | 2, p => p.slots
  | _ + 3, impossible => nomatch impossible

omit [Field F] in
theorem coefficient_count {n : Nat} (s : Storage F n) :
    (coefficients s).length = 2 ^ n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => exact nomatch s

/-- All inhabited updates strictly shrink fixed capacity, including 1 -> 0.
Zero coefficients never cause a shape change or support growth. -/
theorem restriction_capacity {n : Nat} (s : Storage F (n + 1)) (r : F) :
    (coefficients (restrictStorage s r)).length < (coefficients s).length := by
  rw [coefficient_count, coefficient_count, Nat.pow_succ]
  have positive : 0 < 2 ^ n := Nat.pow_pos (by decide)
  omega

/-- The update commutes with interpretation at every field challenge. -/
theorem interpret_restrict {n : Nat} (s : Storage F (n + 1)) (r : F) :
    interpret (restrictStorage s r) = fixFirst (interpret s) r := by
  cases n with
  | zero =>
    funext bits
    simp only [interpret, restrictStorage, fixFirst, half, Affine.evaluate,
      Fin.cons_zero, Bool.false_eq_true, ↓reduceIte]
    ring
  | succ n =>
    cases n with
    | zero =>
      funext bits
      simp only [interpret, restrictStorage, fixFirst, half, Affine.evaluate,
        restrictFirst, Bilinear.evaluate, Fin.cons_zero, Fin.cons_one,
        Bool.false_eq_true, ↓reduceIte]
      ring
    | succ n => exact nomatch s

/-- The adapter does not synthesize a new family polynomial or family law. -/
noncomputable abbrev reference (F : Type) [Field F] : Reference F where
  State := Storage F
  total s := (TableReference.data F).total (interpret s)
  restrict := restrictStorage
  polynomial s := (TableReference.data F).polynomial (interpret s)
  admissible _ := True

theorem laws : ReferenceLaws (reference F) 1 where
  degree_le s _ := TableReference.laws.degree_le (interpret s) trivial
  boundary_eq s _ := TableReference.laws.boundary_eq (interpret s) trivial
  evaluation_eq s r _ := by
    change ((TableReference.data F).polynomial (interpret s)).eval r =
      (TableReference.data F).total (interpret (restrictStorage s r))
    rw [interpret_restrict]
    exact TableReference.laws.evaluation_eq (interpret s) r trivial
  restriction_closed _ _ _ := trivial

theorem interpret_prefix {n : Nat} (count : Nat) (s : Storage F (n + count))
    (challenges : Fin count → F) :
    interpret ((reference F).restrictPrefix count s challenges) =
      fixPrefix count (interpret s) challenges := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change interpret ((reference F).restrictPrefix count
      (restrictStorage s (challenges 0)) (challenges ∘ Fin.succ)) = _
    rw [ih, interpret_restrict]
    rfl

/-- Arbitrary permitted future prefixes preserve every off-cube evaluation of
the remaining polynomial. A zero-length prefix is included. -/
theorem all_future_evaluation {n : Nat} (count : Nat) (s : Storage F (n + count))
    (challenges : Fin count → F) (tail : Fin n → F) :
    extension n (interpret ((reference F).restrictPrefix count s challenges)) tail =
      extension (n + count) (interpret s) (Quadratic.point count challenges tail) := by
  rw [interpret_prefix]
  exact extension_fixPrefix count (interpret s) challenges tail

/-- Reuse the existing representation-simulation theorem for all future
Boolean residual sums, in addition to the stronger pointwise theorem above. -/
theorem all_future_total {n : Nat} (count : Nat) (s : Storage F (n + count))
    (challenges : Fin count → F) :
    (TableReference.data F).total
      ((TableReference.data F).restrictPrefix count (interpret s) challenges) =
      (reference F).total ((reference F).restrictPrefix count s challenges) :=
  Reference.restrictPrefix_total_eq (left := reference F) (right := TableReference.data F)
    (fun s => interpret s) (fun _ => rfl) (fun s r => interpret_restrict s r)
    count s challenges

theorem all_future_closed {n : Nat} (count : Nat) (s : Storage F (n + count))
    (challenges : Fin count → F) :
    (reference F).admissible ((reference F).restrictPrefix count s challenges) :=
  Reference.admissible_restrictPrefix laws count s challenges trivial

/-- Family reuse through the adapter: no second storage-specific soundness
proof. The received endpoint message is arbitrary and fixed before r. -/
theorem family_false_round {n : Nat} (s : Storage F (n + 1)) (m : F × F) (r : F)
    (noCollision : ((Message.endpoints F).polynomial m).eval r ≠
      ((TableReference.data F).polynomial (interpret s)).eval r) :
    (Message.endpoints F).evaluate m r ≠ (reference F).total (restrictStorage s r) := by
  have reused := false_round TableReference.laws Message.endpoints_laws
    (interpret s) trivial m r noCollision
  change (Message.endpoints F).evaluate m r ≠
    (TableReference.data F).total (interpret (restrictStorage s r))
  rw [interpret_restrict]
  exact reused.1

/-- Link the exact source update to the representation simulation. -/
theorem source_update (p : Bilinear F) (r : F) :
    interpret (n := 1) (restrictFirst p r) = fixFirst (interpret (n := 2) p) r :=
  interpret_restrict (n := 1) p r

section Source
open Zkc.Source.Structured
open ZkcExamples.Structured.PolynomialRestrictionBinding
open ZkcExamples.Structured.PolynomialRestrictionBodies

/-- The actual installed source helper returns precisely the storage whose
all-future interpretation and closure were proved above. No target-truth
premise or future-challenge restriction is used to justify the call. -/
theorem source_preserves_future [DecidableEq F] (p : Bilinear F) (x : F) :
    invoke (Evaluation.payloadMeanings (F := F) (G := F) SiteObservations.closed program.payload)
      restrictHelper (restrictArguments p x) = .done (affineValues (restrictFirst p x)) ∧
      (∀ y, (restrictFirst p x).evaluate y = p.evaluate x y) ∧
      (reference F).admissible (n := 1) (restrictStorage (n := 1) p x) :=
  ⟨restrict_invocation SiteObservations.closed p x, restriction_evaluation p x, trivial⟩

end Source

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Agreement on the entire initial Boolean domain is insufficient. -/
theorem boolean_agreement : ∀ b : Bool,
    (if b then (1 : ZMod 7) else 0) ^ 2 = (if b then (1 : ZMod 7) else 0) := by
  decide +kernel

theorem off_cube_disagreement : (2 : ZMod 7) ^ 2 ≠ 2 := by decide +kernel

/-- Refuse the proposed X^2-to-X adapter even though its initial table agrees. -/
theorem boolean_reinterpolation_refused :
    ¬ (∀ x : ZMod 7, x ^ 2 = x) := by
  intro alleged
  exact off_cube_disagreement (alleged 2)

/-- A concrete actual-call result also distinguishes a caller frame from the
future challenge; same scalar type does not authorize swapping these ports. -/
theorem caller_frame_distinguishes :
    ZkcExamples.Structured.PolynomialRestrictionBinding.callerResult
      (G := ZMod 7) (⟨1, 2, 3, 4⟩ : Bilinear (ZMod 7)) 2 3 5 ≠
    ZkcExamples.Structured.PolynomialRestrictionBinding.callerResult
      (G := ZMod 7) (⟨1, 2, 3, 4⟩ : Bilinear (ZMod 7)) 2 5 3 := by
  intro same
  let getFrame : Zkc.Source.Values (Zkc.Source.Structured.assignment (ZMod 7) (ZMod 7))
      (List.replicate 4 (.field "bls12-381.fr" : Zkc.Source.Structured.Ty)) → ZMod 7 :=
    fun values => values.get (.there (.there (.there .here)))
  have frames := congrArg getFrame same
  have unequal : (5 : ZMod 7) ≠ 3 := by decide +kernel
  exact unequal frames

end ZkcSecurity.Examples.PolynomialRestriction
