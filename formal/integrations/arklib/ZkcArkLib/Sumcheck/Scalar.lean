import Zkc.Protocols.Sumcheck.ProductFamily.Wire
import Zkc.Protocols.AlgebraicRounds.BlockEvaluation
import ArkLib.OracleReduction.Security.Basic
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace ZkcArkLib.Sumcheck.Scalar
open Zkc.Protocols.Sumcheck.ProductFamily Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Protocols.AlgebraicRounds.BlockEvaluation OracleSpec ProtocolSpec

open Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Protocols.Sumcheck.ProductFamily Zkc.Compiler.Blocks OracleSpec ProtocolSpec
open scoped NNReal

-- Three scalar coefficient messages precede each public challenge. This is
-- the scalar schedule of the Zkc.Protocols.Sumcheck.ProductFamily source, not ArkLib's polynomial oracle spec.
def protocol (F : Type) (m : Nat) : ProtocolSpec (4 * (m + 1)) where
  dir i := if i.val % 4 = 3 then .V_to_P else .P_to_V
  «Type» _ := F

instance challengeSampleable {F : Type} [SampleableType F] (m : Nat)
    (i : (protocol F m).ChallengeIdx) : SampleableType ((protocol F m).Challenge i) :=
  inferInstanceAs (SampleableType F)

def wire {F : Type} [Zero F] {m : Nat}
    (tr : FullTranscript (protocol F m)) (j : Nat) : F :=
  if h : j < 4 * (m + 1) then tr ⟨j, h⟩ else 0

theorem coefficient_before_challenge (m : Nat) (i : Fin (m+1)) (j : Fin 3) :
    4*i.val+j.val < 4*i.val+3 ∧
    (protocol Unit m).dir ⟨4*i.val+j.val, by have := i.isLt; have := j.isLt; omega⟩ =
      .P_to_V ∧
    (protocol Unit m).dir ⟨4*i.val+3, by have := i.isLt; omega⟩ = .V_to_P := by
  have hj := j.isLt
  have hmod : (4*i.val+j.val)%4 ≠ 3 := by omega
  have hlast : (4*i.val+3)%4 = 3 := by omega
  constructor
  · omega
  · exact ⟨if_neg hmod, if_pos hlast⟩

def accept {F : Type} [CommRing F] [DecidableEq F] (m : Nat)
    (evaluate : Round F → F) (s : F) (tr : FullTranscript (protocol F m)) : Option Unit :=
  let env := sourceEnv s (wire tr)
  if runWith evaluate env 0 (m+1) s = some (Zkc.Protocols.Sumcheck.ProductFamily.finalTarget env m) then some () else none

theorem source_acceptance {F : Type} [CommRing F] [DecidableEq F]
    (m : Nat) (s : F) (tr : FullTranscript (protocol F m)) :
    accept m value s tr = some () ↔
      ∀ c ∈ (Zkc.Protocols.Sumcheck.ProductFamily.typedChecks m).map Zkc.Protocols.Sumcheck.ProductFamily.lowerCheck,
        c.2.1.eval (sourceEnv s (wire tr)) = c.2.2.eval (sourceEnv s (wire tr)) := by
  rw [Zkc.Protocols.Sumcheck.ProductFamily.elaborated_meaning]
  simp [accept, runWith_indexed value (fun _ => rfl)]

theorem checked_acceptance {F : Type} [CommRing F] [DecidableEq F]
    (source target : Block F) (ss ts : Nat)
    (ok : Zkc.Compiler.Blocks.hornerCheck source target ss ts = true) (m : Nat)
    (s : F) (tr : FullTranscript (protocol F m)) :
    accept m (moduleValue target ts) s tr = accept m value s tr ∧
    accept m (moduleValue source ss) s tr = accept m value s tr := by
  have hs := fun g => (checked_values source target ss ts ok g).1
  have ht := fun g => (checked_values source target ss ts ok g).2
  simp only [accept, runWith_indexed _ hs, runWith_indexed _ ht,
    runWith_indexed value (fun _ => rfl), and_self]

def verifier {F ι : Type} [CommRing F] [DecidableEq F]
    (oSpec : OracleSpec ι) (m : Nat) (evaluate : Round F → F) :
    Verifier oSpec F Unit (protocol F m) where
  verify s tr := OptionT.mk (pure (accept m evaluate s tr))

theorem checked_verifier {F ι : Type} [CommRing F] [DecidableEq F]
    (oSpec : OracleSpec ι) (source target : Block F) (ss ts : Nat)
    (ok : Zkc.Compiler.Blocks.hornerCheck source target ss ts = true) (m : Nat) :
    verifier oSpec m (moduleValue target ts) = verifier oSpec m value := by
  have h : accept m (moduleValue target ts) = accept m value := by
    funext s tr; exact (checked_acceptance source target ss ts ok m s tr).1
  simp only [verifier, h]

-- All ArkLib provers, with their state, witnesses and permitted shared-oracle
-- interactions, are unchanged. No honesty assumption appears in this theorem.
theorem checked_reduction {F ι WI WO : Type} [CommRing F] [DecidableEq F]
    (oSpec : OracleSpec ι) (source target : Block F) (ss ts : Nat)
    (ok : Zkc.Compiler.Blocks.hornerCheck source target ss ts = true) (m : Nat)
    (prover : Prover oSpec F WI Unit WO (protocol F m)) (s : F) (w : WI) :
    (Reduction.mk prover (verifier oSpec m (moduleValue target ts))).run s w =
    (Reduction.mk prover (verifier oSpec m value)).run s w := by
  rw [checked_verifier oSpec source target ss ts ok m]

-- Reuses the real security predicate; assumes rather than proves source
-- soundness and introduces neither a numerical bound nor a PPT model.
theorem checked_soundness {F ι S : Type} [CommRing F] [DecidableEq F]
    (oSpec : OracleSpec ι) (m : Nat)
    [∀ i, SampleableType ((protocol F m).Challenge i)]
    (init : ProbComp S) (impl : QueryImpl oSpec (StateT S ProbComp))
    (source target : Block F) (ss ts : Nat)
    (ok : Zkc.Compiler.Blocks.hornerCheck source target ss ts = true)
    (langIn : Set F) (langOut : Set Unit) (error : ℝ≥0) :
    Verifier.soundness init impl langIn langOut
      (verifier oSpec m (moduleValue target ts)) error ↔
    Verifier.soundness init impl langIn langOut (verifier oSpec m value) error := by
  rw [checked_verifier oSpec source target ss ts ok m]


end ZkcArkLib.Sumcheck.Scalar
