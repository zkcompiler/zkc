import ZkcArkLib.Fri.Johnson
import ZkcArkLib.Fri.SourceCalculations
import ZkcArkLibExamples.Fri.VerifierTerminal
import ZkcArkLibExamples.Fri.VirtualStore
import ZkcArkLibExamples.Fri.HolderPadding
import ZkcExamples.Structured.FriBindingExecution
import ZkcArkLibExamples.Fri.PublishedSampling
import ZkcArkLibExamples.Fri.ClearCertificate
import ZkcTools.DeclarationAudit

/-! Focused controls for the mathematical FRI adapters. The two-round example is a mathematical
client with terminal dimension two, not a parameter change to an installed source application.
It reuses the last two certificates from the feasibility study and the existing soundness API.
-/

namespace TestsArkLib.FriAdoption

open ZkcSecurity.ArkLib.Fri
open Zkc.Source.Structured
open Domain OracleComp ReedSolomon.HiddenDerivative

-- A scalar or Boolean terminal payload does not encode a coefficient vector,
-- even at the expected terminal origin.
example (sites : ObservedLayers.Sites) : ObservedLayers.decode sites 2 0 3
    [.message sites.terminal (.boolean true)] = none := by
  simp [ObservedLayers.decode, Zkc.Construction.Domain.Payload.value]

-- The entry root remembers the exact earlier word and challenge values in order.
example (sites : ObservedLayers.Sites) (prior : ObservedFold.History)
    (layers : Layers ZkcSecurity.Domains.KoalaBear.Octic 5 3) :
    ObservedLayers.atRoot sites 5 3 (prior ++ ObservedLayers.observations sites 0 layers) =
      some layers := ObservedLayers.atRoot_observations sites prior layers

-- The actual word expression chooses an antipodal pair, not the original row.
example : bitAnd 31 (wrappingSubtract (logicalShiftRight 32 1) 1) = 15 := by decide
example : wrappingAdd 15 16 = 31 := by decide
example : bitAnd 31 (wrappingSubtract 32 1) ≠ 15 := by decide

-- Dropping the source's representable row-size premise is unsound at log size 64.
example : bitAnd (2 ^ 64 - 1)
    (wrappingSubtract (logicalShiftRight (2 ^ 64) 1) 1) ≠ (2 ^ 64 - 1) % 2 ^ 63 := by decide

-- Exact current padding rejects the overlength mathematical case.
example : ¬ (([1, 2, 3] : List ℚ) ++ List.replicate (2 - 3) 0).length = 2 := by decide
example : bounded 1 ([1] : List ℚ) = true ∧ ([1] : List ℚ).length ≠ 2 ^ 1 := by decide

section
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured.FriSourceBodies
open ZkcSecurity.Domains.KoalaBear (Octic)

-- The installed helper rejects the two-cell input at width one; truncation
-- would turn this mutation into an apparently valid terminal message.
example {I : PIR.Signature} (a b : Octic) :
    invoke (RetainedFold.helpers (I := I)).closed helper21Helper (.cons [a, b] (.cons 1 .nil)) =
      .halt .reject := by
  refine (HolderPadding.installed [a, b] 1 (show 2 < indexLimit by decide) (by decide)).trans ?_
  rfl

-- Even the canonical empty list from interpolating zero produces one sent zero.
example {I : PIR.Signature} :
    invoke (RetainedFold.helpers (I := I)).closed helper21Helper (.cons [] (.cons 1 .nil)) =
      .done (.cons [(0 : Octic)] .nil) := by
  refine (HolderPadding.installed (I := I) [] 1 (by decide) (by decide)).trans ?_
  rfl
end

-- Sampled equality does not identify unsampled positions.
example : ∃ initial : Fin 2 → ℕ, initial 0 = 0 ∧ initial ≠ (fun _ ↦ 0) := by
  refine ⟨Fin.val, rfl, ?_⟩
  intro equality
  have atOne := congrFun equality 1
  norm_num at atOne

-- Duplicate positions still have distinct query ordinals: both checks must hold.
example : ¬ ∃ initial : Fin 2 → ℕ, ∀ query : Fin 2, initial 0 = query.val := by
  rintro ⟨initial, checks⟩
  have zero := checks 0
  have one := checks 1
  norm_num at zero one
  omega

-- The last head of the unchanged dimension-one demo cannot meet the new Johnson premise.
example : ¬ 2 ≤ degreeBound 0 (2 ^ 0) := by decide

private theorem certificate_sixteen : IsJohnsonWeightedCertificate 16 3 9 1 2 6 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight, johnsonWeightedHeightInt,
    johnsonWeightedMoment, johnsonWeightedSlope, johnsonWeightedN, johnsonWeightedW,
    johnsonWeightedR, johnsonWeightedT, johnsonWeightedU, Finset.sum_range_succ]

private theorem certificate_eight : IsJohnsonWeightedCertificate 8 1 5 1 1 4 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight, johnsonWeightedHeightInt,
    johnsonWeightedMoment, johnsonWeightedSlope, johnsonWeightedN, johnsonWeightedW,
    johnsonWeightedR, johnsonWeightedT, johnsonWeightedU, Finset.sum_range_succ]

private theorem threshold_sixteen : 9 ≤ ⌈(16 : ℝ) * (1 - 12 / 25)⌉₊ := by
  have exact : ⌈(16 : ℝ) * (1 - 12 / 25)⌉₊ = 9 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [exact]

private theorem threshold_eight : 5 ≤ ⌈(8 : ℝ) * (1 - 12 / 25)⌉₊ := by
  have exact : ⌈(8 : ℝ) * (1 - 12 / 25)⌉₊ = 5 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [exact]

-- A wrong integer threshold cannot be substituted even when the certificate is valid.
example : ¬ 10 ≤ ⌈(16 : ℝ) * (1 - 12 / 25)⌉₊ := by
  have exact : ⌈(16 : ℝ) * (1 - 12 / 25)⌉₊ = 9 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [exact]
  decide

variable {F : Type} [Field F] [Fintype F] [SampleableType F]

/-- Two different nontrivial head budgets, in the order consumed by `FoldingProximity`. -/
noncomputable def twoRoundError (F : Type) [Fintype F] (round : ℕ) : ENNReal :=
  if round = 0 then min 1 (ENNReal.ofReal ((763 : ℝ) / 3 / Fintype.card F))
  else min 1 (ENNReal.ofReal ((103 : ℝ) / 4 / Fintype.card F))

/-- Assembly checks the degree shift, subdomain and error shift at both rounds. -/
theorem weighted_two_round_proximity (domain : SmoothCosetFftDomain 5 F) :
    FoldingProximity 1 (12 / 25) domain 2 (twoRoundError F) := by
  apply foldingProximity_cons_weightedJohnson (R := 1) (t := 1) (radius := 12 / 25)
      (error := twoRoundError F) (A := 9) (multiplicity := 1) (B := 2) (H := 6)
      domain (by decide) certificate_sixteen (by decide) (by decide) (by decide)
      threshold_sixteen
  · norm_num [twoRoundError, degreeBound, johnsonWeightedRefinedExceptionCount]
  · apply foldingProximity_cons_weightedJohnson (R := 0) (t := 1) (radius := 12 / 25)
        (error := fun round ↦ twoRoundError F (round + 1))
        (A := 5) (multiplicity := 1) (B := 1) (H := 4)
        (domain.subdomain 1) (by decide) certificate_eight (by decide) (by decide) (by decide)
        threshold_eight
    · norm_num [twoRoundError, degreeBound, johnsonWeightedRefinedExceptionCount]
    · trivial

/-- The ordinary Johnson constructor also supplies a nonempty proximity chain. -/
theorem johnson_one_round_proximity (domain : SmoothCosetFftDomain 5 F) :
    FoldingProximity 2 (1 - johnsonAgreement 16 3 (1 / 4)) domain 1
      (fun _ ↦ min 1 (ENNReal.ofReal
        (johnsonExceptionCount 16 3 ⌈johnsonAgreement 16 3 (1 / 4) * 16⌉₊ (1 / 4) /
          (Fintype.card F : ℝ)))) := by
  apply foldingProximity_cons_johnson (R := 0) (t := 2) (eta := 1 / 4)
    domain (by decide) (by decide) (by norm_num)
  · have root : Real.sqrt ((3 : ℝ) / 16) ≤ 3 / 4 := Real.sqrt_le_iff.mpr (by norm_num)
    norm_num [degreeBound, johnsonAgreement, johnsonRhoMinus] at *
    linarith
  · rfl
  · exact le_rfl
  · trivial

variable [DecidableEq F]

/-- The assembled chain supplies the existing all-words escape API without a new engine. -/
theorem weighted_two_round_escapes (domain : SmoothCosetFftDomain 5 F) :
    FoldingEscapes 1 (12 / 25) domain 2 (twoRoundError F) :=
  foldingEscapes_of_proximity 1 (12 / 25) domain 2 _ (weighted_two_round_proximity domain)

/-- A client of the existing ideal soundness theorem, still conditional on geometry and roots. -/
theorem weighted_two_round_soundness (roots : ℕ → F) (shift : F) (queries : ℕ)
    (domain : SmoothCosetFftDomain 5 F)
    (geometry : ∀ i : Fin (2 ^ 5), domain i = point roots shift 5 i)
    (compatible : Compatible roots 5 2) (distance : ℝ)
    (prover : ProbComp ((Fin (2 ^ 5) → F) × Strategy F 5 2)) :
    Pr{let result ← experiment roots 1 shift queries prover}[
      result.2 = true ∧ Far domain (degreeBound 2 (2 ^ 1)) distance
        (toTrace 1 domain result.1).initial] ≤
      (∑ round ∈ Finset.range 2, twoRoundError F round) +
        ENNReal.ofReal (1 - min (12 / 25) distance) ^ queries :=
  soundness roots 1 queries domain shift geometry compatible (12 / 25) distance _
    (weighted_two_round_proximity domain) prover

end TestsArkLib.FriAdoption

-- Audit every declaration in the three new production modules, not just selected roots.
run_cmd (ZkcTools.DeclarationAudit.check
  [`ZkcArkLib.Fri.JohnsonBounds, `ZkcArkLib.Fri.Johnson, `ZkcArkLib.Fri.SourceCalculations]
  "FRI-MATHEMATICAL-ADAPTERS-PASS" (exactModules := true))

run_cmd (ZkcTools.DeclarationAudit.checkBoundary
  [`ZkcArkLib.Fri.JohnsonBounds, `ZkcArkLib.Fri.Johnson, `ZkcArkLib.Fri.SourceCalculations]
  [`ArkLib] [] "FRI-JOHNSON-UPSTREAM-BOUNDARY-PASS")

run_cmd ZkcTools.DeclarationAudit.checkCurrent "FRI-ADOPTION-CONTROLS-PASS"

run_cmd (ZkcTools.DeclarationAudit.check
  [`Zkc.Source.Structured.OracleQueryDerivation, `ZkcExamples.Structured.FriIndexCollections,
   `ZkcExamples.Structured.FriScalarLoop, `ZkcExamples.Structured.FriBoundedPositions,
   `ZkcExamples.Structured.FriBinding, `ZkcExamples.Structured.FriApplications,
   `ZkcArkLibExamples.Fri.RetainedQueries, `ZkcArkLibExamples.Fri.RetainedSampling,
   `ZkcArkLibExamples.Fri.PublishedSampling] "FRI-INSTALLED-SCALAR-SAMPLING-PASS" (exactModules := true))

run_cmd (ZkcTools.DeclarationAudit.check
  [`Zkc.Semantics.HandlerReturn, `Zkc.Source.Structured.OracleForwarding,
   `Zkc.Source.Structured.OracleLocalAction, `Zkc.Source.Structured.ReceiverForwarding,
   `ZkcExamples.Structured.FriBindingExecution] "FRI-RECEIVER-FORWARDING-PASS" (exactModules := true))

run_cmd (ZkcTools.DeclarationAudit.check
  [`ZkcArkLibExamples.Fri.RetainedDomain,
   `ZkcArkLibExamples.Fri.RetainedFold,
   `ZkcArkLibExamples.Fri.HolderFold,
   `ZkcArkLibExamples.Fri.HolderInterpolation,
   `ZkcArkLibExamples.Fri.HolderPadding,
   `ZkcArkLibExamples.Fri.ObservedFold,
   `ZkcArkLibExamples.Fri.ObservedLayers,
   `ZkcArkLibExamples.Fri.ObservedQueries,
   `ZkcArkLibExamples.Fri.TranscriptCharge,
   `ZkcArkLibExamples.Fri.TranscriptTrace,
   `ZkcArkLibExamples.Fri.ClearSites,
   `ZkcArkLibExamples.Fri.ClearCertificate] "FRI-RETAINED-CERTIFICATE-BOUNDARIES-PASS" (exactModules := true))


run_cmd (ZkcTools.DeclarationAudit.check
  [`Zkc.Semantics.CallRestriction, `Zkc.Source.Structured.OracleReadEffects,
   `Zkc.Source.Structured.OracleReadback, `ZkcExamples.Structured.FriPower,
   `ZkcExamples.Structured.FriVirtualBody, `ZkcArkLibExamples.Fri.VirtualReads,
   `ZkcArkLibExamples.Fri.VirtualWord, `ZkcArkLibExamples.Fri.StoredWord,
   `ZkcArkLibExamples.Fri.VirtualStore, `ZkcArkLibExamples.Fri.VerifierTerminal]
  "FRI-VERIFIER-READS-AND-TERMINAL-PASS" (exactModules := true))
