import ZkcExamples.Structured.TotalState
import ZkcExamples.Structured.UnitState
import ZkcExamples.Structured.RepeatViews
import ZkcExamples.Structured.RepeatNestedViews
import ZkcExamples.Structured.RepeatServiceViews
import ZkcExamples.Structured.RepeatServiceWrapperViews
import ZkcExamples.Structured.RepeatLaws
import ZkcExamples.Structured.RepeatNestedLaws
import ZkcExamples.Structured.RepeatServiceLaws
import ZkcExamples.Structured.RepeatServiceWrapperLaws
import ZkcExamples.Structured.SumcheckReduceViews
import ZkcExamples.Structured.SumcheckSourceViews
import ZkcExamples.Structured.SumcheckSourceVerifier
import ZkcExamples.Structured.SumcheckReduceVerifier
import Zkc.Source.Structured.RepeatLaws
import ZkcExamples.NativePrograms.CustomProperty
import Zkc.Specification
import Zkc.Source.Region
import Zkc.Protocols.Sumcheck.Multilinear
import ZkcExamples.Structured.MapContractInstances
import ZkcExamples.Structured.SumcheckHelperBridge
import ZkcExamples.Structured.SumcheckSourceContracts
import ZkcExamples.Structured.SumcheckReduceContracts

/-! An independent Lake consumer of an actual imported source certificate and
an independently authored typed property. No external security package is needed. -/
noncomputable def importedSourceRejects :=
  @ZkcExamples.NativePrograms.CustomProperty.imported_rejects

/-- A downstream transformation proof uses the same contextual contract without
importing test modules or the protocol-specific example operation vocabulary. -/
theorem contextualReplacement {dialect : Zkc.Source.Dialect} {interface : PIR.Signature}
    (meaning : Zkc.Source.RegionMeaning dialect interface) {Γ mid out}
    {left right : Zkc.Source.Region dialect Γ mid}
    (same : Zkc.Source.Region.Equivalent meaning left right)
    (next : Zkc.Source.Region dialect (mid ++ Γ) out)
    (env : Zkc.Source.Environment meaning.Value Γ) :
    PIR.ExactRefinement ((left.bind next).denote meaning env)
      ((right.bind next).denote meaning env) :=
  Zkc.Source.Region.exactRefinement meaning
    (Zkc.Source.Region.bind_congr meaning same (fun _ => rfl)) env

/-- The former generic Common flat-AST lowering theorem is retired. This client
consumes the actual Schnorr Structured participant equation. -/
theorem importedSchnorrSourceCorrespondence
    {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (base key : G) (service : Nat) :
    ZkcExamples.NativePrograms.Schnorr.verifier (F := F) base key service =
      ZkcExamples.NativePrograms.Schnorr.experiment (F := F) base key service :=
  ZkcExamples.NativePrograms.Schnorr.verifier_correspondence base key service

/-- A downstream client consumes complete-process equations for actual admitted
structured compiler artifacts, without importing test modules. -/
noncomputable def importedTotalStateEquation :=
  @ZkcExamples.Structured.TotalState.process_eq_reference

noncomputable def importedUnitStateEquation :=
  @ZkcExamples.Structured.UnitState.process_eq_reference

/-- Complete retained subjects are usable through the normal package boundary.
The two large subjects expose admission separately from their verifier equations. -/
noncomputable def importedRepeatAdmission :=
  @ZkcExamples.Structured.RepeatViews.kernel_admission

noncomputable def importedNestedRepeatAdmission :=
  @ZkcExamples.Structured.RepeatNestedViews.kernel_admission

noncomputable def importedRepeatServiceAdmission :=
  @ZkcExamples.Structured.RepeatServiceViews.kernel_admission

noncomputable def importedRepeatServiceWrapperAdmission :=
  @ZkcExamples.Structured.RepeatServiceWrapperViews.kernel_admission

noncomputable def importedReductionAdmission :=
  @ZkcExamples.Structured.SumcheckReduceViews.kernel_admission

noncomputable def importedFullSumcheckAdmission :=
  @ZkcExamples.Structured.SumcheckSourceViews.kernel_admission

/-- Downstream users consume complete process laws without importing tests. -/
noncomputable def importedRepeatIndependentCounts :=
  @ZkcExamples.Structured.RepeatLaws.independent_counts

noncomputable def importedNestedRepeatEquation :=
  @ZkcExamples.Structured.RepeatNestedLaws.repeated_addition

noncomputable def importedRepeatServiceEquation :=
  @ZkcExamples.Structured.RepeatServiceLaws.contextual_verifier

noncomputable def importedMappedRepeatServiceEquation :=
  @ZkcExamples.Structured.RepeatServiceWrapperLaws.observed_sender

/-- The mathematical multilinear API is independently consumable without an
optional security dependency or an imported Sumcheck subject. -/
theorem multilinearResidualMeaning {F : Type} [CommRing F] {n k : Nat}
    (table : Zkc.Polynomial.Multilinear.Table F (n + k)) (point : Fin k → F) (claim : F) :
    Zkc.Protocols.Sumcheck.Multilinear.ResidualClaim k table point claim ↔
      Zkc.Polynomial.cubeSum n (fun suffix => Zkc.Polynomial.Multilinear.extension
        (n + k) table (Zkc.Polynomial.Quadratic.point k point suffix)) = claim :=
  Zkc.Protocols.Sumcheck.Multilinear.residualClaim_iff table point claim

/-- Marginal-table laws are available to core-only consumers. -/
theorem multilinearMarginalMeaning {F : Type} [CommRing F] {n k : Nat}
    (table : Zkc.Polynomial.Multilinear.Table F (n + k)) (point : Fin k → F) :
    Zkc.Polynomial.Multilinear.extension k
      (Zkc.Polynomial.Multilinear.sumRemaining n k table) point =
      Zkc.Polynomial.Multilinear.booleanSum
        (Zkc.Polynomial.Multilinear.fixPrefix k table point) :=
  Zkc.Polynomial.Multilinear.extension_sumRemaining table point

/-- A downstream consumer can inspect the complete optional-input verifier
process of each original, without importing tests or a security package. -/
noncomputable def importedStructuredSumcheckVerifier :=
  @ZkcExamples.Structured.SumcheckSourceVerifier.verifier_optional

noncomputable def importedStructuredSumcheckChecked :=
  @ZkcExamples.Structured.SumcheckSourceVerifier.verifier_checked

noncomputable def importedStructuredSumcheckReduction :=
  @ZkcExamples.Structured.SumcheckReduceVerifier.verifier_optional

/-- Missing active count stops before receiving any prover message. -/
theorem structuredSumcheckMissingCount {F G : Type}
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (raw : Option (List F)) (claim : Option F) (service : Option Nat) :
    ZkcExamples.Structured.SumcheckSourceViews.program.participant F G 1
      (ZkcExamples.Structured.SumcheckSourceVerifier.sourceRootInputs raw claim none service) =
        .halt .incomplete := by
  exact ZkcExamples.Structured.SumcheckSourceVerifier.verifier_missing raw claim service

/-- The Reduction root returns its present claim unchanged at zero rounds,
with an empty verifier point and no service requirement. -/
theorem structuredSumcheckReductionZero {F G : Type}
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (claim : F) :
    ZkcExamples.Structured.SumcheckReduceViews.program.participant F G 1
      (ZkcExamples.Structured.SumcheckReduceVerifier.reduceRootInputs
        none none (some claim) (some 0) none) =
          .done (.cons none (.cons none (.cons (some []) (.cons (some claim) .nil)))) := by
  rw [ZkcExamples.Structured.SumcheckReduceVerifier.verifier_optional]
  rfl

open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured in
/-- A mapped caller retains self0 at the actual terminal, even when zero rounds
need no service. The root and helper tables remain the complete original ones. -/
theorem structuredSumcheckMappedZero {F G : Type}
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (raw : Option (List F)) (claim : F) :
    invokeProtocol (SumcheckSourceViews.unit.plainProtocolTable F G)
      SumcheckSourceBodies.runSignature
      ⟨some "outer", roleSubstitution [2, 0]⟩ 0
      (SumcheckSourceVerifier.sourceRootInputs raw (some claim) (some 0) none) =
        SumcheckVerifierTerminal.actualOwnedCheck SumcheckSourceViews.unit 0
          raw (some []) (some claim) := by
  rw [SumcheckSourceVerifier.verifier_permuted_optional,
    SumcheckVerifierPrelude.admittedRounds_zero]
  rfl

/-- A downstream client derives helper laws from exact members of its own list. -/
noncomputable def reusableFirstContracts :=
  @ZkcExamples.Structured.MapFirstContracts.laws_of_bodies

noncomputable def reusablePrefixContracts :=
  @ZkcExamples.Structured.MapPrefixContracts.laws_of_bodies

noncomputable def importedMapPrefixContracts :=
  @ZkcExamples.Structured.MapPrefixContractsInstance.prefix_laws

noncomputable def publicHelperMathematicalCheck :=
  @ZkcExamples.Structured.SumcheckHelperLaws.check_mathematical

/-- Two complete original helper inventories instantiate the generic contracts independently. -/
noncomputable def originalReductionMessage :=
  @ZkcExamples.Structured.SumcheckReduceContracts.sums_honestMessage

noncomputable def originalSumcheckPlainCheck :=
  @ZkcExamples.Structured.SumcheckSourceContracts.check_plain

noncomputable def originalSumcheckOptionalWidth :=
  @ZkcExamples.Structured.SumcheckSourceContracts.width_components

-- The public process interface supports ordinary Lean monadic notation.
example {I : PIR.Signature} (process : PIR.Process I Nat) :
    (do let value ← process; pure value) = process := by simp
