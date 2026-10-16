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
import Zkc.Source.Structured.RepeatLaws
import ZkcExamples.NativePrograms.CustomProperty
import ZkcExamples.NativePrograms.FactorHorner
import Zkc.Specification
import Zkc.Source.Common.Region
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
noncomputable def composedSourceSoundness :=
  @ZkcExamples.NativePrograms.FactorHorner.property_interactive_soundness

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

theorem importedStructuredSourceCorrespondence
    (imported : Zkc.Source.Common.Native.Imported)
    (meaning : Zkc.Source.Mathematical.Meaning Zkc.Source.Common.Native.language)
    (condition : meaning.Value .boolean → Bool) (self : Nat)
    (inputs : Zkc.Source.Values (fun ty => Option (meaning.Value ty)) imported.snapshot.inputs) :
    (imported.toRegion self).denote (Zkc.Source.Common.participantMeaning meaning condition self)
        inputs.get =
      (imported.denote meaning condition self inputs).bind
        (fun value => .done (Zkc.Source.Values.singleton value)) :=
  imported.denote_toRegion meaning condition self inputs

/-- A downstream client consumes complete-process equations for actual admitted
structured compiler artifacts, without importing test modules. -/
noncomputable def importedTotalStateEquation :=
  @ZkcExamples.Structured.TotalState.process_eq_reference

noncomputable def importedUnitStateEquation :=
  @ZkcExamples.Structured.UnitState.process_eq_reference

/-- Complete retained subjects are usable through the normal package boundary.
The two large subjects expose admission independently of later Sumcheck laws. -/
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
