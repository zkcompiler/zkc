import ZkcExamples.Structured.TotalState
import ZkcExamples.Structured.UnitState
import ZkcExamples.NativePrograms.CustomProperty
import ZkcExamples.NativePrograms.FactorHorner
import Zkc.Specification
import Zkc.Source.Common.Region
import Zkc.Source.Region
import Zkc.Protocols.Sumcheck.Multilinear

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
