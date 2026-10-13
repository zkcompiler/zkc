import ZkcExamples.NativePrograms.CustomProperty
import ZkcExamples.NativePrograms.FactorHorner
import Zkc.Specification

/-! An independent Lake consumer of an actual imported source certificate and
an independently authored typed property. No external security package is needed. -/
noncomputable def importedSourceRejects :=
  @ZkcExamples.NativePrograms.CustomProperty.imported_rejects
noncomputable def composedSourceSoundness :=
  @ZkcExamples.NativePrograms.FactorHorner.property_interactive_soundness
