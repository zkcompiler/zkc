import ZkcSecurity.Endpoint.Knowledge
import ZkcSecurity.Families.Schnorr
import ZkcSecurity.VCVio.SigmaAndSchnorr
import ZkcSecurity.Families.Sumcheck.Common
import ZkcSecurity.Families.Sumcheck.Committed.Contract
import ZkcSecurity.Families.Sumcheck.FactorOpening.Security
import ZkcSecurity.Examples.NativePrograms.FactorHorner

/-! A standalone consumer of generic security with no ArkLib package. -/
#check ZkcSecurity.Endpoint.knowledge_soundness
#check Zkc.Protocols.Sumcheck.soundness
#check Zkc.Protocols.Sumcheck.Common.VerifierContract.randomized_soundness
#check Zkc.Protocols.Sumcheck.FactorOpening.VerifierContract.conditional_soundness

noncomputable def composedSourceSoundness :=
  @ZkcExamples.NativePrograms.FactorHorner.property_interactive_soundness
