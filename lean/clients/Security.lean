import Zkc.Verification.Claims.Methods.KnowledgeEndpoint
import Zkc.Verification.Bindings.Sigma.Schnorr
import Zkc.Protocol.Library.Families.Sigma.SigmaAndSchnorr
import Zkc.Verification.Families.Sumcheck.Common
import Zkc.Verification.Families.Sumcheck.Committed.Contract
import Zkc.Verification.Families.Sumcheck.FactorOpening.Security
import Zkc.Applications.Security.NativePrograms.FactorHorner

/-! A standalone consumer of generic security with no ArkLib package. -/
#check ZkcSecurity.Endpoint.knowledge_soundness
#check Zkc.Protocols.Sumcheck.soundness
#check Zkc.Protocols.Sumcheck.Common.VerifierContract.randomized_soundness
#check Zkc.Protocols.Sumcheck.FactorOpening.VerifierContract.conditional_soundness

noncomputable def composedSourceSoundness {F : Type} [Field F] [DecidableEq F]
    [Fintype F] :=
  (ZkcExamples.NativePrograms.FactorHorner.contract (F := F)).soundness
