import Zkc.IR.Executable.DomainParticipant
import Zkc.Applications.IR.Construction.SchnorrArtifact
import Zkc.Applications.IR.Construction.SumcheckArtifact
import Zkc.Applications.IR.Construction.DeferredRounds

/-! The shared return-schema condition is checked on finite, looped and
rescheduled retained artifacts. It does not assume protocol validity. -/
namespace Tests.DomainParticipant
open Zkc.Construction Zkc.Executable ZkcExamples.Construction

example : DomainVM.ReturnSchema SchnorrProof.participant := by decide +kernel
example : DomainVM.ReturnSchema SumcheckProof.participant := by decide +kernel
example : DomainVM.ReturnSchema DeferredRounds.participant := by decide +kernel

-- Reading a public group as the declared acceptance Boolean is rejected.
example : ¬ DomainVM.ReturnSchema
    { SchnorrProof.participant with returned := [0, 13] } := by decide +kernel

-- Out-of-range references cannot discharge the boundary through an empty map.
example : ¬ DomainVM.ReturnSchema
    { SchnorrProof.participant with returned := [100000, 13] } := by decide +kernel

end Tests.DomainParticipant
