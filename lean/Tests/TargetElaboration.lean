import Zkc.Construction.TargetElaboration
import ZkcExamples.Construction.SumcheckProof
import ZkcExamples.Construction.SchnorrProofBinding

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

namespace Tests.TargetElaboration
open Zkc.Construction Zkc.Source.Structured

def sumcheckTarget : RetainedTarget
    ZkcExamples.Construction.SumcheckProof.imported
    ZkcExamples.Construction.SumcheckProof.participant.policy
    ZkcExamples.Construction.SumcheckProof.selection.publics := by
  bind_target "public_sum"

def schnorrTarget : RetainedTarget
    ZkcExamples.Construction.SchnorrProof.imported
    ZkcExamples.Construction.SchnorrProof.participant.policy
    ZkcExamples.Construction.SchnorrProof.selection.publics := by
  bind_target "knowledge"

example : (sumcheckTarget.owner.clause sumcheckTarget.clauseIndex).name = "public_sum" := rfl
example : (schnorrTarget.owner.clause schnorrTarget.clauseIndex).name = "knowledge" := rfl

-- A spelling error cannot silently select the first available clause.
example : True := by
  fail_if_success
    have : RetainedTarget
        ZkcExamples.Construction.SumcheckProof.imported
        ZkcExamples.Construction.SumcheckProof.participant.policy
        ZkcExamples.Construction.SumcheckProof.selection.publics := by
      bind_target "missing_target"
  trivial

-- A changed publication map cannot use the old retained relation reading.
example : True := by
  fail_if_success
    have : RetainedTarget
        ZkcExamples.Construction.SumcheckProof.imported
        { ZkcExamples.Construction.SumcheckProof.participant.policy with publicInputs := [] }
        [] := by
      bind_target "public_sum"
  trivial

#print axioms sumcheckTarget
#print axioms schnorrTarget
end Tests.TargetElaboration
