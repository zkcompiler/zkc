import Zkc.Construction.ScalarConnection
import Zkc.Construction.Uniform.ScalarSupportProposer
import ZkcExamples.Structured.Generated.Connections.SchnorrRandomized
import ZkcExamples.Structured.Generated.Connections.SchnorrAnd
import ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator
import ZkcExamples.Structured.Generated.Connections.SmallSumcheck
import ZkcExamples.Structured.Generated.Connections.TwoSums

set_option autoImplicit false
namespace Tests.RetainedScalarConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Construction
open Uniform
open Uniform.ScalarSupport
open ZkcExamples.Structured.Generated.Connections
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

example (inputs : Values (Component (assignment F G)) SchnorrRandomized.program.payload.entry.inputs) :
    Supported false (Occurrence.participant (ringModel F G) SchnorrRandomized.program 1 inputs) := by
  derive_scalar_support



example : ScalarFragment.check true SmallSumcheck.program = true := by decide +kernel
example : ScalarFragment.check true TwoSums.program = true := by decide +kernel
example : ScalarFragment.check false SmallSumcheck.program = false := by decide +kernel

example {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq G] (role : Nat)
    (inputs : Values (Component (assignment F G)) SmallSumcheck.program.payload.entry.inputs) :
    ScalarSupport.Supported true
      (Occurrence.participant (ringModel F G) SmallSumcheck.program role inputs) := by
  derive_scalar_support

example : ScalarFragment.operation false (.exchange .boolean 0 1 "b") = true := rfl
example : ScalarFragment.operation false (.exchange (.field "F") 0 1 "f") = true := rfl
example : ScalarFragment.operation false (.exchange (.group "G") 0 1 "g") = true := rfl
example : ScalarFragment.operation true (.exchange .index 0 1 "i") = false := rfl
example : ScalarFragment.operation true (.exchange (.service "private") 0 1 "s") = false := rfl
example : ¬ ScalarSupport.Message (.service "private") := ScalarSupport.service_not_message _
example : ¬ ScalarSupport.Message .index := ScalarSupport.index_not_message

example : SchnorrAnd.validatorArtifact = SchnorrAndProofParticipant.participant := by rfl
example : ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.artifact =
    SchnorrAnd.validatorArtifact := by rfl

end Tests.RetainedScalarConnection
