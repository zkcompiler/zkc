module

public import VCVio.OracleComp.EvalDist.AnswerMeasure

@[expose] public section

namespace ZkcSecurity.VCVio.UniformChallenge

/-- Opt-in uniform challenge law. The sampling oracle uses VCVio's own law;
its sum with this challenge oracle inherits the component laws. Importing this
module alone does not select a distribution for arbitrary challenge types. -/
noncomputable scoped instance {F : Type} [Finite F] [Nonempty F] :
    OracleSpec.UniformAnswerMeasure (Unit →ₒ F) :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _

end ZkcSecurity.VCVio.UniformChallenge
