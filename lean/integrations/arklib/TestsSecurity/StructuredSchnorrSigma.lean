import ZkcSecurity.Examples.StructuredSchnorrSigma

set_option smartUnfolding false

namespace TestsSecurity.StructuredSchnorrSigma
open ZkcSecurity.Examples.StructuredSchnorrSigma
open ZkcExamples.Structured

variable {F G : Type} [Field F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

example (base proverKey : G) (nonceService challengeService : Nat) :
    sigma (F := F) base proverKey nonceService challengeService =
      Schnorr.sigma F G base := sigma_eq ..

example (base key : G) (service : Nat) (prover : Zkc.Protocols.Schnorr.Common.Strategy F G)
    (first second : F) (distinct : first ≠ second)
    (acceptFirst : (SchnorrInteractive.run base key service prover first).outcome =
      .returned (some true))
    (acceptSecond : (SchnorrInteractive.run base key service prover second).outcome =
      .returned (some true)) :
    SchnorrBinding.formulaBinding.process (SchnorrBinding.arguments base key
      ((prover.response first - prover.response second) / (first - second))) =
      .done (.cons true .nil) :=
  extract_relation base key service prover first second distinct acceptFirst acceptSecond

end TestsSecurity.StructuredSchnorrSigma
