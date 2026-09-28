import Examples.Mathematical.SigmaPrefix

/-! Canonical Sigma example on the installed BLS carriers.

The exported source is byte-compared with fresh `sigma.pir` frontend output.
Admission supplies the actual stored program. The two proved prefix laws cover
fresh reception and query/pure/send sequencing. Full honest execution, native
provider agreement and security remain separate obligations.
-/

set_option autoImplicit false
namespace Examples.Mathematical.Sigma

export SigmaSubject (subject admission closed openMeaning verifier_fresh_receive prover_pure_commitment)

open Zkc.Algebra.Bls12381
variable [Fact baseModulus.Prime]

/-- Standalone honest algebra on the actual scalar/group carriers. Connecting
this equation to the complete admitted trace is a subsequent proof. -/
theorem standalone_honest_algebra (witness nonce : Scalar) (challenge : Challenge) (generator : G1) :
    (nonce + challenge.val * witness) • generator =
      nonce • generator + challenge.val • (witness • generator) :=
  honestEquation witness nonce challenge generator

end Examples.Mathematical.Sigma
