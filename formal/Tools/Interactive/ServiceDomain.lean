import Tools.Interactive.ScalarReference

/-! Installed stateful services are separate from scalar arithmetic support.
Adding a numerical domain does not install randomness, a group, or a transcript.
This is the executable reference's finite service inventory, not a restriction
on the protocol language or the parameterized mathematical interpretations. -/

set_option autoImplicit false

namespace Tools.Interactive.Reference

inductive ServiceDomain where
  | bls | ristretto
  deriving BEq, DecidableEq, Repr

def ServiceDomain.scalar : ServiceDomain → ScalarReference.Domain
  | .bls => .bls
  | .ristretto => .ristretto

def ServiceDomain.identity (domain : ServiceDomain) : String := domain.scalar.identity

def ServiceDomain.parse (identity : String) : Result ServiceDomain :=
  if identity == Bindings.fr then .ok .bls
  else if identity == Bindings.ristrettoScalar then .ok .ristretto
  else .error "reference-service-domain"

/-- Random tapes do not install a nonce or transcript service. -/
inductive RandomDomain where
  | bls | ristretto | bn254
  deriving BEq, DecidableEq, Repr

def RandomDomain.scalar : RandomDomain → ScalarReference.Domain
  | .bls => .bls | .ristretto => .ristretto | .bn254 => .bn254

def RandomDomain.identity (domain : RandomDomain) : String := domain.scalar.identity

def RandomDomain.parse (identity : String) : Result RandomDomain :=
  if identity == Bindings.fr then .ok .bls
  else if identity == Bindings.ristrettoScalar then .ok .ristretto
  else if identity == Bindings.bn254Fr then .ok .bn254
  else .error "reference-random-domain"

end Tools.Interactive.Reference
