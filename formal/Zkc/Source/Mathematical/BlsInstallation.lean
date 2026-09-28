import Zkc.Source.Mathematical.RegistryAdmission
import Zkc.Algebra.Bls12381

/-! Consumer-owned installation for the closed BLS12-381 mathematical profile.

Payloads select meanings as well as signatures. These are finite installed
packages, not definitions supplied by an untrusted subject. Unsupported atomic
types have empty carriers. The generic mathematical language remains broader
than this installation and the separately checked placement profile.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.BlsInstallation
open ManifestAdmission
open Zkc.Algebra.Bls12381

inductive Domain where
  | scalar | group
  deriving DecidableEq, Repr

inductive LogicalType where
  | scalar | nonzero | group | boolean
  deriving DecidableEq, Repr

inductive Operation where
  | fieldAdd | fieldMul | fromNonzero | generator | groupAdd | scale | equal
  deriving DecidableEq, Repr

inductive Service where
  | draw | drawNonzero
  deriving DecidableEq, Repr

def Payload : Category → Type
  | .domain => Domain
  | .operation => Operation
  | .wire => LogicalType
  | .service => Service
  | .law => Empty

def Domain.identity : Domain → Raw.Identity
  | .scalar => ⟨"bls12-381.fr", "1", "b3bf27ba483aa7d7f03213d63048ce07099e67208ffe9baaeb6b67accb94fa98"⟩
  | .group => ⟨"bls12-381.g1", "1", "19ac738a87762ababd318b676384d17abfdfbf0d7c910c210acd6e58e248217a"⟩

def Operation.identity : Operation → Raw.Identity
  | .fieldAdd => ⟨"field.add([\"bls12-381.fr\"])", "1", "163dd647e00047f9e8719c407cafb1135c58d6639897721bf5aae8b2031b412b"⟩
  | .fieldMul => ⟨"field.mul([\"bls12-381.fr\"])", "1", "f22731029e5a8f0940c78e4232be8625e5568d76cf7708f5c97276cb9491f964"⟩
  | .fromNonzero => ⟨"field.from_nonzero([\"bls12-381.fr\"])", "1", "34a6e50a4b8c8efe26b2a34545faa7ff8421d3e6e4385c9e9e8d0033efea4670"⟩
  | .generator => ⟨"curve.generator([\"bls12-381.g1\"])", "1", "eeaf191e399536cee7208dee501001e78cf2410e0ef3b6e5f30ec445f1d16c5a"⟩
  | .groupAdd => ⟨"curve.add([\"bls12-381.g1\"])", "1", "6b153b46b69bc8bbbc0026dd50ea0a8848cfa48017bfbb64e2abe946325527bd"⟩
  | .scale => ⟨"curve.scale([\"bls12-381.g1\"])", "1", "6ee1c3e664331a869979829b9052823fad1002b7ad916619f34281c91cc95e68"⟩
  | .equal => ⟨"curve.equal([\"bls12-381.g1\"])", "1", "6cbeb38aa17b2ec01e06729a1bf573fb632fe9c6d88ce23dc08b9ebbd71ca9bb"⟩

def Service.identity : Service → Raw.Identity
  | .draw => ⟨"random.draw([\"bls12-381.fr\"])", "1", "770c5f3f32bb29ece439952923e57bbd87b6ebec0d7518eaab5aeb07cc7cac07"⟩
  | .drawNonzero => ⟨"random.draw_nonzero([\"bls12-381.fr\"])", "1", "8c3dec7b0edfa28310df27737af7129a54c9cca61906e9e8472441162293b0c5"⟩

def LogicalType.wireIdentity : LogicalType → Raw.Identity
  | .scalar => ⟨"zkcv.field.bls12-381.fr/1", "1", "04d7df8100d8ddd1e0e99605fde258c8e4487c8fa262f3e60c8e26a114bbb3c4"⟩
  | .nonzero => ⟨"zkcv.nonzero_field.bls12-381.fr/1", "1", "ea14c68099c543f9114e21f45dad65dfe9bf81c9f4517e0824eb430f4230aa66"⟩
  | .group => ⟨"zkcv.group.bls12-381.g1/1", "1", "1c39bd2c408c214ea18a1680cd5c4219655ca324c1bb8c2e0523469efdd55a39"⟩
  | .boolean => ⟨"zkcv.bool/1", "1", "21d64d9a5a7c092a594fa0161a3ba7f8c6568d0b35359a78012d4454d8690d87"⟩

def LogicalType.domains : LogicalType → List Domain
  | .scalar | .nonzero => [.scalar]
  | .group => [.group, .scalar]
  | .boolean => []

abbrev Operation.arguments : Operation → List LogicalType
  | .fieldAdd | .fieldMul => [.scalar, .scalar]
  | .fromNonzero => [.nonzero]
  | .generator => []
  | .groupAdd | .equal => [.group, .group]
  | .scale => [.group, .scalar]

abbrev Operation.result : Operation → LogicalType
  | .fieldAdd | .fieldMul | .fromNonzero => .scalar
  | .generator | .groupAdd | .scale => .group
  | .equal => .boolean

def Service.result : Service → LogicalType
  | .draw => .scalar
  | .drawNonzero => .nonzero

abbrev LogicalType.Value (model : GroupModel) : LogicalType → Type
  | .scalar => Scalar
  | .nonzero => Challenge
  | .group => model.Carrier
  | .boolean => Fin 2

/-- The selected operation, not its signature, determines the total function. -/
def Operation.denote (model : GroupModel) : (operation : Operation) →
    Values (LogicalType.Value model) operation.arguments → LogicalType.Value model operation.result
  | .fieldAdd, .cons left (.cons right .nil) => left + right
  | .fieldMul, .cons left (.cons right .nil) => left * right
  | .fromNonzero, .cons value .nil => value.val
  | .generator, .nil => model.generator
  | .groupAdd, .cons left (.cons right .nil) => left + right
  | .scale, .cons point (.cons scalar .nil) => scalar • point
  | .equal, .cons left (.cons right .nil) => if left = right then 1 else 0

def nominal (Group : Type) : Domain → String → List Nat → Type
  | .scalar, "field", [] => Scalar
  | .scalar, "nonzero_field", [] => Challenge
  | .group, "group", [] => Group
  | _, _, _ => Empty

private def requiresDomains (domains : List Domain) : List Requirement :=
  (domains.eraseDups).map fun domain => ⟨.domain, domain.identity⟩

def domainPackage (domain : Domain) : Package Payload .domain :=
  ⟨domain.identity, domain, requiresDomains (if domain = .group then [.scalar] else [])⟩

def operationPackage (operation : Operation) : Package Payload .operation :=
  ⟨operation.identity, operation,
    requiresDomains ((operation.result :: operation.arguments).flatMap LogicalType.domains)⟩

def wirePackage (type : LogicalType) : Package Payload .wire :=
  ⟨type.wireIdentity, type, requiresDomains type.domains⟩

def servicePackage (service : Service) : Package Payload .service :=
  ⟨service.identity, service, requiresDomains service.result.domains⟩

def installation : Installation Payload
  | .domain => ⟨[domainPackage .scalar, domainPackage .group], by decide⟩
  | .operation => ⟨[operationPackage .fieldAdd, operationPackage .fieldMul,
      operationPackage .fromNonzero, operationPackage .generator, operationPackage .groupAdd,
      operationPackage .scale, operationPackage .equal], by decide⟩
  | .wire => ⟨[wirePackage .scalar, wirePackage .nonzero, wirePackage .group,
      wirePackage .boolean], by decide⟩
  | .service => ⟨[servicePackage .draw, servicePackage .drawNonzero], by decide⟩
  | .law => ⟨[], by decide⟩

/-- Classification uses the complete domain identity at the actual index. -/
def classify {domains arity : Nat} (manifest : Raw.Manifest) : TypeExpansion.Shape domains arity → Option LogicalType
  | .atom (.nominal index constructor []) =>
      if manifest.domains[index.val]? = some Domain.scalar.identity then
        if constructor = "field" then some .scalar
        else if constructor = "nonzero_field" then some .nonzero else none
      else if manifest.domains[index.val]? = some Domain.group.identity && constructor == "group" then
        some .group
      else none
  | .fin (.literal value) => if value.val = 2 then some .boolean else none
  | _ => none

def domainCheck {domains arity : Nat} (_manifest : Raw.Manifest) (domain : Domain) :
    TypeExpansion.Atom domains arity → Bool
  | .nominal _ constructor [] => match domain with
      | .scalar => constructor == "field" || constructor == "nonzero_field"
      | .group => constructor == "group"
  | _ => false

def operationCheck {domains arity : Nat} (manifest : Raw.Manifest) (operation : Operation)
    (signature : SignatureAdmission.OperationSignature domains arity) : Option RegistryAdmission.OperationFacts :=
  if signature.identity = operation.identity ∧ signature.statics = [] ∧ signature.capabilities = [] ∧
      signature.arguments.mapM (classify manifest) = some operation.arguments ∧
      classify manifest signature.result = some operation.result then
    some ⟨.total, []⟩
  else none

def serviceCheck {domains arity : Nat} (manifest : Raw.Manifest) (service : Service)
    (signature : SignatureAdmission.ServiceSignature domains arity) : Bool :=
  signature.identity == service.identity && signature.statics.isEmpty && signature.arguments.isEmpty &&
    classify manifest signature.result == some service.result

def contracts (Group : Type) : RegistryAdmission.Contracts Payload where
  installation := installation
  nominal := nominal Group
  polynomial := fun _ _ _ _ => Empty
  residual := fun _ _ _ => Empty
  domain := domainCheck
  operation := operationCheck
  service := serviceCheck
  wire manifest type statics shape := statics.isEmpty && classify manifest shape == some type
  attributes _ _ _ attributes := attributes == .object []

/-- A successful contract check exposes the signature used by the payload's
typed meaning; equal signatures never collapse different package selections. -/
theorem operationCheck_signature {domains arity : Nat} (manifest : Raw.Manifest) (operation : Operation)
    (signature : SignatureAdmission.OperationSignature domains arity) (facts : RegistryAdmission.OperationFacts)
    (accepted : operationCheck manifest operation signature = some facts) :
    signature.identity = operation.identity ∧ signature.statics = [] ∧ signature.capabilities = [] ∧
      signature.arguments.mapM (classify manifest) = some operation.arguments ∧
      classify manifest signature.result = some operation.result := by
  unfold operationCheck at accepted
  split at accepted
  · assumption
  · contradiction

end Zkc.Source.Mathematical.BlsInstallation
