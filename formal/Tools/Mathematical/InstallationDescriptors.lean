import Zkc.Source.Mathematical.BlsInstallation
import Tools.Mathematical.Codec

/-! Independently authored descriptors for the finite mathematical installation.

The domain package identifies the full installed logical catalog; the BLS
mathematical consumer accepts only its declared scalar/group subset. SHA256
of these independently encoded descriptors is checked by the host. Hashing
supplies content identity, not operation or provider correctness.
-/

set_option autoImplicit false
namespace Tools.Mathematical.InstallationDescriptors
open Zkc.Source.Mathematical BlsInstallation

private def strings (values : List String) : Raw.Attribute := .array (values.map .string)

def spelling : LogicalType → String
  | .scalar => "field:bls12-381.fr"
  | .nonzero => "nonzero_field:bls12-381.fr"
  | .group => "group:bls12-381.g1"
  | .boolean => "bool"

private def publicTypes (kinds : List String) : Raw.Attribute :=
  .array (kinds.map fun kind => .array [.string kind, .boolean true, .boolean true, .string "PublicValue"])

def domain (value : Domain) : Raw.Attribute :=
  let (sort, modulus, associated, capabilities, types) := match value with
    | .scalar => ("Field", toString Zkc.Algebra.Bls12381.scalarModulus, .array [],
        strings ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo"],
        publicTypes ["field", "nonzero_field", "vector", "polynomial", "round", "matrix", "table", "point"])
    | .group => ("Group", "", .array [strings ["Scalar", "bls12-381.fr"]],
        strings ["Group", "ScalarAction"], publicTypes ["group", "groups"])
  .array [.string "domain", .string "closed-unary-and-field-families/1", .string value.identity.name,
    .string sort, .string modulus, associated, capabilities, types]

def operationBinding : Operation → String × List String
  | .fieldAdd => ("field.add", ["bls12-381.fr"])
  | .fieldMul => ("field.mul", ["bls12-381.fr"])
  | .fromNonzero => ("field.from_nonzero", ["bls12-381.fr"])
  | .generator => ("curve.generator", ["bls12-381.g1"])
  | .groupAdd => ("curve.add", ["bls12-381.g1"])
  | .scale => ("curve.scale", ["bls12-381.g1"])
  | .equal => ("curve.equal", ["bls12-381.g1"])

def operation (value : Operation) : Raw.Attribute :=
  let binding := operationBinding value
  .array [.string "operation", .string "closed-logical/1", .string binding.1, strings binding.2,
    .string "Total", strings (value.arguments.map spelling), strings [spelling value.result]]

def wire (value : LogicalType) : Raw.Attribute :=
  .array [.string "wire", .string "installed-payload/1", .string value.wireIdentity.name,
    .string (spelling value)]

def serviceBinding : Service → String × List String
  | .draw => ("random.draw", ["bls12-381.fr"])
  | .drawNonzero => ("random.draw_nonzero", ["bls12-381.fr"])

def service (value : Service) : Raw.Attribute :=
  let binding := serviceBinding value
  .array [.string "service", .string "nullary-entropy/1", .string binding.1, strings binding.2,
    .string "rng:bls12-381.fr", .string (spelling value.result),
    .string (match value with | .draw => "Field" | .drawNonzero => "NonzeroField")]

def descriptors : List (Raw.Identity × Raw.Attribute) :=
  ([Domain.scalar, .group].map fun value => (value.identity, domain value)) ++
  ([Operation.fieldAdd, .fieldMul, .fromNonzero, .generator, .groupAdd, .scale, .equal].map
    fun value => (value.identity, operation value)) ++
  ([LogicalType.scalar, .nonzero, .group, .boolean].map fun value => (value.wireIdentity, wire value)) ++
  ([Service.draw, .drawNonzero].map fun value => (value.identity, service value))

def encoded : Except String ByteArray := Codec.encode (.array (descriptors.map fun (identity, descriptor) =>
  .array [strings [identity.name, identity.version, identity.digest], descriptor]))

end Tools.Mathematical.InstallationDescriptors
