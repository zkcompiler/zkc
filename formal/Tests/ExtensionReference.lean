import Tools.Interactive.ReferenceRuntime
import Tools.Artifact.Bindings
import Tests.Checks

set_option autoImplicit false

namespace Tests.ExtensionReference
open Tools.Interactive
open ExtensionReference
open Lean (Json)
open Tests.Checks

private def basis (n : Nat) : Scalar := ⟨Vector.ofFn fun i => if i.val == n then 1 else 0⟩
#eval do
  let checks ← start
  let x := basis 1
  let x7 := basis 7
  checks.holds (x * x7 == embed 3) "X^8 = 3"
  checks.holds (power x 8 == embed 3) "extension power"
  checks.holds (embed 7 * embed 9 == embed 63) "base multiplicative embedding"
  checks.holds (embed 7 + embed 9 == embed 16) "base additive embedding"
  checks.holds ((inverse 0).isOk == false) "zero inverse refuses"
  for a in [x, x7, x + embed 5, ⟨Vector.ofFn fun i => (i.val + 1 : Base)⟩] do
    let .ok b := inverse a | throw (IO.userError "nonzero inverse")
    checks.holds (a * b == 1) "inverse product"
  for value in [ScalarReference.Data.field x,
      .vector [x, x7], .polynomial [x, x7], .round ⟨x, x7, embed 5⟩,
      .matrix ⟨2, 2, [⟨0, 1, x⟩, ⟨1, 0, x7⟩]⟩] do
    let .ok bytes := Tools.Artifact.extensionWire value | throw (IO.userError "encode extension")
    let .ok decodedValue := Tools.Artifact.decodeExtensionWire value.kind bytes | throw (IO.userError "decode extension")
    checks.holds (json decodedValue == json value) "extension wire roundtrip"
    checks.holds ((Tools.Artifact.decodeExtensionWire value.kind (bytes.push 0)).isOk == false) "trailing bytes refuse"
    checks.holds ((Tools.Artifact.decodeExtensionWire value.kind (bytes.extract 0 (bytes.size-1))).isOk == false) "truncation refuses"
    for domain in [ScalarReference.Domain.bls, .ristretto, .koalaBear] do
      checks.holds ((Tools.Artifact.decodeArithmeticWire domain value.kind bytes).isOk == false) "wrong domain refuses"
    let .ok decoded := Tools.Artifact.decodeValue (value.kind ++ ":" ++ Bindings.koalaBearExt8) bytes
      | throw (IO.userError "nominal artifact decode")
    let .ok decodedValue := decoded.toExtension | throw (IO.userError "extension artifact carrier")
    checks.holds (json decodedValue == json value) "artifact extension routing"
  let .ok bytes := Tools.Artifact.extensionWire (.field x) | throw (IO.userError "field wire")
  for i in [:8] do
    let bad := bytes.extract 0 (6+4*i) ++ Tools.Artifact.little 4 Bindings.koalaBearModulus ++ bytes.extract (10+4*i) bytes.size
    checks.holds ((Tools.Artifact.decodeExtensionWire "field" bad).isOk == false) "noncanonical coordinate refuses"
  for count in [0, 1, 7, 9] do
    checks.holds ((scalar (.arr (Array.replicate count (.str "0")))).isOk == false) "fixed coordinate count"
  checks.holds ((scalar (.str "7")).isOk == false) "no decimal whole-extension literal"
  let malformed := Json.arr #[.str "0", .str "0", .str "0", .str "0", .str "0", .str "0", .str "0", .str "2130706433"]
  checks.holds ((scalar malformed).isOk == false) "canonical coordinates"
  checks.holds ((compute "field.constant" ["2130706433"] []).isOk == false) "closed constant bound"
  checks.holds ((compute "vector.add" [] [.vector [x], .vector []]).isOk == false) "shape mismatch"
  checks.holds ((Bindings.resolve true ⟨"embed", "field.embed", [Bindings.koalaBear], "plonky3/field.embed"⟩).isOk == false) "base has no embedding capability"
  checks.holds ((ScalarReference.Domain.parse Bindings.koalaBearExt8).isOk == false) "prime interpreter cannot admit extension"
  checks.finish "extension coordinate and reference codec controls"

end Tests.ExtensionReference
