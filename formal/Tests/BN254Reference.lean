import Tools.Interactive.GenericReference
import Tools.Artifact.Bindings
import Tests.Checks

/-! Executable nominal/codec/arithmetic controls. Curve bytes below are framing
fixtures only; no point-validity or pairing equation follows from admission. -/
set_option autoImplicit false

namespace Tests.BN254Reference
open Tests.Checks
open Tools.Interactive ScalarReference


private def get {α : Type} (value : Result α) : IO α :=
  match value with | .ok x => pure x | .error e => throw (IO.userError e)

private def same (a b : Result (List (Data (Scalar .bn254)))) : Bool :=
  match a, b with | .ok a, .ok b => a == b | .error a, .error b => a == b | _, _ => false

def arithmetic (checks : Checks) : IO Unit := do
  let run := compute .bn254
  checks.holds (same (run "field.add" [] [.field (-1), .field 2]) (.ok [.field 1])) "modular addition"
  checks.holds (same (run "field.mul" [] [.field (-2), .field (-3)]) (.ok [.field 6])) "modular product"
  let [.field inv] ← get (run "field.inverse" [] [.field 3]) | throw (IO.userError "inverse result")
  checks.holds (inv * 3 == 1) "modular inverse"
  checks.holds (!(run "field.inverse" [] [.field 0]).isOk) "zero inverse refused"
  checks.holds (!(decodeScalar .bn254 (.str (toString Bindings.bn254Modulus))).isOk) "canonical scalar"
  checks.holds (!(decodeScalar .bn254 (.str "01")).isOk) "canonical decimal"
  checks.holds (same (run "vector.dot" [] [.vector [1,2,3], .vector [4,5,6]]) (.ok [.field 32])) "dot product"
  checks.holds (!(run "vector.dot" [] [.vector [1,2], .vector [4]]).isOk) "exact vector length"
  checks.holds (same (run "vector.slice" [] [.vector [1,2,3], .index 1, .index 2]) (.ok [.vector [2,3]])) "ordered slice"
  checks.holds (same (run "vector.slice" [] [.vector [1,2,3], .index 3, .index 0]) (.ok [.vector []])) "empty suffix"
  checks.holds (!(run "vector.slice" [] [.vector [1,2,3], .index (2^64-1), .index 2]).isOk) "slice bounds without overflow"
  checks.holds (same (run "poly.from_coefficients" [] [.vector [2,3,0,0]]) (.ok [.polynomial [2,3]])) "normalization"
  checks.holds (same (run "poly.divide_opening" [] [.polynomial [2,3,4], .field 5, .field 117])
    (.ok [.polynomial [23,4]])) "opening quotient"
  checks.holds (!(run "poly.divide_opening" [] [.polynomial [2,3,4], .field 5, .field 116]).isOk) "false opening"
  let maximal : Scalar .bn254 := 19103219067921713944291392827692070036145651957329286315305642004821462161904
  checks.holds (powerValue (5 : Scalar .bn254) ((Bindings.bn254Modulus-1)/2^28) == maximal) "generator5 root"
  checks.holds (powerValue maximal (2^28) == 1 && powerValue maximal (2^27) == -1) "maximal root exact order"
  for n in [1,2,8,32,128] do
    let cs : List (Scalar .bn254) := (List.range (min n 7)).map fun i => (i+1 : Nat)
    let [.vector xs] ← get (run "poly.coset_evaluate" [] [.polynomial cs, .field 7, .index n])
      | throw (IO.userError "coset output")
    checks.holds (same (run "poly.coset_interpolate" [] [.vector xs, .field 7]) (.ok [.polynomial cs])) "coset roundtrip"
    let [.field root] ← get (run "poly.domain_root" [] [.index n]) | throw (IO.userError "root output")
    checks.holds (powerValue root n == 1) "domain order"
    if n > 1 then checks.holds (powerValue root (n/2) == -1) "primitive domain root"
  checks.holds (!(run "poly.coset_evaluate" [] [.polynomial [1], .field 1, .index 256]).isOk) "explicit direct transform bound"
  checks.holds (!(run "poly.domain_root" [] [.index 3]).isOk) "non-power domain"
  checks.holds (!(run "poly.domain_points" [] [.field 0, .index 4]).isOk) "zero coset shift"
  checks.holds (!(run "poly.opening_quotient" [] [.vector [1,2], .field 1, .field 1, .field 1]).isOk) "opening on domain"

def formation (checks : Checks) : IO Unit := do
  let pair ← get (Bindings.resolve true ⟨"pair", "pairing.check", [Bindings.bn254Fr], "arkworks/pairing.check"⟩)
  checks.holds (pair.inputs.map (·.spelling) == ["groups:bn254.g1@arkworks.bn254-g1-vector/1",
    "groups:bn254.g2@arkworks.bn254-g2-vector/1"] && pair.outputs.map (·.spelling) == ["bool@native.bool/1"]) "separate pairing operands"
  for field in [Bindings.fr, Bindings.ristrettoScalar, Bindings.bn254G1, Bindings.bn254G2] do
    checks.holds (!(Bindings.resolve false ⟨"pair", "pairing.check", [field], ""⟩).isOk) "pairing domain"
  for bad in ["group:bn254.fr", "field:bn254.g1", "groups:bn254.g2@arkworks.bn254-g1-vector/1",
      "field:bn254.fr@arkworks.fr/1", "nonce:bn254.fr", "table:bn254.fr"] do
    checks.holds (!(Bindings.valueType (bad.contains '@') bad).isOk) "nominal/representation swap"
  let f := Zkc.Source.Requirements.Term.root "F"
  let sig ← get (Generic.signature [("F", .field)] "pairing.check" [f])
  checks.holds (sig.inputs.map (·.domain) == [some (.project f "PairingG1"), some (.project f "PairingG2")]) "symbolic group distinction"
  checks.holds (!(Requirements.check [.relation "Field" [f]] sig.needs).isOk) "PairingField required"
  checks.holds ((Requirements.check [.relation "PairingField" [f]] sig.needs).isOk) "PairingField provided"
  checks.holds (!(Generic.prepareSource (.arr #[.str "zkc.relations/1", .arr #[], .arr #[]])).isOk) "relation envelope refused"

def matrixIdentity (checks : Checks) : IO Unit := do
  let matrix : Data (Scalar .bn254) := .matrix ⟨2,3,[⟨0,1,7⟩,⟨1,2,-1⟩]⟩
  let request ← get (MatrixIdentity.prime .bn254 matrix)
  let encoded := Lean.Json.arr #[.str "zkc.matrix/1", .str "bn254.fr", ScalarReference.json .bn254 matrix]
  checks.holds (request == .arr #[.str "zkc.hash/1", .str "sha256", .str (Tools.Artifact.hex encoded.compress.toUTF8)]) "canonical matrix hash payload"
  checks.holds (!(Bindings.attributes false "matrix.identity_check" [String.ofList (List.replicate 64 'A')]).isOk) "uppercase digest refused"
  checks.holds (!(Bindings.attributes false "matrix.identity_check" ["00"]).isOk) "digest length refused"
  let digest := String.ofList (List.replicate 64 '0')
  checks.holds (← get (MatrixIdentity.acceptsDigest [digest] (.str digest))) "exact digest comparison"
  checks.holds (!(← get (MatrixIdentity.acceptsDigest [digest] (.str (String.ofList (List.replicate 64 '1')))))) "different digest"
  checks.holds (!(MatrixIdentity.prime .bn254 (.matrix ⟨1,1,[⟨0,0,0⟩]⟩)).isOk) "noncanonical matrix refused"

def codecs (checks : Checks) : IO Unit := do
  let values : List (Data (Scalar .bn254)) := [.field (-1), .vector [1,2,-3],
    .polynomial [1,2,3], .round ⟨1,2,3⟩, .matrix ⟨2,3,[⟨0,1,7⟩,⟨1,2,-1⟩]⟩]
  for value in values do
    let bytes ← get (Tools.Artifact.arithmeticWire .bn254 value)
    let decoded ← get (Tools.Artifact.decodeArithmeticWire .bn254 value.kind bytes)
    checks.holds (decoded == value) "arithmetic codec roundtrip"
    checks.holds (!(Tools.Artifact.decodeArithmeticWire .bls value.kind bytes).isOk) "cross field tag"
    for n in [:bytes.size] do
      checks.holds (!(Tools.Artifact.decodeArithmeticWire .bn254 value.kind (bytes.extract 0 n)).isOk) "truncation"
  for (identity, width) in [(Bindings.bn254G1,32), (Bindings.bn254G2,64)] do
    let bytes := Tools.Artifact.magic.push (← get (Tools.Artifact.bn254GroupTag identity "group")) ++
      ByteArray.mk (Array.replicate width 0)
    let value ← get (Reference.decodeValue (.arr #[.str ("group:"++identity), .str (Tools.Artifact.hex bytes)]))
    checks.holds (value.ty.identity == identity) "group nominal framing"
    let other := if identity == Bindings.bn254G1 then Bindings.bn254G2 else Bindings.bn254G1
    checks.holds (!(Tools.Artifact.checkBn254Wire other "group" bytes).isOk) "group tag swap"
    checks.holds (!(Tools.Artifact.checkBn254Wire identity "groups" bytes).isOk) "group/vector tag swap"
    checks.holds (!(Tools.Artifact.checkBn254Wire identity "group" (bytes.push 0)).isOk) "group trailing bytes"

def run : IO Unit := do
  let checks ← start
  Tests.BN254Reference.arithmetic checks
  Tests.BN254Reference.formation checks
  Tests.BN254Reference.codecs checks
  Tests.BN254Reference.matrixIdentity checks
  checks.finish "BN254 independent arithmetic, formation, framing and matrix-identity controls (cosets <= 128; no curve-validity claim)"

#eval run

end Tests.BN254Reference
