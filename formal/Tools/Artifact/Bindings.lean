import Tools.Artifact.Codec
import Tools.Interactive.GenericModule

/-! Nominal admission for the finite artifact interpreter. Original generic
source is prepared independently of native construction. Arithmetic carriers
retain their actual nominal field; group wires retain their domain and exact
framing. Physical layouts never determine the mathematical source identity. -/

set_option autoImplicit false

namespace Tools.Artifact
open Lean (Json)
open Tools.Interactive

def prepareExplicitSource (json : Json) : Result Generic.Prepared := do
  let prepared ← Generic.prepareSource json
  for definition in prepared.library.definitions do
    ensure (definition.definition.arguments.all (fun a => a.2.kind != "transcript") &&
      definition.definition.results.all (fun t => t.kind != "transcript")) "artifact-source-transcript"
  return prepared

def artifactSource (json : Json) : Result Source := do
  return (← prepareExplicitSource json).source

def artifactOrigins (json : Json) : Result (List Algorithms.Origin) := do
  return (← prepareExplicitSource json).algorithmOrigins

def nominalKind (kind : String) : Result Ty := do
  let identities := ["", "bls12-381.fr", "bls12-381.g1",
    "multilinear.kzg.bls12-381/1", "merlin3.bls12-381.fr64be/1"]
  let [identity] := identities.filter (Bindings.logicalIdentity kind)
    | throw "artifact-nominal-value"
  return (Bindings.ValueType.mk kind identity "").spelling

def Value.fromArithmetic : (d : ScalarReference.Domain) → ScalarReference.Data (ScalarReference.Scalar d) → Value
  | .bls, .field x => .field x
  | .bls, .round r => .round r
  | _, .boolean b => .boolean b
  | d, value => .arithmetic d value

def Value.toArithmetic : (d : ScalarReference.Domain) → Value → Result (ScalarReference.Data (ScalarReference.Scalar d))
  | .bls, .field x => .ok (.field x)
  | .bls, .round r => .ok (.round r)
  | _, .boolean b => .ok (.boolean b)
  | _, .arithmetic _ (.index n) | _, .extension (.index n) => .ok (.index n)
  | _, .arithmetic _ (.indices ns) | _, .extension (.indices ns) => .ok (.indices ns)
  | d, .arithmetic d' value =>
      if h : d' = d then .ok (h ▸ value) else .error "artifact-nominal-value"
  | _, _ => .error "artifact-nominal-value"

def Value.fromExtension : ExtensionReference.Data → Value
  | .boolean b => .boolean b
  | value => .extension value

def Value.toExtension : Value → Result ExtensionReference.Data
  | .arithmetic _ (.index n) => .ok (.index n)
  | .arithmetic _ (.indices ns) => .ok (.indices ns)
  | .extension value => .ok value
  | _ => .error "artifact-nominal-value"

def Value.typeFor (value : Value) : Result Ty := do
  match value with
  | .oracle v =>
      return (Bindings.ValueType.mk v.kind v.domain.identity "").spelling
  | .extension value =>
      return (Bindings.ValueType.mk value.kind (if Bindings.domainIndependent value.kind then "" else Bindings.koalaBearExt8) "").spelling
  | .arithmetic d value =>
      return (Bindings.ValueType.mk value.kind (if Bindings.domainIndependent value.kind then "" else d.identity) "").spelling
  | .nominalBytes identity kind _ =>
      ensure (Bindings.logicalIdentity kind identity) "artifact-nominal-value"
      return (Bindings.ValueType.mk kind identity "").spelling
  | .extensionRng _ =>
      return "rng:" ++ Bindings.koalaBearExt8
  | .ristrettoRng _ =>
      return "rng:ristretto255.scalar"
  | _ => nominalKind value.ty

def Value.jsonFor (value : Value) : Result Json := do
  let [.str _, encoded] ← Decode.array (← value.json) | throw "artifact-value-json"
  return .arr #[.str (← value.typeFor), encoded]

def decodeValue (ty : Ty) (bytes : ByteArray) : Result Value := do
  let nominal ← Bindings.valueType false ty
  let kind := nominal.kind
  if Bindings.rowDomain nominal.identity then
    return .oracle (← OracleReference.decode (← OracleReference.Domain.parse nominal.identity) kind bytes)
  if kind == "index" || kind == "indices" then
    return Value.fromArithmetic .bls (← decodeArithmeticWire .bls kind bytes)
  if nominal.identity == Bindings.koalaBearExt8 then
    return Value.fromExtension (← decodeExtensionWire kind bytes)
  if ["field", "matrix", "round", "vector", "polynomial"].contains kind then
    let d ← ScalarReference.Domain.parse nominal.identity
    return Value.fromArithmetic d (← decodeArithmeticWire d kind bytes)
  if nominal.identity == Bindings.bn254G1 || nominal.identity == Bindings.bn254G2 then
    checkBn254Wire nominal.identity kind bytes
    return .nominalBytes nominal.identity kind bytes
  if nominal.identity == Bindings.ristrettoGroup then
    checkRistrettoWire kind bytes
    return .nominalBytes nominal.identity kind bytes
  let value ← if kind == "verifier_key" then do
      ensure (bytes.size ≥ 81 && bytes.extract 0 8 == "ZKCAR006".toUTF8 && bytes[8]! == 1) "verifier-key-header"
      let n := valueLE (bytes.extract 9 17)
      ensure (0 < n && n ≤ limits.rank && bytes.size == 81 + 144 + 48*n) "verifier-key-shape"
      pure (.verifierKey bytes)
    else decodeWire kind bytes
  ensure ((← value.typeFor) == ty) "artifact-nominal-value"
  return value

structure SelectedOperation where
  contract : String
  arguments : List String
  signature : KernelSignature

def selectOperation (source : Source) (name : String) (attributes : List String) : Result SelectedOperation := do
  let signature ← environmentSignature source.environment "logical" name attributes
  match source.environment with
  | .explicit bindings =>
      let binding ← lookup name (bindings.map fun b => (b.name, b))
      return ⟨binding.contract, binding.arguments, signature⟩

end Tools.Artifact
