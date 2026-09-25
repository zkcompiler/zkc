import Tools.Interactive.Bindings
import Tools.Interactive.OracleReference
import Tools.Artifact.Codec
import Tools.Interactive.CommitmentCodec
import Zkc.Source.ResultBundle

/-! Logical values for explicit-binding reference execution. Mathematical field
and polynomial values are independent of physical layout. Group values retain
canonical-wire structure; subgroup validity and group equations require an
explicit external primitive service. No additive-group test model is used here.
-/

set_option autoImplicit false

namespace Tools.Interactive.Reference
open Lean (Json)
open Zkc.Source

/-- Private immutable custody constructed only after a successful commit. -/
structure OpeningState where
  identity : CommitmentIdentity
  original : Math.Table
  commitment : ByteArray

inductive Value where
  | variant (descriptor : Variant.Descriptor) (alternative : Name) (payload : List Value)
  | resourceUnit (domain identity : String) (generation : Nat)
  | oracle (value : OracleReference.Data)
  | extension (value : ExtensionReference.Data)
  | arithmetic (domain : ScalarReference.Domain) (value : ScalarReference.Data (ScalarReference.Scalar domain))
  | bnGroup (g2 : Bool) (many : Bool) (wire : ByteArray)
  | brng (identity : Name) (generation : Nat)
  | rgroup (wire : ByteArray)
  | rgroups (wire : ByteArray)
  | erng (identity : Name) (generation : Nat)
  | rrng (identity : Name) (generation : Nat)
  | rnonce (identity : Name) (generation : Nat)
  | field (value : Math.Fr)
  | table (value : Math.Table)
  | point (coordinates : List Math.Fr)
  | round (value : Math.Round Math.Fr)
  | boolean (value : Bool)
  | group (wire : ByteArray)
  | groups (wire : ByteArray)
  | commitment (wire : ByteArray)
  | proof (wire : ByteArray)
  | proverKey (identity : CommitmentIdentity)
  | verifierKey (identity : CommitmentIdentity)
  | opening (state : OpeningState)
  | rng (identity : Name) (generation : Nat)
  | nonce (identity : Name) (generation : Nat)
  | transcript (suite : String) (identity : Name) (generation : Nat)

def Value.ty : Value → Bindings.ValueType
  | .variant descriptor .. => ⟨"variant", descriptor.identity, ""⟩
  | .resourceUnit domain .. => ⟨"resource_unit", domain, ""⟩
  | .oracle v => ⟨v.kind, v.domain.identity, ""⟩
  | .extension value => ⟨value.kind, if Bindings.domainIndependent value.kind then "" else Bindings.koalaBearExt8, ""⟩
  | .arithmetic d value => ⟨value.kind, if Bindings.domainIndependent value.kind then "" else d.identity, ""⟩
  | .bnGroup g2 many _ => ⟨if many then "groups" else "group", if g2 then Bindings.bn254G2 else Bindings.bn254G1, ""⟩
  | .brng .. => ⟨"rng", Bindings.bn254Fr, ""⟩
  | .rgroup _ => ⟨"group", Bindings.ristrettoGroup, ""⟩
  | .rgroups _ => ⟨"groups", Bindings.ristrettoGroup, ""⟩
  | .erng .. => ⟨"rng", Bindings.koalaBearExt8, ""⟩
  | .rrng .. => ⟨"rng", Bindings.ristrettoScalar, ""⟩
  | .rnonce .. => ⟨"nonce", Bindings.ristrettoScalar, ""⟩
  | .field _ => ⟨"field", "bls12-381.fr", ""⟩
  | .table _ => ⟨"table", "bls12-381.fr", ""⟩
  | .point _ => ⟨"point", "bls12-381.fr", ""⟩
  | .round _ => ⟨"round", "bls12-381.fr", ""⟩
  | .boolean _ => ⟨"bool", "", ""⟩
  | .group _ => ⟨"group", "bls12-381.g1", ""⟩
  | .groups _ => ⟨"groups", "bls12-381.g1", ""⟩
  | .commitment _ => ⟨"commitment", "multilinear.kzg.bls12-381/1", ""⟩
  | .proof _ => ⟨"proof", "multilinear.kzg.bls12-381/1", ""⟩
  | .proverKey _ => ⟨"prover_key", "multilinear.kzg.bls12-381/1", ""⟩
  | .verifierKey _ => ⟨"verifier_key", "multilinear.kzg.bls12-381/1", ""⟩
  | .opening _ => ⟨"opening_state", "multilinear.kzg.bls12-381/1", ""⟩
  | .rng .. => ⟨"rng", "bls12-381.fr", ""⟩
  | .nonce .. => ⟨"nonce", "bls12-381.fr", ""⟩
  | .transcript suite .. => ⟨"transcript", suite, ""⟩

def Value.public : Value → Bool
  | .variant .. => false
  | .resourceUnit .. => false
  | .oracle v => v.public
  | .brng .. | .erng .. | .rrng .. | .rnonce .. | .rng .. | .nonce .. | .transcript .. | .proverKey _ | .verifierKey _ | .opening _ => false
  | _ => true

def Value.size : Value → Nat
  | .variant descriptor alternative payload => descriptor.spelling.utf8ByteSize + alternative.utf8ByteSize + (payload.map Value.size).sum
  | .resourceUnit .. => 0
  | .oracle v => v.size
  | .extension value => 8 * value.size
  | .arithmetic _ value => value.size
  | .bnGroup _ _ b | .rgroup b | .rgroups b => b.size
  | .table t => 1 + t.cells.length
  | .point p => 1 + p.length
  | .round _ => 4
  | .group b | .groups b | .commitment b | .proof b => b.size
  | .opening s => 1 + s.original.cells.length + s.commitment.size
  | .proverKey _ | .verifierKey _ => 65
  | _ => 1

private def natural (n : Nat) : Json := .str (toString n)
private def scalarJson (f : Math.Fr) : Json := natural f.val
private def fields (fs : List Math.Fr) : Json := .arr (fs.map scalarJson).toArray

def Value.json (value : Value) : Json :=
  let payload := match value with
    | .variant _ alternative payload => .arr #[.str alternative, .arr (payload.map Value.json).toArray]
    | .resourceUnit _ identity generation => .arr #[.str identity, natural generation]
    | .oracle v => match v.wire with
      | .ok wire => .str (Tools.Artifact.hex wire)
      | .error _ => .str "private"
    | .extension value => ExtensionReference.json value
    | .arithmetic d value => ScalarReference.json d value
    | .bnGroup _ _ b | .rgroup b | .rgroups b => .str (Tools.Artifact.hex b)
    | .field f => scalarJson f
    | .table t => .arr #[natural t.rank, fields t.cells]
    | .point p => fields p
    | .round r => .arr #[scalarJson r.constant, scalarJson r.linear, scalarJson r.quadratic]
    | .boolean b => .str (if b then "true" else "false")
    | .group bytes | .groups bytes | .commitment bytes | .proof bytes => .str (Tools.Artifact.hex bytes)
    | .proverKey identity | .verifierKey identity => identity.json
    | .opening state => .arr #[state.identity.json,
        .arr #[natural state.original.rank, fields state.original.cells],
        .str (Tools.Artifact.hex state.commitment)]
    | .brng identity generation | .erng identity generation | .rrng identity generation | .rnonce identity generation
    | .rng identity generation | .nonce identity generation | .transcript _ identity generation =>
        .arr #[.str identity, natural generation]
  .arr #[.str value.ty.spelling, payload]

/-- Boundary validation recurses only through the selected payload. -/
def Value.validateAt : Nat → Value → Result Unit
  | 0, _ => throw "variant-depth"
  | depth + 1, .variant descriptor alternative payload => do
      let _ ← Bindings.valueType false descriptor.spelling
      let expected ← lookup alternative descriptor.alternatives
      ensure (payload.map (fun v => v.ty.spelling) == expected) "variant-payload-types"
      payload.forM (Value.validateAt depth)
  | _, _ => pure ()

def Value.validate (value : Value) : Result Unit := value.validateAt 9

def Value.pack (ty alternative : String) (payload : List Value) : Result Value := do
  let parsed ← Bindings.valueType false ty
  ensure (parsed.kind == "variant") "variant-type"
  let descriptor ← Variant.parse ty
  let value := Value.variant descriptor alternative payload
  value.validate
  return value

/-- No inactive handle exists in the reference carrier. -/
def Value.leaves : Value → List Value
  | .variant _ _ payload => payload.flatMap Value.leaves
  | value => [value]

@[simp] theorem variant_leaves (descriptor : Variant.Descriptor) (alternative : Name) (payload : List Value) :
    (Value.variant descriptor alternative payload).leaves = payload.flatMap Value.leaves := by simp [Value.leaves]

@[simp] theorem variant_private (descriptor : Variant.Descriptor) (alternative : Name) (payload : List Value) :
    (Value.variant descriptor alternative payload).public = false := rfl

def valuesJson (values : List Value) : Json := .arr (values.map Value.json).toArray

def decodeScalar (j : Json) : Result Math.Fr := do
  let n ← Decode.natural j
  ensure (n < fieldModulus) "noncanonical-field"
  return (n : Math.Fr)

def decodeScalars (j : Json) : Result (List Math.Fr) := do
  (← Decode.array j (2 ^ limits.rank)).mapM decodeScalar

/-- Preserve the existing BLS constructors; all new arithmetic still uses the
same parameterized carrier and computation. -/
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
      if h : d' = d then .ok (h ▸ value) else .error "reference-value-type"
  | _, _ => .error "reference-value-type"

def Value.fromExtension : ExtensionReference.Data → Value
  | .boolean b => .boolean b
  | value => .extension value

def Value.toExtension : Value → Result ExtensionReference.Data
  | .arithmetic _ (.index n) => .ok (.index n)
  | .arithmetic _ (.indices ns) => .ok (.indices ns)
  | .extension value => .ok value
  | _ => .error "reference-value-type"

def decodeValue (json : Json) : Result Value := do
  let [.str spelling, payload] ← Decode.array json | throw "reference-value"
  let ty ← Bindings.valueType false spelling
  if Bindings.rowDomain ty.identity then
    return .oracle (← OracleReference.decode (← OracleReference.Domain.parse ty.identity) ty.kind
      (← Tools.Artifact.unhex (← Decode.string payload)))
  if ty.kind == "index" || ty.kind == "indices" then
    return Value.fromArithmetic .bls (← ScalarReference.decode .bls ty.kind payload)
  if ty.identity == Bindings.koalaBearExt8 && ty.kind != "rng" then
    return Value.fromExtension (← ExtensionReference.decode ty.kind payload)
  if ["field", "matrix", "vector", "polynomial", "round"].contains ty.kind then
    let domain ← ScalarReference.Domain.parse ty.identity
    return Value.fromArithmetic domain (← ScalarReference.decode domain ty.kind payload)
  if ty.identity == Bindings.bn254G1 || ty.identity == Bindings.bn254G2 then
    let bytes ← Tools.Artifact.unhex (← Decode.string payload)
    Tools.Artifact.checkBn254Wire ty.identity ty.kind bytes
    return .bnGroup (ty.identity == Bindings.bn254G2) (ty.kind == "groups") bytes
  if ty.identity == Bindings.ristrettoGroup then
    let bytes ← Tools.Artifact.unhex (← Decode.string payload)
    Tools.Artifact.checkRistrettoWire ty.kind bytes
    return if ty.kind == "group" then .rgroup bytes else .rgroups bytes
  let value ← match ty.kind with
    | "field" => return Value.field (← decodeScalar payload)
    | "table" => do
        let [rank, cells] ← Decode.array payload | throw "reference-table"
        return .table (← Math.Table.admit (← Decode.natural rank) (← decodeScalars cells))
    | "point" => do
        let p ← decodeScalars payload
        ensure (p.length ≤ limits.rank) "point-limit"
        return .point p
    | "round" => do
        let [a, b, c] ← decodeScalars payload | throw "reference-round"
        return .round ⟨a, b, c⟩
    | "bool" => do
        let .str text := payload | throw "reference-bool"
        ensure (text == "true" || text == "false") "reference-bool"
        return .boolean (text == "true")
    | "group" | "groups" => do
        let bytes ← Tools.Artifact.unhex (← Decode.string payload)
        let _ ← Tools.Artifact.decodeWire ty.kind bytes
        return if ty.kind == "group" then .group bytes else .groups bytes
    | "commitment" | "proof" => do
        let bytes ← Tools.Artifact.unhex (← Decode.string payload)
        let _ ← CommitmentIdentity.fromWire ty.kind bytes
        return if ty.kind == "commitment" then .commitment bytes else .proof bytes
    | "prover_key" => return .proverKey (← CommitmentIdentity.decode payload)
    | "verifier_key" => return .verifierKey (← CommitmentIdentity.decode payload)
    | "rng" | "nonce" | "transcript" => do
        let [identity, generation] ← Decode.array payload | throw "reference-rng"
        let identity ← Decode.name identity
        let generation ← Decode.natural generation
        return if ty.kind == "transcript" then .transcript ty.identity identity generation
        else if ty.identity == Bindings.bn254Fr then .brng identity generation
        else if ty.identity == Bindings.koalaBearExt8 && ty.kind == "rng" then .erng identity generation
        else if ty.identity == Bindings.ristrettoScalar then
          if ty.kind == "rng" then .rrng identity generation else .rnonce identity generation
        else if ty.kind == "rng" then .rng identity generation else .nonce identity generation
    | _ => throw "reference-value-not-supported"
  ensure (value.ty == ty) "reference-value-type"
  return value

/-- Issued-resource data for admission; public values have no handle. -/
def Value.capability : Value → Option (String × Name × Nat)
  | .resourceUnit _ identity generation => some ("resource_unit", identity, generation)
  | .brng identity generation => some ("rng", identity, generation)
  | .erng identity generation => some ("rng", identity, generation)
  | .rrng identity generation => some ("rng", identity, generation)
  | .rnonce identity generation => some ("nonce", identity, generation)
  | .rng identity generation => some ("rng", identity, generation)
  | .nonce identity generation => some ("nonce", identity, generation)
  | .transcript _ identity generation => some ("transcript", identity, generation)
  | _ => none

def Value.commitmentIdentity : Value → Result (Option CommitmentIdentity)
  | .commitment bytes => return some (← CommitmentIdentity.fromWire "commitment" bytes)
  | .proof bytes => return some (← CommitmentIdentity.fromWire "proof" bytes)
  | .proverKey identity | .verifierKey identity => return some identity
  | .opening state => return some state.identity
  | _ => return none

/-- Canonical logical wire, independently encoded from mathematical values. -/
def Value.wire (value : Value) : Result ByteArray :=
  match value with
  | .oracle v => v.wire
  | .extension value => Tools.Artifact.extensionWire value
  | .arithmetic d value => Tools.Artifact.arithmeticWire d value
  | .bnGroup g2 many bytes => do
      Tools.Artifact.checkBn254Wire (if g2 then Bindings.bn254G2 else Bindings.bn254G1)
        (if many then "groups" else "group") bytes
      return bytes
  | .rgroup bytes => do Tools.Artifact.checkRistrettoWire "group" bytes; return bytes
  | .rgroups bytes => do Tools.Artifact.checkRistrettoWire "groups" bytes; return bytes
  | .field f => (Tools.Artifact.Value.field f).wire
  | .table t => (Tools.Artifact.Value.table t).wire
  | .point p => (Tools.Artifact.Value.point p).wire
  | .round r => (Tools.Artifact.Value.round r).wire
  | .boolean b => (Tools.Artifact.Value.boolean b).wire
  | .group bytes | .groups bytes | .commitment bytes | .proof bytes => .ok bytes
  | _ => .error "nonserializable-message"

abbrev TypedValue (ty : Bindings.ValueType) := {value : Value // value.ty = ty}

def typedValues : (types : List Bindings.ValueType) → List Value →
    Result (Values TypedValue types)
  | [], [] => .ok .nil
  | ty :: types, value :: rest => do
      value.validate
      if same : value.ty = ty then return .cons ⟨value, same⟩ (← typedValues types rest)
      else throw "reference-value-type"
  | _, _ => .error "reference-value-arity"

def untypedValues {types : List Bindings.ValueType} : Values TypedValue types → List Value
  | .nil => []
  | .cons value rest => value.val :: untypedValues rest

end Tools.Interactive.Reference
