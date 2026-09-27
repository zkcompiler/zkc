import Tools.Interactive.Decode

/-! The finite installed full-type vocabulary for the explicit-binding portable
consumer. This is independent of native selection and backend advertisement.
The old profile transport does not determine these operation signatures. -/

set_option autoImplicit false

namespace Tools.Interactive.Bindings

structure ValueType where
  ofParts ::
  kind : String
  identity : String
  representation : String
  arguments : List Logical.Argument
  deriving BEq, Repr, DecidableEq

/-- Compatibility constructor for existing atomic logical types. -/
def ValueType.mk (kind identity : String) (representation : String := "") : ValueType :=
  ⟨kind, identity, representation, []⟩

def ValueType.ofLogical (logical : Logical.GroundType) (representation : String := "") : ValueType :=
  match logical with
  | .atom kind identity => .mk kind identity representation
  | .application head args => ⟨head, "", representation, args⟩

def ValueType.logical (ty : ValueType) : Logical.GroundType :=
  if ty.arguments.isEmpty then .atom ty.kind ty.identity
  else .application ty.kind ty.arguments

def ValueType.spelling (ty : ValueType) : String :=
  let base := ty.logical.spelling
  if ty.representation.isEmpty then base else base ++ "@" ++ ty.representation

/-- Characteristic bound for canonical natural embeddings, not extension cardinality. -/
def scalarModulus (identity : String) : Result Nat :=
  if identity == fr then .ok fieldModulus
  else if identity == bn254Fr then .ok bn254Modulus
  else if identity == ristrettoScalar then .ok ristrettoModulus
  else if identity == koalaBear || identity == koalaBearExt8 then .ok koalaBearModulus
  else .error "binding-field-domain"

def numericalContract (contract : String) : Bool :=
  ["poly.coset_evaluate", "poly.coset_interpolate", "poly.domain_point", "poly.domain_root",
   "poly.domain_points", "poly.even_odd_fold", "poly.opening_quotient"].contains contract

/-- Contracts that take part in the protocol transcript history: they absorb into
it, or they draw from it. A match arm is entered on a private tag, so the history
and every later challenge would become a function of that tag. The internal
`transcript.` family and the external duplex states are decided here together,
because an external state is ordinary checked data and carries no attribute that
would mark it. Construction and stateless hashing touch no history:
docs/spec/profiles/compiler/local-variants.md,
docs/spec/realization/external-constructions.md. -/
def historyContract (contract : String) : Bool :=
  contract.startsWith "transcript." ||
    ["external.monero.update", "external.openvm.observe", "external.openvm.sample",
     "external.openvm.sample_ext", "external.openvm.sample_bits",
     "external.openvm.check_witness"].contains contract

/-- Common structural admission, independent of representation selection. -/
def validLogical (depth : Nat) (text : String) : Bool :=
  (Logical.parseWithDepth depth text).isOk

def logicalIdentity (kind identity : String) : Bool :=
  if kind == "variant" then (Logical.parse ("variant:" ++ identity)).isOk
  else leafLogicalIdentity kind identity

/-- Unknown nominal types have no default. Kind alone never selects a backend. -/
def defaultRepresentation (kind identity : String) : String :=
  if !logicalIdentity kind identity then ""
  else if kind == "variant" then "logical.variant/1"
  else if kind == "resource_unit" then "logical.resource_unit/1"
  else if domainIndependent kind then "native." ++ kind ++ "/1"
  else if ["rng", "nonce", "transcript"].contains kind then "host.resource/1"
  else if rowDomain identity then
    "plonky3.merkle-" ++ (match kind with
      | "commitment" => "root" | "proof" => "path" | "opening_state" => "state"
      | "commitments" => "roots" | _ => "states") ++ "/1"
  else if identity == koalaBearExt8 then
    match kind with
    | "field" => "plonky3.koala-bear.ext8-binomial3/1"
    | "matrix" => "plonky3.koala-bear.ext8-binomial3-sparse-coo/1"
    | "vector" => "plonky3.koala-bear.ext8-binomial3-vector/1"
    | "polynomial" => "plonky3.koala-bear.ext8-binomial3-polynomial/1"
    | "round" => "plonky3.koala-bear.ext8-binomial3-quadratic/1"
    | _ => ""
  else if identity == koalaBear then
    match kind with
    | "field" => "plonky3.koala-bear/1"
    | "matrix" => "plonky3.koala-bear-sparse-coo/1"
    | "vector" => "plonky3.koala-bear-vector/1"
    | "polynomial" => "plonky3.koala-bear-polynomial/1"
    | "round" => "plonky3.koala-bear-quadratic/1"
    | _ => ""
  else if identity == bn254Fr then
    match kind with
    | "field" => "arkworks.bn254-fr/1"
    | "matrix" => "arkworks.bn254-fr-sparse-coo/1"
    | "vector" => "arkworks.bn254-fr-vector/1"
    | "polynomial" => "arkworks.bn254-fr-polynomial/1"
    | "round" => "arkworks.bn254-fr-round/1"
    | _ => ""
  else if identity == bn254G1 || identity == bn254G2 then
    "arkworks.bn254-" ++ (if identity == bn254G1 then "g1" else "g2") ++
      (if kind == "groups" then "-vector/1" else "/1")
  else if identity == ristrettoScalar then
    match kind with
    | "field" => "dalek.scalar/1"
    | "matrix" => "dalek.scalar-sparse-coo/1"
    | "vector" => "dalek.scalar-vector/1"
    | "polynomial" => "dalek.polynomial/1"
    | "round" => "dalek.quadratic/1"
    | _ => ""
  else if identity == ristrettoGroup then
    if kind == "group" then "dalek.ristretto/1" else "dalek.ristretto-vector/1"
  else match kind with
    | "field" => "arkworks.fr/1"
    | "matrix" => "arkworks.fr-sparse-coo/1"
    | "vector" => "arkworks.fr-vector/1"
    | "polynomial" => "arkworks.polynomial/1"
    | "table" => "arkworks.mle-lsb/1"
    | "point" => "arkworks.point/1"
    | "round" => "arkworks.quadratic/1"
    | "group" => "arkworks.g1/1"
    | "groups" => "arkworks.g1-vector/1"
    | _ => "arkworks.multilinear-pcs/1"

/-- Complete-type selection: no realization for arbitrary element types. -/
def ValueType.defaultRepresentation (ty : ValueType) : String :=
  if ty.arguments.isEmpty then Bindings.defaultRepresentation ty.kind ty.identity
  else if ty.kind == "fixed_vector" && ty.identity.isEmpty then
    match ty.arguments with
    | [.type (.atom "field" field), .natural n] =>
        if field == koalaBear && n ≤ Logical.naturalLimit then "plonky3.fixed-vector/1" else ""
    | _ => ""
  else ""

def ValueType.valid (physical : Bool) (ty : ValueType) : Bool :=
  (ty.arguments.isEmpty || ty.identity.isEmpty) &&
      (Logical.parse ty.logical.spelling).toOption == some ty.logical &&
      if physical then
        !ty.representation.isEmpty &&
          (ty.representation == ty.defaultRepresentation ||
          (ty.kind == "table" && ty.identity == fr && ty.representation == "arkworks.mle-msb/1") ||
          (ty.kind == "vector" && ty.identity == fr && ty.representation == "arkworks.fr-diagonal/1") ||
          (ty.kind == "groups" && ty.identity == ristrettoGroup && ty.representation == "dalek.ristretto-diagonal/1"))
      else ty.representation.isEmpty

def valueType (physical : Bool) (text : String) : Result ValueType := do
  ensure (text.utf8ByteSize ≤ if text.startsWith "variant:" then 256 * 1024 + (if physical then 18 else 0)
    else Logical.byteLimit + (if physical then 128 else 0)) "binding-type-limit"
  let (logical, representation) ← match text.splitOn "@" with
    | [logical] => pure (logical, "")
    | [logical, representation] => pure (logical, representation)
    | _ => throw "binding-type"
  let result := ValueType.ofLogical (← Logical.parse logical) representation
  ensure (result.valid physical && result.spelling == text) (if physical then "binding-representation" else "binding-type")
  return result

/-- Active leaves use checked default representations at physical stages. -/
def variantPayload (ty : Ty) (alternative : Name) : Result (List Ty) := do
  let parsed ← valueType (ty.contains '@') ty
  ensure (parsed.kind == "variant") "variant-type"
  let descriptor ← Variant.parse ("variant:" ++ parsed.identity)
  let leaves ← lookup alternative descriptor.alternatives
  leaves.mapM fun leaf => do
    let value ← valueType false leaf
    return if parsed.representation.isEmpty then leaf
      else {value with representation := value.defaultRepresentation}.spelling

def codec (kind identity : String) : String :=
  if !Logical.publicKind kind || !leafLogicalIdentity kind identity then ""
  else
  if domainIndependent kind then "zkcv." ++ kind ++ "/1"
  else if rowDomain identity then
    "zkcv." ++ kind ++ ".rows-merkle-keccak256." ++
      (if identity == rowBase then koalaBear else koalaBearExt8) ++ "/1"
  else if ["commitment", "proof"].contains kind then "zkcv." ++ kind ++ ".multilinear-kzg.bls12-381/1"
  else "zkcv." ++ kind ++ "." ++ identity ++ "/1"

def serializableKinds : List String :=
  ["index", "indices", "field", "matrix", "vector", "polynomial", "table", "point", "round", "bool", "group", "groups", "commitment", "commitments", "proof"]

def staticIdentity (identity : String) : Bool :=
  let domains := [bn254Fr, bn254G1, bn254G2, fr, ristrettoScalar, koalaBear, koalaBearExt8, g1, ristrettoGroup, pcs, rowBase, rowExtension, transcriptIdentity, ristrettoTranscript, spongefishTranscript, extensionTranscript]
  domains.contains identity ||
    (("" :: domains).flatMap fun domain => serializableKinds.filterMap fun kind =>
      if logicalIdentity kind domain then some (codec kind domain) else none).contains identity

inductive StaticSort where
  | field | group | commitment | transcript | codec | type | natural
  deriving BEq, Repr, DecidableEq

def StaticSort.parse : String → Result StaticSort
  | "Type" => .ok .type
  | "Nat" => .ok .natural
  | "Field" => .ok .field
  | "Group" => .ok .group
  | "Commitment" => .ok .commitment
  | "Transcript" => .ok .transcript
  | "Codec" => .ok .codec
  | _ => .error "generic-declared-sort"

def StaticSort.accepts (sort : StaticSort) (identity : String) : Bool :=
  match sort with
  | .type => (Logical.parse identity).isOk
  | .natural => (Logical.natural identity).isOk
  | .field => scalarDomain identity
  | .group => groupDomain identity
  | .commitment => identity == pcs || rowDomain identity
  | .transcript => transcriptDomain identity
  | .codec => identity.startsWith "zkcv." && staticIdentity identity

def associatedSort (sort : StaticSort) (member : String) : Result StaticSort :=
  if (sort == .field && member == "BaseField") ||
      (sort == .group && member == "Scalar") ||
      (sort == .commitment && ["ValueField", "PointField", "EvaluationField"].contains member) ||
      (sort == .transcript && member == "ChallengeField") then .ok .field
  else if sort == .field && ["PairingG1", "PairingG2"].contains member then .ok .group
  else .error "generic-associated-sort"

def associatedIdentity (identity member : String) : Result String :=
  if (identity == g1 && member == "Scalar") ||
      (identity == pcs && ["ValueField", "PointField", "EvaluationField"].contains member) ||
      ((identity == transcriptIdentity || identity == spongefishTranscript) && member == "ChallengeField") then .ok fr
  else if (identity == ristrettoGroup && member == "Scalar") ||
      (identity == ristrettoTranscript && member == "ChallengeField") then .ok ristrettoScalar
  else if rowDomain identity && member == "ValueField" then .ok (if identity == rowBase then koalaBear else koalaBearExt8)
  else if identity == extensionTranscript && member == "ChallengeField" then .ok koalaBearExt8
  else if identity == koalaBearExt8 && member == "BaseField" then .ok koalaBear
  else if (identity == bn254G1 || identity == bn254G2) && member == "Scalar" then .ok bn254Fr
  else if identity == bn254Fr && member == "PairingG1" then .ok bn254G1
  else if identity == bn254Fr && member == "PairingG2" then .ok bn254G2
  else .error "binding-associated-identity"

abbrev Declaration := OperationBinding

structure Signature where
  inputs : List ValueType
  outputs : List ValueType
  deriving BEq, Repr, DecidableEq

/-- Five bounded labels in the installed transcript origin alphabet. -/
def validTranscriptAttributes (attrs : List String) : Bool :=
  attrs.length == 5 && attrs.all (fun s => !s.isEmpty && s.utf8ByteSize ≤ 128 &&
    s.toList.all (fun c => Decode.asciiLetter c || Decode.asciiDigit c ||
      c == '_' || c == '.' || c == '-'))

/-- Source constants are natural casts; closed operations carry canonical
field values. All other installed attributes already have closed meaning. -/
def attributes (generic : Bool) (contract : String) (attrs : List String) (identity : String := fr) : Result Unit := do
  if contract == "field.constant" || contract == "vector.constant" then
    if contract == "field.constant" then ensure (attrs.length == 1) "kernel-attributes"
    for text in attrs do
      ensure (text.utf8ByteSize ≤ (if generic then 1024 else 78)) "natural-limit"
      ensure (!text.isEmpty && text.toList.all Decode.asciiDigit) "expected-natural"
      let some value := text.toNat? | throw "expected-natural"
      ensure (toString value == text) "noncanonical-natural"
      if !generic then ensure (value < (← scalarModulus identity)) "noncanonical-field"
  else if contract == "index.constant" then
    let [text] := attrs | throw "kernel-attributes"
    ensure ((← Decode.natural (.str text)) < 2^64) "kernel-attributes"
  else if contract == "matrix.identity_check" then
    let [digest] := attrs | throw "kernel-attributes"
    ensure (digest.length == 64 && digest.toList.all (fun c =>
      Decode.asciiDigit c || ('a' ≤ c && c ≤ 'f'))) "kernel-attributes"
  else if contract == "matrix.shape_check" then
    ensure (attrs.length == 2) "kernel-attributes"
    for text in attrs do
      let n ← Decode.natural (.str text)
      ensure (n ≤ 65536) "kernel-attributes"
  else if contract == "vector.scatter_sum" then
    ensure (!attrs.isEmpty) "kernel-attributes"
    for text in attrs do
      ensure ((← Decode.natural (.str text)) ≤ 18446744073709551615) "kernel-attributes"
  else if ["curve.at", "vector.splat", "vector.powers", "vector.at", "vector.length_check",
      "poly.degree_check", "random.vector"].contains contract then
    let [text] := attrs | throw "kernel-attributes"
    ensure ((← Decode.natural (.str text)) ≤ 1048576) "kernel-attributes"
  else if contract == "vector.gather" || contract == "vector.matvec" then
    ensure (attrs.length ≤ 1048576) "kernel-attributes"
    if contract == "vector.matvec" then ensure (attrs.length == 3) "kernel-attributes"
    let numbers ← attrs.mapM fun text => do
      let n ← Decode.natural (.str text)
      ensure (n ≤ 1048576) "kernel-attributes"
      return n
    if contract == "vector.matvec" then
      let [_, _, transpose] := numbers | throw "kernel-attributes"
      ensure (transpose ≤ 1) "kernel-attributes"
  else if contract.startsWith "transcript." then
    ensure (validTranscriptAttributes attrs) "kernel-attributes"
  else ensure attrs.isEmpty "kernel-attributes"


end Tools.Interactive.Bindings
