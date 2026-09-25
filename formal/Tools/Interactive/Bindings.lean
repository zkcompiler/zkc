import Tools.Interactive.Decode

/-! The finite installed full-type vocabulary for the explicit-binding portable
consumer. This is independent of native selection and backend advertisement.
The old profile transport does not determine these operation signatures. -/

set_option autoImplicit false

namespace Tools.Interactive.Bindings

def fr := "bls12-381.fr"
def g1 := "bls12-381.g1"
def bn254Fr := "bn254.fr"
def bn254G1 := "bn254.g1"
def bn254G2 := "bn254.g2"
def bn254Modulus : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617
def pcs := "multilinear.kzg.bls12-381/1"
def extensionTranscript := "merlin3.koala-bear.ext8-binomial3.rejection31le/1"
def transcriptIdentity := "merlin3.bls12-381.fr64be/1"
def spongefishTranscript := "spongefish0.7.4.keccak.bls12-381.fr64be/1"

structure ValueType where
  kind : String
  identity : String
  representation : String := ""
  deriving BEq, Repr, DecidableEq

def ristrettoScalar := "ristretto255.scalar"
def ristrettoGroup := "ristretto255.group"
def ristrettoTranscript := "merlin3.ristretto255.scalar64le/1"
def ristrettoModulus : Nat := 2^252 + 27742317777372353535851937790883648493
def koalaBear := "koala-bear"
def koalaBearExt8 := "koala-bear.ext8-binomial3"
def rowBase := "rows.merkle-keccak256.koala-bear/1"
def rowExtension := "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
def rowDomain (identity : String) : Bool := identity == rowBase || identity == rowExtension
def oracleContract (name : String) : Bool :=
  name.startsWith "oracle." || name.startsWith "commitments." || name.startsWith "opening_states."
def koalaBearModulus : Nat := 2^31 - 2^24 + 1

/-- Characteristic bound for canonical natural embeddings, not extension cardinality. -/
def scalarModulus (identity : String) : Result Nat :=
  if identity == fr then .ok fieldModulus
  else if identity == bn254Fr then .ok bn254Modulus
  else if identity == ristrettoScalar then .ok ristrettoModulus
  else if identity == koalaBear || identity == koalaBearExt8 then .ok koalaBearModulus
  else .error "binding-field-domain"

def scalarDomain (identity : String) : Bool :=
  identity == fr || identity == bn254Fr || identity == ristrettoScalar || identity == koalaBear || identity == koalaBearExt8
def groupDomain (identity : String) : Bool := identity == g1 || identity == bn254G1 || identity == bn254G2 || identity == ristrettoGroup
def transcriptDomain (identity : String) : Bool :=
  identity == transcriptIdentity || identity == ristrettoTranscript || identity == spongefishTranscript || identity == extensionTranscript

def domainIndependent (kind : String) : Bool := ["bool", "index", "indices"].contains kind

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

/-- Exact nominal slot, with no algebraic facts or wire encoding. -/
def resourceUnitDomain (identity : String) : Bool :=
  let letter := fun c : Char => ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
  !identity.isEmpty && identity.utf8ByteSize ≤ 128 &&
    (identity.toList.head?).any letter &&
    identity.toList.all (fun c => letter c || ('0' ≤ c && c ≤ '9') || c == '_' || c == '-' || c == '.')

def resourceUnitContract (contract : String) : Bool :=
  ["resource_unit.create", "resource_unit.pass", "resource_unit.consume"].contains contract

def leafLogicalIdentity (kind identity : String) : Bool :=
  if kind == "resource_unit" then resourceUnitDomain identity
  else
  if domainIndependent kind then identity.isEmpty
  else if ["field", "matrix", "vector", "polynomial", "round"].contains kind then scalarDomain identity
  else if kind == "rng" then identity == fr || identity == bn254Fr || identity == ristrettoScalar || identity == koalaBearExt8
  else if kind == "nonce" then identity == fr || identity == ristrettoScalar
  else if ["table", "point"].contains kind then identity == fr
  else if ["group", "groups"].contains kind then groupDomain identity
  else if ["commitments", "opening_states"].contains kind then rowDomain identity
  else if ["commitment", "proof", "opening_state"].contains kind then identity == pcs || rowDomain identity
  else if ["prover_key", "verifier_key"].contains kind then identity == pcs
  else kind == "transcript" && transcriptDomain identity

/-- A leaf spelling is canonical: a domain-independent kind carries no colon, so
`bool` and `bool:` are one type with one name. Admitting both would give one
payload two nominal identities, because a descriptor keeps the text it was given.
Readers do not silently normalize a different identity to an admitted spelling:
docs/spec/profiles/compiler/local-variants.md. -/
def leafLogical (text : String) : Bool :=
  if domainIndependent text then true else match text.splitOn ":" with
    | [kind, identity] => !identity.isEmpty && leafLogicalIdentity kind identity
    | _ => false

/-- Recursive validity is bounded independently of JSON nesting. -/
def validLogical : Nat → String → Bool
  | 0, _ => false
  | depth + 1, text =>
    if text.startsWith "variant:" then
      match Variant.parse text with
      | .error _ => false
      | .ok descriptor => descriptor.alternatives.all fun (_, payload) => payload.all fun ty =>
          if ty.startsWith "variant:" then validLogical depth ty
          else !ty.contains '@' && ty.utf8ByteSize ≤ 512 && leafLogical ty
    else leafLogical text

def logicalIdentity (kind identity : String) : Bool :=
  if kind == "variant" then validLogical 8 ("variant:" ++ identity)
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

def ValueType.valid (physical : Bool) (ty : ValueType) : Bool :=
  logicalIdentity ty.kind ty.identity &&
    if physical then
      ty.representation == defaultRepresentation ty.kind ty.identity ||
        (ty.kind == "table" && ty.identity == fr && ty.representation == "arkworks.mle-msb/1") ||
        (ty.kind == "vector" && ty.identity == fr && ty.representation == "arkworks.fr-diagonal/1") ||
        (ty.kind == "groups" && ty.identity == ristrettoGroup && ty.representation == "dalek.ristretto-diagonal/1")
    else ty.representation.isEmpty

def ValueType.spelling (ty : ValueType) : String :=
  let base := if domainIndependent ty.kind then ty.kind else ty.kind ++ ":" ++ ty.identity
  if ty.representation.isEmpty then base else base ++ "@" ++ ty.representation

def valueType (physical : Bool) (text : String) : Result ValueType := do
  ensure (text.utf8ByteSize ≤ if text.startsWith "variant:" then 256 * 1024 + (if physical then 18 else 0) else 512) "binding-type-limit"
  let parts := text.splitOn "@"
  let (logical, representation) ← match parts with
    | [logical] => pure (logical, "")
    | [logical, representation] => pure (logical, representation)
    | _ => throw "binding-type"
  let result ← if domainIndependent logical then pure (ValueType.mk logical "" representation)
    else match logical.splitOn ":" with
      | [kind, identity] => pure (ValueType.mk kind identity representation)
      | _ => throw "binding-type"
  ensure (result.valid physical && result.spelling == text) "binding-type"
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
      else {value with representation := defaultRepresentation value.kind value.identity}.spelling

def codec (kind identity : String) : String :=
  if kind == "resource_unit" || kind == "variant" then ""
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
  | field | group | commitment | transcript | codec
  deriving BEq, Repr, DecidableEq

def StaticSort.parse : String → Result StaticSort
  | "Field" => .ok .field
  | "Group" => .ok .group
  | "Commitment" => .ok .commitment
  | "Transcript" => .ok .transcript
  | "Codec" => .ok .codec
  | _ => .error "generic-declared-sort"

def StaticSort.accepts (sort : StaticSort) (identity : String) : Bool :=
  match sort with
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

def shape (contract : String) : Result (List String × List String) :=
  match contract with
  | "pairing.check" => .ok (["groups", "groups"], ["bool"])
  | "oracle.commit" => .ok (["vector", "index"], ["commitment", "opening_state"])
  | "oracle.open" => .ok (["opening_state", "index"], ["vector", "proof"])
  | "oracle.check" => .ok (["commitment", "index", "index", "index", "vector", "proof"], ["bool"])
  | "commitments.empty" => .ok ([], ["commitments"])
  | "commitments.append" => .ok (["commitments", "commitment"], ["commitments"])
  | "commitments.at" => .ok (["commitments", "index"], ["commitment"])
  | "commitments.length" => .ok (["commitments"], ["index"])
  | "opening_states.empty" => .ok ([], ["opening_states"])
  | "opening_states.append" => .ok (["opening_states", "opening_state"], ["opening_states"])
  | "opening_states.at" => .ok (["opening_states", "index"], ["opening_state"])
  | "opening_states.length" => .ok (["opening_states"], ["index"])
  | "vector.slice" => .ok (["vector", "index", "index"], ["vector"])
  | "vector.get" => .ok (["vector", "index"], ["field"])
  | "vector.length" => .ok (["vector"], ["index"])
  | "vector.rotate" => .ok (["vector", "index"], ["vector"])
  | "vector.interleave" => .ok (["vector", "vector"], ["vector"])
  | "vector.prefix_product" => .ok (["vector"], ["vector"])
  | "vector.prefix_sum" => .ok (["vector"], ["vector"])
  | "vector.inverse" => .ok (["vector"], ["vector"])
  | "vector.embed" => .ok (["vector"], ["vector"])
  | "vector.fill" => .ok (["field", "index"], ["vector"])
  | "vector.geometric" => .ok (["field", "index"], ["vector"])
  | "field.from_index" => .ok (["index"], ["field"])
  | "poly.coefficient_count" => .ok (["polynomial"], ["index"])
  | "poly.coset_evaluate" => .ok (["polynomial", "field", "index"], ["vector"])
  | "poly.coset_interpolate" => .ok (["vector", "field"], ["polynomial"])
  | "poly.domain_point" => .ok (["field", "index", "index"], ["field"])
  | "poly.domain_root" => .ok (["index"], ["field"])
  | "poly.domain_points" => .ok (["field", "index"], ["vector"])
  | "poly.even_odd_fold" => .ok (["vector", "field", "field"], ["vector"])
  | "poly.divide_opening" => .ok (["polynomial", "field", "field"], ["polynomial"])
  | "poly.opening_quotient" => .ok (["vector", "field", "field", "field"], ["vector"])
  | "index.constant" => .ok ([], ["index"])
  | "index.add" => .ok (["index", "index"], ["index"])
  | "index.sub" => .ok (["index", "index"], ["index"])
  | "index.mul" => .ok (["index", "index"], ["index"])
  | "index.div" => .ok (["index", "index"], ["index"])
  | "index.mod" => .ok (["index", "index"], ["index"])
  | "index.equal" => .ok (["index", "index"], ["bool"])
  | "index.less" => .ok (["index", "index"], ["bool"])
  | "external.monero.init" => .ok (["indices"], ["indices"])
  | "external.monero.hash" => .ok (["indices"], ["indices"])
  | "external.monero.update" => .ok (["indices", "indices"], ["indices", "indices"])
  | "external.openvm.init" => .ok ([], ["indices"])
  | "external.openvm.observe" => .ok (["indices", "indices"], ["indices"])
  | "external.openvm.sample" => .ok (["indices"], ["indices", "index"])
  | "external.openvm.sample_ext" => .ok (["indices"], ["indices", "indices"])
  | "external.openvm.sample_bits" => .ok (["indices", "index"], ["indices", "index"])
  | "external.openvm.check_witness" => .ok (["indices", "index", "index"], ["indices", "bool"])
  | "indices.empty" => .ok ([], ["indices"])
  | "indices.append" => .ok (["indices", "index"], ["indices"])
  | "indices.at" => .ok (["indices", "index"], ["index"])
  | "indices.length" => .ok (["indices"], ["index"])
  | "field.constant" => .ok ([], ["field"])
  | "field.add" | "field.mul" | "field.sub" => .ok (["field", "field"], ["field"])
  | "field.neg" | "field.inverse" | "field.embed" => .ok (["field"], ["field"])
  | "matrix.mul_vector" | "matrix.transpose_mul_vector" => .ok (["matrix", "vector"], ["vector"])
  | "matrix.bilinear" => .ok (["matrix", "vector", "vector"], ["field"])
  | "matrix.identity_check" => .ok (["matrix"], ["bool"])
  | "matrix.shape_check" => .ok (["matrix"], ["bool"])
  | "vector.constant" | "vector.empty" => .ok ([], ["vector"])
  | "vector.append" => .ok (["vector", "field"], ["vector"])
  | "vector.splat" | "vector.powers" => .ok (["field"], ["vector"])
  | "vector.add" | "vector.sub" | "vector.mul" | "vector.concat" | "vector.kronecker" | "vector.matvec" =>
      .ok (["vector", "vector"], ["vector"])
  | "vector.scale" => .ok (["vector", "field"], ["vector"])
  | "vector.sum" | "vector.at" => .ok (["vector"], ["field"])
  | "vector.dot" => .ok (["vector", "vector"], ["field"])
  | "vector.split" => .ok (["vector"], ["vector", "vector"])
  | "vector.length_check" => .ok (["vector"], ["bool"])
  | "vector.scatter_sum" | "vector.gather" => .ok (["vector"], ["vector"])
  | "vector.from_point" | "poly.equality_weights" => .ok (["point"], ["vector"])
  | "vector.to_point" => .ok (["vector"], ["point"])
  | "vector.from_table" => .ok (["table"], ["vector"])
  | "vector.to_table" => .ok (["vector"], ["table"])
  | "poly.from_coefficients" => .ok (["vector"], ["polynomial"])
  | "poly.coefficients" => .ok (["polynomial"], ["vector"])
  | "poly.degree_check" => .ok (["polynomial"], ["bool"])
  | "poly.univariate_evaluate" => .ok (["polynomial", "field"], ["field"])
  | "poly.univariate_boundary" => .ok (["polynomial"], ["field"])
  | "random.vector" => .ok (["rng"], ["vector", "rng"])
  | "curve.neg" => .ok (["group"], ["group"])
  | "curve.nonidentity" => .ok (["group"], ["bool"])
  | "curve.msm" => .ok (["vector", "groups"], ["group"])
  | "curve.scale_each" => .ok (["vector", "groups"], ["groups"])
  | "curve.vector_add" | "curve.concat" => .ok (["groups", "groups"], ["groups"])
  | "curve.vector_scale" => .ok (["groups", "field"], ["groups"])
  | "curve.split" => .ok (["groups"], ["groups", "groups"])
  | "field.equal" => .ok (["field", "field"], ["bool"])
  | "bool.and" | "bool.or" => .ok (["bool", "bool"], ["bool"])
  | "bool.not" => .ok (["bool"], ["bool"])
  | "control.require" => .ok (["bool"], [])
  | "poly.product_sum" => .ok (["table", "table"], ["field"])
  | "poly.product_round" => .ok (["table", "table"], ["round"])
  | "poly.boundary" => .ok (["round"], ["field"])
  | "poly.round_evaluate" => .ok (["round", "field"], ["field"])
  | "poly.fold" => .ok (["table", "field"], ["table"])
  | "poly.evaluate" => .ok (["table", "point"], ["field"])
  | "poly.empty_point" => .ok ([], ["point"])
  | "poly.append_point" => .ok (["point", "field"], ["point"])
  | "pcs.commit" => .ok (["prover_key", "table"], ["commitment", "opening_state"])
  | "pcs.open" => .ok (["opening_state", "point"], ["field", "proof"])
  | "pcs.check" => .ok (["verifier_key", "commitment", "point", "field", "proof"], ["bool"])
  | "pcs.equal" => .ok (["commitment", "commitment"], ["bool"])
  | "random.index" => .ok (["rng", "index"], ["index", "rng"])
  | "transcript.draw_index" => .ok (["transcript", "index"], ["index", "transcript"])
  | "random.draw" => .ok (["rng"], ["field", "rng"])
  | "curve.generator" => .ok ([], ["group"])
  | "curve.add" => .ok (["group", "group"], ["group"])
  | "curve.scale" => .ok (["group", "field"], ["group"])
  | "curve.equal" => .ok (["group", "group"], ["bool"])
  | "curve.empty" => .ok ([], ["groups"])
  | "curve.append" => .ok (["groups", "group"], ["groups"])
  | "curve.at" => .ok (["groups"], ["group"])
  | "curve.get" => .ok (["groups", "index"], ["group"])
  | "curve.length" => .ok (["groups"], ["index"])
  | "curve.commit" => .ok (["groups", "nonce"], ["groups", "nonce"])
  | "curve.response" => .ok (["field", "field", "nonce"], ["field"])
  | "transcript.challenge" => .ok (["transcript"], ["field", "transcript"])
  | _ =>
      if contract.startsWith "transcript.observe." then
        let kind := (contract.drop "transcript.observe.".length).toString
        if serializableKinds.contains kind then
          .ok (["transcript", kind], ["transcript"])
        else .error "binding-contract"
      else .error "binding-contract"

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

/-- Resolve an explicit contract independently. Implementation eligibility is
checked even at logical stages, while their ports retain logical types. -/
def resolve (physical : Bool) (binding : Declaration) : Result Signature := do
  if resourceUnitContract binding.contract then
    let [domain] := binding.arguments | throw "binding-resource-unit-domain"
    ensure (resourceUnitDomain domain) "binding-resource-unit-domain"
    ensure ((!physical && binding.implementation.isEmpty) || binding.implementation == "logical/" ++ binding.contract) "binding-implementation"
    let ty := ValueType.mk "resource_unit" domain (if physical then "logical.resource_unit/1" else "")
    return ⟨if binding.contract == "resource_unit.create" then [] else [ty],
      if binding.contract == "resource_unit.consume" then [] else [ty]⟩
  if binding.contract == "table.relayout" then
    ensure physical "binding-adapter-at-logical-stage"
    ensure (binding.implementation == "arkworks/table.relayout") "binding-implementation"
    let [field, sourceRepresentation, targetRepresentation] := binding.arguments | throw "binding-static-arity"
    let a := ValueType.mk "table" field sourceRepresentation
    let b := ValueType.mk "table" field targetRepresentation
    ensure (a.valid true && b.valid true && sourceRepresentation != targetRepresentation) "binding-adapter-type"
    return ⟨[a], [b]⟩
  let (inputs, outputs) ← shape binding.contract
  if oracleContract binding.contract then
    let [scheme] := binding.arguments | throw "binding-static-arity"
    ensure (rowDomain scheme &&
      ((!physical && binding.implementation.isEmpty) ||
        binding.implementation == "plonky3/" ++ binding.contract)) "binding-static-arguments"
    let field ← associatedIdentity scheme "ValueField"
    let make := fun kind =>
      let identity := if domainIndependent kind then "" else if kind == "vector" then field else scheme
      ValueType.mk kind identity (if physical then defaultRepresentation kind identity else "")
    return ⟨inputs.map make, outputs.map make⟩
  if binding.contract == "pairing.check" then
    ensure (binding.arguments == [bn254Fr]) "binding-static-arguments"
    ensure ((!physical && binding.implementation.isEmpty) ||
      binding.implementation == "arkworks/pairing.check") "binding-implementation"
    let make := fun kind identity => ValueType.mk kind identity
      (if physical then defaultRepresentation kind identity else "")
    return ⟨[make "groups" bn254G1, make "groups" bn254G2], [make "bool" ""]⟩
  let args := binding.arguments
  let observing := binding.contract.startsWith "transcript.observe."
  let observingKind := (binding.contract.drop "transcript.observe.".length).toString
  let mut field := fr
  let mut group := g1
  let mut transcript := transcriptIdentity
  if binding.contract.startsWith "transcript." then
    let t :: _ := args | throw "binding-static-arity"
    ensure (transcriptDomain t) "binding-static-arguments"
    transcript := t
    field ← associatedIdentity t "ChallengeField"
    group := if field == fr then g1 else ristrettoGroup
    if observing then
      let identity := if domainIndependent observingKind then "" else args[1]?.getD ""
      let expected := if domainIndependent observingKind then [t, codec observingKind identity]
        else [t, identity, codec observingKind identity]
      ensure (args == expected && logicalIdentity observingKind identity) "binding-static-arguments"
      let payloadField := if ["group", "groups"].contains observingKind then
          (associatedIdentity identity "Scalar").toOption.getD ""
        else if ["commitment", "commitments", "proof"].contains observingKind then (associatedIdentity identity "ValueField").toOption.getD "" else identity
      ensure (domainIndependent observingKind || payloadField == field || (t == extensionTranscript && payloadField == koalaBear)) "binding-static-arguments"
    else ensure (args == [t]) "binding-static-arguments"
  else if binding.contract.startsWith "pcs." then
    ensure (args == [pcs]) "binding-static-arguments"
  else if binding.contract.startsWith "curve." && binding.contract != "curve.response" then
    let [g] := args | throw "binding-static-arity"
    ensure (groupDomain g) "binding-static-arguments"
    group := g
    field ← associatedIdentity g "Scalar"
  else if binding.contract == "bool.and" || binding.contract == "bool.not" ||
      binding.contract == "bool.or" || binding.contract == "control.require" ||
      binding.contract.startsWith "index." || binding.contract.startsWith "indices." || binding.contract.startsWith "external." then
    ensure args.isEmpty "binding-static-arguments"
  else
    let [f] := args | throw "binding-static-arity"
    ensure (scalarDomain f) "binding-static-arguments"
    field := f
  if binding.contract == "random.index" then ensure (field == koalaBearExt8) "binding-index-randomness"
  if binding.contract == "transcript.draw_index" then ensure (transcript == extensionTranscript) "binding-index-transcript"
  if numericalContract binding.contract then
    ensure (field == bn254Fr || field == koalaBear || field == koalaBearExt8) "binding-two-adic-field"
  if binding.contract == "poly.even_odd_fold" then
    ensure ((← scalarModulus field) > 2) "binding-requirement"
  let typed := fun kind =>
    let identity := if domainIndependent kind then ""
      else if ["group", "groups"].contains kind then group
      else if ["commitment", "proof", "opening_state", "prover_key", "verifier_key"].contains kind then pcs
      else if kind == "transcript" then transcript else field
    ValueType.mk kind identity ""
  let inputTypes ← if observing then pure [typed "transcript", ⟨observingKind, if domainIndependent observingKind then "" else args[1]?.getD "", ""⟩]
    else if binding.contract == "field.embed" || binding.contract == "vector.embed" then do
      let base ← associatedIdentity field "BaseField"
      pure [ValueType.mk (if binding.contract == "field.embed" then "field" else "vector") base ""]
    else pure (inputs.map typed)
  let logical := Signature.mk inputTypes (outputs.map typed)
  ensure ((logical.inputs ++ logical.outputs).all (·.valid false)) "binding-domain-not-supported"
  let msb := binding.implementation == "arkworks-msb/" ++ binding.contract
  let diagonal := binding.implementation == "arkworks-diagonal/" ++ binding.contract ||
    binding.implementation == "dalek-diagonal/" ++ binding.contract
  let msbContracts := ["poly.product_sum", "poly.product_round", "poly.boundary", "poly.round_evaluate",
    "poly.fold", "poly.evaluate", "poly.empty_point", "poly.append_point",
    "vector.from_table", "vector.to_table"]
  let diagonalAllowed := (field == fr && ["vector.mul", "vector.dot"].contains binding.contract &&
      binding.implementation == "arkworks-diagonal/" ++ binding.contract) ||
    (group == ristrettoGroup && ["curve.scale_each", "curve.msm"].contains binding.contract &&
      binding.implementation == "dalek-diagonal/" ++ binding.contract)
  -- Mathematical binding only. Public-operand leakage admission is host-owned.
  let publicMsm := group == ristrettoGroup && binding.contract == "curve.msm" &&
    binding.implementation == "dalek-vartime/curve.msm"
  let backend := if binding.contract.startsWith "index." || binding.contract.startsWith "indices." || binding.contract.startsWith "external." then "native/"
    else if binding.contract.startsWith "transcript." && transcript == spongefishTranscript then "spongefish/"
    else if field == ristrettoScalar then "dalek/"
    else if field == koalaBear || field == koalaBearExt8 then "plonky3/" else "arkworks/"
  ensure ((!physical && binding.implementation.isEmpty) ||
    binding.implementation == backend ++ binding.contract ||
    (msb && field == fr && msbContracts.contains binding.contract) || diagonalAllowed || publicMsm) "binding-implementation"
  let port := fun (output : Bool) (i : Nat) (ty : ValueType) =>
    let diagPort := diagonal && ((output && i == 0 &&
      ["vector.mul", "curve.scale_each"].contains binding.contract) ||
      (!output && i == 1 && ["vector.dot", "curve.msm"].contains binding.contract))
    let representation := if !physical then ""
      else if diagPort then
        if ty.kind == "vector" then "arkworks.fr-diagonal/1" else "dalek.ristretto-diagonal/1"
      else if msb && ty.kind == "table" then "arkworks.mle-msb/1"
      else defaultRepresentation ty.kind ty.identity
    { ty with representation }
  return ⟨logical.inputs.zipIdx |>.map (fun (ty, i) => port false i ty),
    logical.outputs.zipIdx |>.map (fun (ty, i) => port true i ty)⟩

/-- Finite implementation names for a partially configured definition. Exact
nominal applicability is checked again by resolve at specialization. -/
def implementationName (contract implementation : String) : Bool :=
  ([bn254Fr, bn254G1, bn254G2, fr, ristrettoScalar, koalaBear, koalaBearExt8, g1, ristrettoGroup, pcs, rowBase, rowExtension, transcriptIdentity, ristrettoTranscript, spongefishTranscript, extensionTranscript].map
    fun identity => resolve false ⟨"", contract, [identity], implementation⟩).any Except.isOk ||
  (resolve false ⟨"", contract, [], implementation⟩).isOk ||
  (serializableKinds.flatMap fun kind => [transcriptIdentity, ristrettoTranscript, spongefishTranscript, extensionTranscript].flatMap fun t =>
    ["", bn254Fr, bn254G1, bn254G2, fr, ristrettoScalar, koalaBear, koalaBearExt8, g1, ristrettoGroup, pcs, rowBase, rowExtension].map fun identity =>
      resolve false ⟨"", contract,
        if kind == "bool" then [t, codec kind identity] else [t, identity, codec kind identity], implementation⟩).any Except.isOk

end Tools.Interactive.Bindings
