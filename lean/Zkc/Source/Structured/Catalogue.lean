module

@[expose] public section

/-! Domain catalogues: the admission-side record of nominal domain identities.

A catalogue row mirrors a native nominal domain (`DomainCatalog`): an identity
string, its sort, its associated member identities, its capability facts and,
for a field, its modulus (the characteristic). Services mirror the native
random-service registry: a contract, the field it samples and the query methods
it offers. The environment catalogue also lists the admitted sort instances of
the structured profile. Admission resolves every occurrence of an identity
against these rows; it never compares a domain name with a fixed string.

Consistency (`Catalogue.check`) is the native catalogue constructor's rules for
nominal rows: valid and unique identities; a modulus only on field rows,
spelled canonically and at least two; unique members, each declared for the
row's sort and naming an identity of the member's sort; unique capability
facts, each declared for the row's sort; and the pairing association of a
`PairingField` row. Nothing here assumes a characteristic: a characteristic-two
field and an extension field without `PrimeField` are well-formed rows.
Refusals name the failed condition. Capability and method metadata does not
install an operation interpretation; index-block requests and gates remain
outside the supported structured profile. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- The sorts of nominal domain identities. -/
inductive DomainSort where
  | field | group | commitment | transcript
  deriving DecidableEq, Repr

namespace DomainSort

/-- The native spelling of a sort. -/
def spelling : DomainSort → String
  | .field => "Field"
  | .group => "Group"
  | .commitment => "Commitment"
  | .transcript => "Transcript"

def ofSpelling : String → Option DomainSort
  | "Field" => some .field
  | "Group" => some .group
  | "Commitment" => some .commitment
  | "Transcript" => some .transcript
  | _ => none

end DomainSort

/-- The sort of the identity an associated member names, for the rows of a
sort that declare it (native `ZKC_Member` declarations). -/
def memberSort : DomainSort → String → Option DomainSort
  | .field, "PairingG1" | .field, "PairingG2" | .field, "PairingGT" => some .group
  | .field, "BaseField" => some .field
  | .group, "Scalar" => some .field
  | .commitment, "ValueField" | .commitment, "PointField" | .commitment, "EvaluationField" =>
      some .field
  | .transcript, "ChallengeField" => some .field
  | _, _ => none

/-- The sort of the rows a capability fact applies to (native single-sort
`ZKC_Capability` declarations). -/
def capabilitySort : String → Option DomainSort
  | "CharacteristicNotTwo" | "CommRing" | "ExtensionField" | "Field"
  | "IndexRandomness" | "IndexBlockRandomness"
  | "PairingField" | "PrimeField" | "TwoAdicField" => some .field
  | "Group" | "ScalarAction" => some .group
  | "MultilinearOpening" | "MultiOpening" | "VectorCommitment" => some .commitment
  | "FieldTranscript" | "IndexTranscript" | "IndexBlockTranscript" | "Transcript" => some .transcript
  | _ => none

/-- A nominal domain identity. The modulus of a field row is its
characteristic: the prime modulus of a prime field, the characteristic of an
extension. -/
structure Nominal where
  identity : String
  sort : DomainSort
  members : List (String × String)
  capabilities : List String
  modulus : Option Nat
  deriving DecidableEq, Repr

def Nominal.member (nominal : Nominal) (member : String) : Option String :=
  (nominal.members.find? (·.1 == member)).map (·.2)

def Nominal.holds (nominal : Nominal) (capability : String) : Bool :=
  nominal.capabilities.contains capability

/-- A random service: its contract, the field it samples and its query
methods. `draw` returns one element of the sampled field; `index` needs
`IndexRandomness` and `indices` independently needs `IndexBlockRandomness` on
that field. Listing a method does not supply its interpretation. -/
structure Service where
  contract : String
  sampled : String
  methods : List String
  deriving DecidableEq, Repr

/-- A catalogue. Exported catalogues carry the rows a unit uses; the
environment catalogue also lists the admitted sort instances (`kind`, identity)
of the structured profile. -/
structure Catalogue where
  nominals : List Nominal
  services : List Service
  types : List (String × String) := []
  deriving DecidableEq, Repr

/-- A native catalogue identity: a letter or underscore, then letters, digits
and `_ . - /`, at most 256 bytes. -/
def identityValid (name : String) : Bool :=
  name.utf8ByteSize ≤ 256 && match name.toList with
  | [] => false
  | first :: rest =>
    let letter := fun c => ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')
    (letter first || first == '_') && rest.all fun c =>
      letter c || ('0' ≤ c && c ≤ '9') || c == '_' || c == '.' || c == '-' || c == '/'

/-- The native modulus rule: at least two. Its spelling has at most 1024
decimal digits, which the decoder checks. -/
def modulusValid (modulus : Nat) : Bool :=
  2 ≤ modulus

namespace Catalogue

def find (catalogue : Catalogue) (identity : String) : Except String Nominal :=
  match catalogue.nominals.find? (·.identity == identity) with
  | some nominal => .ok nominal
  | none => .error "structured-domain-unknown"

/-- An identity of the expected sort. -/
def expect (catalogue : Catalogue) (identity : String) (sort : DomainSort) :
    Except String Nominal := do
  let nominal ← catalogue.find identity
  if nominal.sort != sort then throw "structured-domain-sort"
  return nominal

def identitySort (catalogue : Catalogue) (identity : String) : Option DomainSort :=
  (catalogue.nominals.find? (·.identity == identity)).map (·.sort)

/-- The association of a `PairingField` row: two distinct source groups with
scalar actions of this field and, when present, a target group with one. -/
def pairingValid (catalogue : Catalogue) (nominal : Nominal) : Bool :=
  let acts := fun (group : String) =>
    match catalogue.nominals.find? (·.identity == group) with
    | some row => row.holds "ScalarAction" && row.member "Scalar" == some nominal.identity
    | none => false
  match nominal.member "PairingG1", nominal.member "PairingG2" with
  | some g1, some g2 =>
    g1 != g2 && acts g1 && acts g2 &&
      match nominal.member "PairingGT" with
      | some gt => gt != g1 && gt != g2 && acts gt
      | none => true
  | _, _ => false

/-- One row's own rules and its member references. -/
def checkNominal (catalogue : Catalogue) (nominal : Nominal) : Except String Unit := do
  if !identityValid nominal.identity then throw "structured-catalogue-identity"
  match nominal.modulus with
  | some modulus =>
    if nominal.sort != .field || !modulusValid modulus then throw "structured-catalogue-modulus"
  | none => pure ()
  let members := nominal.members.map (·.1)
  if members.eraseDups.length != members.length then throw "structured-catalogue-duplicate"
  for (member, identity) in nominal.members do
    match memberSort nominal.sort member with
    | none => throw "structured-catalogue-member"
    | some sort =>
      if catalogue.identitySort identity != some sort then throw "structured-catalogue-member"
  if nominal.capabilities.eraseDups.length != nominal.capabilities.length then
    throw "structured-catalogue-duplicate"
  if !nominal.capabilities.all (capabilitySort · == some nominal.sort) then
    throw "structured-catalogue-capability"
  if nominal.holds "PairingField" && !catalogue.pairingValid nominal then
    throw "structured-catalogue-pairing"

/-- A service samples a field row of the catalogue. Its exact ordered methods
are `draw`, then `index` when the field has `IndexRandomness`, then `indices`
when it has `IndexBlockRandomness`; the two capability facts are independent. -/
def checkService (catalogue : Catalogue) (service : Service) : Except String Unit := do
  if !identityValid service.contract then throw "structured-catalogue-identity"
  let field ← catalogue.expect service.sampled .field |>.mapError fun _ => "structured-catalogue-service"
  let methods := ["draw"] ++ (if field.holds "IndexRandomness" then ["index"] else []) ++
    (if field.holds "IndexBlockRandomness" then ["indices"] else [])
  if service.methods != methods then throw "structured-catalogue-service"

/-- Internal consistency, as the native catalogue constructor checks it. -/
def check (catalogue : Catalogue) : Except String Unit := do
  let identities := catalogue.nominals.map (·.identity)
  if identities.eraseDups.length != identities.length then throw "structured-catalogue-duplicate"
  let contracts := catalogue.services.map (·.contract)
  if contracts.eraseDups.length != contracts.length then throw "structured-catalogue-duplicate"
  for nominal in catalogue.nominals do catalogue.checkNominal nominal
  for service in catalogue.services do catalogue.checkService service

/-- Every exported row is the environment's row for that identity. -/
def agrees (exported environment : Catalogue) : Except String Unit := do
  for nominal in exported.nominals do
    match environment.nominals.find? (·.identity == nominal.identity) with
    | some row => if row != nominal then throw "structured-catalogue-mismatch"
    | none => throw "structured-catalogue-unknown"
  for service in exported.services do
    match environment.services.find? (·.contract == service.contract) with
    | some row => if row != service then throw "structured-catalogue-mismatch"
    | none => throw "structured-catalogue-unknown"

/-- An identity of the sort with the capability fact. -/
def require (catalogue : Catalogue) (identity : String) (sort : DomainSort) (capability : String) :
    Except String Unit := do
  let nominal ← catalogue.expect identity sort
  if !nominal.holds capability then throw "structured-domain-capability"

/-- A constant canonical for the field: below its modulus. -/
def belowModulus (catalogue : Catalogue) (identity : String) (value : Nat) : Except String Unit := do
  let nominal ← catalogue.expect identity .field
  match nominal.modulus with
  | some modulus => if value < modulus then pure () else throw "structured-field-canonical"
  | none => throw "structured-field-canonical"

/-- A group scaled by elements of its declared scalar field. -/
def requireScale (catalogue : Catalogue) (group field : String) : Except String Unit := do
  let nominal ← catalogue.expect group .group
  if !nominal.holds "ScalarAction" then throw "structured-domain-capability"
  if nominal.member "Scalar" != some field then throw "structured-domain-member"

/-- A declared base-to-extension embedding. Both carriers must be fields; the
extension names its base and both rows carry the same characteristic. These
catalogue checks select the operation, but its algebraic laws remain a separate
obligation of the interpretation. -/
def requireEmbedding (catalogue : Catalogue) (extension base : String) : Except String Unit := do
  let extended ← catalogue.expect extension .field
  let ground ← catalogue.expect base .field
  if !extended.holds "ExtensionField" || !extended.holds "Field" || !ground.holds "Field" then
    throw "structured-domain-capability"
  if extended.member "BaseField" != some base then throw "structured-domain-member"
  if extended.modulus.isNone || extended.modulus != ground.modulus then
    throw "structured-domain-modulus"

def findService (catalogue : Catalogue) (contract : String) : Except String Service :=
  match catalogue.services.find? (·.contract == contract) with
  | some service => .ok service
  | none => .error "structured-service-contract"

/-- A draw from a service that samples the field. -/
def requireDraw (catalogue : Catalogue) (contract field : String) : Except String Unit := do
  let service ← catalogue.findService contract
  if service.sampled != field || !service.methods.contains "draw" then
    throw "structured-service-contract"

end Catalogue

/-! The BLS12-381 environment: the native rows of the scalar field, its
pairing groups and the random service, and the sort instances the structured
profile admits. -/

def blsScalar : String := "bls12-381.fr"
def blsGroup : String := "bls12-381.g1"
def blsGroupTwo : String := "bls12-381.g2"
def blsTarget : String := "bls12-381.gt"
def blsRandom : String := "random.bls12-381.fr/0"
def blsModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

def blsCatalogue : Catalogue where
  nominals := [
    { identity := blsScalar, sort := .field,
      members := [("PairingG1", blsGroup), ("PairingG2", blsGroupTwo), ("PairingGT", blsTarget)],
      capabilities := ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"],
      modulus := some blsModulus },
    { identity := blsGroup, sort := .group, members := [("Scalar", blsScalar)],
      capabilities := ["Group", "ScalarAction"], modulus := none },
    { identity := blsGroupTwo, sort := .group, members := [("Scalar", blsScalar)],
      capabilities := ["Group", "ScalarAction"], modulus := none },
    { identity := blsTarget, sort := .group, members := [("Scalar", blsScalar)],
      capabilities := ["Group", "ScalarAction"], modulus := none }]
  services := [{ contract := blsRandom, sampled := blsScalar, methods := ["draw"] }]
  types := [("field", blsScalar), ("vector", blsScalar), ("group", blsGroup)]

/-- Installed KoalaBear rows, with the characteristic shared by the prime field
and its octic extension. Carrier cardinalities belong to the selected model. -/
def koalaBearCatalogue : Catalogue where
  nominals := [
    { identity := "koala-bear", sort := .field, members := [],
      capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"],
      modulus := some 2130706433 },
    { identity := "koala-bear.ext8-binomial3", sort := .field,
      members := [("BaseField", "koala-bear")],
      capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo",
        "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], modulus := some 2130706433 }]
  services := [{ contract := "random.koala-bear.ext8-binomial3/0",
                 sampled := "koala-bear.ext8-binomial3", methods := ["draw", "index", "indices"] }]
  types := [("field", "koala-bear"), ("vector", "koala-bear"),
    ("field", "koala-bear.ext8-binomial3"), ("vector", "koala-bear.ext8-binomial3")]

/-- The installed rows understood by the structured importer. Admission of a
row or type is separate from operation support and mathematical law evidence. -/
def admittedCatalogue : Catalogue where
  nominals := blsCatalogue.nominals ++ koalaBearCatalogue.nominals
  services := blsCatalogue.services ++ koalaBearCatalogue.services
  types := blsCatalogue.types ++ koalaBearCatalogue.types

/-- The rows a unit over this environment exports when it lists every row:
the environment's nominal and service rows, without its admitted instances. -/
def blsRows : Catalogue where
  nominals := blsCatalogue.nominals
  services := blsCatalogue.services

end Zkc.Source.Structured
