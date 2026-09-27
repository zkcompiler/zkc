import Tools.Interactive.VariantDescriptor

/-! Handwritten installed logical constructors, kind-directed structural parsing,
and permission derivation. Carrier data never installs constructor authority. -/

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

def scalarDomain (identity : String) : Bool :=
  identity == fr || identity == bn254Fr || identity == ristrettoScalar || identity == koalaBear || identity == koalaBearExt8
def groupDomain (identity : String) : Bool := identity == g1 || identity == bn254G1 || identity == bn254G2 || identity == ristrettoGroup
def transcriptDomain (identity : String) : Bool :=
  identity == transcriptIdentity || identity == ristrettoTranscript || identity == spongefishTranscript || identity == extensionTranscript

def domainIndependent (kind : String) : Bool := ["bool", "index", "indices"].contains kind

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

end Tools.Interactive.Bindings

namespace Tools.Interactive.Logical
open Bindings

def byteLimit : Nat := 4096
def depthLimit : Nat := 8
def nodeLimit : Nat := 200000
def naturalLimit : Nat := 1048576

inductive ParameterKind where
  | domain (sort : String)
  | type
  | natural
  deriving BEq, DecidableEq, Repr

/-- This table is local installation, never a protocol declaration. -/
def parameterKinds (head : String) : Except String (List ParameterKind) :=
  if domainIndependent head then .ok []
  else if ["matrix", "vector", "polynomial", "field", "table", "point", "round", "rng", "nonce"].contains head then
    .ok [.domain "Field"]
  else if ["group", "groups"].contains head then .ok [.domain "Group"]
  else if ["prover_key", "verifier_key", "commitment", "commitments", "proof", "opening_state", "opening_states"].contains head then
    .ok [.domain "Commitment"]
  else if head == "transcript" then .ok [.domain "Transcript"]
  else if head == "resource_unit" then .ok [.domain "ResourceUnit"]
  else if head == "fixed_vector" then .ok [.type, .natural]
  else .error "binding-type-constructor"

mutual
  inductive GroundType where
    | atom (kind identity : String)
    | application (head : String) (arguments : List Argument)
    deriving BEq, Repr
  inductive Argument where
    | domain (identity : String)
    | type (value : GroundType)
    | natural (value : Nat)
    deriving BEq, Repr
end

mutual
  private def groundDecEq (a b : GroundType) : Decidable (a = b) :=
    match a, b with
    | .atom k i, .atom l j => decidable_of_iff (k = l ∧ i = j) (by simp)
    | .application k xs, .application l ys =>
        haveI := argumentsDecEq xs ys
        decidable_of_iff (k = l ∧ xs = ys) (by simp)
    | .atom .., .application .. | .application .., .atom .. => isFalse (by intro h; cases h)
  private def argumentDecEq (a b : Argument) : Decidable (a = b) :=
    match a, b with
    | .domain x, .domain y => decidable_of_iff (x = y) (by simp)
    | .natural x, .natural y => decidable_of_iff (x = y) (by simp)
    | .type x, .type y =>
        haveI := groundDecEq x y
        decidable_of_iff (x = y) (by simp)
    | .domain _, .natural _ | .domain _, .type _ |
      .natural _, .domain _ | .natural _, .type _ |
      .type _, .domain _ | .type _, .natural _ => isFalse (by intro h; cases h)
  private def argumentsDecEq (xs ys : List Argument) : Decidable (xs = ys) :=
    match xs, ys with
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
        haveI := argumentDecEq x y
        haveI := argumentsDecEq xs ys
        decidable_of_iff (x = y ∧ xs = ys) (by simp)
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq GroundType := groundDecEq
instance : DecidableEq Argument := argumentDecEq

mutual
  def GroundType.spelling : GroundType → String
    | .atom kind identity => if domainIndependent kind then kind else kind ++ ":" ++ identity
    | .application head args => head ++ "<" ++ String.intercalate "," (args.map Argument.spelling) ++ ">"
  def Argument.spelling : Argument → String
    | .domain identity => identity
    | .type ty => ty.spelling
    | .natural n => toString n
end

private def require (condition : Bool) (code : String) : Except String Unit :=
  if condition then .ok () else .error code

def natural (text : String) : Except String Nat := do
  require (!text.isEmpty && text.utf8ByteSize ≤ 7 &&
    text.toList.all (fun c => '0' ≤ c && c ≤ '9')) "binding-type-natural"
  let some n := text.toNat? | throw "binding-type-natural"
  require (toString n == text && n ≤ naturalLimit) "binding-type-natural"
  return n

/-- Split only at the enclosing application's commas. Kinds are checked later.
The scan also forbids representations and whitespace at every nesting level. -/
def applicationParts (text : String) : Except String (String × List String) := do
  require (text.utf8ByteSize ≤ byteLimit) "binding-type-limit"
  let head := String.ofList (text.toList.takeWhile (· != '<'))
  require (Variant.name head && text.endsWith ">" && head.length < text.length) "binding-type"
  let inner := ((text.drop (head.length + 1)).toString.dropEnd 1).toString
  let mut depth := 0
  let mut current : List Char := []
  let mut arguments : List String := []
  for c in inner.toList do
    require (33 ≤ c.toNat && c.toNat ≤ 126 && c != '@') "binding-type"
    if c == '<' then
      depth := depth + 1
      require (depth ≤ depthLimit) "binding-type-depth"
    if c == '>' then
      require (depth > 0) "binding-type"
      depth := depth - 1
    if c == ',' && depth == 0 then
      require (!current.isEmpty) "binding-type"
      arguments := String.ofList current.reverse :: arguments
      current := []
    else current := c :: current
  require (depth == 0 && !current.isEmpty) "binding-type"
  return (head, (String.ofList current.reverse :: arguments).reverse)

private def domainAccepts (sort identity : String) : Bool :=
  match sort with
  | "Field" => scalarDomain identity
  | "Group" => groupDomain identity
  | "Commitment" => identity == pcs || rowDomain identity
  | "Transcript" => transcriptDomain identity
  | "ResourceUnit" => resourceUnitDomain identity
  | _ => false

/-- Fuel counts enclosing applications and variants; atomic leaves do not spend
depth. State counts all visited types and kinded arguments, including payloads. -/
private def parseAt (depth : Nat) (text : String) : StateT Nat (Except String) GroundType := do
  let visited ← get
  require (visited < nodeLimit) "binding-type-nodes"
  set (visited + 1)
  require (!text.contains '@') "binding-type"
  if text.startsWith "variant:" then
    let depth + 1 := depth | throw "binding-type-depth"
    let descriptor ← Variant.parse text
    for (_, payload) in descriptor.alternatives do
      for child in payload do
        let _ ← parseAt depth child
    return .atom "variant" descriptor.identity
  require (text.utf8ByteSize ≤ byteLimit) "binding-type-limit"
  if text.contains '<' then
    let depth + 1 := depth | throw "binding-type-depth"
    let (head, texts) ← applicationParts text
    let kinds ← parameterKinds head
    require (kinds != [] && !(kinds matches [.domain _]) && kinds.length == texts.length) "binding-type-arity"
    let arguments ← (kinds.zip texts).mapM fun (kind, argument) => do
      match kind with
      | .type => return Argument.type (← parseAt depth argument)
      | .domain sort =>
          require (domainAccepts sort argument) "binding-type-domain"
          modify (· + 1)
          return .domain argument
      | .natural =>
          let n ← natural argument
          modify (· + 1)
          return .natural n
    require ((← get) ≤ nodeLimit) "binding-type-nodes"
    return .application head arguments
  require (leafLogical text) "binding-type"
  if domainIndependent text then return .atom text ""
  let [kind, identity] := text.splitOn ":" | throw "binding-type"
  return .atom kind identity
termination_by depth

/-- A reduced work budget is useful for focused exhaustion checks without
constructing a resource-boundary input. Public admission uses the full budget. -/
def parseBudgeted (depth nodes : Nat) (text : String) : Except String GroundType := do
  let (ty, _) ← (parseAt (min depth depthLimit) text).run (nodeLimit - min nodes nodeLimit)
  require (ty.spelling == text) "binding-type"
  return ty

def parseWithDepth (depth : Nat) (text : String) : Except String GroundType :=
  parseBudgeted depth nodeLimit text

def parse (text : String) : Except String GroundType := parseWithDepth depthLimit text

/-- Public serialization is an explicit finite codec installation. -/
def publicKind (kind : String) : Bool :=
  ["index", "indices", "matrix", "vector", "polynomial", "field", "table", "point", "round", "bool",
   "commitment", "commitments", "proof", "group", "groups"].contains kind

structure Permissions where
  copy : Bool
  drop : Bool
  isPublic : Bool
  deriving BEq, Repr

private def permissionsAt : Nat → GroundType → Permissions
  | 0, .application .. => ⟨false, false, false⟩
  | 0, .atom "variant" _ => ⟨false, false, false⟩
  | depth + 1, .application head args =>
      let children := args.filterMap fun arg => match arg with
        | .type ty => some (permissionsAt depth ty)
        | _ => none
      let installed := head == "fixed_vector"
      ⟨installed && children.all (·.copy), installed && children.all (·.drop), false⟩
  | depth + 1, .atom "variant" identity =>
      match Variant.parse ("variant:" ++ identity) with
      | .error _ => ⟨false, false, false⟩
      | .ok descriptor =>
          let children := descriptor.alternatives.flatMap fun arm => arm.2.map fun text =>
            match parse text with
            | .ok ty => permissionsAt depth ty
            | .error _ => ⟨false, false, false⟩
          ⟨children.all (·.copy), children.all (·.drop), false⟩
  | _, .atom kind identity =>
      let copy := leafLogicalIdentity kind identity &&
        (publicKind kind || ["opening_state", "opening_states", "prover_key", "verifier_key"].contains kind)
      ⟨copy, copy || (kind == "resource_unit" && resourceUnitDomain identity),
        leafLogicalIdentity kind identity && publicKind kind⟩

/-- Revalidate a constructed tree: a parsed or manually constructed head is not
permission authority. Physical suffix validation belongs to Bindings.valueType. -/
def permissions (text : String) : Permissions :=
  let logical := ((text.splitOn "@").head!)
  match parse logical with
  | .ok ty => permissionsAt depthLimit ty
  | .error _ => ⟨false, false, false⟩

end Tools.Interactive.Logical
