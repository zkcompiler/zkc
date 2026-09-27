import Tools.Interactive.Bindings
import Tools.Interactive.Requirements

/-! Symbolic local signatures, before nominal identity or implementation
selection. Associated fields remain distinct terms until a promise equates them. -/

set_option autoImplicit false

namespace Tools.Interactive.Generic
open Bindings Zkc.Source.Requirements

abbrev Parameters := List (String × StaticSort)

def termName : Term → String
  | .root name => name
  | .project base member => termName base ++ "." ++ member
  | .apply name arguments => reprStr (Term.apply name arguments)

def parameterSort : Logical.ParameterKind → Result StaticSort
  | .type => .ok .type
  | .natural => .ok .natural
  | .domain sort => StaticSort.parse sort

/-- The existing constant-root namespace carries kind-interpreted strings. -/
def constantSort (text : String) : Result StaticSort := do
  if (Logical.natural text).isOk then return .natural
  if (Logical.parse text).isOk then return .type
  let some sort := [StaticSort.field, .group, .commitment, .transcript, .codec].find? (·.accepts text)
    | throw "generic-constant-sort"
  return sort

def termSort (parameters : Parameters) : Term → Result StaticSort
  | .root name =>
      if name.startsWith "$" then constantSort (name.drop 1).toString else lookup name parameters
  | .project base member => do associatedSort (← termSort parameters base) member
  | .apply head arguments => do
      let expected ← (← Logical.parameterKinds head).mapM parameterSort
      ensure ((← arguments.mapM (termSort parameters)) == expected) "generic-type-sort"
      return .type

private def parseRoot (parameters : Parameters) (text : String) : Result Term := do
  if (Logical.natural text).isOk then return .root ("$" ++ text)
  ensure (Decode.validName text && text.utf8ByteSize ≤ 128) "generic-term"
  let root :: members := text.splitOn "." | throw "generic-term"
  let term := members.foldl Term.project (.root root)
  let _ ← termSort parameters term
  return term

private def parseTermAt (parameters : Parameters) (depth : Nat) (text : String) : Result Term := do
  ensure (!text.isEmpty && text.utf8ByteSize ≤ Logical.byteLimit && !text.contains '@') "generic-term"
  if text.contains '<' then
    let depth + 1 := depth | throw "binding-type-depth"
    let (head, arguments) ← Logical.applicationParts text
    let kinds ← Logical.parameterKinds head
    ensure (!(kinds matches [.domain _]) && !kinds.isEmpty && kinds.length == arguments.length) "generic-type-arity"
    let terms ← arguments.mapM (parseTermAt parameters depth)
    let term := Term.apply head terms
    let _ ← termSort parameters term
    return term
  if text.contains ':' then
    let [head, argument] := text.splitOn ":" | throw "generic-type"
    let [.domain _] ← Logical.parameterKinds head | throw "generic-type-arity"
    let term := Term.apply head [← parseRoot parameters argument]
    let _ ← termSort parameters term
    return term
  if Bindings.domainIndependent text then return .apply text []
  parseRoot parameters text
termination_by depth

def parseTerm (parameters : Parameters) (text : String) : Result Term :=
  parseTermAt parameters Logical.depthLimit text

def kindSort (kind : String) : Result (Option StaticSort) := do
  match ← Logical.parameterKinds kind with
  | [] => return none
  | [.domain sort] => return some (← StaticSort.parse sort)
  | _ => throw "generic-type-arity"

/-- Existing shallow aggregates remain valid. A structured signature stores its
complete Type-valued application term in `body`; its children are ordinary scope
terms, not encoded domain identities. This uses the existing requirement DAG. -/
structure ValueType where
  kind : String
  body : Option Term
  deriving DecidableEq, Repr

/-- Atomic compatibility view; structured types have no single domain. -/
def ValueType.domain (ty : ValueType) : Option Term :=
  if (((kindSort ty.kind).toOption.bind id)).isSome then ty.body else none

def ValueType.ofArguments (kind : String) (arguments : List Term) : ValueType :=
  match arguments with
  | [] => ⟨kind, none⟩
  | [argument] =>
      if (((kindSort kind).toOption.bind id)).isSome then ⟨kind, some argument⟩
      else ⟨kind, some (.apply kind arguments)⟩
  | _ => ⟨kind, some (.apply kind arguments)⟩

def ValueType.term (ty : ValueType) : Term :=
  if ty.kind.isEmpty then ty.body.getD (.root "")
  else match ty.body with
    | some (.apply head args) =>
        if head == ty.kind then .apply head args else .apply ty.kind ty.body.toList
    | _ => .apply ty.kind ty.body.toList

def ValueType.arguments (ty : ValueType) : List Term :=
  match ty.term with | .apply _ args => args | term => [term]

/-- A Type parameter without a copy promise is conservatively affine. No solver
relation or default permission is invented for such a parameter. -/
private def copyableTerm : Term → Bool
  | .apply head arguments =>
      if head == "fixed_vector" then match arguments with
        | [element, _] => copyableTerm element
        | _ => false
      else Logical.publicKind head || ["opening_state", "opening_states", "prover_key", "verifier_key"].contains head
  | .root name =>
      name.startsWith "$" && (Logical.permissions (name.drop 1).toString).copy
  | _ => false

def ValueType.affine (ty : ValueType) : Bool := !copyableTerm ty.term

def valueType (parameters : Parameters) (text : String) : Result ValueType := do
  let term ← parseTerm parameters text
  ensure ((← termSort parameters term) == .type) "generic-type-sort"
  match term with
  | .apply head arguments => return ValueType.ofArguments head arguments
  | _ => return ⟨"", some term⟩

def relationSorts (name : String) : Result (List StaticSort) := do
  match name with
  | "PairingField" | "Field" | "CommRing" | "PrimeField" | "IndexRandomness" | "ExtensionField" | "TwoAdicField" | "CharacteristicNotTwo" => return [.field]
  | "Group" | "ScalarAction" => return [.group]
  | "MultilinearOpening" | "VectorCommitment" => return [.commitment]
  | "Transcript" | "FieldTranscript" | "IndexTranscript" => return [.transcript]
  | _ =>
      ensure (name.startsWith "Encodes.") "generic-declared-predicate"
      let kind := (name.drop "Encodes.".length).toString
      ensure (["bool", "index", "indices", "matrix", "vector", "polynomial", "field", "table", "point", "round", "group", "groups", "commitment", "commitments", "proof"].contains kind)
        "generic-declared-predicate"
      return [.codec] ++ (← kindSort kind).toList

def closedRelation (name : String) (arguments : List String) : Result Bool := do
  let sorts ← relationSorts name
  if arguments.length != sorts.length then return false
  if !((sorts.zip arguments).all fun (sort, value) => sort.accepts value) then return false
  if name.startsWith "Encodes." then
    let kind := (name.drop "Encodes.".length).toString
    return arguments[0]? == some (Bindings.codec kind (arguments[1]?.getD ""))
  -- Capabilities are nominal installation facts, not consequences of sort alone.
  if name == "VectorCommitment" then return arguments == [Bindings.rowBase] || arguments == [Bindings.rowExtension]
  if name == "MultilinearOpening" then return arguments == [Bindings.pcs]
  if name == "IndexRandomness" then return arguments == [Bindings.koalaBearExt8]
  if name == "IndexTranscript" then return arguments == [Bindings.extensionTranscript]
  if name == "PairingField" then return arguments == [Bindings.bn254Fr]
  if name == "TwoAdicField" then return arguments == [Bindings.bn254Fr] || arguments == [Bindings.koalaBear] || arguments == [Bindings.koalaBearExt8]
  if name == "ExtensionField" then return arguments == [Bindings.koalaBearExt8]
  if name == "PrimeField" then return arguments != [Bindings.koalaBearExt8]
  return true

/-- Constants use an internal root spelling outside the source binder grammar. -/
def constantIdentity : Term → Option String
  | .root name => if name.startsWith "$" then some (name.drop 1).toString else none
  | .project base member => do
      (Bindings.associatedIdentity (← constantIdentity base) member).toOption
  | .apply head arguments => do
      let values ← arguments.mapM constantIdentity
      let kinds ← (Logical.parameterKinds head).toOption
      if values.length != kinds.length then none else do
        let text := if kinds.isEmpty then head else if kinds matches [.domain _] then
            head ++ ":" ++ values.headD ""
          else head ++ "<" ++ String.intercalate "," values ++ ">"
        return (← (Logical.parse text).toOption).spelling

def groundRequirement (predicate : Predicate) : Result Bool := do
  match predicate with
  | .equal a b =>
      match constantIdentity a, constantIdentity b with
      | some a, some b => ensure (a == b) "binding-requirement"; return true
      | _, _ => return false
  | .relation name terms =>
      let values := terms.map constantIdentity
      if values.all Option.isSome then
        ensure (← closedRelation name (values.filterMap id)) "binding-requirement"
        return true
      return false

def predicate (parameters : Parameters) (name : String) (arguments : List Term) : Result Predicate := do
  let actual ← arguments.mapM (termSort parameters)
  if name == "=" then
    let [a, b] := actual | throw "generic-predicate-arity"
    ensure (a == b) "generic-predicate-sort"
    let [a, b] := arguments | throw "generic-predicate-arity"
    return .equal a b
  ensure (actual == (← relationSorts name)) "generic-predicate-sort"
  return .relation name arguments

structure Signature where
  inputs : List ValueType
  outputs : List ValueType
  needs : List Predicate
  deriving Repr

def signature (parameters : Parameters) (contract : String) (arguments : List Term) : Result Signature := do
  if ["fixed_vector.from_vector", "fixed_vector.to_vector", "fixed_vector.dot"].contains contract then
    let [field, length] := arguments | throw "generic-static-arity"
    ensure ((← termSort parameters field) == .field && (← termSort parameters length) == .natural) "generic-static-sort"
    let fixed := ValueType.ofArguments "fixed_vector" [.apply "field" [field], length]
    let vector : ValueType := ⟨"vector", some field⟩
    let scalar : ValueType := ⟨"field", some field⟩
    let needs := [Predicate.relation "Field" [field]]
    return match contract with
      | "fixed_vector.from_vector" => ⟨[vector], [fixed], needs⟩
      | "fixed_vector.to_vector" => ⟨[fixed], [vector], needs⟩
      | _ => ⟨[fixed, fixed], [scalar], needs⟩
  if contract == "pairing.check" then
    let [f] := arguments | throw "generic-static-arity"
    ensure ((← termSort parameters f) == .field) "generic-static-sort"
    return ⟨[⟨"groups", some (.project f "PairingG1")⟩,
      ⟨"groups", some (.project f "PairingG2")⟩], [⟨"bool", none⟩],
      [.relation "PairingField" [f]]⟩
  if contract == "field.embed" || contract == "vector.embed" then
    let [e] := arguments | throw "generic-static-arity"
    ensure ((← termSort parameters e) == .field) "generic-static-sort"
    let kind := if contract == "field.embed" then "field" else "vector"
    return ⟨[⟨kind, some (.project e "BaseField")⟩], [⟨kind, some e⟩],
      [.relation "ExtensionField" [e]]⟩
  let (inputs, outputs) ← Bindings.shape contract
  let mut roots : List (String × Term) := []
  let mut needs : List Predicate := []
  if Bindings.oracleContract contract then
    let [c] := arguments | throw "generic-static-arity"
    ensure ((← termSort parameters c) == .commitment) "generic-static-sort"
    roots := [("vector", .project c "ValueField")]
    for kind in ["commitment", "proof", "opening_state", "commitments", "opening_states"] do
      roots := (kind, c) :: roots
    needs := [.relation "VectorCommitment" [c]]
  else if contract.startsWith "pcs." then
    let [c] := arguments | throw "generic-static-arity"
    ensure ((← termSort parameters c) == .commitment) "generic-static-sort"
    roots := [("table", .project c "ValueField"), ("point", .project c "PointField"),
      ("field", .project c "EvaluationField")]
    for kind in ["commitment", "proof", "opening_state", "prover_key", "verifier_key"] do
      roots := (kind, c) :: roots
    needs := [.relation "MultilinearOpening" [c]]
  else if contract.startsWith "curve." && contract != "curve.response" then
    let [g] := arguments | throw "generic-static-arity"
    ensure ((← termSort parameters g) == .group) "generic-static-sort"
    roots := [("group", g), ("groups", g), ("field", .project g "Scalar"), ("vector", .project g "Scalar"), ("nonce", .project g "Scalar")]
    needs := [.relation "ScalarAction" [g]]
  else if contract.startsWith "transcript." then
    let t :: rest := arguments | throw "generic-static-arity"
    ensure ((← termSort parameters t) == .transcript) "generic-static-sort"
    roots := [("transcript", t)]
    if contract == "transcript.challenge" || contract == "transcript.draw_index" then
      ensure rest.isEmpty "generic-static-arity"
      roots := ("field", .project t "ChallengeField") :: roots
      needs := [.relation (if contract == "transcript.draw_index" then "IndexTranscript" else "FieldTranscript") [t]]
    else
      let kind := (contract.drop "transcript.observe.".length).toString
      let codecArgs ← if Bindings.domainIndependent kind then do
          let [e] := rest | throw "generic-static-arity"
          pure [e]
        else do
          let [payload, e] := rest | throw "generic-static-arity"
          roots := (kind, payload) :: roots
          pure [e, payload]
      needs := [.relation "Transcript" [t], ← predicate parameters ("Encodes." ++ kind) codecArgs]
  else if contract == "bool.and" || contract == "bool.not" ||
      contract == "bool.or" || contract == "control.require" ||
      contract.startsWith "index." || contract.startsWith "indices." || contract.startsWith "external." then
    ensure arguments.isEmpty "generic-static-arity"
  else
    let [f] := arguments | throw "generic-static-arity"
    ensure ((← termSort parameters f) == .field) "generic-static-sort"
    roots := ["field", "matrix", "vector", "polynomial", "table", "point", "round", "rng", "nonce"].map fun kind => (kind, f)
    needs := [.relation (if contract == "random.index" then "IndexRandomness" else if Bindings.numericalContract contract then "TwoAdicField" else if contract.startsWith "poly." then "CommRing" else "Field") [f]]
    if contract == "poly.even_odd_fold" then
      needs := needs ++ [.relation "CharacteristicNotTwo" [f]]
  let makeType := fun kind => do
    if Bindings.domainIndependent kind then pure (ValueType.mk kind none)
    else pure (ValueType.mk kind (some (← lookup kind roots)))
  return ⟨← inputs.mapM makeType, ← outputs.mapM makeType, needs⟩

def typeEqualities (actual expected : ValueType) : Result (List Predicate) := do
  if actual.kind.isEmpty || expected.kind.isEmpty then return [.equal actual.term expected.term]
  ensure (actual.kind == expected.kind && actual.arguments.length == expected.arguments.length) "generic-value-type"
  return (actual.arguments.zip expected.arguments).map fun (a, b) => .equal a b

end Tools.Interactive.Generic
