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

def termSort (parameters : Parameters) : Term → Result StaticSort
  | .root name => lookup name parameters
  | .project base member => do associatedSort (← termSort parameters base) member
  -- Static components are linked by the frontend. The portable generic-domain
  -- profile has no application constructor and must not invent its sort.
  | .apply _ _ => throw "generic-application"

def parseTerm (parameters : Parameters) (text : String) : Result Term := do
  ensure (Decode.validName text && text.utf8ByteSize ≤ 128) "generic-term"
  let root :: members := text.splitOn "." | throw "generic-term"
  let term := members.foldl Term.project (.root root)
  let _ ← termSort parameters term
  return term

def kindSort : String → Result (Option StaticSort)
  | "bool" | "index" | "indices" => .ok none
  | "matrix" | "vector" | "polynomial" | "field" | "table" | "point" | "round" | "rng" | "nonce" => .ok (some .field)
  | "group" | "groups" => .ok (some .group)
  | "prover_key" | "verifier_key" | "commitment" | "commitments" | "proof" | "opening_state" | "opening_states" => .ok (some .commitment)
  | "transcript" => .ok (some .transcript)
  | _ => .error "generic-type-constructor"

structure ValueType where
  kind : String
  domain : Option Term
  deriving DecidableEq, Repr

def ValueType.affine (ty : ValueType) : Bool := ["rng", "nonce", "transcript"].contains ty.kind

def valueType (parameters : Parameters) (text : String) : Result ValueType := do
  match text.splitOn ":" with
  | [kind] =>
      ensure (Bindings.domainIndependent kind) "generic-type-arity"
      return ⟨kind, none⟩
  | [kind, term] =>
      let some sort ← kindSort kind | throw "generic-type-arity"
      let term ← parseTerm parameters term
      ensure ((← termSort parameters term) == sort) "generic-type-sort"
      return ⟨kind, some term⟩
  | _ => throw "generic-type"

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
  | .apply _ _ => none

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
  ensure (actual.kind == expected.kind) "generic-value-type"
  match actual.domain, expected.domain with
  | none, none => return []
  | some a, some b => return [.equal a b]
  | _, _ => throw "generic-value-type"

end Tools.Interactive.Generic
