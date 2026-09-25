import Lean.Data.Json
import Zkc.Source.Requirements

/-! Independent transport for native requirement certificates.
This checks derivability under the input declarations, not their installation
or cryptographic validity. Unresolved answers are not negative judgments. -/

set_option autoImplicit false

namespace Tools.RequirementChecker
open Lean (Json)
open Zkc.Source.Requirements

abbrev Result := Except String

private def ensure (test : Bool) (code : String) : Result Unit :=
  if test then .ok () else .error code

private def array (value : Json) (limit : Nat := 1024) : Result (Array Json) := do
  let result ← value.getArr?
  ensure (result.size ≤ limit) "requirements-limit"
  return result

private def name (value : Json) : Result String := do
  let result ← value.getStr?
  ensure (!result.isEmpty && result.utf8ByteSize ≤ 256) "requirements-name"
  return result

private def index (value : Json) : Result Nat := do
  let n ← value.getNat?
  ensure (n ≤ 65536) "requirements-index"
  return n

private def term (terms : Array Term) (value : Json) : Result Term := do
  let some result := terms[← index value]? | throw "requirements-term-index"
  return result

/- Bound the expanded structural work before constructing/comparing recursive
terms. A small backward-indexed DAG can otherwise unfold exponentially. This is
a transport limit, not a restriction on the mathematical derivation rules. -/
private def checkWork (ts ps gs ss : Json) : Result Unit := do
  let mut weights : Array Nat := #[]
  let mut total := 0
  for item in ← array ts 128 do
    let weight ← match (← array item).toList with
      | [.null, _] => pure 1
      | [parent, _] => do
          let some prior := weights[← index parent]? | throw "requirements-term-index"
          pure (1 + prior)
      | [.str "apply", _, children] => do
          let mut weight := 1
          for child in ← array children 16 do
            let some prior := weights[← index child]? | throw "requirements-term-index"
            weight := weight + prior
          pure weight
      | _ => throw "requirements-term"
    total := total + weight
    ensure (total ≤ 16384) "requirements-work-limit"
    weights := weights.push weight
  let predicateWork := fun value => do
    let [_, args] := (← array value).toList | throw "requirements-predicate"
    let mut weight := 1
    for arg in ← array args 16 do
      let some prior := weights[← index arg]? | throw "requirements-term-index"
      weight := weight + prior
    pure weight
  let mut work := 0
  for p in (← array ps) ++ (← array gs) do
    work := work + (← predicateWork p)
    ensure (work ≤ 262144) "requirements-work-limit"
  work := 0
  for s in ← array ss 65536 do
    let [p, _, _, _] := (← array s).toList | throw "requirements-step"
    work := work + (← predicateWork p)
    ensure (work ≤ 262144) "requirements-work-limit"

private def terms (value : Json) : Result (Array Term) := do
  let mut result := #[]
  for item in ← array value 128 do
    match (← array item).toList with
    | [.null, key] =>
        let next := Term.root (← name key)
        ensure (!(result.toList.contains next)) "requirements-duplicate-term"
        result := result.push next
    | [parent, key] =>
        let next := Term.project (← term result parent) (← name key)
        ensure (!(result.toList.contains next)) "requirements-duplicate-term"
        result := result.push next
    | [.str "apply", head, children] =>
        let next := Term.apply (← name head) (← (← array children 16).toList.mapM (term result))
        ensure (!(result.toList.contains next)) "requirements-duplicate-term"
        result := result.push next
    | _ => throw "requirements-term"
  return result

private def predicate (terms : Array Term) (value : Json) : Result Predicate := do
  match (← array value).toList with
  | [.str "=", args] =>
      match (← array args).toList with
      | [left, right] => return .equal (← term terms left) (← term terms right)
      | _ => throw "requirements-equality"
  | [relation, args] =>
      return .relation (← name relation) (← (← array args 16).toList.mapM (term terms))
  | _ => throw "requirements-predicate"

private def implication (value : Json) : Result Implication := do
  match (← array value).toList with
  | [a, b] =>
      let a ← name a
      let b ← name b
      ensure (a != "=" && b != "=") "requirements-implication"
      return ⟨a, b⟩
  | _ => throw "requirements-implication"

private def step (terms : Array Term) (value : Json) : Result Step := do
  match (← array value).toList with
  | [conclusion, tag, premises, declaration] =>
      let premises ← (← array premises 17).toList.mapM index
      let declaration ← index declaration
      let tag ← tag.getStr?
      ensure (tag == "assumption" || tag == "implication" || declaration == 0)
        "requirements-declaration"
      let rule ← match tag, premises with
        | "assumption", [] => pure (Rule.assumption declaration)
        | "reflexivity", [] => pure .reflexivity
        | "symmetry", [a] => pure (.symmetry a)
        | "transitivity", [a, b] => pure (.transitivity a b)
        | "projection", [a] => pure (.projection a)
        | "application", args => pure (.application args)
        | "transport", a :: rest => pure (.transport a rest)
        | "implication", [a] => pure (.implication a declaration)
        | _, _ => throw "requirements-rule"
      return ⟨← predicate terms conclusion, rule⟩
  | _ => throw "requirements-step"

def check (request certificate : Json) : Result Json := do
  match (← array request).toList, (← array certificate).toList with
  | [.str version, ts, ps, rs, gs], [.str certificateVersion, ss, answers] =>
      ensure (version == "zkc.requirements/1" && certificateVersion == "zkc.requirements-certificate/1")
        "requirements-version"
      checkWork ts ps gs ss
      let terms ← terms ts
      let assumptions ← (← array ps).toList.mapM (predicate terms)
      let rules ← (← array rs 128).toList.mapM implication
      let goals ← (← array gs).toList.mapM (predicate terms)
      let steps ← (← array ss 65536).toList.mapM (step terms)
      let some facts := Zkc.Source.Requirements.check assumptions rules steps
        | throw "requirements-invalid-derivation"
      let answers ← array answers
      ensure (answers.size == goals.length) "requirements-goal-count"
      let mut statuses := #[]
      for (answer, goal) in answers.toList.zip goals do
        if answer == .null then
          statuses := statuses.push (.str "unresolved")
        else
          let some fact := facts[← index answer]? | throw "requirements-proof-index"
          ensure (decide (fact.val = goal)) "requirements-wrong-conclusion"
          statuses := statuses.push (.str "proved")
      return .arr #[.str "checked", .arr statuses]
  | _, _ => throw "requirements-format"

private def byteLimit : Nat := 16 * 1024 * 1024

/-- Bound parser work before invoking JSON: certificate indices are small
naturals, and the carrier has neither objects nor exponent/decimal numbers. -/
private def preflight (input : String) : Result Unit := do
  ensure (input.utf8ByteSize ≤ byteLimit) "requirements-bytes"
  let mut quoted := false
  let mut escaped := false
  let mut depth := 0
  let mut digits := 0
  for c in input.toList do
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then
      quoted := true
      digits := 0
    else if c == '[' then
      depth := depth + 1
      ensure (depth ≤ 64) "requirements-depth"
      digits := 0
    else if c == ']' then
      ensure (depth > 0) "requirements-json"
      depth := depth - 1
      digits := 0
    else if '0' ≤ c && c ≤ '9' then
      digits := digits + 1
      ensure (digits ≤ 6) "requirements-number"
    else
      -- Only `null` has an unquoted alphabetic spelling in this carrier.
      -- JSON's `-0` is a natural zero, matching the native reader. Other
      -- negative values fail `index`; exponent expansion remains forbidden.
      ensure (c == '-' || c == ',' || c == ' ' || c == '\n' || c == '\r' || c == '\t' ||
        c == 'n' || c == 'u' || c == 'l') "requirements-token"
      digits := 0
  ensure (!quoted && depth == 0) "requirements-json"

def dispatch (input : String) : Result Json := do
  preflight input
  let value ← Json.parse input
  match (← array value).toList with
  | [request, certificate] => check request certificate
  | _ => throw "requirements-envelope"

end Tools.RequirementChecker
