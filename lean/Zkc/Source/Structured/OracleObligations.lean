module

public import Zkc.Source.Structured.Format

@[expose] public section

/-! Independently derived condition templates and ordered virtual footprints.
This checks proposal correspondence to the retained snapshot, not logical oracle
admission, the truth of a premise, or realization/security soundness. -/
namespace Zkc.Source.Structured.OracleObligations
open Lean

inductive Purpose where
  | inputPair | sendShape | virtualAdmissibility | queryDomain
  deriving BEq, Repr

def Purpose.spelling : Purpose → String
  | .inputPair => "input_pair"
  | .sendShape => "send_shape"
  | .virtualAdmissibility => "virtual_admissibility"
  | .queryDomain => "query_domain"

structure Condition where
  purpose : Purpose
  row : List Nat
  deriving BEq, Repr

structure Query where
  row : List Nat
  source : Nat
  position : Nat
  deriving BEq, Repr

structure Footprint where
  definition : Nat
  sources : Nat
  queries : List Query
  deriving BEq, Repr

structure Report where
  source : String
  entry : String
  conditions : List Condition
  footprints : List Footprint
  deriving BEq, Repr

def byteLimit : Nat := 1024 * 1024

def wire (report : Report) : Json := .arr #[.str "zkc.oracle-obligations/0",
  .str report.source, .str report.entry,
  toJson (report.conditions.map fun condition => Json.arr #[.str condition.purpose.spelling, toJson condition.row]),
  toJson (report.footprints.map fun footprint => Json.arr #[toJson footprint.definition,
    toJson footprint.sources, toJson (footprint.queries.map fun query => Json.arr #[toJson query.row,
      toJson query.source, toJson query.position])])]

structure DerivationState where
  remaining : Nat := 100000
  conditions : List Condition := []

abbrev Derivation := StateT DerivationState (Except String)

def charge (amount : Nat) : Derivation Unit := do
  let state ← get
  if amount > state.remaining then throw "oracle-obligations-limit"
  set { state with remaining := state.remaining - amount }

def purpose : Descriptor → Option Purpose
  | .oracle (.input ..) => some .inputPair
  | .oracle (.send ..) => some .sendShape
  | .oracle (.virtual ..) => some .virtualAdmissibility
  | .oracle (.query ..) => some .queryDomain
  | _ => none

def block : Nat → List Nat → Block → Option Nat → Nat → Derivation (List Query)
  | 0, _, _, _, _ => throw "oracle-obligations-limit"
  | fuel + 1, path, .block instructions _, sources, inputs => do
    let mut parameters : List (Option Nat) := (List.range inputs).map some
    let mut queries := []
    for (instruction, i) in instructions.zipIdx do
      let .instruction descriptor operands results regions _ := instruction
      let row := path ++ [1, i]
      charge (1 + operands.length + results.length + row.length)
      if let some kind := purpose descriptor then
        modify fun state => {state with conditions := ⟨kind, row⟩ :: state.conditions}
      if let some count := sources then
        if !regions.isEmpty then throw "oracle-obligations-source"
        if let .oracle (.query owner _) := descriptor then
          if owner.isSome then throw "oracle-obligations-source"
          let [handle, position] := operands | throw "oracle-obligations-source"
          let some (some parameter) := parameters[handle]? | throw "oracle-obligations-source"
          if parameter ≥ count || position ≥ parameters.length then throw "oracle-obligations-source"
          queries := ⟨row, parameter, position⟩ :: queries
        parameters := List.replicate results.length none ++ parameters
      for (region, r) in regions.zipIdx do
        let .region _ _ body := region
        let _ ← block fuel (row ++ [3, r, 2]) body none 0
    return queries.reverse

/-- Source addresses refer to actual rows, without expanding calls or loops.
Dynamic activation and the full helper meaning remain in the original subject. -/
def derive (snapshot : Snapshot) : Except String Report := do
  let action : Derivation (List Footprint) := do
    let mut footprints := []
    for (definition, i) in snapshot.definitions.zipIdx do
      match definition with
      | .function function =>
        let _ ← block 64 [7, i, 9] function.body none 0
      | .oracle declaration =>
        let sources := (declaration.inputs.takeWhile fun type =>
          match type with | .oracle _ => true | _ => false).length
        let queries ← block 64 [7, i, 7] declaration.body (some sources) declaration.inputs.length
        footprints := ⟨i, sources, queries⟩ :: footprints
      | _ => pure ()
    return footprints.reverse
  let (footprints, state) ← action.run {}
  let report := Report.mk snapshot.source snapshot.entry state.conditions.reverse footprints
  if (wire report).compress.utf8ByteSize + 1 > byteLimit then throw "oracle-obligations-limit"
  return report

def path (json : Json) : Except String (List Nat) := do
  let indices ← (← Format.array json 512).mapM Format.natural
  if indices.any (· > 4096) then throw "oracle-obligations-shape"
  return indices

def condition (json : Json) : Except String Condition := do
  let [kind, row] ← Format.array json 2 | throw "oracle-obligations-shape"
  let kind ← match kind with
    | .str "input_pair" => pure Purpose.inputPair
    | .str "send_shape" => pure Purpose.sendShape
    | .str "virtual_admissibility" => pure Purpose.virtualAdmissibility
    | .str "query_domain" => pure Purpose.queryDomain
    | _ => throw "oracle-obligations-shape"
  return ⟨kind, ← path row⟩

def query (json : Json) : Except String Query := do
  let [row, source, position] ← Format.array json 3 | throw "oracle-obligations-shape"
  return ⟨← path row, ← Format.natural source, ← Format.natural position⟩

def footprint (json : Json) : Except String Footprint := do
  let [definition, sources, queries] ← Format.array json 3 | throw "oracle-obligations-shape"
  return ⟨← Format.natural definition, ← Format.natural sources,
    ← (← Format.array queries 4096).mapM query⟩

def decode (json : Json) : Except String Report := do
  if json.compress.utf8ByteSize > byteLimit then throw "oracle-obligations-limit"
  let [.str "zkc.oracle-obligations/0", source, entry, conditions, footprints] ← Format.array json 5
    | throw "oracle-obligations-shape"
  return ⟨← Format.string source, ← Format.string entry,
    ← (← Format.array conditions 4096).mapM condition,
    ← (← Format.array footprints 128).mapM footprint⟩

/-- Bound untrusted text before parsing. Whitespace is irrelevant to record
comparison, but still consumes the native report's one MiB input budget. -/
def parse (text : String) : Except String Json := do
  if text.utf8ByteSize > byteLimit then throw "oracle-obligations-limit"
  let mut depth := 0
  let mut quoted := false
  let mut escaped := false
  for char in text.toList do
    if quoted then
      if escaped then escaped := false
      else if char == '\\' then escaped := true
      else if char == '"' then quoted := false
    else if char == '"' then quoted := true
    else if char == '[' then
      depth := depth + 1
      if depth > 16 then throw "oracle-obligations-limit"
    else if char == ']' then depth := depth - 1
  Format.parse text byteLimit

/-- An exact derived proposal cannot omit a reached-prefix check template or
identify distinct repeated queries. This does not discharge the templates. -/
def check (snapshot : Snapshot) (json : Json) : Except String Report := do
  let actual ← decode json
  let expected ← derive snapshot
  unless actual == expected do throw "oracle-obligations-mismatch"
  return actual

end Zkc.Source.Structured.OracleObligations
