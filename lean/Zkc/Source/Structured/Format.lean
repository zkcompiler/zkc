module

public import Zkc.Source.Structured.Vocabulary
public import Zkc.Source.Format

@[expose] public section

/-! Strict, bounded, arrays-only decoder for the single original-stage schema.
Decoder depth is capacity policy; it is not fuel for the program's meaning. -/

namespace Zkc.Source.Structured.Format
open Lean

def array (json : Json) (limit : Nat := 512) : Except String (List Json) := do
  let values ← json.getArr?.mapError fun _ => "structured-array"
  if values.size > limit then throw "structured-list-limit"
  return values.toList

def string (json : Json) (empty : Bool := false) : Except String String := do
  let value ← json.getStr?.mapError fun _ => "structured-string"
  if value.utf8ByteSize > 512 || (!empty && value.isEmpty) then throw "structured-string"
  return value

def natural (json : Json) (limit : Nat := 4096) : Except String Nat := do
  let value ← Source.Format.natural json |>.mapError fun _ => "structured-natural"
  if value > limit then throw "structured-number-limit"
  return value

def decimal (text : String) : Except String Nat := do
  let some value := Source.Format.canonicalDecimal text | throw "structured-decimal"
  return value

def field (json : Json) : Except String String := do
  let name ← string json
  if name != scalarDomain then throw "structured-field-domain"
  return name

def group (json : Json) : Except String String := do
  let name ← string json
  if name != groupDomain then throw "structured-group-domain"
  return name

def service (json : Json) : Except String String := do
  let name ← string json
  if name != scalarServiceContract then throw "structured-service-contract"
  return name

def type (json : Json) : Except String Ty := do
  match ← array json with
  | [.str "bool"] => return .boolean
  | [.str "index"] => return .index
  | [.str "field", name] => return .field (← field name)
  | [.str "vector", name] => return .vector (← field name)
  | [.str "group", name] => return .group (← group name)
  | [.str "service", name] => return .service (← service name)
  | _ => throw "structured-type-unsupported"

def types (json : Json) : Except String (List Ty) := do
  (← array json).mapM type
def refs (json : Json) : Except String (List Nat) := do
  (← array json).mapM natural

def strings (json : Json) (limit : Nat := 512) : Except String (List String) := do
  (← array json limit).mapM string

def scopes (json : Json) : Except String (List (List String)) := do
  (← array json).mapM (fun scope => strings scope 16)

/-- Shape and capacity only: roster uniqueness, scope membership and signature
alignment are checked by semantic admission, including for unused protocols. -/
def interface (json : Json) : Except String (Option ProtocolInterface) := do
  match ← array json with
  | [] => return none
  | [.str "protocol", roles, inputs, outputs] =>
      return some ⟨← strings roles 16, ← scopes inputs, ← scopes outputs⟩
  | _ => throw "structured-interface"

def descriptor (json : Json) : Except String Descriptor := do
  match ← array json with
  | [.str "field.constant", d, n] =>
      let text ← string n
      let value ← decimal text
      if value ≥ scalarModulus then throw "structured-field-canonical"
      return .fieldConstant (← field d) text
  | [.str "field.add", d] => return .fieldAdd (← field d)
  | [.str "field.subtract", d] => return .fieldSubtract (← field d)
  | [.str "field.multiply", d] => return .fieldMultiply (← field d)
  | [.str "field.equal", d] => return .fieldEqual (← field d)
  | [.str "group.identity", g] => return .groupIdentity (← group g)
  | [.str "group.add", g] => return .groupAdd (← group g)
  | [.str "group.scale", g, f] => return .groupScale (← group g) (← field f)
  | [.str "group.equal", g] => return .groupEqual (← group g)
  | [.str "bool.constant", .bool b] => return .booleanConstant b
  | [.str "bool.and"] => return .booleanAnd
  | [.str "bool.or"] => return .booleanOr
  | [.str "bool.xor"] => return .booleanXor
  | [.str "bool.equal"] => return .booleanEqual
  | [.str "bool.not_equal"] => return .booleanNotEqual
  | [.str "select", ty] => return .select (← type ty)
  | [.str "bounded_at", d] => return .boundedAt (← field d)
  | [.str "call", name] => return .call (← string name)
  | [.str "apply", name] => return .apply (← string name)
  | [.str "local_call", name, role] => return .localCall (← string name) (← string role)
  | [.str "fold", domain, step, predicate] =>
      return .fold (← string domain) (← string step) (← string predicate true)
  | [.str "if"] => return .branch
  | [.str "for"] => return .loop
  | [.str "for_condition"] => return .loopCondition
  | [.str "guard", owner] => return .guard (← string owner)
  | [.str "restrict", roles] => return .restrict (← strings roles 16)
  | [.str "exchange", sender, receiver] => return .exchange (← string sender) (← string receiver)
  | [.str "draw", owner, f] => return .draw (← string owner) (← field f)
  | [.str "statement", relation, selectors, acceptance] =>
      return .statement (← string relation) (← strings selectors) (← natural acceptance)
  | _ => throw "structured-operation-unsupported"

def terminator (json : Json) : Except String Terminator := do
  match ← array json with
  | [.str "return", values] => return .ret (← refs values)
  | [.str "yield", values] => return .yield (← refs values)
  | [.str "condition", values] => return .condition (← refs values)
  | [.str "stop", reason, site] =>
      return .stop (← Source.Format.stop.decode reason |>.mapError fun _ => "structured-stop")
        (← string site)
  | _ => throw "structured-terminator"

def block : Nat → Json → Except String Block
  | 0, _ => .error "structured-region-depth"
  | depth + 1, json => do
    match ← array json with
    | [.str "block", instructions, terminal] =>
      let instructions ← (← array instructions 4096).mapM fun instruction => do
        match ← array instruction with
        | [op, operands, results, regions, site] =>
          let regions ← (← array regions 2).mapM fun region => do
            match ← array region with
            | [inputs, outputs, body] =>
                return WireRegion.region (← types inputs) (← types outputs) (← block depth body)
            | _ => throw "structured-region"
          return Instruction.instruction (← descriptor op) (← refs operands)
            (← types results) regions (← string site true)
        | _ => throw "structured-instruction"
      return .block instructions (← terminator terminal)
    | _ => throw "structured-block"

def domain (json : Json) : Except String Domain := do
  match ← array json with
  | [.str "domain", name, inputs, constructor] =>
    let constructor ← match ← array constructor with
      | [.str "elements", container] => pure (.elements (← natural container))
      | [.str "indices", container, axis] => pure (.indices (← natural container) (← natural axis 0))
      | _ => throw "structured-domain-constructor"
    return ⟨← string name, ← types inputs, constructor⟩
  | _ => throw "structured-domain"

def kind : Json → Except String Kind
  | .str "protocol" => .ok .protocol
  | .str "math" => .ok .math
  | .str "local" => .ok .local
  | _ => .error "structured-kind"
def visibility : Json → Except String Visibility
  | .str "public" => .ok .publicDef
  | .str "private" => .ok .privateDef
  | _ => .error "structured-visibility"

def bound (json : Json) : Except String Bound := do
  match ← array json with
  | [.str "index_bound", index, container, axis] =>
      return ⟨← natural index, ← natural container, ← natural axis 0⟩
  | _ => throw "structured-precondition"

def origin (json : Json) : Except String (Option (String × List (String × String))) := do
  match ← array json with
  | [] => return none
  | [name, bindings] =>
    let bindings ← (← array bindings 128).mapM fun binding => do
      match ← array binding with
      | [key, value] => return (← string key, ← string value)
      | _ => throw "structured-origin-binding"
    return some (← string name, bindings)
  | _ => throw "structured-origin"

def purpose : Json → Except String String
  | .str "parameter" => .ok "parameter"
  | .str "statement" => .ok "statement"
  | .str "witness" => .ok "witness"
  | _ => .error "structured-relation-purpose"

def relation (json : Json) : Except String Relation := do
  match ← array json with
  | [.str "relation", name, visible, kind, key, revision, inputs, outputs, purposes] =>
      return ⟨← string name, ← visibility visible, ← string kind, ← string key,
        ← string revision, ← types inputs, ← types outputs, ← (← array purposes).mapM purpose⟩
  | _ => throw "structured-relation"

def definition (json : Json) : Except String Definition := do
  match ← array json with
  | [.str "function", name, mode, visible, inputs, outputs, ports, premises, source, body] =>
    return .function ⟨← string name, ← kind mode, ← visibility visible,
      ← types inputs, ← types outputs, ← interface ports, ← (← array premises).mapM bound,
      ← origin source, ← block 64 body⟩
  | [.str "finite", name, visible, inputs, outputs, domain, step, predicate] =>
    return .finite ⟨← string name, ← visibility visible, ← types inputs, ← types outputs,
      ← string domain, ← string step, ← string predicate true⟩
  | _ => throw "structured-definition"

def digestValid (source : String) : Bool :=
  source.length == 71 && source.toList.take 7 == "sha256:".toList &&
    (source.toList.drop 7).all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

def snapshot (json : Json) : Except String Snapshot := do
  match ← array json with
  | [.str "zkc.structured-source/0", .str "original", digest, entry, domains, relations, definitions] =>
    let source ← string digest
    if !digestValid source then throw "structured-source-digest"
    return ⟨source, ← string entry, ← (← array domains 128).mapM domain,
      ← (← array relations 128).mapM relation, ← (← array definitions 128).mapM definition⟩
  | _ => throw "structured-envelope"

/-- Lexical limits precede the recursive JSON parser, including inside unused bodies. -/
def parse (text : String) (byteLimit : Nat := 16 * 1024 * 1024) : Except String Json := do
  if text.utf8ByteSize > byteLimit then throw "byte-limit"
  let mut depth := 0
  let mut quoted := false
  let mut escaped := false
  for char in text.toList do
    if quoted then
      if escaped then escaped := false
      else if char == '\\' then escaped := true
      else if char == '"' then quoted := false
    else if char == '"' then quoted := true
    else if char == '-' then throw "expected-natural"
    else if char == '{' || char == '}' then throw "invalid-shape"
    else if char == '[' then
      depth := depth + 1
      if depth > 64 then throw "depth-limit"
    else if char == ']' then depth := depth - 1
  Source.Format.parse byteLimit text |>.mapError Source.Format.Error.code

end Zkc.Source.Structured.Format
