module

public import Zkc.Source.Structured.Primitives
public import Zkc.Source.Structured.Limits
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

def natural (json : Json) (limit : Nat := Limits.instructions) : Except String Nat := do
  let value ← Source.Format.natural json |>.mapError fun _ => "structured-natural"
  if value > limit then throw "structured-number-limit"
  return value

def decimal (text : String) : Except String Nat := do
  let some value := Source.Format.canonicalDecimal text | throw "structured-decimal"
  return value

def indexDecimal (text : String) : Except String Nat := do
  if text.utf8ByteSize > 20 then throw "structured-index-canonical"
  let value ← decimal text
  if value ≥ indexLimit then throw "structured-index-canonical"
  return value

/-- Identities are decoded as strings; admission resolves them against the
unit's catalogue rows. -/
def field (json : Json) : Except String String := string json

def group (json : Json) : Except String String := string json

def service (json : Json) : Except String String := string json

mutual
 def typeAt : Nat → Json → Except String Ty
  | 0, _ => .error "structured-type-depth"
  | depth + 1, json => do
    match ← array json with
    | [.str "bool"] => return .boolean
    | [.str "index"] => return .index
    | [.str "indices"] => return .indices
    | [.str "field", name] => return .field (← field name)
    | [.str "vector", name] => return .vector (← field name)
    | [.str "group", name] => return .group (← group name)
    | [.str "groups", name] => return .groups (← group name)
    | [.str "oracle", kind] => return .oracle (← oracleKindAt depth kind)
    | [.str "oracle_sequence", kind, maximum] =>
      return .oracleSequence (← oracleKindAt depth kind) (← indexDecimal (← string maximum))
    | [.str "service", name] => return .service (← service name)
    | [.str "sequence", element] => return .sequence (← typeAt depth element)
    | [.str "product", identity, constructor, fields] =>
      let fields ← (← array fields).mapM (typeAt depth)
      return .product (← string identity) (← string constructor) (ProductFields.ofList fields)
    | _ => throw "structured-type-unsupported"

 def oracleKindAt : Nat → Json → Except String OracleKind
  | 0, _ => .error "structured-type-depth"
  | depth + 1, json => do
    match ← array json with
    | [.str "table", arguments] =>
      match ← array arguments 2 with
      | [.arr #[.str "type", row]] => return .table (← typeAt depth row) none
      | [.arr #[.str "type", row], .arr #[.str "nat", rows]] =>
        return .table (← typeAt depth row) (some (← indexDecimal (← string rows)))
      | _ => throw "structured-oracle-kind"
    | _ => throw "structured-oracle-kind"
end

def oracleKind (json : Json) : Except String OracleKind := oracleKindAt 64 json

def type (json : Json) : Except String Ty := typeAt 64 json

def types (json : Json) : Except String (List Ty) := do
  (← array json).mapM type
/-- JSON mask elements must be Booleans, including in unused declarations. -/
def booleans (json : Json) : Except String (List Bool) := do
  (← array json).mapM fun value => match value with
    | .bool value => pure value
    | _ => throw "structured-map-mask"

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

def optional {α : Type} (decode : Json → Except String α) : Json → Except String (Option α)
  | .null => pure none
  | value => some <$> decode value

def oracleNatural (json : Json) : Except String Nat := do indexDecimal (← string json)

def descriptor (json : Json) : Except String Descriptor := do
  match ← array json with
  | [.str "oracle_input", holder, receivers, kind, maximum] =>
      return .oracle (.input (← string holder) (← strings receivers 16)
        (← oracleKind kind) (← optional oracleNatural maximum))
  | [.str "oracle_send", holder, receivers, kind, maximum] =>
      return .oracle (.send (← string holder) (← strings receivers 16)
        (← oracleKind kind) (← optional oracleNatural maximum))
  | [.str "oracle_query", owner, kind] =>
      return .oracle (.query (← optional (fun value => string value) owner) (← oracleKind kind))
  | [.str "oracle_contents", owner, kind] =>
      return .oracle (.contents (← string owner) (← oracleKind kind))
  | [.str "oracle_components", holder, receivers, kind] =>
      return .oracle (.components (← string holder) (← strings receivers 16) (← oracleKind kind))
  | [.str "oracle_rows", kind] => return .oracle (.rows (← oracleKind kind))
  | [.str "oracle_forget_rows", source, target] =>
      return .oracle (.forgetRows (← oracleKind source) (← oracleKind target))
  | [.str "oracle_virtual", declaration, holder, receivers, kind] =>
      return .oracle (.virtual (← string declaration) (← string holder)
        (← strings receivers 16) (← oracleKind kind))
  | [.str "oracle_sequence_empty", kind, maximum] =>
      return .oracle (.sequenceEmpty (← oracleKind kind) (← oracleNatural maximum))
  | [.str "oracle_sequence_append", kind, maximum, roles] =>
      return .oracle (.sequenceAppend (← oracleKind kind) (← oracleNatural maximum) (← strings roles 16))
  | [.str "oracle_sequence_at", kind, maximum, roles] =>
      return .oracle (.sequenceAt (← oracleKind kind) (← oracleNatural maximum) (← strings roles 16))
  | [.str "oracle_sequence_length", kind, maximum] =>
      return .oracle (.sequenceLength (← oracleKind kind) (← oracleNatural maximum))
  | [.str "exec", operation, binding, parameters] =>
      return .exec (← string operation) (← string binding) (← strings parameters)
  | [.str "index.constant", n] =>
      let text ← string n
      let _ ← indexDecimal text
      return .indexConstant text
  | [.str "index.equal"] => return .indexEqual
  | [.str "index.less"] => return .indexLess
  | [.str "index.power_of_two"] => return .indexPowerOfTwo
  | [.str "multilinear.restrict_prefix", d] => return .multilinearRestrictPrefix (← field d)
  | [.str "vector.length", d] => return .vectorLength (← field d)
  | [.str "field.constant", d, n] =>
      let text ← string n
      let _ ← decimal text
      return .fieldConstant (← field d) text
  | [.str "field.add", d] => return .fieldAdd (← field d)
  | [.str "field.subtract", d] => return .fieldSubtract (← field d)
  | [.str "field.multiply", d] => return .fieldMultiply (← field d)
  | [.str "field.embed", extension, base] => return .fieldEmbed (← field extension) (← field base)
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
  | [.str "product.make", constructor] => return .makeProduct (← string constructor)
  | [.str "product.get", index] => return .getProduct (← natural index 511)
  | [.str "call", name] => return .call (← string name)
  | [.str "apply", name] => return .apply (← string name)
  | [.str "protocol_apply", name, roles] => return .protocolApply (← string name) (← strings roles 16)
  | [.str "protocol_repeat", carried, maximum, roles, stateScopes] =>
      return .protocolRepeat (← natural carried 512) (← natural maximum 1048576)
        (← strings roles 16) (← scopes stateScopes)
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
  | [.str "statement", relation, selectors, acceptance, target] =>
      let target ← match target with
        | .null => pure none
        | value => some <$> string value
      return .statement (← string relation) (← strings selectors) (← natural acceptance) target
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
      let instructions ← (← array instructions Limits.instructions).mapM fun instruction => do
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

def domainConstructor (json : Json) : Except String DomainConstructor := do
  match ← array json with
  | [.str "elements", container] => return .elements (← natural container)
  | [.str "indices", container, axis] => return .indices (← natural container) (← natural axis 0)
  | [.str "range", lower, upper] => return .range (← natural lower) (← natural upper)
  | [.str "zip", operands] => return .zip (← refs operands)
  | [.str "product", operands] => return .product (← refs operands)
  | _ => throw "structured-domain-constructor"

def domain (json : Json) : Except String Domain := do
  match ← array json with
  | [.str "domain", name, inputs, constructors, result] =>
    return ⟨← string name, ← types inputs,
      ← (← array constructors 4096).mapM domainConstructor, ← natural result⟩
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

def origin (mode : Kind) (json : Json) : Except String (Option FunctionOrigin) := do
  match mode with
  | .protocol => return some (.protocol (← OriginFormat.protocol json))
  | .local => return some (← OriginFormat.localOrigin json)
  | .oracle => throw "structured-origin-kind"
  | .math =>
    unless (← array json).isEmpty do throw "structured-origin-kind"
    return none

def purpose : Json → Except String String
  | .str "parameter" => .ok "parameter"
  | .str "statement" => .ok "statement"
  | .str "witness" => .ok "witness"
  | _ => .error "structured-relation-purpose"

def contractSelector (json : Json) : Except String ContractSelector := do
  match ← array json with
  | [direction, port, role] =>
    let direction ← match direction with
      | .str "input" => pure ContractDirection.input
      | .str "output" => pure ContractDirection.output
      | _ => throw "structured-contract-direction"
    return ⟨direction, ← natural port, ← string role⟩
  | _ => throw "structured-contract-selector"

def relationApplication (json : Json) : Except String RelationApplication := do
  match ← array json with
  | [relation, selectors] =>
    return ⟨← string relation, ← (← array selectors).mapM contractSelector⟩
  | _ => throw "structured-contract-application"

def contractClause (json : Json) : Except String ContractClause := do
  match ← array json with
  | [kind, name, subject, residual, decision] =>
    let kind ← match kind with
      | .str "target" => pure ContractKind.target
      | .str "input" => pure ContractKind.input
      | .str "output" => pure ContractKind.output
      | .str "continuation" => pure ContractKind.continuation
      | _ => throw "structured-contract-kind"
    return ⟨kind, ← string name, ← relationApplication subject,
      ← optional relationApplication residual, ← optional contractSelector decision⟩
  | _ => throw "structured-contract-clause"

def protocolContract (json : Json) : Except String ProtocolContract := do
  match ← array json with
  | [owner, clauses] => return ⟨← string owner, ← (← array clauses).mapM contractClause⟩
  | _ => throw "structured-contract"

def relation (json : Json) : Except String Relation := do
  match ← array json with
  | [.str "relation", name, visible, kind, key, revision, staticArguments, inputs, outputs, purposes, formula] => do
      let arguments ← (← OriginFormat.array staticArguments Limits.originBindings).mapM (OriginFormat.term Limits.nesting)
      unless originTermsWithin Limits.originTerms arguments do throw "structured-relation-static-arguments"
      return ⟨← string name, ← visibility visible, ← string kind, ← string key,
        ← string revision, ← types inputs, ← types outputs, ← (← array purposes).mapM purpose, ← optional (fun value => string value) formula,
        arguments⟩
  | _ => throw "structured-relation"

def binding (json : Json) : Except String Binding := do
  match ← array json with
  | [.str "binding", name, contract, arguments, implementation] =>
    let value : Binding := ⟨← string name, ← string contract,
      ← strings arguments, ← string implementation true⟩
    if !value.valid then throw "structured-binding"
    return value
  | _ => throw "structured-binding"

def definition (json : Json) : Except String Definition := do
  match ← array json with
  | [.str "oracle", name, inputs, kind, admissibility, shape, maximum, body] =>
      return .oracle ⟨← string name, ← types inputs, ← oracleKind kind,
        ← string admissibility, ← optional oracleNatural shape, ← optional oracleNatural maximum,
        ← block Limits.nesting body⟩
  | [.str "function", name, mode, visible, inputs, outputs, ports, premises, source, body] =>
    let mode ← kind mode
    return .function ⟨← string name, mode, ← visibility visible,
      ← types inputs, ← types outputs, ← interface ports, ← (← array premises).mapM bound,
      ← origin mode source, ← block Limits.nesting body⟩
  | [.str "finite", name, visible, inputs, outputs, domain, step, predicate] =>
    return .finite ⟨← string name, ← visibility visible, ← types inputs, ← types outputs,
      ← string domain, ← string step, ← string predicate true⟩
  | [.str "realize", name, inputs, outputs, helper] =>
    return .realization ⟨← string name, ← types inputs, ← types outputs, ← string helper⟩
  | [.str "collect", name, visible, inputs, outputs, domain, body, predicate] =>
    return .collect ⟨← string name, ← visibility visible, ← types inputs, ← types outputs,
      ← string domain, ← string body, ← string predicate true⟩
  | [.str "map", name, inputs, outputs, helper, rowwise] =>
    return .map ⟨← string name, ← types inputs, ← types outputs, ← string helper, ← booleans rowwise⟩
  | _ => throw "structured-definition"

def domainSort (json : Json) : Except String DomainSort := do
  let some sort := DomainSort.ofSpelling (← string json) | throw "structured-catalogue-sort"
  return sort

def modulus : Json → Except String (Option Nat)
  | .null => pure none
  | json => do
    let text ← json.getStr?.mapError fun _ => "structured-catalogue-modulus"
    let some value := Source.Format.canonicalDecimal text 1024 | throw "structured-catalogue-modulus"
    return some value

def nominal (json : Json) : Except String Nominal := do
  match ← array json with
  | [.str "nominal", identity, sort, members, capabilities, value] =>
    let members ← (← array members).mapM fun member => do
      match ← array member with
      | [name, identity] => return (← string name, ← string identity)
      | _ => throw "structured-catalogue-member"
    return ⟨← string identity, ← domainSort sort, members, ← strings capabilities, ← modulus value⟩
  | _ => throw "structured-catalogue"

def serviceRow (json : Json) : Except String Service := do
  match ← array json with
  | [.str "service", contract, sampled, methods] =>
    return ⟨← string contract, ← string sampled, ← strings methods⟩
  | _ => throw "structured-catalogue"

def catalogue (json : Json) : Except String Catalogue := do
  match ← array json with
  | [nominals, services] =>
    return { nominals := ← (← array nominals Limits.tableEntries).mapM nominal,
             services := ← (← array services Limits.tableEntries).mapM serviceRow }
  | _ => throw "structured-catalogue"

def digestValid (source : String) : Bool :=
  source.length == 71 && source.toList.take 7 == "sha256:".toList &&
    (source.toList.drop 7).all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

def sourceRecord (json : Json) : Except String SourceRecord := do
  let [type, .str resource, .bool sealed, fields] ← array json | throw "component-declaration"
  unless ["ordinary", "affine", "linear"].contains resource do throw "component-declaration"
  let fields ← (← array fields).mapM fun field => do
    let [name, type] ← array field | throw "component-declaration"
    return (← string name, ← OriginFormat.term Limits.nesting type)
  return ⟨← OriginFormat.term Limits.nesting type, resource, sealed, fields⟩

def sourcePort (json : Json) : Except String SourcePort := do
  let [name, type, roles, offset, count] ← array json | throw "component-declaration"
  return ⟨← string name, ← OriginFormat.term Limits.nesting type,
    ← strings roles 16, ← natural offset, ← natural count 512⟩

def sourceDeclarations (json : Json) : Except String SourceDeclarations := do
  let [records, protocols] ← array json | throw "component-declaration"
  let protocols ← (← array protocols Limits.tableEntries).mapM fun protocol => do
    let [name, inputs, outputs] ← array protocol | throw "component-declaration"
    return SourceProtocol.mk (← string name) (← (← array inputs).mapM sourcePort)
      (← (← array outputs).mapM sourcePort)
  return ⟨← (← array records Limits.tableEntries).mapM sourceRecord, protocols⟩

def snapshot (json : Json) : Except String Snapshot := do
  match ← array json with
  | [.str "zkc.structured-source/0", .str "original", digest, entry, domains, relations, bindings, definitions, contracts, rows, declarations] =>
    let source ← string digest
    if !digestValid source then throw "structured-source-digest"
    return ⟨source, ← string entry, ← (← array domains Limits.tableEntries).mapM domain,
      ← (← array relations Limits.tableEntries).mapM relation, ← (← array bindings Limits.tableEntries).mapM binding,
      ← (← array definitions Limits.tableEntries).mapM definition,
      ← (← array contracts Limits.tableEntries).mapM protocolContract, ← catalogue rows, ← sourceDeclarations declarations⟩
  | _ => throw "structured-envelope"

/-- Count arrays, including empty child lists, with the root at depth one. -/
def lexicalDepthWithin : Nat → Json → Bool
  | 0, .arr _ => false
  | remaining + 1, .arr values => values.all (lexicalDepthWithin remaining)
  | _, _ => true

def checkLexicalDepth (remaining : Nat) (json : Json) : Except String Unit := do
  unless lexicalDepthWithin remaining json do throw "depth-limit"

/-- Only the exact protocol-function row has a typed-origin exemption. Decode
that slot strictly before excluding it from ordinary lexical depth. -/
def checkDefinitionDepth (json : Json) : Except String Unit := do
  match json with
  | .arr fields =>
    match fields.toList with
    | [.str "function", _, .str "protocol", _, _, _, _, _, source, _] =>
      let _ ← OriginFormat.protocol source
      checkLexicalDepth (Limits.nesting - 2) (.arr (fields.set! 8 .null))
    | _ => checkLexicalDepth (Limits.nesting - 2) json
  | _ => checkLexicalDepth (Limits.nesting - 2) json

/-- Recognize origins only in the definitions table of the exact current
envelope. Wrong envelope tags or arities and standalone fragments get no
exemption. Other schema validation remains the snapshot decoder's job. -/
def checkSourceDepth (json : Json) : Except String Unit := do
  match json with
  | .arr slots =>
    match slots.toList with
    | [.str "zkc.structured-source/0", .str "original", _, _, _, _, _, .arr definitions, _, _, _] =>
      checkLexicalDepth Limits.nesting (.arr (slots.set! 7 .null))
      definitions.toList.forM checkDefinitionDepth
    | _ => checkLexicalDepth Limits.nesting json
  | _ => checkLexicalDepth Limits.nesting json

/-- Guard arbitrary nesting before the recursive parser, then enforce ordinary
lexical depth everywhere except exact, strictly decoded protocol-origin slots,
including in unused declarations. -/
def parse (text : String) (byteLimit : Nat := Limits.parsedBytes) : Except String Json := do
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
      if depth > Limits.parsedNesting then throw "depth-limit"
    else if char == ']' then depth := depth - 1
  let json ← Source.Format.parse byteLimit text |>.mapError Source.Format.Error.code
  checkSourceDepth json
  return json

end Zkc.Source.Structured.Format
