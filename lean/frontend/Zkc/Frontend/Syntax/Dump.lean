module

public import Zkc.Frontend.Syntax.Tree

@[expose] public section

set_option autoImplicit false

/-!
# A stable text form of the tree

One node per line: the field of its parent, the constructor, the span when asked for, and its
scalar fields; then its children, indented by two spaces. An absent child is `-`; an array
prints its length. Every field is printed, so two trees are equal up to spans exactly when their
dumps without spans are equal.
-/

namespace Zkc.Frontend.Syntax.Dump

structure State where
  withSpans : Bool
  lines : Array String

abbrev DumpM := StateM State

def emit (depth : Nat) (text : String) : DumpM Unit :=
  modify fun state => { state with lines := state.lines.push ("".pushn ' ' (2 * depth) ++ text) }

def spanText (span : Span) : DumpM String := do
  return if (← get).withSpans then s!" @{span.render}" else ""

def quote (text : String) : String :=
  "\"" ++ (text.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

/-- A node line: `key: constructor @span atoms`. -/
def node (depth : Nat) (key constructor : String) (span : Span) (atoms : List String := []) :
    DumpM Unit := do
  let atomText := String.join (atoms.map (" " ++ ·))
  emit depth s!"{key}: {constructor}{← spanText span}{atomText}"

def absent (depth : Nat) (key : String) : DumpM Unit := emit depth s!"{key}: -"

def optional {α : Type} (depth : Nat) (key : String) (f : Nat → String → α → DumpM Unit) :
    Option α → DumpM Unit
  | some value => f depth key value
  | none => absent depth key

def array {α : Type} (depth : Nat) (key : String) (f : Nat → String → α → DumpM Unit)
    (items : Array α) : DumpM Unit := do
  emit depth s!"{key}: [{items.size}]"
  for item in items do f (depth + 1) "-" item

def flag (name : String) (value : Bool) : String := s!"{name}={value}"

def name (depth : Nat) (key : String) (value : Name) : DumpM Unit := do
  emit depth s!"{key}: {quote value.text}{← spanText value.span}"

def number (depth : Nat) (key : String) (value : Number) : DumpM Unit := do
  emit depth s!"{key}: {value.value}{← spanText value.span}"

def stringLiteral (depth : Nat) (key : String) (value : StringLiteral) : DumpM Unit := do
  emit depth s!"{key}: {quote value.content}{← spanText value.span}"

def byteString (depth : Nat) (key : String) (value : ByteString) : DumpM Unit := do
  let form := match value.kind with | .bytes => "b" | .hex => "hex"
  emit depth s!"{key}: {form}{quote value.content}{← spanText value.span}"

def spellingText : Spelling → String
  | .symbol => "symbol"
  | .named => "named"

def binderText : BinderOperator → String
  | .sum => "sum" | .product => "product" | .all => "all" | .any => "any"

def compareText : CompareOperator → String
  | .equal => "==" | .notEqual => "!=" | .less => "<" | .lessEqual => "<="
  | .greater => ">" | .greaterEqual => ">="

def sumText : SumOperator → String
  | .add => "+" | .subtract => "-" | .concatenate => "++"

def productText : ProductOperator → String
  | .multiply => "*" | .divide => "/" | .remainder => "%"

mutual
  /-- A path without static arguments is one line, its names joined by `::`. -/
  partial def path (depth : Nat) (key : String) : Path → DumpM Unit
    | .path span segments => do
      let plain := segments.filterMap fun
        | .segment _ segmentName none => some segmentName.text
        | .segment _ _ (some _) => none
      if plain.size == segments.size then
        emit depth s!"{key}: Path {"::".intercalate plain.toList}{← spanText span}"
      else
        node depth key "Path" span
        array (depth + 1) "segments" segment segments

  partial def segment (depth : Nat) (key : String) : Segment → DumpM Unit
    | .segment span segmentName staticArgs => do
      node depth key "Segment" span
      name (depth + 1) "name" segmentName
      optional (depth + 1) "staticArgs" staticArgsNode staticArgs

  partial def staticArgsNode (depth : Nat) (key : String) : StaticArgs → DumpM Unit
    | .staticArgs span args => do
      node depth key "StaticArgs" span
      array (depth + 1) "args" staticArg args

  partial def staticArg (depth : Nat) (key : String) : StaticArg → DumpM Unit
    | .term span argName term => do
      node depth key "StaticArg.term" span
      optional (depth + 1) "name" name argName
      expr (depth + 1) "term" term
    | .inferred span argName => do
      node depth key "StaticArg.inferred" span
      optional (depth + 1) "name" name argName
    | .spec span argName term => do
      node depth key "StaticArg.spec" span
      name (depth + 1) "name" argName
      expr (depth + 1) "term" term

  partial def typeExpr (depth : Nat) (key : String) : TypeExpr → DumpM Unit
    | .bool span => node depth key "Type.bool" span
    | .nat span => node depth key "Type.nat" span
    | .rational span => node depth key "Type.rational" span
    | .index span size => do
      node depth key "Type.index" span
      expr (depth + 1) "size" size
    | .nonzero span type => do
      node depth key "Type.nonzero" span
      typeExpr (depth + 1) "type" type
    | .sequence span element size => do
      node depth key "Type.sequence" span
      typeExpr (depth + 1) "element" element
      optional (depth + 1) "size" expr size
    | .tuple span fields => do
      node depth key "Type.tuple" span
      array (depth + 1) "fields" tupleField fields
    | .path span value => do
      node depth key "Type.path" span
      path (depth + 1) "path" value

  partial def tupleField (depth : Nat) (key : String) : TupleField → DumpM Unit
    | .tupleField span fieldName type => do
      node depth key "TupleField" span
      optional (depth + 1) "name" name fieldName
      typeExpr (depth + 1) "type" type

  partial def expr (depth : Nat) (key : String) : Expr → DumpM Unit
    | .ifExpr span condition thenBranch elseBranch => do
      node depth key "IfExpr" span
      expr (depth + 1) "condition" condition
      expr (depth + 1) "then" thenBranch
      expr (depth + 1) "else" elseBranch
    | .orExpr span left right => do
      node depth key "OrExpr" span
      expr (depth + 1) "left" left
      expr (depth + 1) "right" right
    | .andExpr span left right => do
      node depth key "AndExpr" span
      expr (depth + 1) "left" left
      expr (depth + 1) "right" right
    | .notExpr span operand => do
      node depth key "NotExpr" span
      expr (depth + 1) "operand" operand
    | .compare span operator left right => do
      node depth key "Compare" span [compareText operator]
      expr (depth + 1) "left" left
      expr (depth + 1) "right" right
    | .sum span operator left right => do
      node depth key "Sum" span [sumText operator]
      expr (depth + 1) "left" left
      expr (depth + 1) "right" right
    | .product span operator left right => do
      node depth key "Product" span [productText operator]
      expr (depth + 1) "left" left
      expr (depth + 1) "right" right
    | .unary span operand => do
      node depth key "Unary" span
      expr (depth + 1) "operand" operand
    | .power span base exponent => do
      node depth key "Power" span
      expr (depth + 1) "base" base
      expr (depth + 1) "exponent" exponent
    | .field span target fieldName => do
      node depth key "Postfix.field" span
      expr (depth + 1) "target" target
      name (depth + 1) "name" fieldName
    | .method span target methodName staticArgs args => do
      node depth key "Postfix.method" span
      expr (depth + 1) "target" target
      name (depth + 1) "name" methodName
      optional (depth + 1) "staticArgs" staticArgsNode staticArgs
      callArgs (depth + 1) "args" args
    | .position span target position => do
      node depth key "Postfix.position" span
      expr (depth + 1) "target" target
      number (depth + 1) "position" position
    | .index span target index => do
      node depth key "Postfix.index" span
      expr (depth + 1) "target" target
      expr (depth + 1) "index" index
    | .slice span target lower upper => do
      node depth key "Postfix.slice" span
      expr (depth + 1) "target" target
      optional (depth + 1) "lower" expr lower
      optional (depth + 1) "upper" expr upper
    | .number value => number depth key value
    | .byteString value => byteString depth key value
    | .trueLiteral span => node depth key "true" span
    | .falseLiteral span => node depth key "false" span
    | .path span value => do
      node depth key "Primary.path" span
      path (depth + 1) "path" value
    | .call span callee args => do
      node depth key "Primary.call" span
      path (depth + 1) "callee" callee
      callArgs (depth + 1) "args" args
    | .record span type fields => do
      node depth key "Primary.record" span
      path (depth + 1) "type" type
      array (depth + 1) "fields" fieldInit fields
    | .unit span => node depth key "Primary.unit" span
    | .paren span inner => do
      node depth key "Primary.paren" span
      expr (depth + 1) "inner" inner
    | .tuple span components => do
      node depth key "Primary.tuple" span
      array (depth + 1) "components" tupleComponent components
    | .list span elements => do
      node depth key "Primary.list" span
      array (depth + 1) "elements" expr elements
    | .repetition span element count => do
      node depth key "Primary.repetition" span
      expr (depth + 1) "element" element
      expr (depth + 1) "count" count
    | .comprehension span element pattern domain filter => do
      node depth key "Primary.comprehension" span
      expr (depth + 1) "element" element
      patternNode (depth + 1) "pattern" pattern
      domainNode (depth + 1) "domain" domain
      optional (depth + 1) "filter" expr filter
    | .recordUpdate span record fields => do
      node depth key "Primary.recordUpdate" span
      expr (depth + 1) "record" record
      array (depth + 1) "fields" fieldUpdate fields
    | .binderForm span operator spelling pattern domain body => do
      node depth key "Primary.binderForm" span [binderText operator, spellingText spelling]
      patternNode (depth + 1) "pattern" pattern
      domainNode (depth + 1) "domain" domain
      expr (depth + 1) "body" body
    | .innerProduct span spelling left right => do
      node depth key "Primary.innerProduct" span [spellingText spelling]
      expr (depth + 1) "left" left
      expr (depth + 1) "right" right
    | .boolType span => node depth key "Primary.bool" span
    | .natType span => node depth key "Primary.nat" span
    | .rationalType span => node depth key "Primary.rational" span
    | .indexType span size => do
      node depth key "Primary.index" span
      expr (depth + 1) "size" size
    | .nonzeroType span type => do
      node depth key "Primary.nonzero" span
      typeExpr (depth + 1) "type" type

  partial def tupleComponent (depth : Nat) (key : String) : TupleComponent → DumpM Unit
    | .component span componentName value => do
      node depth key "TupleComponent" span
      optional (depth + 1) "name" name componentName
      expr (depth + 1) "value" value

  partial def callArgs (depth : Nat) (key : String) : CallArgs → DumpM Unit
    | .callArgs span arguments witnesses => do
      node depth key "CallArgs" span
      array (depth + 1) "arguments" argument arguments
      optional (depth + 1) "witnesses" (fun d k xs => array d k argument xs) witnesses

  partial def argument (depth : Nat) (key : String) : Argument → DumpM Unit
    | .positional span value => do
      node depth key "Argument.positional" span
      expr (depth + 1) "value" value
    | .named span argName value => do
      node depth key "Argument.named" span
      name (depth + 1) "name" argName
      expr (depth + 1) "value" value
    | .spec span argName value => do
      node depth key "Argument.spec" span
      name (depth + 1) "name" argName
      expr (depth + 1) "value" value

  partial def fieldInit (depth : Nat) (key : String) : FieldInit → DumpM Unit
    | .fieldInit span fieldName value => do
      node depth key "FieldInit" span
      name (depth + 1) "name" fieldName
      optional (depth + 1) "value" expr value

  partial def fieldUpdate (depth : Nat) (key : String) : FieldUpdate → DumpM Unit
    | .fieldUpdate span fieldName value => do
      node depth key "FieldUpdate" span
      name (depth + 1) "name" fieldName
      expr (depth + 1) "value" value

  partial def domainNode (depth : Nat) (key : String) : Domain → DumpM Unit
    | .domain span start stop => do
      node depth key "Domain" span
      expr (depth + 1) "start" start
      optional (depth + 1) "stop" expr stop

  partial def patternNode (depth : Nat) (key : String) : Pattern → DumpM Unit
    | .name value => do
      emit depth s!"{key}: Pattern.name {quote value.text}{← spanText value.span}"
    | .wildcard span => node depth key "Pattern.wildcard" span
    | .tuple span items => do
      node depth key "Pattern.tuple" span
      array (depth + 1) "items" patternNode items
    | .record span type fields => do
      node depth key "Pattern.record" span
      path (depth + 1) "type" type
      array (depth + 1) "fields" fieldPattern fields

  partial def fieldPattern (depth : Nat) (key : String) : FieldPattern → DumpM Unit
    | .fieldPattern span fieldName pattern => do
      node depth key "FieldPattern" span
      name (depth + 1) "name" fieldName
      optional (depth + 1) "pattern" patternNode pattern
end

partial def casePattern (depth : Nat) (key : String) : CasePattern → DumpM Unit
  | .pattern value => patternNode depth key value
  | .number value => number depth key value
  | .trueLiteral span => node depth key "true" span
  | .falseLiteral span => node depth key "false" span
  | .variant span value payload => do
    node depth key "CasePattern.variant" span
    path (depth + 1) "path" value
    optional (depth + 1) "payload" (fun d k xs => array d k casePattern xs) payload
  | .tuple span items => do
    node depth key "CasePattern.tuple" span
    array (depth + 1) "items" casePattern items

def sortExpr (depth : Nat) (key : String) : SortExpr → DumpM Unit
  | .nat span => node depth key "Sort.nat" span
  | .linear span => node depth key "Sort.linear" span
  | .path value => path depth key value

def bound (depth : Nat) (key : String) (value : Bound) : DumpM Unit := do
  node depth key "Bound" value.span
  array (depth + 1) "sorts" sortExpr value.sorts

def staticParam (depth : Nat) (key : String) (value : StaticParam) : DumpM Unit := do
  node depth key "StaticParam" value.span [flag "spec" value.spec]
  name (depth + 1) "name" value.name
  optional (depth + 1) "bound" bound value.bound

def staticParams (depth : Nat) (key : String) (value : StaticParams) : DumpM Unit := do
  node depth key "StaticParams" value.span
  array (depth + 1) "params" staticParam value.params

def constraint (depth : Nat) (key : String) : Constraint → DumpM Unit
  | .bound span subject value => do
    node depth key "Constraint.bound" span
    expr (depth + 1) "subject" subject
    bound (depth + 1) "bound" value
  | .compare span operator left right => do
    node depth key "Constraint.compare" span [compareText operator]
    expr (depth + 1) "left" left
    expr (depth + 1) "right" right

def whereNode (depth : Nat) (key : String) (value : Where) : DumpM Unit := do
  node depth key "Where" value.span
  array (depth + 1) "constraints" constraint value.constraints

def holders (depth : Nat) (key : String) : Holders → DumpM Unit
  | .role value => do emit depth s!"{key}: Holders.role {quote value.text}{← spanText value.span}"
  | .roles span roles => do
    node depth key "Holders.roles" span
    array (depth + 1) "roles" name roles

def placement (depth : Nat) (key : String) (value : Placement) : DumpM Unit := do
  node depth key "Placement" value.span
  holders (depth + 1) "holders" value.holders
  optional (depth + 1) "readers" holders value.readers

def reason (depth : Nat) (key : String) : Reason → DumpM Unit
  | .reject span => node depth key "reject" span
  | .abort span => node depth key "abort" span
  | .refused span => node depth key "refused" span
  | .exhausted span => node depth key "exhausted" span

def siteAttr (depth : Nat) (key : String) (value : SiteAttr) : DumpM Unit := do
  node depth key "SiteAttr" value.span
  name (depth + 1) "name" value.name

def roleMapEntry (depth : Nat) (key : String) (value : RoleMapEntry) : DumpM Unit := do
  node depth key "RoleMapEntry" value.span
  name (depth + 1) "callee" value.callee
  name (depth + 1) "caller" value.caller

def roleMap (depth : Nat) (key : String) (value : RoleMap) : DumpM Unit := do
  node depth key "RoleMap" value.span
  array (depth + 1) "entries" roleMapEntry value.entries

def application (depth : Nat) (key : String) (value : Application) : DumpM Unit := do
  node depth key "Application" value.span
  path (depth + 1) "callee" value.callee
  callArgs (depth + 1) "args" value.args
  optional (depth + 1) "roleMap" roleMap value.roleMap

def event (depth : Nat) (key : String) : Event → DumpM Unit
  | .send span payload sender receivers oracle => do
    node depth key "Send" span
    expr (depth + 1) "payload" payload
    optional (depth + 1) "from" name sender
    array (depth + 1) "to" name receivers
    optional (depth + 1) "oracle" expr oracle
  | .draw span type sender receivers => do
    node depth key "Draw" span
    typeExpr (depth + 1) "type" type
    name (depth + 1) "from" sender
    array (depth + 1) "to" name receivers
  | .sample span type => do
    node depth key "Sample" span
    typeExpr (depth + 1) "type" type
  | .query span handle opener positions deferred => do
    node depth key "Query" span [flag "deferred" deferred]
    expr (depth + 1) "handle" handle
    optional (depth + 1) "from" name opener
    expr (depth + 1) "at" positions
  | .attempt span => node depth key "Attempt" span
  | .application value => application depth key value

def eventStmt (depth : Nat) (key : String) : EventStmt → DumpM Unit
  | .bound span site pattern type holdersValue eventValue => do
    node depth key "EventStmt.bound" span
    optional (depth + 1) "site" siteAttr site
    patternNode (depth + 1) "pattern" pattern
    optional (depth + 1) "type" typeExpr type
    optional (depth + 1) "holders" holders holdersValue
    event (depth + 1) "event" eventValue
  | .application span site value => do
    node depth key "EventStmt.application" span
    optional (depth + 1) "site" siteAttr site
    application (depth + 1) "application" value

def claim (depth : Nat) (key : String) (value : Claim) : DumpM Unit := do
  node depth key "Claim" value.span
  expr (depth + 1) "handle" value.handle
  match value.opening with
  | some opening => do
    node (depth + 1) "opening" "ClaimOpening" opening.span
    expr (depth + 2) "position" opening.position
    expr (depth + 2) "value" opening.value
  | none => absent (depth + 1) "opening"

def collected (depth : Nat) (key : String) (value : Collected) : DumpM Unit := do
  node depth key "Collected" value.span
  name (depth + 1) "name" value.name
  expr (depth + 1) "value" value.value

mutual
  partial def stmt (depth : Nat) (key : String) : Stmt → DumpM Unit
    | .binding span pattern type holdersValue value => do
      node depth key "Binding" span
      patternNode (depth + 1) "pattern" pattern
      optional (depth + 1) "type" typeExpr type
      optional (depth + 1) "holders" holders holdersValue
      expr (depth + 1) "value" value
    | .mutDecl span mutName type placementValue value => do
      node depth key "MutDecl" span
      name (depth + 1) "name" mutName
      optional (depth + 1) "type" typeExpr type
      optional (depth + 1) "placement" placement placementValue
      expr (depth + 1) "value" value
    | .update span updateName value => do
      node depth key "Update" span
      name (depth + 1) "name" updateName
      expr (depth + 1) "value" value
    | .eventStmt value => eventStmt depth key value
    | .«open» span site claims => do
      node depth key "Open" span
      optional (depth + 1) "site" siteAttr site
      array (depth + 1) "claims" claim claims
    | .guard span holdersValue condition reasonValue => do
      node depth key "Guard" span
      optional (depth + 1) "holders" holders holdersValue
      expr (depth + 1) "condition" condition
      optional (depth + 1) "reason" reason reasonValue
    | .«if» span condition thenSuite elseBranch => do
      node depth key "If" span
      expr (depth + 1) "condition" condition
      array (depth + 1) "then" stmt thenSuite
      optional (depth + 1) "else" elseNode elseBranch
    | .«match» span scrutinee cases => do
      node depth key "Match" span
      expr (depth + 1) "scrutinee" scrutinee
      array (depth + 1) "cases" caseNode cases
    | .«for» span pattern domain collectedValues body => do
      node depth key "For" span
      patternNode (depth + 1) "pattern" pattern
      domainNode (depth + 1) "domain" domain
      optional (depth + 1) "collect" (fun d k xs => array d k collected xs) collectedValues
      array (depth + 1) "body" stmt body
    | .empty span => node depth key "Empty" span

  partial def elseNode (depth : Nat) (key : String) : ElseBranch → DumpM Unit
    | .suite span statements => do
      node depth key "Else.suite" span
      array (depth + 1) "statements" stmt statements
    | .elseIf statement => stmt depth key statement

  partial def caseNode (depth : Nat) (key : String) : Case → DumpM Unit
    | .«case» span pattern body => do
      node depth key "Case" span
      casePattern (depth + 1) "pattern" pattern
      array (depth + 1) "body" stmt body
end

def param (depth : Nat) (key : String) (value : Param) : DumpM Unit := do
  node depth key "Param" value.span
  name (depth + 1) "name" value.name
  typeExpr (depth + 1) "type" value.type

def primitive (depth : Nat) (key : String) (value : Primitive) : DumpM Unit := do
  node depth key "Primitive" value.span
  stringLiteral (depth + 1) "row" value.row
  array (depth + 1) "args" staticArg value.args

def asset (depth : Nat) (key : String) (value : Asset) : DumpM Unit := do
  node depth key "Asset" value.span
  name (depth + 1) "name" value.name

def external (depth : Nat) (key : String) (value : External) : DumpM Unit := do
  node depth key "External" value.span
  stringLiteral (depth + 1) "name" value.name

def kernelAttr (depth : Nat) (key : String) (value : KernelAttr) : DumpM Unit := do
  node depth key "KernelAttr" value.span
  stringLiteral (depth + 1) "name" value.name

def body (depth : Nat) (key : String) : Body → DumpM Unit
  | .expression span value => do
    node depth key "Body.expression" span
    expr (depth + 1) "value" value
  | .suiteExpression span value => do
    node depth key "Body.suiteExpression" span
    expr (depth + 1) "value" value
  | .statements span statements result => do
    node depth key "Body.statements" span
    array (depth + 1) "statements" stmt statements
    expr (depth + 1) "return" result

def defBinding (depth : Nat) (key : String) : DefBinding → DumpM Unit
  | .body value => body depth key value
  | .primitive value => primitive depth key value
  | .external value => external depth key value

def defNode (depth : Nat) (key : String) (value : Def) : DumpM Unit := do
  let modifier := match value.modifier with
    | some (.spec _) => "spec" | some (.entry _) => "entry" | none => "-"
  node depth key "Def" value.span [flag "pub" value.pub, s!"modifier={modifier}"]
  optional (depth + 1) "kernel" kernelAttr value.kernel
  name (depth + 1) "name" value.name
  optional (depth + 1) "staticParams" staticParams value.staticParams
  array (depth + 1) "params" param value.params
  optional (depth + 1) "result" typeExpr value.result
  optional (depth + 1) "where" whereNode value.whereClause
  defBinding (depth + 1) "binding" value.binding

def port (depth : Nat) (key : String) : Port → DumpM Unit
  | .port span portName type placementValue isPrivate => do
    node depth key "Port" span [flag "private" isPrivate]
    name (depth + 1) "name" portName
    typeExpr (depth + 1) "type" type
    placement (depth + 1) "placement" placementValue
  | .spec span portName type => do
    node depth key "Port.spec" span
    name (depth + 1) "name" portName
    typeExpr (depth + 1) "type" type

def result (depth : Nat) (key : String) (value : Result) : DumpM Unit := do
  node depth key "Result" value.span
  name (depth + 1) "name" value.name
  typeExpr (depth + 1) "type" value.type
  placement (depth + 1) "placement" value.placement

def results (depth : Nat) (key : String) : Results → DumpM Unit
  | .one value => result depth key value
  | .several span values => do
    node depth key "Results" span
    array (depth + 1) "results" result values

def protocolHead (depth : Nat) (key : String) (value : ProtocolHead) : DumpM Unit := do
  node depth key "ProtocolHead" value.span
  name (depth + 1) "name" value.name
  optional (depth + 1) "staticParams" staticParams value.staticParams
  array (depth + 1) "roles" name value.roles
  array (depth + 1) "ports" port value.ports
  optional (depth + 1) "results" results value.results
  optional (depth + 1) "where" whereNode value.whereClause

def protocol (depth : Nat) (key : String) (value : Protocol) : DumpM Unit := do
  node depth key "Protocol" value.span [flag "pub" value.pub, flag "spec" value.spec]
  protocolHead (depth + 1) "head" value.head
  array (depth + 1) "body" stmt value.body
  optional (depth + 1) "return" expr value.result

def typeDecl (depth : Nat) (key : String) : TypeDecl → DumpM Unit
  | .type span pub declName params value => do
    node depth key "TypeDecl" span [flag "pub" pub]
    name (depth + 1) "name" declName
    optional (depth + 1) "staticParams" staticParams params
    match value with
    | .type type => typeExpr (depth + 1) "type" type
    | .primitive prim => primitive (depth + 1) "primitive" prim
  | .specType span pub declName params ext => do
    node depth key "TypeDecl.spec" span [flag "pub" pub]
    name (depth + 1) "name" declName
    optional (depth + 1) "staticParams" staticParams params
    external (depth + 1) "external" ext

def field (depth : Nat) (key : String) (value : Field) : DumpM Unit := do
  node depth key "Field" value.span [flag "pub" value.pub]
  name (depth + 1) "name" value.name
  typeExpr (depth + 1) "type" value.type

def struct (depth : Nat) (key : String) (value : Struct) : DumpM Unit := do
  node depth key "Struct" value.span [flag "pub" value.pub, flag "linear" value.linear]
  name (depth + 1) "name" value.name
  optional (depth + 1) "staticParams" staticParams value.staticParams
  array (depth + 1) "fields" field value.fields

def alternative (depth : Nat) (key : String) (value : Alternative) : DumpM Unit := do
  node depth key "Alternative" value.span
  name (depth + 1) "name" value.name
  array (depth + 1) "payload" typeExpr value.payload

def enum (depth : Nat) (key : String) (value : Enum) : DumpM Unit := do
  node depth key "Enum" value.span [flag "pub" value.pub]
  name (depth + 1) "name" value.name
  optional (depth + 1) "staticParams" staticParams value.staticParams
  array (depth + 1) "alternatives" alternative value.alternatives

def law (depth : Nat) (key : String) (value : Law) : DumpM Unit := do
  node depth key "Law" value.span
  name (depth + 1) "name" value.name
  optional (depth + 1) "staticParams" staticParams value.staticParams
  array (depth + 1) "params" param value.params
  optional (depth + 1) "where" whereNode value.whereClause
  body (depth + 1) "body" value.body

def member (depth : Nat) (key : String) : Member → DumpM Unit
  | .typeMember span memberName params boundValue => do
    node depth key "Member.type" span
    name (depth + 1) "name" memberName
    optional (depth + 1) "staticParams" staticParams params
    optional (depth + 1) "bound" bound boundValue
  | .natMember span memberName => do
    node depth key "Member.nat" span
    name (depth + 1) "name" memberName
  | .moduleMember span memberName boundValue => do
    node depth key "Member.module" span
    name (depth + 1) "name" memberName
    bound (depth + 1) "bound" boundValue
  | .defMember span modifier memberName params parameters resultType whereClause => do
    let modifierText := match modifier with
      | some (.«partial» _) => "partial" | some (.spec _) => "spec" | none => "-"
    node depth key "Member.def" span [s!"modifier={modifierText}"]
    name (depth + 1) "name" memberName
    optional (depth + 1) "staticParams" staticParams params
    array (depth + 1) "params" param parameters
    optional (depth + 1) "result" typeExpr resultType
    optional (depth + 1) "where" whereNode whereClause
  | .protocolMember head => protocolHead depth key head
  | .lawMember value => law depth key value

def interface (depth : Nat) (key : String) (value : Interface) : DumpM Unit := do
  node depth key "Interface" value.span [flag "pub" value.pub]
  name (depth + 1) "name" value.name
  optional (depth + 1) "staticParams" staticParams value.staticParams
  optional (depth + 1) "where" whereNode value.whereClause
  optional (depth + 1) "members" (fun d k xs => array d k member xs) value.members

def oracleDef (depth : Nat) (key : String) (value : OracleDef) : DumpM Unit := do
  node depth key "OracleDef" value.span [flag "pub" value.pub]
  name (depth + 1) "name" value.name
  optional (depth + 1) "staticParams" staticParams value.staticParams
  array (depth + 1) "params" param value.params
  path (depth + 1) "kind" value.kind
  optional (depth + 1) "where" whereNode value.whereClause
  name (depth + 1) "at" value.position
  expr (depth + 1) "row" value.row

def relation (depth : Nat) (key : String) (value : Relation) : DumpM Unit := do
  node depth key "Relation" value.span [flag "pub" value.pub]
  name (depth + 1) "name" value.name
  optional (depth + 1) "staticParams" staticParams value.staticParams
  array (depth + 1) "statement" param value.statement
  optional (depth + 1) "witness" (fun d k xs => array d k param xs) value.witness
  optional (depth + 1) "where" whereNode value.whereClause
  match value.binding with
  | .body value => body (depth + 1) "body" value
  | .external value => external (depth + 1) "external" value

def siteRef (depth : Nat) (key : String) (value : SiteRef) : DumpM Unit := do
  node depth key "SiteRef" value.span
  array (depth + 1) "names" name value.names

def label (depth : Nat) (key : String) (value : Label) : DumpM Unit := do
  node depth key "Label" value.span
  name (depth + 1) "name" value.name

def extractor (depth : Nat) (key : String) : Extractor → DumpM Unit
  | .path value => path depth key value
  | .external span value => do
    node depth key "Extractor.external" span
    stringLiteral (depth + 1) "name" value

def ability : Ability → String
  | .coins _ => "coins" | .programming _ => "programming" | .trapdoor _ => "trapdoor"

def clause (depth : Nat) (key : String) : Clause → DumpM Unit
  | .requires span labelValue condition => do
    node depth key "Clause.requires" span
    optional (depth + 1) "label" label labelValue
    expr (depth + 1) "condition" condition
  | .ensures span labelValue condition => do
    node depth key "Clause.ensures" span
    optional (depth + 1) "label" label labelValue
    expr (depth + 1) "condition" condition
  | .invariant span labelValue condition loop => do
    node depth key "Clause.invariant" span
    optional (depth + 1) "label" label labelValue
    expr (depth + 1) "condition" condition
    name (depth + 1) "at" loop
  | .reduces span role labelValue source target => do
    node depth key "Clause.reduces" span
    optional (depth + 1) "role" name role
    optional (depth + 1) "label" label labelValue
    expr (depth + 1) "source" source
    expr (depth + 1) "target" target
  | .proves span role labelValue relationValue => do
    node depth key "Clause.proves" span
    optional (depth + 1) "role" name role
    optional (depth + 1) "label" label labelValue
    expr (depth + 1) "relation" relationValue
  | .through span relationValue loop => do
    node depth key "Clause.through" span
    expr (depth + 1) "relation" relationValue
    name (depth + 1) "at" loop
  | .knowledge span labelValue relationValue extractorValue alternative => do
    node depth key "Clause.knowledge" span
    optional (depth + 1) "label" label labelValue
    expr (depth + 1) "relation" relationValue
    extractor (depth + 1) "by" extractorValue
    match alternative with
    | some value => do
      node (depth + 1) "or" "KnowledgeAlternative" value.span
      expr (depth + 2) "relation" value.relation
      optional (depth + 2) "by" path value.extractor
    | none => absent (depth + 1) "or"
  | .zeroKnowledge span labelValue simulator abilities => do
    node depth key "Clause.zeroKnowledge" span (abilities.toList.map ability)
    optional (depth + 1) "label" label labelValue
    extractor (depth + 1) "by" simulator
  | .charge span site boundValue => do
    node depth key "Clause.charge" span
    siteRef (depth + 1) "site" site
    expr (depth + 1) "bound" boundValue

def contract (depth : Nat) (key : String) (value : Contract) : DumpM Unit := do
  node depth key "Contract" value.span
  path (depth + 1) "target" value.target
  array (depth + 1) "clauses" clause value.clauses

def adjust (depth : Nat) (key : String) : Adjust → DumpM Unit
  | .carry span site => do
    node depth key "Adjust.carry" span
    siteRef (depth + 1) "site" site
  | .recover span site recovery => do
    node depth key "Adjust.recover" span
    siteRef (depth + 1) "site" site
    path (depth + 1) "by" recovery

def key (depth : Nat) (fieldKey : String) (value : Key) : DumpM Unit := do
  let kind := match value.kind with | .proverKey => "prover_key" | .verifierKey => "verifier_key"
  node depth fieldKey "Key" value.span [kind]
  siteRef (depth + 1) "site" value.site

def schemeLine (depth : Nat) (fieldKey : String) : SchemeLine → DumpM Unit
  | .construction span construction => do
    match construction with
    | .derived innerSpan suitePath => do
      node depth fieldKey "SchemeLine.construction" span ["derived"]
      emit (depth + 1) s!"construction:{← spanText innerSpan}"
      path (depth + 1) "suite" suitePath
    | .interactive _ => node depth fieldKey "SchemeLine.construction" span ["interactive"]
    | .authored _ => node depth fieldKey "SchemeLine.construction" span ["authored"]
  | .prover span role => do
    node depth fieldKey "SchemeLine.prover" span
    name (depth + 1) "role" role
  | .offline span roles => do
    node depth fieldKey "SchemeLine.offline" span
    array (depth + 1) "roles" name roles
  | .ideal span roles => do
    node depth fieldKey "SchemeLine.ideal" span
    array (depth + 1) "roles" name roles
  | .context span contextName type => do
    node depth fieldKey "SchemeLine.context" span
    name (depth + 1) "name" contextName
    typeExpr (depth + 1) "type" type
  | .commit span subject scheme keys => do
    node depth fieldKey "SchemeLine.commit" span
    match subject with
    | .term term => expr (depth + 1) "subject" term
    | .site site => siteRef (depth + 1) "subject" site
    path (depth + 1) "with" scheme
    optional (depth + 1) "keys" (fun d k xs => array d k key xs) keys
  | .pin span site hash digest => do
    node depth fieldKey "SchemeLine.pin" span
    siteRef (depth + 1) "site" site
    path (depth + 1) "hash" hash
    byteString (depth + 1) "digest" digest
  | .grind span bits sites => do
    node depth fieldKey "SchemeLine.grind" span
    expr (depth + 1) "bits" bits
    array (depth + 1) "sites" siteRef sites
  | .retry span count site => do
    node depth fieldKey "SchemeLine.retry" span
    expr (depth + 1) "count" count
    siteRef (depth + 1) "site" site
  | .samples span derivation => do
    node depth fieldKey "SchemeLine.samples" span
    path (depth + 1) "by" derivation
  | .layout span layout adjustments => do
    node depth fieldKey "SchemeLine.layout" span
    path (depth + 1) "layout" layout
    optional (depth + 1) "adjust" (fun d k xs => array d k adjust xs) adjustments

def scheme (depth : Nat) (key : String) (value : Scheme) : DumpM Unit := do
  node depth key "Scheme" value.span [flag "pub" value.pub]
  name (depth + 1) "name" value.name
  path (depth + 1) "protocol" value.protocol
  array (depth + 1) "lines" schemeLine value.lines

partial def goalValue (depth : Nat) (key : String) : GoalValue → DumpM Unit
  | .path span value args => do
    node depth key "GoalValue.path" span
    path (depth + 1) "path" value
    optional (depth + 1) "args" callArgs args
  | .tuple span items => do
    node depth key "GoalValue.tuple" span
    array (depth + 1) "items" goalValue items

def goalArg (depth : Nat) (key : String) : GoalArg → DumpM Unit
  | .named span argName value => do
    node depth key "GoalArg.named" span
    name (depth + 1) "name" argName
    goalValue (depth + 1) "value" value
  | .spec span argName size => do
    node depth key "GoalArg.spec" span
    name (depth + 1) "name" argName
    expr (depth + 1) "size" size

def goal (depth : Nat) (key : String) (value : Goal) : DumpM Unit := do
  node depth key "Goal" value.span [flag "pub" value.pub]
  name (depth + 1) "name" value.name
  path (depth + 1) "property" value.property
  path (depth + 1) "scheme" value.scheme
  array (depth + 1) "args" goalArg value.args
  optional (depth + 1) "ceiling" expr value.ceiling

def staticName (depth : Nat) (key : String) (value : StaticName) : DumpM Unit := do
  node depth key "StaticName" value.span [flag "pub" value.pub]
  name (depth + 1) "name" value.name
  expr (depth + 1) "size" value.size

def useNode (depth : Nat) (key : String) (value : Use) : DumpM Unit := do
  node depth key "Use" value.span [flag "pub" value.pub]
  path (depth + 1) "path" value.path
  match value.tail with
  | .whole => absent (depth + 1) "tail"
  | .alias aliasName => name (depth + 1) "as" aliasName
  | .names span names => do
    node (depth + 1) "names" "UseNames" span
    array (depth + 2) "names" name names

def moduleMember (depth : Nat) (key : String) (value : ModuleMember) : DumpM Unit := do
  node depth key "ModuleMember" value.span
  name (depth + 1) "name" value.name
  path (depth + 1) "path" value.path

def memberDef (depth : Nat) (key : String) (value : MemberDef) : DumpM Unit := do
  node depth key "MemberDef" value.span [flag "spec" value.spec]
  optional (depth + 1) "kernel" kernelAttr value.kernel
  name (depth + 1) "name" value.name
  array (depth + 1) "params" name value.params
  defBinding (depth + 1) "binding" value.binding

mutual
  partial def item (depth : Nat) (key : String) : Item → DumpM Unit
    | .use value => useNode depth key value
    | .«section» value => sectionNode depth key value
    | .«module» value => moduleNode depth key value
    | .interface value => interface depth key value
    | .typeDecl value => typeDecl depth key value
    | .struct value => struct depth key value
    | .enum value => enum depth key value
    | .«def» value => defNode depth key value
    | .oracleDef value => oracleDef depth key value
    | .protocol value => protocol depth key value
    | .relation value => relation depth key value
    | .contract value => contract depth key value
    | .scheme value => scheme depth key value
    | .goal value => goal depth key value
    | .law value => law depth key value
    | .staticName value => staticName depth key value

  partial def sectionNode (depth : Nat) (key : String) : Section → DumpM Unit
    | .«section» span params whereClause items => do
      node depth key "Section" span
      optional (depth + 1) "staticParams" staticParams params
      optional (depth + 1) "where" whereNode whereClause
      array (depth + 1) "items" item items

  partial def moduleNode (depth : Nat) (key : String) : Module → DumpM Unit
    | .«module» span pub moduleName params boundValue whereClause moduleBody => do
      node depth key "Module" span [flag "pub" pub]
      name (depth + 1) "name" moduleName
      optional (depth + 1) "staticParams" staticParams params
      optional (depth + 1) "bound" bound boundValue
      optional (depth + 1) "where" whereNode whereClause
      match moduleBody with
      | .suite items => array (depth + 1) "items" moduleItem items
      | .primitive value => primitive (depth + 1) "primitive" value
      | .asset value => asset (depth + 1) "asset" value

  partial def moduleItem (depth : Nat) (key : String) : ModuleItem → DumpM Unit
    | .item value => item depth key value
    | .moduleMember value => moduleMember depth key value
    | .memberDef value => memberDef depth key value
end

def file (value : File) : DumpM Unit := do
  node 0 "file" "File" value.span
  node 1 "path" "ModulePath" value.path.span
  array 2 "names" name value.path.names
  optional 1 "staticParams" staticParams value.staticParams
  optional 1 "where" whereNode value.whereClause
  array 1 "items" item value.items

end Dump

/-- The tree in its stable text form, with spans or without. -/
def dumpFile (tree : File) (withSpans : Bool := true) : String :=
  let ((), state) := (Dump.file tree).run { withSpans, lines := #[] }
  String.intercalate "\n" state.lines.toList ++ "\n"

end Zkc.Frontend.Syntax
