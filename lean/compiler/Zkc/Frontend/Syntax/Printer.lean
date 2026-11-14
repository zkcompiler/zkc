module

public import Zkc.Frontend.Syntax.Spans
public import Zkc.Frontend.Syntax.Layout

@[expose] public section

set_option autoImplicit false

/-!
# The printer (§3.6)

Prints a tree as text with the layout of FM1: four spaces per suite, the spacing of operators
and punctuation, logical lines broken at 100 characters by `Layout`. It prints the tree as it
is: every alternative as recorded, every parenthesis the tree holds, each mathematical form in
the spelling it records. The annotations that FM2 removes are removed by `canonicalize`, not
here; the formatter is `print ∘ canonicalize`.

Comments are not tokens and are not in the tree. The printer places each comment of the source
before the first line-level construct that starts after it (an item, a member, a field, an
alternative, a statement, a case, a clause, a scheme line), at the indentation of that
construct, and the comments after the last construct at the end of the file. Blank lines:
exactly one between top-level items, except that consecutive `use` items keep the source's
choice; elsewhere one blank line where the source has one or more, and none at the start of a
suite.
-/

namespace Zkc.Frontend.Syntax.Printer

open Layout

/-! ## Logical lines as atoms -/

abbrev LineM := StateM (Array Atom)

def t (text : String) : LineM Unit := modify (·.push (.text text))

def opening (text : String) : LineM Unit := modify (·.push (.opening text))

def closing (text : String) : LineM Unit := modify (·.push (.closing text))

def comma : LineM Unit := modify (·.push .comma)

/-- A bracket whose items are separated by commas. -/
def group {α : Type} (open_ close : String) (items : Array α) (item : α → LineM Unit) :
    LineM Unit := do
  opening open_
  let mut first := true
  for value in items do
    unless first do comma
    item value
    first := false
  closing close

def joinedText {α : Type} (separator : String) (items : Array α) (item : α → LineM Unit) :
    LineM Unit := do
  let mut first := true
  for value in items do
    unless first do t separator
    item value
    first := false

def name (value : Name) : LineM Unit := t value.text

def stringLiteral (value : StringLiteral) : LineM Unit := t s!"\"{value.content}\""

def byteString (value : ByteString) : LineM Unit :=
  match value.kind with
  | .bytes => t s!"b\"{value.content}\""
  | .hex => t s!"hex\"{value.content}\""

def compareText : CompareOperator → String
  | .equal => " == " | .notEqual => " != " | .less => " < " | .lessEqual => " <= "
  | .greater => " > " | .greaterEqual => " >= "

def binderSymbol : BinderOperator → String
  | .sum => "∑" | .product => "∏" | .all => "∀" | .any => "∃"

def binderName : BinderOperator → String
  | .sum => "sum" | .product => "product" | .all => "all" | .any => "any"

mutual
  partial def path : Path → LineM Unit
    | .path _ segments => joinedText "::" segments segment

  partial def segment : Segment → LineM Unit
    | .segment _ segmentName staticArgs => do
      name segmentName
      if let some args := staticArgs then staticArgsAtoms args

  partial def staticArgsAtoms : StaticArgs → LineM Unit
    | .staticArgs _ args => group "<" ">" args staticArg

  partial def staticArg : StaticArg → LineM Unit
    | .term _ argName term => do
      if let some value := argName then name value; t " = "
      expr term
    | .inferred _ argName => do
      if let some value := argName then name value; t " = "
      t "_"
    | .spec _ argName term => do
      t "spec "; name argName; t " = "; expr term

  partial def typeExpr : TypeExpr → LineM Unit
    | .bool _ => t "bool"
    | .nat _ => t "nat"
    | .rational _ => t "rational"
    | .index _ size => do t "index"; group "<" ">" #[size] expr
    | .nonzero _ type => do t "nonzero"; group "<" ">" #[type] typeExpr
    | .sequence _ element size => do
      opening "["
      typeExpr element
      if let some value := size then t "; "; expr value
      closing "]"
    | .tuple _ fields => group "(" ")" fields tupleField
    | .path _ value => path value

  partial def tupleField : TupleField → LineM Unit
    | .tupleField _ fieldName type => do
      if let some value := fieldName then name value; t ": "
      typeExpr type

  partial def expr : Expr → LineM Unit
    | .ifExpr _ condition thenBranch elseBranch => do
      t "if "; expr condition; t " then "; expr thenBranch; t " else "; expr elseBranch
    | .orExpr _ left right => do expr left; t " or "; expr right
    | .andExpr _ left right => do expr left; t " and "; expr right
    | .notExpr _ operand => do t "not "; expr operand
    | .compare _ operator left right => do expr left; t (compareText operator); expr right
    | .sum _ operator left right => do
      expr left
      t (match operator with | .add => " + " | .subtract => " - " | .concatenate => " ++ ")
      expr right
    | .product _ operator left right => do
      expr left
      t (match operator with | .multiply => " * " | .divide => " / " | .remainder => " % ")
      expr right
    | .unary _ operand => do t "-"; expr operand
    | .power _ base exponent => do expr base; t "^"; expr exponent
    | .field _ target fieldName => do expr target; t "."; name fieldName
    | .method _ target methodName staticArgs args => do
      expr target; t "."; name methodName
      if let some value := staticArgs then staticArgsAtoms value
      callArgs args
    | .position _ target position => do expr target; t s!".{position.value}"
    | .index _ target index => do expr target; group "[" "]" #[index] expr
    | .slice _ target lower upper => do
      expr target
      opening "["
      if let some value := lower then expr value
      t ".."
      if let some value := upper then expr value
      closing "]"
    | .number value => t (toString value.value)
    | .byteString value => byteString value
    | .trueLiteral _ => t "true"
    | .falseLiteral _ => t "false"
    | .path _ value => path value
    | .call _ callee args => do path callee; callArgs args
    | .record _ type fields => do path type; group "{" "}" fields fieldInit
    | .unit _ => t "()"
    | .paren _ inner => group "(" ")" #[inner] expr
    | .tuple _ components => group "(" ")" components tupleComponent
    | .list _ elements => group "[" "]" elements expr
    | .repetition _ element count => do
      opening "["; expr element; t "; "; expr count; closing "]"
    | .comprehension _ element pattern domain filter => do
      opening "["
      comprehensionBody element pattern domain filter
      closing "]"
    | .recordUpdate _ record fields => do
      opening "{"
      expr record
      t " with "
      let mut first := true
      for field in fields do
        unless first do comma
        fieldUpdate field
        first := false
      closing "}"
    | .binderForm _ operator spelling pattern domain body =>
      match spelling with
      | .symbol => do
        t s!"{binderSymbol operator} "; patternAtoms pattern; t " ∈ "; domainAtoms domain
        t ", "; expr body
      | .named => do
        t (binderName operator)
        opening "("
        opening "["
        comprehensionBody body pattern domain none
        closing "]"
        closing ")"
    | .innerProduct _ spelling left right =>
      match spelling with
      | .symbol => group "⟪" "⟫" #[left, right] expr
      | .named => do t "inner"; group "(" ")" #[left, right] expr
    | .boolType _ => t "bool"
    | .natType _ => t "nat"
    | .rationalType _ => t "rational"
    | .indexType _ size => do t "index"; group "<" ">" #[size] expr
    | .nonzeroType _ type => do t "nonzero"; group "<" ">" #[type] typeExpr

  partial def comprehensionBody (element : Expr) (pattern : Pattern) (domain : Domain)
      (filter : Option Expr) : LineM Unit := do
    expr element; t " for "; patternAtoms pattern; t " in "; domainAtoms domain
    if let some value := filter then t " if "; expr value

  partial def tupleComponent : TupleComponent → LineM Unit
    | .component _ componentName value => do
      if let some label := componentName then name label; t ": "
      expr value

  partial def callArgs : CallArgs → LineM Unit
    | .callArgs _ arguments witnesses => do
      opening "("
      let mut first := true
      for value in arguments do
        unless first do comma
        argument value
        first := false
      if let some values := witnesses then
        t "; "
        let mut firstWitness := true
        for value in values do
          unless firstWitness do comma
          argument value
          firstWitness := false
      closing ")"

  partial def argument : Argument → LineM Unit
    | .positional _ value => expr value
    | .named _ argName value => do name argName; t " = "; expr value
    | .spec _ argName value => do t "spec "; name argName; t " = "; expr value

  partial def fieldInit : FieldInit → LineM Unit
    | .fieldInit _ fieldName value => do
      name fieldName
      if let some v := value then t " = "; expr v

  partial def fieldUpdate : FieldUpdate → LineM Unit
    | .fieldUpdate _ fieldName value => do name fieldName; t " = "; expr value

  partial def domainAtoms : Domain → LineM Unit
    | .domain _ start stop => do
      expr start
      if let some value := stop then t ".."; expr value

  partial def patternAtoms : Pattern → LineM Unit
    | .name value => name value
    | .wildcard _ => t "_"
    | .tuple _ items => group "(" ")" items patternAtoms
    | .record _ type fields => do path type; group "{" "}" fields fieldPattern

  partial def fieldPattern : FieldPattern → LineM Unit
    | .fieldPattern _ fieldName pattern => do
      name fieldName
      if let some value := pattern then t " = "; patternAtoms value
end

partial def casePattern : CasePattern → LineM Unit
  | .pattern value => patternAtoms value
  | .number value => t (toString value.value)
  | .trueLiteral _ => t "true"
  | .falseLiteral _ => t "false"
  | .variant _ value payload => do
    path value
    if let some items := payload then group "(" ")" items casePattern
  | .tuple _ items => group "(" ")" items casePattern

def sortAtoms : SortExpr → LineM Unit
  | .nat _ => t "nat"
  | .linear _ => t "linear"
  | .path value => path value

def bound (value : Bound) : LineM Unit := joinedText " + " value.sorts sortAtoms

def staticParams (value : StaticParams) : LineM Unit :=
  group "<" ">" value.params fun param => do
    if param.spec then t "spec "
    name param.name
    if let some b := param.bound then t ": "; bound b

def whereAtoms (value : Where) : LineM Unit := do
  t "where "
  group "(" ")" value.constraints fun
    | .bound _ subject b => do expr subject; t ": "; bound b
    | .compare _ operator left right => do expr left; t (compareText operator); expr right

def holders : Holders → LineM Unit
  | .role value => name value
  | .roles _ roles => group "(" ")" roles name

def placement (value : Placement) : LineM Unit := do
  holders value.holders
  if let some readers := value.readers then t " -> "; holders readers

def roleMap (value : RoleMap) : LineM Unit := do
  t " @"
  group "(" ")" value.entries fun entry => do name entry.callee; t " = "; name entry.caller

def application (value : Application) : LineM Unit := do
  path value.callee
  callArgs value.args
  if let some map := value.roleMap then roleMap map

def event : Event → LineM Unit
  | .send _ payload sender receivers oracle => do
    t "send "; expr payload
    if let some role := sender then t " from "; name role
    t " to "; joinedText ", " receivers name
    if let some kind := oracle then t " as oracle"; group "<" ">" #[kind] expr
  | .draw _ type sender receivers => do
    t "draw "; typeExpr type; t " from "; name sender; t " to "; joinedText ", " receivers name
  | .sample _ type => do t "sample "; typeExpr type
  | .query _ handle opener positions deferred => do
    t "query "; expr handle
    if let some role := opener then t " from "; name role
    t " at "; expr positions
    if deferred then t " deferred"
  | .attempt _ => t "attempt"
  | .application value => application value

def reasonText : Reason → String
  | .reject _ => "reject" | .abort _ => "abort" | .refused _ => "refused"
  | .exhausted _ => "exhausted"

def params (values : Array Param) : LineM Unit :=
  group "(" ")" values fun param => do name param.name; t ": "; typeExpr param.type

def primitiveAtoms (value : Primitive) : LineM Unit := do
  t "primitive"
  opening "("
  stringLiteral value.row
  for arg in value.args do
    comma
    staticArg arg
  closing ")"

def externalAtoms (value : External) : LineM Unit := do
  t "external"; group "(" ")" #[value.name] stringLiteral

def siteRef (value : SiteRef) : LineM Unit := do
  t "sites."; joinedText "." value.names name

def extractor : Extractor → LineM Unit
  | .path value => path value
  | .external _ value => do t "external"; group "(" ")" #[value] stringLiteral

def label (value : Option Label) : LineM Unit :=
  match value with
  | some l => do name l.name; t ": "
  | none => pure ()

partial def goalValue : GoalValue → LineM Unit
  | .path _ value args => do
    path value
    if let some a := args then callArgs a
  | .tuple _ items => group "(" ")" items goalValue

def atoms (action : LineM Unit) : Array Atom := (action.run #[]).2

/-! ## Lines, suites and comments -/

/-- What stands before the first comment or construct that is printed next. -/
inductive Blank where
  /-- exactly one blank line -/
  | force
  /-- one blank line where the source has one or more -/
  | keep
  /-- no blank line -/
  | none
  deriving BEq

structure State where
  lines : Array String
  comments : Array Comment
  next : Nat
  /-- the source line of the last construct or comment printed -/
  lastLine : Nat

abbrev PrintM := StateM State

def pushLine (line : String) : PrintM Unit := modify fun s => { s with lines := s.lines.push line }

def pushBlank : PrintM Unit := do
  let state ← get
  if state.lines.isEmpty then return
  if state.lines.back! == "" then return
  pushLine ""

def blankBefore (policy : Blank) (line : Nat) : PrintM Bool := do
  let last := (← get).lastLine
  return match policy with
    | .force => true
    | .keep => line > last + 1 ∧ last > 0
    | .none => false

/-- The comments that come before `start`, then the blank line before the construct. -/
def leading (indent : Nat) (start : Span) (policy : Blank) : PrintM Unit := do
  let mut first := true
  repeat
    let state ← get
    if h : state.next < state.comments.size then
      let comment := state.comments[state.next]
      if comment.startByte < start.startByte.toNat then
        if ← blankBefore (if first then policy else .keep) comment.line then pushBlank
        pushLine ("".pushn ' ' indent ++ comment.text)
        set { (← get) with next := state.next + 1, lastLine := comment.line }
        first := false
        continue
    break
  if ← blankBefore (if first then policy else .keep) start.startLine.toNat then pushBlank

def finish (span : Span) : PrintM Unit :=
  modify fun s => { s with lastLine := max s.lastLine span.stopLine.toNat }

/-- A logical line, broken by `Layout`. -/
def line (indent : Nat) (action : LineM Unit) : PrintM Unit := do
  for text in layout indent (atoms action) do pushLine text

/-- A construct of one logical line. -/
def simple (indent : Nat) (policy : Blank) (span : Span) (action : LineM Unit) : PrintM Unit := do
  leading indent span policy
  line indent action
  finish span

/-- The suite of a construct: the first item without a blank line before it. -/
def suiteOf {α : Type} (items : Array α) (each : Blank → α → PrintM Unit) : PrintM Unit := do
  let mut first := true
  for item in items do
    each (if first then .none else .keep) item
    first := false

mutual
  partial def stmt (indent : Nat) (policy : Blank) : Stmt → PrintM Unit
    | .binding span pattern type holdersValue value =>
      simple indent policy span do
        patternAtoms pattern
        if let some ty := type then t ": "; typeExpr ty
        if let some h := holdersValue then t " @"; holders h
        t " = "; expr value
    | .mutDecl span mutName type placementValue value =>
      simple indent policy span do
        t "mut "; name mutName
        if let some ty := type then t ": "; typeExpr ty
        if let some p := placementValue then t " @"; placement p
        t " = "; expr value
    | .update span updateName value =>
      simple indent policy span do name updateName; t " := "; expr value
    | .eventStmt (.bound span site pattern type holdersValue eventValue) => do
      leading indent span policy
      if let some siteAttribute := site then line indent (do t "#[site("; name siteAttribute.name; t ")]")
      line indent do
        patternAtoms pattern
        if let some ty := type then t ": "; typeExpr ty
        if let some h := holdersValue then t " @"; holders h
        t " <- "; event eventValue
      finish span
    | .eventStmt (.application span site value) => do
      leading indent span policy
      if let some siteAttribute := site then line indent (do t "#[site("; name siteAttribute.name; t ")]")
      line indent (application value)
      finish span
    | .«open» span site claims => do
      leading indent span policy
      if let some siteAttribute := site then line indent (do t "#[site("; name siteAttribute.name; t ")]")
      line indent do
        t "open "
        joinedText ", " claims fun claim => do
          expr claim.handle
          if let some opening := claim.opening then
            t " at "; expr opening.position; t " == "; expr opening.value
      finish span
    | .guard span holdersValue condition reason =>
      simple indent policy span do
        t "guard"
        if let some h := holdersValue then t " @"; holders h
        t " "; expr condition
        if let some r := reason then t s!" else {reasonText r}"
    | .«if» span condition thenSuite elseBranch => do
      leading indent span policy
      line indent (do t "if "; expr condition; t ":")
      ifRest indent thenSuite elseBranch
      finish span
    | .«match» span scrutinee cases => do
      leading indent span policy
      line indent (do t "match "; expr scrutinee; t ":")
      suiteOf cases fun casePolicy value => caseNode (indent + 4) casePolicy value
      finish span
    | .«for» span pattern domain collected body => do
      leading indent span policy
      line indent do
        t "for "; patternAtoms pattern; t " in "; domainAtoms domain
        if let some values := collected then
          t " collect "
          group "(" ")" values fun item => do name item.name; t " = "; expr item.value
        t ":"
      statements (indent + 4) body
      finish span
    | .empty span => simple indent policy span (t "()")

  partial def ifRest (indent : Nat) (thenSuite : Array Stmt) (elseBranch : Option ElseBranch) :
      PrintM Unit := do
    statements (indent + 4) thenSuite
    match elseBranch with
    | none => pure ()
    | some (.suite _ body) =>
      line indent (t "else:")
      statements (indent + 4) body
    | some (.elseIf (.«if» _ condition nestedThen nestedElse)) =>
      line indent (do t "else if "; expr condition; t ":")
      ifRest indent nestedThen nestedElse
    | some (.elseIf other) =>
      -- not produced by the parser: an `else` whose branch is a statement other than `if`
      line indent (t "else:")
      stmt (indent + 4) .none other

  partial def caseNode (indent : Nat) (policy : Blank) : Case → PrintM Unit
    | .«case» span pattern body => do
      leading indent span policy
      line indent (do t "case "; casePattern pattern; t ":")
      statements (indent + 4) body
      finish span

  partial def statements (indent : Nat) (body : Array Stmt) : PrintM Unit :=
    suiteOf body (stmt indent)
end

/-- `return e` as the last line of a body: a construct of its own for the comments before it. -/
def returnLine (indent : Nat) (policy : Blank) (value : Expr) : PrintM Unit :=
  simple indent policy value.span (do t "return "; expr value)

/-- A body (§5.5) after the head that it ends: the head is printed by `head`. -/
def bodyAfter (indent : Nat) (head : LineM Unit) : Body → PrintM Unit
  | .expression _ value => line indent (do head; t ": "; expr value)
  | .suiteExpression _ value => do
    line indent (do head; t ":")
    simple (indent + 4) .none value.span (expr value)
  | .statements _ body result => do
    line indent (do head; t ":")
    statements (indent + 4) body
    returnLine (indent + 4) (if body.isEmpty then .none else .keep) result

def defBindingAfter (indent : Nat) (head : LineM Unit) : DefBinding → PrintM Unit
  | .body value => bodyAfter indent head value
  | .primitive value => line indent (do head; t " = "; primitiveAtoms value)
  | .external value => line indent (do head; t " = "; externalAtoms value)

def kernelLine (indent : Nat) (kernel : Option KernelAttr) : PrintM Unit := do
  if let some siteAttribute := kernel then
    line indent (do t "#[kernel("; stringLiteral siteAttribute.name; t ")]")

def pubText (pub : Bool) : String := if pub then "pub " else ""

def protocolHead (value : ProtocolHead) : LineM Unit := do
  t "protocol "; name value.name
  if let some sp := value.staticParams then staticParams sp
  t " roles"
  group "(" ")" value.roles name
  group "(" ")" value.ports fun
    | .port _ portName type p isPrivate => do
      name portName; t ": "; typeExpr type; t " @"; placement p
      if isPrivate then t " private"
    | .spec _ portName type => do t "spec "; name portName; t ": "; typeExpr type
  if let some results := value.results then
    t " -> "
    let result (r : Result) : LineM Unit := do
      name r.name; t ": "; typeExpr r.type; t " @"; placement r.placement
    match results with
    | .one r => result r
    | .several _ rs => group "(" ")" rs result
  if let some w := value.whereClause then t " "; whereAtoms w

def lawHead (value : Law) : LineM Unit := do
  t "law "; name value.name
  if let some sp := value.staticParams then staticParams sp
  params value.params
  if let some w := value.whereClause then t " "; whereAtoms w

def lawNode (indent : Nat) (policy : Blank) (value : Law) : PrintM Unit := do
  leading indent value.span policy
  bodyAfter indent (lawHead value) value.body
  finish value.span

def defNode (indent : Nat) (policy : Blank) (value : Def) : PrintM Unit := do
  leading indent value.span policy
  kernelLine indent value.kernel
  let head : LineM Unit := do
    t (pubText value.pub)
    match value.modifier with
    | some (.spec _) => t "spec "
    | some (.entry _) => t "entry "
    | none => pure ()
    t "def "; name value.name
    if let some sp := value.staticParams then staticParams sp
    params value.params
    if let some result := value.result then t " -> "; typeExpr result
    if let some w := value.whereClause then t " "; whereAtoms w
  defBindingAfter indent head value.binding
  finish value.span

def member (indent : Nat) (policy : Blank) : Member → PrintM Unit
  | .typeMember span memberName sp b =>
    simple indent policy span do
      t "type "; name memberName
      if let some s := sp then staticParams s
      if let some value := b then t ": "; bound value
  | .natMember span memberName => simple indent policy span (do t "nat "; name memberName)
  | .moduleMember span memberName b =>
    simple indent policy span (do t "module "; name memberName; t ": "; bound b)
  | .defMember span modifier memberName sp ps result w =>
    simple indent policy span do
      match modifier with
      | some (.«partial» _) => t "partial "
      | some (.spec _) => t "spec "
      | none => pure ()
      t "def "; name memberName
      if let some s := sp then staticParams s
      params ps
      if let some r := result then t " -> "; typeExpr r
      if let some value := w then t " "; whereAtoms value
  | .protocolMember head => simple indent policy head.span (protocolHead head)
  | .lawMember value => lawNode indent policy value

def clause (indent : Nat) (policy : Blank) (value : Clause) : PrintM Unit :=
  simple indent policy value.span do
    match value with
    | .requires _ l condition => do t "requires "; label l; expr condition
    | .ensures _ l condition => do t "ensures "; label l; expr condition
    | .invariant _ l condition loop => do
      t "invariant "; label l; expr condition; t " at "; name loop
    | .reduces _ role l source target => do
      t "reduces "
      if let some r := role then t "@"; name r; t " "
      label l; expr source; t " to "; expr target
    | .proves _ role l relation => do
      t "proves "
      if let some r := role then t "@"; name r; t " "
      label l; expr relation
    | .through _ relation loop => do t "through "; expr relation; t " at "; name loop
    | .knowledge _ l relation ex alternative => do
      t "knowledge "; label l; expr relation; t " by "; extractor ex
      if let some alt := alternative then
        t " or "; expr alt.relation
        if let some by_ := alt.extractor then t " by "; path by_
    | .zeroKnowledge _ l simulator abilities => do
      t "zero_knowledge "; label l; t "by "; extractor simulator
      unless abilities.isEmpty do
        t " using "
        joinedText ", " abilities fun
          | .coins _ => t "coins" | .programming _ => t "programming" | .trapdoor _ => t "trapdoor"
    | .charge _ site b => do t "charge "; siteRef site; t " <= "; expr b

def schemeLine (indent : Nat) (policy : Blank) (value : SchemeLine) : PrintM Unit :=
  match value with
  | .layout span layoutPath adjustments => do
    leading indent span policy
    match adjustments with
    | none => line indent (do t "layout "; path layoutPath)
    | some items =>
      line indent (do t "layout "; path layoutPath; t ":")
      suiteOf items fun itemPolicy item =>
        simple (indent + 4) itemPolicy item.span do
          match item with
          | .carry _ site => do t "carry "; siteRef site
          | .recover _ site recovery => do t "recover "; siteRef site; t " by "; path recovery
    finish span
  | _ => simple indent policy value.span do
    match value with
    | .construction _ (.derived _ suitePath) => do
      t "construction derived"; group "(" ")" #[suitePath] path
    | .construction _ (.interactive _) => t "construction interactive"
    | .construction _ (.authored _) => t "construction authored"
    | .prover _ role => do t "prover "; name role
    | .offline _ roles => do t "offline "; joinedText ", " roles name
    | .ideal _ roles => do t "ideal "; joinedText ", " roles name
    | .context _ contextName type => do t "context "; name contextName; t ": "; typeExpr type
    | .commit _ subject scheme keys => do
      t "commit "
      match subject with
      | .term term => expr term
      | .site site => siteRef site
      t " with "; path scheme
      if let some ks := keys then
        group "(" ")" ks fun key => do
          t (match key.kind with | .proverKey => "prover_key" | .verifierKey => "verifier_key")
          t " = "; siteRef key.site
    | .pin _ site hash digest => do
      t "pin "; siteRef site; t " = "; path hash; t ": "; byteString digest
    | .grind _ bits sites => do
      t "grind "; expr bits; t " bits at "; joinedText ", " sites siteRef
    | .retry _ count site => do t "retry "; expr count; t " from "; siteRef site
    | .samples _ derivation => do t "samples derived by "; path derivation
    | .layout .. => pure ()

def typeDecl (indent : Nat) (policy : Blank) (value : TypeDecl) : PrintM Unit :=
  simple indent policy value.span do
    match value with
    | .type _ pub declName sp typeValue => do
      t (pubText pub); t "type "; name declName
      if let some s := sp then staticParams s
      t " = "
      match typeValue with
      | .type type => typeExpr type
      | .primitive p => primitiveAtoms p
    | .specType _ pub declName sp ext => do
      t (pubText pub); t "spec type "; name declName
      if let some s := sp then staticParams s
      t " = "; externalAtoms ext

def memberDef (indent : Nat) (policy : Blank) (value : MemberDef) : PrintM Unit := do
  leading indent value.span policy
  kernelLine indent value.kernel
  let head : LineM Unit := do
    if value.spec then t "spec "
    t "def "; name value.name
    group "(" ")" value.params name
  defBindingAfter indent head value.binding
  finish value.span

def headed (indent : Nat) (policy : Blank) (span : Span) (head : LineM Unit) : PrintM Unit := do
  leading indent span policy
  line indent head

mutual
  partial def item (indent : Nat) (policy : Blank) : Item → PrintM Unit
    | .use value =>
      simple indent policy value.span do
        t (pubText value.pub); t "use "; path value.path
        match value.tail with
        | .whole => pure ()
        | .alias aliasName => do t " as "; name aliasName
        | .names _ names => do t "::"; group "{" "}" names name
    | .«section» (.«section» span sp w items) => do
      headed indent policy span do
        t "section"
        if let some s := sp then t " "; staticParams s
        if let some value := w then t " "; whereAtoms value
        t ":"
      suiteOf items (item (indent + 4))
      finish span
    | .«module» (.«module» span pub moduleName sp b w body) => do
      let head : LineM Unit := do
        t (pubText pub); t "module "; name moduleName
        if let some s := sp then staticParams s
        if let some value := b then t ": "; bound value
        if let some value := w then t " "; whereAtoms value
      match body with
      | .suite items =>
        headed indent policy span (do head; t ":")
        suiteOf items (moduleItem (indent + 4))
      | .primitive value => headed indent policy span (do head; t " = "; primitiveAtoms value)
      | .asset value =>
        headed indent policy span (do head; t " = asset"; group "(" ")" #[value.name] name)
      finish span
    | .interface value => do
      let head : LineM Unit := do
        t (pubText value.pub); t "interface "; name value.name
        if let some s := value.staticParams then staticParams s
        if let some w := value.whereClause then t " "; whereAtoms w
      match value.members with
      | none => headed indent policy value.span head
      | some members =>
        headed indent policy value.span (do head; t ":")
        suiteOf members (member (indent + 4))
      finish value.span
    | .typeDecl value => typeDecl indent policy value
    | .struct value => do
      headed indent policy value.span do
        t (pubText value.pub)
        if value.linear then t "linear "
        t "struct "; name value.name
        if let some s := value.staticParams then staticParams s
        t ":"
      suiteOf value.fields fun fieldPolicy field =>
        simple (indent + 4) fieldPolicy field.span do
          t (pubText field.pub); name field.name; t ": "; typeExpr field.type
      finish value.span
    | .enum value => do
      headed indent policy value.span do
        t (pubText value.pub); t "enum "; name value.name
        if let some s := value.staticParams then staticParams s
        t ":"
      suiteOf value.alternatives fun altPolicy alt =>
        simple (indent + 4) altPolicy alt.span do
          name alt.name
          unless alt.payload.isEmpty do group "(" ")" alt.payload typeExpr
      finish value.span
    | .«def» value => defNode indent policy value
    | .oracleDef value => do
      headed indent policy value.span do
        t (pubText value.pub); t "oracle def "; name value.name
        if let some s := value.staticParams then staticParams s
        params value.params
        t ": "; path value.kind
        if let some w := value.whereClause then t " "; whereAtoms w
        t ":"
      simple (indent + 4) .none value.position.span do
        t "at "; name value.position; t ": "; expr value.row
      finish value.span
    | .protocol value => do
      headed indent policy value.span do
        t (pubText value.pub)
        if value.spec then t "spec "
        protocolHead value.head
        t ":"
      statements (indent + 4) value.body
      if let some result := value.result then
        returnLine (indent + 4) (if value.body.isEmpty then .none else .keep) result
      finish value.span
    | .relation value => do
      leading indent value.span policy
      let head : LineM Unit := do
        t (pubText value.pub); t "relation "; name value.name
        if let some s := value.staticParams then staticParams s
        opening "("
        let mut first := true
        for param in value.statement do
          unless first do comma
          name param.name; t ": "; typeExpr param.type
          first := false
        if let some witness := value.witness then
          t "; "
          let mut firstWitness := true
          for param in witness do
            unless firstWitness do comma
            name param.name; t ": "; typeExpr param.type
            firstWitness := false
        closing ")"
        if let some w := value.whereClause then t " "; whereAtoms w
      match value.binding with
      | .body b => bodyAfter indent head b
      | .external ext => line indent (do head; t " = "; externalAtoms ext)
      finish value.span
    | .contract value => do
      headed indent policy value.span (do t "spec for "; path value.target; t ":")
      suiteOf value.clauses (clause (indent + 4))
      finish value.span
    | .scheme value => do
      headed indent policy value.span do
        t (pubText value.pub); t "scheme "; name value.name; t " = "; path value.protocol; t ":"
      suiteOf value.lines (schemeLine (indent + 4))
      finish value.span
    | .goal value =>
      simple indent policy value.span do
        t (pubText value.pub); t "goal "; name value.name; t " = "; path value.property
        opening "("
        path value.scheme
        for arg in value.args do
          comma
          match arg with
          | .named _ argName v => do name argName; t " = "; goalValue v
          | .spec _ argName size => do t "spec "; name argName; t " = "; expr size
        closing ")"
        if let some ceiling := value.ceiling then t " <= "; expr ceiling
    | .law value => lawNode indent policy value
    | .staticName value =>
      simple indent policy value.span do
        t (pubText value.pub); t "nat "; name value.name; t " = "; expr value.size

  partial def moduleItem (indent : Nat) (policy : Blank) : ModuleItem → PrintM Unit
    | .item value => item indent policy value
    | .moduleMember value =>
      simple indent policy value.span do
        t "module "; name value.name; t " = "; path value.path
    | .memberDef value => memberDef indent policy value
end

def isUse : Item → Bool
  | .use _ => true
  | _ => false

def file (value : File) : PrintM Unit := do
  leading 0 value.span .none
  line 0 do
    t "module "; joinedText "::" value.path.names name
    if let some s := value.staticParams then staticParams s
    if let some w := value.whereClause then t " "; whereAtoms w
  modify fun s => { s with lastLine := max s.lastLine value.path.span.stopLine.toNat }
  let mut previous : Option Item := none
  for current in value.items do
    let policy := match previous with
      | some before => if isUse before ∧ isUse current then Blank.keep else .force
      | none => .force
    item 0 policy current
    previous := some current
  -- the comments after the last item
  let state ← get
  for comment in state.comments.extract state.next state.comments.size do
    if ← blankBefore .keep comment.line then pushBlank
    pushLine comment.text
    modify fun s => { s with lastLine := comment.line }

end Printer

/-- The text of a tree: `comments` are the comments of its source, placed as `Printer`
describes; give `#[]` for none. -/
def printFile (tree : File) (comments : Array Comment := #[]) : String :=
  let ((), state) := (Printer.file tree).run { lines := #[], comments, next := 0, lastLine := 0 }
  String.intercalate "\n" state.lines.toList ++ "\n"

end Zkc.Frontend.Syntax
