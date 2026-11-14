module

public import Zkc.Frontend.Syntax.Span
public import Zkc.Frontend.Syntax.Token

@[expose] public section

set_option autoImplicit false

/-!
# The syntax tree

The types mirror the productions of §5 of the reference: one type per production, one
constructor per alternative, named after the production. Nothing is desugared and nothing is
resolved: a derived form is kept as written, a contextual word is recognised by position, and a
name is not looked up. Every constructor that is not only a choice between other productions
carries the span of its text; such a choice (an `Item` that is a `Def`, say) has the span of the
node it holds, given by the `span` functions at the end.

Two productions are Lean keywords and are renamed: `Type` is `TypeExpr` and `Sort` is
`SortExpr`. A sequence that the grammar writes inline (`Name "=" Expr` in a record update, the
part after `at` in a claim) has a small type of its own.
-/

namespace Zkc.Frontend.Syntax

/-- `Name`: an identifier, or a contextual word in a position where it is a name. -/
structure Name where
  span : Span
  text : String
  deriving Inhabited

/-- `Number`: decimal digits; it has no largest value. -/
structure Number where
  span : Span
  value : Nat
  deriving Inhabited

/-- `String`: the characters between the quotes. -/
structure StringLiteral where
  span : Span
  content : String
  deriving Inhabited

inductive ByteStringKind where
  /-- `b"…"`: one byte per character. -/
  | bytes
  /-- `hex"…"`: two hexadecimal digits per byte. -/
  | hex
  deriving Inhabited, BEq

/-- `ByteString`: its form and the characters between the quotes, as written. -/
structure ByteString where
  span : Span
  kind : ByteStringKind
  content : String
  deriving Inhabited

/-- The bytes of a byte string: one per character of `b"…"`, one per two hexadecimal digits of
`hex"…"`. -/
def ByteString.values (literal : ByteString) : List Nat :=
  match literal.kind with
  | .bytes => literal.content.toList.map (·.toNat)
  | .hex =>
    let digit (c : Char) : Nat :=
      if c.isDigit then c.toNat - '0'.toNat
      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
      else 0
    let rec pairs : List Char → List Nat
      | a :: b :: rest => (digit a * 16 + digit b) :: pairs rest
      | _ => []
    pairs literal.content.toList

/-- Which spelling of a mathematical form was written (§3.5): the symbol, or the call of the
function of the fixed table (`sum`, `product`, `all`, `any`, `inner`). -/
inductive Spelling where
  | symbol
  | named
  deriving Inhabited, BEq

/-- The four binder forms: `∑`, `∏`, `∀`, `∃`. -/
inductive BinderOperator where
  | sum | product | all | any
  deriving Inhabited, BEq

inductive CompareOperator where
  | equal | notEqual | less | lessEqual | greater | greaterEqual
  deriving Inhabited, BEq

inductive SumOperator where
  /-- `+` -/
  | add
  /-- `-` -/
  | subtract
  /-- `++` -/
  | concatenate
  deriving Inhabited, BEq

inductive ProductOperator where
  /-- `*` -/
  | multiply
  /-- `/` -/
  | divide
  /-- `%` -/
  | remainder
  deriving Inhabited, BEq

mutual
  /-- `Path ::= Segment { "::" Segment }` -/
  inductive Path where
    | path (span : Span) (segments : Array Segment)

  /-- `Segment ::= Name [ StaticArgs ]` -/
  inductive Segment where
    | segment (span : Span) (name : Name) (staticArgs : Option StaticArgs)

  /-- `StaticArgs ::= "<" StaticArg { "," StaticArg } ">"` -/
  inductive StaticArgs where
    | staticArgs (span : Span) (args : Array StaticArg)

  /-- `StaticArg ::= [ Name "=" ] ( StaticTerm | "_" ) | "spec" Name "=" StaticTerm`.
  A `StaticTerm` is an `Expr` read with the extensions of GR5. -/
  inductive StaticArg where
    | term (span : Span) (name : Option Name) (term : Expr)
    | inferred (span : Span) (name : Option Name)
    | spec (span : Span) (name : Name) (term : Expr)

  /-- `Type` (§5.3). A `Size` is an `Expr` read as a static term. -/
  inductive TypeExpr where
    | bool (span : Span)
    | nat (span : Span)
    | rational (span : Span)
    | index (span : Span) (size : Expr)
    | nonzero (span : Span) (type : TypeExpr)
    /-- `"[" Type [ ";" Size ] "]"` -/
    | sequence (span : Span) (element : TypeExpr) (size : Option Expr)
    /-- `"(" [ TupleField "," TupleField { "," TupleField } ] ")"`; `()` has no field. -/
    | tuple (span : Span) (fields : Array TupleField)
    | path (span : Span) (path : Path)

  /-- `TupleField ::= [ Name ":" ] Type` -/
  inductive TupleField where
    | tupleField (span : Span) (name : Option Name) (type : TypeExpr)

  /-- `Expr` and the productions below it (§5.6). The levels of precedence are the
  productions `OrExpr` to `Power`; a constructor of a level holds one application of its
  operator. `Postfix` and `Primary` alternatives follow, then the primaries that GR5 adds in a
  static term. -/
  inductive Expr where
    /-- `IfExpr ::= "if" Expr "then" Expr "else" Expr` -/
    | ifExpr (span : Span) (condition thenBranch elseBranch : Expr)
    /-- `OrExpr ::= AndExpr { "or" AndExpr }`, one `or` -/
    | orExpr (span : Span) (left right : Expr)
    /-- `AndExpr ::= NotExpr { "and" NotExpr }`, one `and` -/
    | andExpr (span : Span) (left right : Expr)
    /-- `NotExpr ::= "not" NotExpr` -/
    | notExpr (span : Span) (operand : Expr)
    /-- `Compare ::= Sum [ op Sum ]` -/
    | compare (span : Span) (operator : CompareOperator) (left right : Expr)
    /-- `Sum ::= Product { ( "+" | "-" | "++" ) Product }`, one operator -/
    | sum (span : Span) (operator : SumOperator) (left right : Expr)
    /-- `Product ::= Unary { ( "*" | "/" | "%" ) Unary }`, one operator -/
    | product (span : Span) (operator : ProductOperator) (left right : Expr)
    /-- `Unary ::= "-" Unary` -/
    | unary (span : Span) (operand : Expr)
    /-- `Power ::= Postfix "^" Unary` -/
    | power (span : Span) (base exponent : Expr)
    /-- `Postfix`: `"." Name` -/
    | field (span : Span) (target : Expr) (name : Name)
    /-- `Postfix`: `"." Name [ StaticArgs ] CallArgs` -/
    | method (span : Span) (target : Expr) (name : Name) (staticArgs : Option StaticArgs)
        (args : CallArgs)
    /-- `Postfix`: `"." Number` -/
    | position (span : Span) (target : Expr) (position : Number)
    /-- `Postfix`: `"[" Expr "]"` -/
    | index (span : Span) (target : Expr) (index : Expr)
    /-- `Postfix`: `"[" [ Expr ] ".." [ Expr ] "]"` -/
    | slice (span : Span) (target : Expr) (lower upper : Option Expr)
    | number (number : Number)
    | byteString (byteString : ByteString)
    | trueLiteral (span : Span)
    | falseLiteral (span : Span)
    /-- `Path` alone -/
    | path (span : Span) (path : Path)
    /-- `Path CallArgs` -/
    | call (span : Span) (callee : Path) (args : CallArgs)
    /-- `Path "{" [ FieldInit { "," FieldInit } ] "}"` -/
    | record (span : Span) (type : Path) (fields : Array FieldInit)
    /-- `"(" ")"` -/
    | unit (span : Span)
    /-- `"(" Expr ")"` -/
    | paren (span : Span) (inner : Expr)
    /-- `"(" Expr "," Expr { "," Expr } ")"`; in a static term a component may be named. -/
    | tuple (span : Span) (components : Array TupleComponent)
    /-- `"[" [ Expr { "," Expr } ] "]"` -/
    | list (span : Span) (elements : Array Expr)
    /-- `"[" Expr ";" Size "]"` -/
    | repetition (span : Span) (element : Expr) (count : Expr)
    /-- `"[" Expr "for" Pattern "in" Domain [ "if" Expr ] "]"` -/
    | comprehension (span : Span) (element : Expr) (pattern : Pattern) (domain : Domain)
        (filter : Option Expr)
    /-- `"{" Expr "with" Name "=" Expr { "," Name "=" Expr } "}"` -/
    | recordUpdate (span : Span) (record : Expr) (fields : Array FieldUpdate)
    /-- `( "∑" | "∏" | "∀" | "∃" ) Pattern "∈" Domain "," Expr`, or its named spelling
    `sum([Expr for Pattern in Domain])` -/
    | binderForm (span : Span) (operator : BinderOperator) (spelling : Spelling)
        (pattern : Pattern) (domain : Domain) (body : Expr)
    /-- `"⟪" Expr "," Expr "⟫"`, or its named spelling `inner(Expr, Expr)` -/
    | innerProduct (span : Span) (spelling : Spelling) (left right : Expr)
    /-- GR5: `"bool"` in a static term -/
    | boolType (span : Span)
    /-- GR5: `"nat"` in a static term -/
    | natType (span : Span)
    /-- GR5: `"rational"` in a static term -/
    | rationalType (span : Span)
    /-- GR5: `"index" "<" Size ">"` in a static term -/
    | indexType (span : Span) (size : Expr)
    /-- GR5: `"nonzero" "<" Type ">"` in a static term -/
    | nonzeroType (span : Span) (type : TypeExpr)

  /-- A component of a parenthesized list; GR5 lets it be named in a static term. -/
  inductive TupleComponent where
    | component (span : Span) (name : Option Name) (value : Expr)

  /-- `CallArgs ::= "(" [ Argument { "," Argument } ] [ ";" Argument { "," Argument } ] ")"`.
  `witnesses` is present when `;` is written. -/
  inductive CallArgs where
    | callArgs (span : Span) (arguments : Array Argument) (witnesses : Option (Array Argument))

  /-- `Argument ::= Expr | Name "=" Expr | "spec" Name "=" Expr` -/
  inductive Argument where
    | positional (span : Span) (value : Expr)
    | named (span : Span) (name : Name) (value : Expr)
    | spec (span : Span) (name : Name) (value : Expr)

  /-- `FieldInit ::= Name [ "=" Expr ]` -/
  inductive FieldInit where
    | fieldInit (span : Span) (name : Name) (value : Option Expr)

  /-- `Name "=" Expr` in a record update. -/
  inductive FieldUpdate where
    | fieldUpdate (span : Span) (name : Name) (value : Expr)

  /-- `Domain ::= Sum [ ".." Sum ]` -/
  inductive Domain where
    | domain (span : Span) (start : Expr) (stop : Option Expr)

  /-- `Pattern` (§5.7) -/
  inductive Pattern where
    | name (name : Name)
    | wildcard (span : Span)
    | tuple (span : Span) (items : Array Pattern)
    | record (span : Span) (type : Path) (fields : Array FieldPattern)

  /-- `FieldPattern ::= Name [ "=" Pattern ]` -/
  inductive FieldPattern where
    | fieldPattern (span : Span) (name : Name) (pattern : Option Pattern)
end

instance : Inhabited Path := ⟨.path default #[]⟩
instance : Inhabited Expr := ⟨.unit default⟩
instance : Inhabited TypeExpr := ⟨.bool default⟩
instance : Inhabited Pattern := ⟨.wildcard default⟩
instance : Inhabited StaticArgs := ⟨.staticArgs default #[]⟩
instance : Inhabited CallArgs := ⟨.callArgs default #[] none⟩
instance : Inhabited Domain := ⟨.domain default default none⟩

/-- `CasePattern` (§5.7). A single `Name` is read as the `Pattern` alternative; whether it names
an alternative of a variant is the checker's to decide. A path of several segments, or with
static arguments or a payload, is the `Path` alternative. -/
inductive CasePattern where
  | pattern (pattern : Pattern)
  | number (number : Number)
  | trueLiteral (span : Span)
  | falseLiteral (span : Span)
  /-- `Path [ "(" CasePattern { "," CasePattern } ")" ]` -/
  | variant (span : Span) (path : Path) (payload : Option (Array CasePattern))
  /-- `"(" CasePattern "," CasePattern { "," CasePattern } ")"` -/
  | tuple (span : Span) (items : Array CasePattern)

instance : Inhabited CasePattern := ⟨.trueLiteral default⟩

/-- `SortExpr` is the production `Sort ::= "nat" | "linear" | Path`. -/
inductive SortExpr where
  | nat (span : Span)
  | linear (span : Span)
  | path (path : Path)
  deriving Inhabited

/-- `Bound ::= Sort { "+" Sort }` -/
structure Bound where
  span : Span
  sorts : Array SortExpr
  deriving Inhabited

/-- `StaticParam ::= [ "spec" ] Name [ ":" Bound ]` -/
structure StaticParam where
  span : Span
  spec : Bool
  name : Name
  bound : Option Bound
  deriving Inhabited

/-- `StaticParams ::= "<" StaticParam { "," StaticParam } ">"` -/
structure StaticParams where
  span : Span
  params : Array StaticParam
  deriving Inhabited

/-- `Constraint ::= StaticTerm ":" Bound | StaticTerm op StaticTerm` -/
inductive Constraint where
  | bound (span : Span) (subject : Expr) (bound : Bound)
  | compare (span : Span) (operator : CompareOperator) (left right : Expr)
  deriving Inhabited

/-- `Where ::= "where" "(" Constraint { "," Constraint } ")"` -/
structure Where where
  span : Span
  constraints : Array Constraint
  deriving Inhabited

/-- `Holders ::= Role | "(" Role { "," Role } ")"` -/
inductive Holders where
  | role (role : Name)
  | roles (span : Span) (roles : Array Name)
  deriving Inhabited

/-- `Placement ::= Holders [ "->" Holders ]` -/
structure Placement where
  span : Span
  holders : Holders
  readers : Option Holders
  deriving Inhabited

/-- `Reason ::= "reject" | "abort" | "refused" | "exhausted"` -/
inductive Reason where
  | reject (span : Span)
  | abort (span : Span)
  | refused (span : Span)
  | exhausted (span : Span)
  deriving Inhabited

/-- `SiteAttr ::= "#" "[" "site" "(" Name ")" "]" NEWLINE` -/
structure SiteAttr where
  span : Span
  name : Name
  deriving Inhabited

/-- `Role "=" Role` in a role map: the callee's role, then the caller's. -/
structure RoleMapEntry where
  span : Span
  callee : Name
  caller : Name
  deriving Inhabited

/-- `"@" "(" Role "=" Role { "," Role "=" Role } ")"` after an application. -/
structure RoleMap where
  span : Span
  entries : Array RoleMapEntry
  deriving Inhabited

/-- `Application ::= Path CallArgs [ RoleMap ]` -/
structure Application where
  span : Span
  callee : Path
  args : CallArgs
  roleMap : Option RoleMap
  deriving Inhabited

/-- `Event ::= Send | Draw | Sample | Query | Attempt | Application` -/
inductive Event where
  /-- `"send" Expr [ "from" Role ] "to" Role { "," Role } [ "as" "oracle" "<" StaticTerm ">" ]` -/
  | send (span : Span) (payload : Expr) (sender : Option Name) (receivers : Array Name)
      (oracle : Option Expr)
  /-- `"draw" Type "from" Role "to" Role { "," Role }` -/
  | draw (span : Span) (type : TypeExpr) (sender : Name) (receivers : Array Name)
  /-- `"sample" Type` -/
  | sample (span : Span) (type : TypeExpr)
  /-- `"query" Expr [ "from" Role ] "at" Expr [ "deferred" ]` -/
  | query (span : Span) (handle : Expr) (opener : Option Name) (positions : Expr)
      (deferred : Bool)
  | attempt (span : Span)
  | application (application : Application)
  deriving Inhabited

/-- `EventStmt ::= [ SiteAttr ] ( Pattern [ ":" Type ] [ "@" Holders ] "<-" Event | Application )
NEWLINE` -/
inductive EventStmt where
  | bound (span : Span) (site : Option SiteAttr) (pattern : Pattern) (type : Option TypeExpr)
      (holders : Option Holders) (event : Event)
  | application (span : Span) (site : Option SiteAttr) (application : Application)
  deriving Inhabited

/-- `"at" Sum "==" Sum` after the handle of a claim. -/
structure ClaimOpening where
  span : Span
  position : Expr
  value : Expr
  deriving Inhabited

/-- `Claim ::= Sum [ "at" Sum "==" Sum ]` -/
structure Claim where
  span : Span
  handle : Expr
  opening : Option ClaimOpening
  deriving Inhabited

/-- `Collected ::= Name "=" Expr` -/
structure Collected where
  span : Span
  name : Name
  value : Expr
  deriving Inhabited

mutual
  /-- `Stmt` (§5.8); `EventStmt` and `Open` are those of §5.9. -/
  inductive Stmt where
    /-- `Binding ::= Pattern [ ":" Type ] [ "@" Holders ] "=" Expr NEWLINE` -/
    | binding (span : Span) (pattern : Pattern) (type : Option TypeExpr) (holders : Option Holders)
        (value : Expr)
    /-- `MutDecl ::= "mut" Name [ ":" Type ] [ "@" Placement ] "=" Expr NEWLINE` -/
    | mutDecl (span : Span) (name : Name) (type : Option TypeExpr) (placement : Option Placement)
        (value : Expr)
    /-- `Update ::= Name ":=" Expr NEWLINE` -/
    | update (span : Span) (name : Name) (value : Expr)
    | eventStmt (statement : EventStmt)
    /-- `Open ::= [ SiteAttr ] "open" Claim { "," Claim } NEWLINE` -/
    | «open» (span : Span) (site : Option SiteAttr) (claims : Array Claim)
    /-- `Guard ::= "guard" [ "@" Holders ] OrExpr [ "else" Reason ] NEWLINE` -/
    | guard (span : Span) (holders : Option Holders) (condition : Expr) (reason : Option Reason)
    /-- `If ::= "if" Expr ":" Suite(Stmt) [ "else" ( ":" Suite(Stmt) | If ) ]` -/
    | «if» (span : Span) (condition : Expr) (thenSuite : Array Stmt)
        (elseBranch : Option ElseBranch)
    /-- `Match ::= "match" Expr ":" NEWLINE INDENT Case { Case } DEDENT` -/
    | «match» (span : Span) (scrutinee : Expr) (cases : Array Case)
    /-- `For ::= "for" Pattern "in" Domain [ "collect" "(" Collected { "," Collected } ")" ] ":"
    Suite(Stmt)` -/
    | «for» (span : Span) (pattern : Pattern) (domain : Domain)
        (collected : Option (Array Collected)) (body : Array Stmt)
    /-- `Empty ::= "(" ")" NEWLINE` -/
    | empty (span : Span)

  /-- What follows `else` in an `If`: a suite, or another `If`. -/
  inductive ElseBranch where
    | suite (span : Span) (statements : Array Stmt)
    | elseIf (statement : Stmt)

  /-- `Case ::= "case" CasePattern ":" Suite(Stmt)` -/
  inductive Case where
    | «case» (span : Span) (pattern : CasePattern) (body : Array Stmt)
end

instance : Inhabited Stmt := ⟨.empty default⟩

/-- `Param ::= Name ":" Type` -/
structure Param where
  span : Span
  name : Name
  type : TypeExpr
  deriving Inhabited

/-- `Primitive ::= "primitive" "(" String { "," StaticArg } ")" NEWLINE` -/
structure Primitive where
  span : Span
  row : StringLiteral
  args : Array StaticArg
  deriving Inhabited

/-- `Asset ::= "asset" "(" Name ")" NEWLINE` -/
structure Asset where
  span : Span
  name : Name
  deriving Inhabited

/-- `External ::= "external" "(" String ")" NEWLINE` -/
structure External where
  span : Span
  name : StringLiteral
  deriving Inhabited

/-- `KernelAttr ::= "#" "[" "kernel" "(" String ")" "]" NEWLINE` -/
structure KernelAttr where
  span : Span
  name : StringLiteral
  deriving Inhabited

/-- `Body` (§5.5): the three alternatives. -/
inductive Body where
  /-- `":" Expr NEWLINE` -/
  | expression (span : Span) (value : Expr)
  /-- `":" NEWLINE INDENT Expr NEWLINE DEDENT` -/
  | suiteExpression (span : Span) (value : Expr)
  /-- `":" NEWLINE INDENT { Stmt } "return" Expr NEWLINE DEDENT` -/
  | statements (span : Span) (statements : Array Stmt) (result : Expr)
  deriving Inhabited

/-- `Body | "=" ( Primitive | External )` at the end of a `Def` or a `MemberDef`. -/
inductive DefBinding where
  | body (body : Body)
  | primitive (primitive : Primitive)
  | external (external : External)
  deriving Inhabited

/-- `"spec"` or `"entry"` before `def`. -/
inductive DefModifier where
  | spec (span : Span)
  | entry (span : Span)
  deriving Inhabited

/-- `Def ::= [ KernelAttr ] [ "pub" ] [ "spec" | "entry" ] "def" Name [ StaticParams ]
"(" [ Param { "," Param } ] ")" [ "->" Type ] [ Where ] ( Body | "=" ( Primitive | External ) )` -/
structure Def where
  span : Span
  kernel : Option KernelAttr
  pub : Bool
  modifier : Option DefModifier
  name : Name
  staticParams : Option StaticParams
  params : Array Param
  result : Option TypeExpr
  whereClause : Option Where
  binding : DefBinding
  deriving Inhabited

/-- `Port ::= Name ":" Type "@" Placement [ "private" ] | "spec" Name ":" Type` -/
inductive Port where
  | port (span : Span) (name : Name) (type : TypeExpr) (placement : Placement) (isPrivate : Bool)
  | spec (span : Span) (name : Name) (type : TypeExpr)
  deriving Inhabited

/-- `Result ::= Name ":" Type "@" Placement` -/
structure Result where
  span : Span
  name : Name
  type : TypeExpr
  placement : Placement
  deriving Inhabited

/-- `Results ::= Result | "(" Result "," Result { "," Result } ")"` -/
inductive Results where
  | one (result : Result)
  | several (span : Span) (results : Array Result)
  deriving Inhabited

/-- `ProtocolHead ::= "protocol" Name [ StaticParams ] "roles" "(" Role { "," Role } ")"
"(" [ Port { "," Port } ] ")" [ "->" Results ] [ Where ]` -/
structure ProtocolHead where
  span : Span
  name : Name
  staticParams : Option StaticParams
  roles : Array Name
  ports : Array Port
  results : Option Results
  whereClause : Option Where
  deriving Inhabited

/-- `Protocol ::= [ "pub" ] [ "spec" ] ProtocolHead ":" NEWLINE INDENT { Stmt }
[ "return" Expr NEWLINE ] DEDENT` -/
structure Protocol where
  span : Span
  pub : Bool
  spec : Bool
  head : ProtocolHead
  body : Array Stmt
  result : Option Expr
  deriving Inhabited

/-- `Type NEWLINE | Primitive` after `=` in a `TypeDecl`. -/
inductive TypeValue where
  | type (type : TypeExpr)
  | primitive (primitive : Primitive)
  deriving Inhabited

/-- `TypeDecl` (§5.4) -/
inductive TypeDecl where
  /-- `[ "pub" ] "type" Name [ StaticParams ] "=" ( Type NEWLINE | Primitive )` -/
  | type (span : Span) (pub : Bool) (name : Name) (staticParams : Option StaticParams)
      (value : TypeValue)
  /-- `[ "pub" ] "spec" "type" Name [ StaticParams ] "=" External` -/
  | specType (span : Span) (pub : Bool) (name : Name) (staticParams : Option StaticParams)
      (external : External)
  deriving Inhabited

/-- `Field ::= [ "pub" ] Name ":" Type NEWLINE` -/
structure Field where
  span : Span
  pub : Bool
  name : Name
  type : TypeExpr
  deriving Inhabited

/-- `Struct ::= [ "pub" ] [ "linear" ] "struct" Name [ StaticParams ] ":" Suite(Field)` -/
structure Struct where
  span : Span
  pub : Bool
  linear : Bool
  name : Name
  staticParams : Option StaticParams
  fields : Array Field
  deriving Inhabited

/-- `Alternative ::= Name [ "(" Type { "," Type } ")" ] NEWLINE`; no payload is empty. -/
structure Alternative where
  span : Span
  name : Name
  payload : Array TypeExpr
  deriving Inhabited

/-- `Enum ::= [ "pub" ] "enum" Name [ StaticParams ] ":" Suite(Alternative)` -/
structure Enum where
  span : Span
  pub : Bool
  name : Name
  staticParams : Option StaticParams
  alternatives : Array Alternative
  deriving Inhabited

/-- `Law ::= "law" Name [ StaticParams ] "(" [ Param { "," Param } ] ")" [ Where ] Body` -/
structure Law where
  span : Span
  name : Name
  staticParams : Option StaticParams
  params : Array Param
  whereClause : Option Where
  body : Body
  deriving Inhabited

/-- `"partial"` or `"spec"` before `def` in a member of an interface. -/
inductive MemberModifier where
  | «partial» (span : Span)
  | spec (span : Span)
  deriving Inhabited

/-- `Member` (§5.11) -/
inductive Member where
  /-- `"type" Name [ StaticParams ] [ ":" Bound ] NEWLINE` -/
  | typeMember (span : Span) (name : Name) (staticParams : Option StaticParams)
      (bound : Option Bound)
  /-- `"nat" Name NEWLINE` -/
  | natMember (span : Span) (name : Name)
  /-- `"module" Name ":" Bound NEWLINE` -/
  | moduleMember (span : Span) (name : Name) (bound : Bound)
  /-- `[ "partial" | "spec" ] "def" Name [ StaticParams ] "(" [ Param { "," Param } ] ")"
  [ "->" Type ] [ Where ] NEWLINE` -/
  | defMember (span : Span) (modifier : Option MemberModifier) (name : Name)
      (staticParams : Option StaticParams) (params : Array Param) (result : Option TypeExpr)
      (whereClause : Option Where)
  /-- `ProtocolHead NEWLINE` -/
  | protocolMember (head : ProtocolHead)
  | lawMember (law : Law)
  deriving Inhabited

/-- `Interface ::= [ "pub" ] "interface" Name [ StaticParams ] [ Where ]
( ":" Suite(Member) | NEWLINE )`; `members` is absent for the alternative without a suite. -/
structure Interface where
  span : Span
  pub : Bool
  name : Name
  staticParams : Option StaticParams
  whereClause : Option Where
  members : Option (Array Member)
  deriving Inhabited

/-- `ModuleMember ::= "module" Name "=" Path NEWLINE` -/
structure ModuleMember where
  span : Span
  name : Name
  path : Path
  deriving Inhabited

/-- `MemberDef ::= [ KernelAttr ] [ "spec" ] "def" Name "(" [ Name { "," Name } ] ")"
( Body | "=" ( Primitive | External ) )` -/
structure MemberDef where
  span : Span
  kernel : Option KernelAttr
  spec : Bool
  name : Name
  params : Array Name
  binding : DefBinding
  deriving Inhabited

/-- `OracleDef ::= [ "pub" ] "oracle" "def" Name [ StaticParams ] "(" [ Param { "," Param } ] ")"
":" Path [ Where ] ":" NEWLINE INDENT "at" Name ":" Expr NEWLINE DEDENT` -/
structure OracleDef where
  span : Span
  pub : Bool
  name : Name
  staticParams : Option StaticParams
  params : Array Param
  kind : Path
  whereClause : Option Where
  position : Name
  row : Expr
  deriving Inhabited

/-- `Body | "=" External` at the end of a `Relation`. -/
inductive RelationBinding where
  | body (body : Body)
  | external (external : External)
  deriving Inhabited

/-- `Relation ::= [ "pub" ] "relation" Name [ StaticParams ]
"(" [ Param { "," Param } ] [ ";" Param { "," Param } ] ")" [ Where ] ( Body | "=" External )`.
`witness` is present when `;` is written. -/
structure Relation where
  span : Span
  pub : Bool
  name : Name
  staticParams : Option StaticParams
  statement : Array Param
  witness : Option (Array Param)
  whereClause : Option Where
  binding : RelationBinding
  deriving Inhabited

/-- `Label ::= Name ":"` -/
structure Label where
  span : Span
  name : Name
  deriving Inhabited

/-- `Extractor ::= Path | "external" "(" String ")"` -/
inductive Extractor where
  | path (path : Path)
  | external (span : Span) (name : StringLiteral)
  deriving Inhabited

/-- `Ability ::= "coins" | "programming" | "trapdoor"` -/
inductive Ability where
  | coins (span : Span)
  | programming (span : Span)
  | trapdoor (span : Span)
  deriving Inhabited

/-- `SiteRef ::= "sites" "." Name { "." Name }` -/
structure SiteRef where
  span : Span
  names : Array Name
  deriving Inhabited

/-- `"or" Expr [ "by" Path ]` at the end of a `knowledge` clause. -/
structure KnowledgeAlternative where
  span : Span
  relation : Expr
  extractor : Option Path
  deriving Inhabited

/-- `Clause` (§5.12) -/
inductive Clause where
  /-- `"requires" [ Label ] Expr NEWLINE` -/
  | requires (span : Span) (label : Option Label) (condition : Expr)
  /-- `"ensures" [ Label ] Expr NEWLINE` -/
  | ensures (span : Span) (label : Option Label) (condition : Expr)
  /-- `"invariant" [ Label ] Expr "at" Name NEWLINE` -/
  | invariant (span : Span) (label : Option Label) (condition : Expr) (loop : Name)
  /-- `"reduces" [ "@" Role ] [ Label ] Expr "to" Expr NEWLINE` -/
  | reduces (span : Span) (role : Option Name) (label : Option Label) (source target : Expr)
  /-- `"proves" [ "@" Role ] [ Label ] Expr NEWLINE` -/
  | proves (span : Span) (role : Option Name) (label : Option Label) (relation : Expr)
  /-- `"through" Expr "at" Name NEWLINE` -/
  | through (span : Span) (relation : Expr) (loop : Name)
  /-- `"knowledge" [ Label ] Expr "by" Extractor [ "or" Expr [ "by" Path ] ] NEWLINE` -/
  | knowledge (span : Span) (label : Option Label) (relation : Expr) (extractor : Extractor)
      (alternative : Option KnowledgeAlternative)
  /-- `"zero_knowledge" [ Label ] "by" Extractor [ "using" Ability { "," Ability } ] NEWLINE` -/
  | zeroKnowledge (span : Span) (label : Option Label) (simulator : Extractor)
      (abilities : Array Ability)
  /-- `"charge" SiteRef "<=" Expr NEWLINE` -/
  | charge (span : Span) (site : SiteRef) (bound : Expr)
  deriving Inhabited

/-- `Contract ::= "spec" "for" Path ":" Suite(Clause)` -/
structure Contract where
  span : Span
  target : Path
  clauses : Array Clause
  deriving Inhabited

/-- `"derived" "(" Path ")" | "interactive" | "authored"` after `construction`. -/
inductive Construction where
  | derived (span : Span) (suite : Path)
  | interactive (span : Span)
  | authored (span : Span)
  deriving Inhabited

/-- `StaticTerm | SiteRef` after `commit`. -/
inductive CommitSubject where
  | term (term : Expr)
  | site (site : SiteRef)
  deriving Inhabited

inductive KeyKind where
  | proverKey
  | verifierKey
  deriving Inhabited, BEq

/-- `Key ::= ( "prover_key" | "verifier_key" ) "=" SiteRef` -/
structure Key where
  span : Span
  kind : KeyKind
  site : SiteRef
  deriving Inhabited

/-- `Adjust ::= "carry" SiteRef NEWLINE | "recover" SiteRef "by" Path NEWLINE` -/
inductive Adjust where
  | carry (span : Span) (site : SiteRef)
  | recover (span : Span) (site : SiteRef) (recovery : Path)
  deriving Inhabited

/-- `SchemeLine` (§5.13) -/
inductive SchemeLine where
  | construction (span : Span) (construction : Construction)
  /-- `"prover" Role NEWLINE` -/
  | prover (span : Span) (role : Name)
  /-- `"offline" Role { "," Role } NEWLINE` -/
  | offline (span : Span) (roles : Array Name)
  /-- `"ideal" Role { "," Role } NEWLINE` -/
  | ideal (span : Span) (roles : Array Name)
  /-- `"context" Name ":" Type NEWLINE` -/
  | context (span : Span) (name : Name) (type : TypeExpr)
  /-- `"commit" ( StaticTerm | SiteRef ) "with" Path [ "(" Key { "," Key } ")" ] NEWLINE` -/
  | commit (span : Span) (subject : CommitSubject) (scheme : Path) (keys : Option (Array Key))
  /-- `"pin" SiteRef "=" Path ":" ByteString NEWLINE` -/
  | pin (span : Span) (site : SiteRef) (hash : Path) (digest : ByteString)
  /-- `"grind" Size "bits" "at" SiteRef { "," SiteRef } NEWLINE` -/
  | grind (span : Span) (bits : Expr) (sites : Array SiteRef)
  /-- `"retry" Size "from" SiteRef NEWLINE` -/
  | retry (span : Span) (count : Expr) (site : SiteRef)
  /-- `"samples" "derived" "by" Path NEWLINE` -/
  | samples (span : Span) (derivation : Path)
  /-- `"layout" Path ( NEWLINE | ":" Suite(Adjust) )` -/
  | layout (span : Span) (layout : Path) (adjustments : Option (Array Adjust))
  deriving Inhabited

/-- `Scheme ::= [ "pub" ] "scheme" Name "=" Path ":" Suite(SchemeLine)` -/
structure Scheme where
  span : Span
  pub : Bool
  name : Name
  protocol : Path
  lines : Array SchemeLine
  deriving Inhabited

/-- `GoalValue ::= Path [ CallArgs ] | "(" GoalValue "," GoalValue { "," GoalValue } ")"` -/
inductive GoalValue where
  | path (span : Span) (path : Path) (args : Option CallArgs)
  | tuple (span : Span) (items : Array GoalValue)

instance : Inhabited GoalValue := ⟨.tuple default #[]⟩

/-- `GoalArg ::= Name "=" GoalValue | "spec" Name "=" Size` -/
inductive GoalArg where
  | named (span : Span) (name : Name) (value : GoalValue)
  | spec (span : Span) (name : Name) (size : Expr)
  deriving Inhabited

/-- `Goal ::= [ "pub" ] "goal" Name "=" Path "(" Path { "," GoalArg } ")" [ "<=" Expr ] NEWLINE` -/
structure Goal where
  span : Span
  pub : Bool
  name : Name
  property : Path
  scheme : Path
  args : Array GoalArg
  ceiling : Option Expr
  deriving Inhabited

/-- `StaticName ::= [ "pub" ] "nat" Name "=" Size NEWLINE` -/
structure StaticName where
  span : Span
  pub : Bool
  name : Name
  size : Expr
  deriving Inhabited

/-- What follows the path of a `use`. -/
inductive UseTail where
  /-- nothing: the path is bound under its last name -/
  | whole
  /-- `"as" Name` -/
  | alias (name : Name)
  /-- `"::" "{" Name { "," Name } "}"` -/
  | names (span : Span) (names : Array Name)
  deriving Inhabited

/-- `Use ::= [ "pub" ] "use" Path [ "as" Name | "::" "{" Name { "," Name } "}" ] NEWLINE` -/
structure Use where
  span : Span
  pub : Bool
  path : Path
  tail : UseTail
  deriving Inhabited

mutual
  /-- `Item` (§5.1) -/
  inductive Item where
    | use (declaration : Use)
    | «section» (declaration : Section)
    | «module» (declaration : Module)
    | interface (declaration : Interface)
    | typeDecl (declaration : TypeDecl)
    | struct (declaration : Struct)
    | enum (declaration : Enum)
    | «def» (declaration : Def)
    | oracleDef (declaration : OracleDef)
    | protocol (declaration : Protocol)
    | relation (declaration : Relation)
    | contract (declaration : Contract)
    | scheme (declaration : Scheme)
    | goal (declaration : Goal)
    | law (declaration : Law)
    | staticName (declaration : StaticName)

  /-- `Section ::= "section" ( StaticParams [ Where ] | Where ) ":" Suite(Item)` -/
  inductive Section where
    | «section» (span : Span) (staticParams : Option StaticParams) (whereClause : Option Where)
        (items : Array Item)

  /-- `Module ::= [ "pub" ] "module" Name [ StaticParams ] [ ":" Bound ] [ Where ]
  ( ":" Suite(ModuleItem) | "=" ( Primitive | Asset ) )` -/
  inductive Module where
    | «module» (span : Span) (pub : Bool) (name : Name) (staticParams : Option StaticParams)
        (bound : Option Bound) (whereClause : Option Where) (body : ModuleBody)

  /-- `":" Suite(ModuleItem) | "=" ( Primitive | Asset )` at the end of a `Module`. -/
  inductive ModuleBody where
    | suite (items : Array ModuleItem)
    | primitive (primitive : Primitive)
    | asset (asset : Asset)

  /-- `ModuleItem ::= Item | ModuleMember | MemberDef` -/
  inductive ModuleItem where
    | item (item : Item)
    | moduleMember (moduleMember : ModuleMember)
    | memberDef (memberDef : MemberDef)
end

instance : Inhabited Item := ⟨.law default⟩

/-- `ModulePath ::= Name { "::" Name }` -/
structure ModulePath where
  span : Span
  names : Array Name
  deriving Inhabited

/-- `File ::= "module" ModulePath [ StaticParams ] [ Where ] NEWLINE { Item }` -/
structure File where
  span : Span
  path : ModulePath
  staticParams : Option StaticParams
  whereClause : Option Where
  items : Array Item
  deriving Inhabited

/-- A parsed source file: its tree and its comments, which are not tokens and are kept beside
the tree for the formatter. -/
structure SourceFile where
  tree : File
  comments : Array Comment
  /-- The bytes the file was read from: what a message quotes by place. -/
  source : ByteArray := ByteArray.empty
  deriving Inhabited

end Zkc.Frontend.Syntax
