module

public import Zkc.Frontend.Syntax.Parser.Stmt

@[expose] public section

set_option autoImplicit false

/-!
# Declarations (§5.1 to §5.5, §5.9 to §5.13) and the file
-/

namespace Zkc.Frontend.Syntax.Parser

/-- `SortExpr ::= "nat" | "linear" | Path`; `linear` is the word in this position (§3.4). -/
def parseSort : ParseM SortExpr := do
  let start ← peek
  if start.kind == .kwNat then
    discard advance
    return .nat (← spanFrom start)
  if (← atWord "linear") ∧ (← peekKind 1) != .colonColon ∧ (← peekKind 1) != .staticOpen then
    discard advance
    return .linear (← spanFrom start)
  return .path (← parsePath)

/-- `Bound ::= Sort { "+" Sort }` -/
def parseBound : ParseM Bound := do
  let start ← peek
  let mut sorts := #[← parseSort]
  while ← accept .plus do
    sorts := sorts.push (← parseSort)
  return { span := ← spanFrom start, sorts }

/-- `StaticParam ::= [ "spec" ] Name [ ":" Bound ]`; `spec` stands only before a parameter
whose bound is `nat` (§5.2). The prose of §5.2 names no rule; SP11 is the rule of such
parameters, and the conformance tests name it. -/
def parseStaticParam : ParseM StaticParam := do
  let start ← peek
  let spec ← accept .kwSpec
  let name ← parseName
  let bound ← if ← accept .colon then some <$> parseBound else pure none
  let span ← spanFrom start
  if spec then
    let isNat := match bound with
      | some { sorts := #[.nat _], .. } => true
      | _ => false
    unless isNat do
      failAt start "SP11" s!"`spec` marks a natural: write `spec {name.text}: nat`"
  return { span, spec, name, bound }

/-- `StaticParams ::= "<" StaticParam { "," StaticParam } ">"` -/
def parseStaticParams : ParseM StaticParams := do
  let start ← expectStaticOpen
  let params ← commaList .staticClose parseStaticParam
  discard (expect .staticClose)
  return { span := ← spanFrom start, params }

def parseStaticParams? : ParseM (Option StaticParams) := do
  if (← peekKind) == .staticOpen ∨ (← peekKind) == .less then some <$> parseStaticParams
  else pure none

/-- `Constraint ::= StaticTerm ":" Bound | StaticTerm op StaticTerm` -/
def parseConstraint : ParseM Constraint := do
  let start ← peek
  let subject ← parseStaticTerm
  if ← accept .colon then
    let bound ← parseBound
    return .bound (← spanFrom start) subject bound
  match compareOperator? (← peekKind) with
  | some operator =>
    discard advance
    let right ← parseStaticTerm
    return .compare (← spanFrom start) operator subject right
  | none => unexpected "`:` or a comparison"

/-- `Where ::= "where" "(" Constraint { "," Constraint } ")"` -/
def parseWhere : ParseM Where := do
  let start ← expect .kwWhere
  discard (expect .leftParen)
  let constraints ← commaList .rightParen parseConstraint
  discard (expect .rightParen)
  return { span := ← spanFrom start, constraints }

def parseWhere? : ParseM (Option Where) := do
  if (← peekKind) == .kwWhere then some <$> parseWhere else pure none

def parseStringLiteral : ParseM StringLiteral := do
  let token ← peek
  let content ← peekText
  discard (expect .string)
  return { span := tokenSpan (← get).file token, content }

/-- `Primitive ::= "primitive" "(" String { "," StaticArg } ")" NEWLINE` -/
def parsePrimitive : ParseM Primitive := do
  let start ← expect .kwPrimitive
  discard (expect .leftParen)
  let row ← parseStringLiteral
  let mut args := #[]
  while ← accept .comma do
    if (← peekKind) == .rightParen then break
    args := args.push (← parseStaticArg)
  discard (expect .rightParen)
  let span ← spanFrom start
  discard (expect .newline)
  return { span, row, args }

/-- `Asset ::= "asset" "(" Name ")" NEWLINE` -/
def parseAsset : ParseM Asset := do
  let start ← expect .kwAsset
  discard (expect .leftParen)
  let name ← parseName
  discard (expect .rightParen)
  let span ← spanFrom start
  discard (expect .newline)
  return { span, name }

/-- `External ::= "external" "(" String ")" NEWLINE` -/
def parseExternal : ParseM External := do
  let start ← expect .kwExternal
  discard (expect .leftParen)
  let name ← parseStringLiteral
  discard (expect .rightParen)
  let span ← spanFrom start
  discard (expect .newline)
  return { span, name }

/-- `KernelAttr ::= "#" "[" "kernel" "(" String ")" "]" NEWLINE` -/
def parseKernelAttr : ParseM KernelAttr := do
  let start ← expect .hash
  discard (expect .leftBracket)
  if ← atWord "site" then
    fail "EV3" "`#[site(…)]` names an event of a protocol body"
  discard (expectWord "kernel")
  discard (expect .leftParen)
  let name ← parseStringLiteral
  discard (expect .rightParen)
  discard (expect .rightBracket)
  let span ← spanFrom start
  discard (expect .newline)
  return { span, name }

/-- `Param ::= Name ":" Type` -/
def parseParam : ParseM Param := do
  let start ← peek
  let name ← parseName
  discard (expect .colon)
  let type ← parseType
  return { span := ← spanFrom start, name, type }

/-- `"(" [ Param { "," Param } ] ")"` -/
def parseParams : ParseM (Array Param) := do
  discard (expect .leftParen)
  let params ← commaList .rightParen parseParam (allowEmpty := true)
  discard (expect .rightParen)
  return params

/-- What a body belongs to: GR1 and FN4 for a `def`; one expression for a `law` and a
`relation` (§5.11, §5.12). -/
inductive BodyOwner where
  | function
  | law
  | relation
  deriving BEq

/-- `Body` (§5.5, GR1): one expression on the line, one expression in a suite, or statements
followed by `return`. -/
def parseBody (owner : BodyOwner) : ParseM Body := do
  let start ← expect .colon
  if (← peekKind) != .newline then
    let value ← parseExpr
    let span ← spanFrom start
    discard (expect .newline)
    return .expression span value
  discard advance
  discard (expect .indent)
  let mut statements := #[]
  repeat
    if (← peekKind) == .kwReturn then
      discard advance
      let result ← parseExpr
      discard (expect .newline)
      if (← peekKind) != .dedent then fail "CT5" returnLastMessage
      let span ← spanFrom start
      discard advance
      if owner != .function then
        failAt start "GR1" s!"the body of a {if owner == .law then "law" else "relation"} is one expression"
      return .statements span statements result
    match ← parseLine false with
    | .statement statement => statements := statements.push statement
    | .expression lineStart value =>
      if statements.isEmpty ∧ (← peekKind) == .dedent then
        let span ← spanFrom start
        discard advance
        return .suiteExpression span value
      failAt lineStart "GR1"
        "an expression is not a statement; a body is one expression, or statements and `return`"
    if (← peekKind) == .dedent then
      failAt start "FN4" "a function body ends in `return e`"
  failAt start "FN4" "a function body ends in `return e`"

/-- `Body | "=" ( Primitive | External )`. `= External` stands only on a `spec def` (§5.5). -/
def parseDefBinding (isSpec : Bool) : ParseM DefBinding := do
  if ← accept .equals then
    match (← peekKind) with
    | .kwPrimitive => return .primitive (← parsePrimitive)
    | .kwExternal =>
      unless isSpec do
        fail "NL9" "`external` names the formal library; only a `spec def` or a `relation` is bound to it"
      return .external (← parseExternal)
    | _ => unexpected "`primitive` or `external`"
  return .body (← parseBody .function)

/-- `Def` (§5.5) after its kernel attribute. -/
def parseDef (start : Token) (kernel : Option KernelAttr) (pub : Bool) : ParseM Def := do
  let modifier ← match (← peekKind) with
    | .kwSpec => let token ← advance; pure (some (DefModifier.spec (tokenSpan (← get).file token)))
    | .identifier =>
      if ← atWord "entry" then
        let token ← advance
        pure (some (DefModifier.entry (tokenSpan (← get).file token)))
      else pure none
    | _ => pure none
  discard (expect .kwDef)
  let name ← parseName
  let staticParams ← parseStaticParams?
  let params ← parseParams
  let result ← if ← accept .rightArrow then some <$> parseType else pure none
  let whereClause ← parseWhere?
  let isSpec := match modifier with | some (.spec _) => true | _ => false
  let binding ← parseDefBinding isSpec
  return { span := ← spanFrom start, kernel, pub, modifier, name, staticParams, params, result,
           whereClause, binding }

/-- `Port ::= Name ":" Type "@" Placement [ "private" ] | "spec" Name ":" Type` -/
def parsePort : ParseM Port := do
  let start ← peek
  if ← accept .kwSpec then
    let name ← parseName
    discard (expect .colon)
    let type ← parseType
    return .spec (← spanFrom start) name type
  let name ← parseName
  discard (expect .colon)
  let type ← parseType
  unless ← accept .at do
    fail "HO5" s!"port `{name.text}` has no holders: write `{name.text}: T @P`, or `spec {name.text}: T`"
  let placement ← parsePlacement
  let isPrivate ← if ← atWord "private" then discard advance; pure true else pure false
  return .port (← spanFrom start) name type placement isPrivate

/-- `Result ::= Name ":" Type "@" Placement` -/
def parseResult : ParseM Result := do
  let start ← peek
  let name ← parseName
  discard (expect .colon)
  let type ← parseType
  discard (expect .at)
  let placement ← parsePlacement
  return { span := ← spanFrom start, name, type, placement }

/-- `Results ::= Result | "(" Result "," Result { "," Result } ")"` -/
def parseResults : ParseM Results := do
  let start ← peek
  if start.kind == .leftParen then
    discard advance
    let first ← parseResult
    discard (expect .comma)
    let mut results := #[first, ← parseResult]
    while (← peekKind) == .comma do
      discard advance
      if (← peekKind) == .rightParen then break
      results := results.push (← parseResult)
    discard (expect .rightParen)
    return .several (← spanFrom start) results
  return .one (← parseResult)

/-- `ProtocolHead` (§5.9) -/
def parseProtocolHead : ParseM ProtocolHead := do
  let start ← expect .kwProtocol
  let name ← parseName
  let staticParams ← parseStaticParams?
  discard (expect .kwRoles)
  discard (expect .leftParen)
  let roles ← commaList .rightParen parseName
  discard (expect .rightParen)
  discard (expect .leftParen)
  let ports ← commaList .rightParen parsePort (allowEmpty := true)
  discard (expect .rightParen)
  let results ← if ← accept .rightArrow then some <$> parseResults else pure none
  let whereClause ← parseWhere?
  return { span := ← spanFrom start, name, staticParams, roles, ports, results, whereClause }

/-- `Protocol` (§5.9) after `pub` and `spec`. -/
def parseProtocol (start : Token) (pub spec : Bool) : ParseM Protocol := do
  let head ← parseProtocolHead
  discard (expect .colon)
  discard (expect .newline)
  discard (expect .indent)
  let mut body := #[]
  let mut result := none
  repeat
    if (← peekKind) == .kwReturn then
      discard advance
      result := some (← parseExpr)
      discard (expect .newline)
      if (← peekKind) != .dedent then fail "CT5" returnLastMessage
      break
    match ← parseLine true with
    | .statement statement => body := body.push statement
    | .expression lineStart _ => failAt lineStart "GR1" expressionStatementMessage
    if (← peekKind) == .dedent then break
  let span ← spanFrom start
  discard advance
  return { span, pub, spec, head, body, result }

/-- `TypeDecl` (§5.4) after `pub`. -/
def parseTypeDecl (start : Token) (pub : Bool) : ParseM TypeDecl := do
  if ← accept .kwSpec then
    discard (expect .kwType)
    let name ← parseName
    let staticParams ← parseStaticParams?
    discard (expect .equals)
    let external ← parseExternal
    return .specType (← spanFrom start) pub name staticParams external
  discard (expect .kwType)
  let name ← parseName
  let staticParams ← parseStaticParams?
  discard (expect .equals)
  match (← peekKind) with
  | .kwPrimitive =>
    let primitive ← parsePrimitive
    return .type (← spanFrom start) pub name staticParams (.primitive primitive)
  | .kwAsset => fail "NL9" "a type is not bound to an asset; bind a module: `module M: I = asset(name)`"
  | .kwExternal =>
    fail "NL9" "`external` names the formal library; a type of the formal library is a `spec type`"
  | _ =>
    let type ← parseType
    let span ← spanFrom start
    discard (expect .newline)
    return .type span pub name staticParams (.type type)

/-- `Struct ::= [ "pub" ] [ "linear" ] "struct" Name [ StaticParams ] ":" Suite(Field)` -/
def parseStruct (start : Token) (pub : Bool) : ParseM Struct := do
  let linear ← if ← atWord "linear" then discard advance; pure true else pure false
  discard (expect .kwStruct)
  let name ← parseName
  let staticParams ← parseStaticParams?
  discard (expect .colon)
  let field : ParseM Field := do
    let fieldStart ← peek
    let fieldPub ← accept .kwPub
    let fieldName ← parseName
    discard (expect .colon)
    let type ← parseType
    let span ← spanFrom fieldStart
    discard (expect .newline)
    return { span, pub := fieldPub, name := fieldName, type }
  let fields ← suite field
  return { span := ← spanFrom start, pub, linear, name, staticParams, fields }

/-- `Enum ::= [ "pub" ] "enum" Name [ StaticParams ] ":" Suite(Alternative)` -/
def parseEnum (start : Token) (pub : Bool) : ParseM Enum := do
  discard (expect .kwEnum)
  let name ← parseName
  let staticParams ← parseStaticParams?
  discard (expect .colon)
  let alternative : ParseM Alternative := do
    let alternativeStart ← peek
    let alternativeName ← parseName
    let payload ← if ← accept .leftParen then
        let types ← commaList .rightParen parseType
        discard (expect .rightParen)
        pure types
      else pure #[]
    let span ← spanFrom alternativeStart
    discard (expect .newline)
    return { span, name := alternativeName, payload }
  let alternatives ← suite alternative
  return { span := ← spanFrom start, pub, name, staticParams, alternatives }

/-- `Law ::= "law" Name [ StaticParams ] "(" [ Param { "," Param } ] ")" [ Where ] Body` -/
def parseLaw : ParseM Law := do
  let start ← expectWord "law"
  let name ← parseName
  let staticParams ← parseStaticParams?
  let params ← parseParams
  let whereClause ← parseWhere?
  let body ← parseBody .law
  return { span := ← spanFrom start, name, staticParams, params, whereClause, body }

/-- Whether the next tokens start a law: the word `law`, a name, and `(` or `<` (§5.0). -/
def atLaw : ParseM Bool := do
  return (← atWord "law") ∧ (← peekKind 1) == .identifier
    ∧ ((← peekKind 2) == .leftParen ∨ (← peekKind 2) == .staticOpen)

/-- `Member` (§5.11) -/
def parseMember : ParseM Member := do
  let start ← peek
  match start.kind with
  | .kwType =>
    discard advance
    let name ← parseName
    let staticParams ← parseStaticParams?
    let bound ← if ← accept .colon then some <$> parseBound else pure none
    let span ← spanFrom start
    discard (expect .newline)
    return .typeMember span name staticParams bound
  | .kwNat =>
    discard advance
    let name ← parseName
    let span ← spanFrom start
    discard (expect .newline)
    return .natMember span name
  | .kwModule =>
    discard advance
    let name ← parseName
    discard (expect .colon)
    let bound ← parseBound
    let span ← spanFrom start
    discard (expect .newline)
    return .moduleMember span name bound
  | .kwProtocol =>
    let head ← parseProtocolHead
    discard (expect .newline)
    return .protocolMember head
  | _ =>
    if ← atLaw then return .lawMember (← parseLaw)
    let modifier ← if (← peekKind) == .kwSpec then
        let token ← advance
        pure (some (MemberModifier.spec (tokenSpan (← get).file token)))
      else if (← atWord "partial") ∧ (← peekKind 1) == .kwDef then
        let token ← advance
        pure (some (MemberModifier.«partial» (tokenSpan (← get).file token)))
      else pure none
    discard (expect .kwDef)
    let name ← parseName
    let staticParams ← parseStaticParams?
    let params ← parseParams
    let result ← if ← accept .rightArrow then some <$> parseType else pure none
    let whereClause ← parseWhere?
    let span ← spanFrom start
    discard (expect .newline)
    return .defMember span modifier name staticParams params result whereClause

/-- `Interface` (§5.11) after `pub`. -/
def parseInterface (start : Token) (pub : Bool) : ParseM Interface := do
  discard (expect .kwInterface)
  let name ← parseName
  let staticParams ← parseStaticParams?
  let whereClause ← parseWhere?
  if (← peekKind) == .newline then
    let span ← spanFrom start
    discard advance
    return { span, pub, name, staticParams, whereClause, members := none }
  discard (expect .colon)
  let members ← suite parseMember
  return { span := ← spanFrom start, pub, name, staticParams, whereClause, members := some members }

/-- `OracleDef` (§5.10) after `pub`. -/
def parseOracleDef (start : Token) (pub : Bool) : ParseM OracleDef := do
  discard (expectWord "oracle")
  discard (expect .kwDef)
  let name ← parseName
  let staticParams ← parseStaticParams?
  let params ← parseParams
  discard (expect .colon)
  let kind ← parsePath
  let whereClause ← parseWhere?
  discard (expect .colon)
  discard (expect .newline)
  discard (expect .indent)
  discard (expectWord "at")
  let position ← parseName
  discard (expect .colon)
  let row ← parseExpr
  discard (expect .newline)
  let span ← spanFrom start
  discard (expect .dedent)
  return { span, pub, name, staticParams, params, kind, whereClause, position, row }

/-- `Relation` (§5.12) after `pub`. -/
def parseRelation (start : Token) (pub : Bool) : ParseM Relation := do
  discard (expect .kwRelation)
  let name ← parseName
  let staticParams ← parseStaticParams?
  discard (expect .leftParen)
  let mut statement := #[]
  if (← peekKind) != .rightParen ∧ (← peekKind) != .semicolon then
    statement := statement.push (← parseParam)
    while (← peekKind) == .comma do
      discard advance
      if (← peekKind) == .rightParen then break
      statement := statement.push (← parseParam)
  let witness ← if ← accept .semicolon then
      let mut witness := #[← parseParam]
      while (← peekKind) == .comma do
        discard advance
        if (← peekKind) == .rightParen then break
        witness := witness.push (← parseParam)
      pure (some witness)
    else pure none
  discard (expect .rightParen)
  let whereClause ← parseWhere?
  let binding ← if ← accept .equals then
      match (← peekKind) with
      | .kwExternal => pure (RelationBinding.external (← parseExternal))
      | .kwAsset =>
        fail "NL9" "a relation is not bound to an asset: write its formula over the module that reads the data"
      | _ => unexpected "`external`"
    else pure (RelationBinding.body (← parseBody .relation))
  return { span := ← spanFrom start, pub, name, staticParams, statement, witness, whereClause,
           binding }

/-- `SiteRef ::= "sites" "." Name { "." Name }` -/
def parseSiteRef : ParseM SiteRef := do
  let start ← expect .kwSites
  discard (expect .dot)
  let mut names := #[← parseName]
  while ← accept .dot do
    names := names.push (← parseName)
  return { span := ← spanFrom start, names }

/-- `Label ::= Name ":"`, two tokens of lookahead. -/
def parseLabel? : ParseM (Option Label) := do
  let start ← peek
  if start.kind == .identifier ∧ (← peekKind 1) == .colon then
    let name ← parseName
    discard advance
    return some { span := ← spanFrom start, name }
  return none

/-- `Extractor ::= Path | "external" "(" String ")"` -/
def parseExtractor : ParseM Extractor := do
  let start ← peek
  if start.kind == .kwExternal then
    discard advance
    discard (expect .leftParen)
    let name ← parseStringLiteral
    discard (expect .rightParen)
    return .external (← spanFrom start) name
  return .path (← parsePath)

def parseRoleTag? : ParseM (Option Name) := do
  if ← accept .at then some <$> parseName else pure none

/-- `Clause` (§5.12) -/
def parseClause : ParseM Clause := do
  let start ← peek
  let word ← if start.kind == .identifier then peekText else pure ""
  let clause ← match word with
    | "requires" | "ensures" =>
      discard advance
      let label ← parseLabel?
      let condition ← parseExpr
      let span ← spanFrom start
      pure (if word == "requires" then Clause.requires span label condition
        else Clause.ensures span label condition)
    | "invariant" =>
      discard advance
      let label ← parseLabel?
      let condition ← parseExpr
      discard (expectWord "at")
      let loop ← parseName
      pure (.invariant (← spanFrom start) label condition loop)
    | "reduces" =>
      discard advance
      let role ← parseRoleTag?
      let label ← parseLabel?
      let source ← parseExpr
      discard (expectWord "to")
      let target ← parseExpr
      pure (.reduces (← spanFrom start) role label source target)
    | "proves" =>
      discard advance
      let role ← parseRoleTag?
      let label ← parseLabel?
      let relation ← parseExpr
      pure (.proves (← spanFrom start) role label relation)
    | "through" =>
      discard advance
      let relation ← parseExpr
      discard (expectWord "at")
      let loop ← parseName
      pure (.through (← spanFrom start) relation loop)
    | "knowledge" =>
      discard advance
      let label ← parseLabel?
      let relation ← parseExpr
      discard (expectWord "by")
      let extractor ← parseExtractor
      let alternative ← if (← peekKind) == .kwOr then
          let alternativeStart ← advance
          let alternativeRelation ← parseExpr
          let alternativeExtractor ← if ← atWord "by" then
              discard advance
              some <$> parsePath
            else pure none
          pure (some { span := ← spanFrom alternativeStart, relation := alternativeRelation
                       extractor := alternativeExtractor : KnowledgeAlternative })
        else pure none
      pure (.knowledge (← spanFrom start) label relation extractor alternative)
    | "zero_knowledge" =>
      discard advance
      let label ← parseLabel?
      discard (expectWord "by")
      let simulator ← parseExtractor
      let mut abilities := #[]
      if ← atWord "using" then
        if simulator matches .external .. then
          fail "SX6" "`using` does not follow `external( … )`"
        discard advance
        repeat
          let token ← peek
          let span := tokenSpan (← get).file token
          let text ← peekText
          let ability? : Option Ability := if token.kind != .identifier then none
            else match text with
              | "coins" => some (.coins span)
              | "programming" => some (.programming span)
              | "trapdoor" => some (.trapdoor span)
              | _ => none
          match ability? with
          | some ability => discard advance; abilities := abilities.push ability
          | none => fail "SX6" "an ability is `coins`, `programming` or `trapdoor`"
          unless ← accept .comma do break
      pure (.zeroKnowledge (← spanFrom start) label simulator abilities)
    | "charge" =>
      discard advance
      let site ← parseSiteRef
      discard (expect .lessEqual)
      let bound ← parseExpr
      pure (.charge (← spanFrom start) site bound)
    | _ => fail "SX6" s!"`{← describe}` does not start a clause"
  discard (expect .newline)
  return clause

/-- `Contract ::= "spec" "for" Path ":" Suite(Clause)` -/
def parseContract : ParseM Contract := do
  let start ← expect .kwSpec
  discard (expect .kwFor)
  let target ← parsePath
  discard (expect .colon)
  let clauses ← suite parseClause
  return { span := ← spanFrom start, target, clauses }

/-- `Adjust ::= "carry" SiteRef NEWLINE | "recover" SiteRef "by" Path NEWLINE` -/
def parseAdjust : ParseM Adjust := do
  let start ← peek
  let adjust ← if ← atWord "carry" then
      discard advance
      let site ← parseSiteRef
      pure (Adjust.carry (← spanFrom start) site)
    else
      discard (expectWord "recover")
      let site ← parseSiteRef
      discard (expectWord "by")
      let recovery ← parsePath
      pure (Adjust.recover (← spanFrom start) site recovery)
  discard (expect .newline)
  return adjust

/-- `SchemeLine` (§5.13) -/
def parseSchemeLine : ParseM SchemeLine := do
  let start ← peek
  let word ← if start.kind == .identifier then peekText else pure ""
  match word with
  | "layout" =>
    discard advance
    let layout ← parsePath
    if ← accept .colon then
      let adjustments ← suite parseAdjust
      return .layout (← spanFrom start) layout (some adjustments)
    let span ← spanFrom start
    discard (expect .newline)
    return .layout span layout none
  | _ =>
  let line ← match word with
    | "construction" =>
      discard advance
      let constructionStart ← peek
      let construction ← if ← atWord "derived" then
          discard advance
          discard (expect .leftParen)
          if (← peekKind) == .string then
            fail "SC5"
              "the suite of `derived` is a path to a module that implements `zkc::construction::Suite`; a catalogue suite is a module of `zkc::suites`"
          let suitePath ← parsePath
          discard (expect .rightParen)
          pure (Construction.derived (← spanFrom constructionStart) suitePath)
        else if ← atWord "interactive" then
          discard advance
          pure (Construction.interactive (← spanFrom constructionStart))
        else if ← atWord "authored" then
          discard advance
          pure (Construction.authored (← spanFrom constructionStart))
        else fail "SC5" "a construction is `derived(suite)`, `interactive` or `authored`"
      pure (SchemeLine.construction (← spanFrom start) construction)
    | "prover" =>
      discard advance
      let role ← parseName
      pure (.prover (← spanFrom start) role)
    | "offline" | "ideal" =>
      discard advance
      let roles ← parseRoleList
      if (← peekKind) == .equals then
        fail "SC2" "`ideal R` has no right side: the functionality of an ideal role is connected by the host"
      let span ← spanFrom start
      pure (if word == "offline" then SchemeLine.offline span roles else .ideal span roles)
    | "context" =>
      discard advance
      let name ← parseName
      discard (expect .colon)
      let type ← parseType
      pure (.context (← spanFrom start) name type)
    | "commit" =>
      discard advance
      let subject ← if (← peekKind) == .kwSites then CommitSubject.site <$> parseSiteRef
        else CommitSubject.term <$> parseStaticTerm
      discard (expectWord "with")
      let scheme ← parsePath
      let keys ← if ← accept .leftParen then
          let key : ParseM Key := do
            let keyStart ← peek
            let kind ← if ← atWord "prover_key" then pure KeyKind.proverKey
              else if ← atWord "verifier_key" then pure KeyKind.verifierKey
              else unexpected "`prover_key` or `verifier_key`"
            discard advance
            discard (expect .equals)
            let site ← parseSiteRef
            return { span := ← spanFrom keyStart, kind, site }
          let keys ← commaList .rightParen key
          discard (expect .rightParen)
          pure (some keys)
        else pure none
      pure (.commit (← spanFrom start) subject scheme keys)
    | "pin" =>
      discard advance
      let site ← parseSiteRef
      discard (expect .equals)
      let hash ← parsePath
      discard (expect .colon)
      let digest ← parseByteString
      pure (.pin (← spanFrom start) site hash digest)
    | "grind" =>
      discard advance
      let bits ← parseStaticTerm
      discard (expectWord "bits")
      discard (expectWord "at")
      let mut sites := #[← parseSiteRef]
      while ← accept .comma do
        sites := sites.push (← parseSiteRef)
      pure (.grind (← spanFrom start) bits sites)
    | "retry" =>
      discard advance
      let count ← parseStaticTerm
      discard (expectWord "from")
      let site ← parseSiteRef
      pure (.retry (← spanFrom start) count site)
    | "samples" =>
      discard advance
      discard (expectWord "derived")
      discard (expectWord "by")
      let derivation ← parsePath
      pure (.samples (← spanFrom start) derivation)
    | _ => fail "SC5" s!"`{← describe}` does not start a line of a scheme"
  discard (expect .newline)
  return line

/-- `Scheme ::= [ "pub" ] "scheme" Name "=" Path ":" Suite(SchemeLine)` -/
def parseScheme (start : Token) (pub : Bool) : ParseM Scheme := do
  discard (expect .kwScheme)
  let name ← parseName
  discard (expect .equals)
  let protocol ← parsePath
  discard (expect .colon)
  let lines ← suite parseSchemeLine
  return { span := ← spanFrom start, pub, name, protocol, lines }

/-- `GoalValue ::= Path [ CallArgs ] | "(" GoalValue "," GoalValue { "," GoalValue } ")"` -/
partial def parseGoalValue : ParseM GoalValue := do
  let start ← peek
  if start.kind == .leftParen then
    discard advance
    let first ← parseGoalValue
    discard (expect .comma)
    let mut items := #[first, ← parseGoalValue]
    while (← peekKind) == .comma do
      discard advance
      if (← peekKind) == .rightParen then break
      items := items.push (← parseGoalValue)
    discard (expect .rightParen)
    return .tuple (← spanFrom start) items
  let path ← parsePath
  let args ← if (← peekKind) == .leftParen then some <$> parseCallArgs else pure none
  return .path (← spanFrom start) path args

/-- `GoalArg ::= Name "=" GoalValue | "spec" Name "=" Size` -/
def parseGoalArg : ParseM GoalArg := do
  let start ← peek
  if ← accept .kwSpec then
    let name ← parseName
    discard (expect .equals)
    let size ← parseStaticTerm
    return .spec (← spanFrom start) name size
  let name ← parseName
  discard (expect .equals)
  let value ← parseGoalValue
  return .named (← spanFrom start) name value

/-- `Goal ::= [ "pub" ] "goal" Name "=" Path "(" Path { "," GoalArg } ")" [ "<=" Expr ] NEWLINE` -/
def parseGoal (start : Token) (pub : Bool) : ParseM Goal := do
  discard (expect .kwGoal)
  let name ← parseName
  discard (expect .equals)
  let property ← parsePath
  discard (expect .leftParen)
  let scheme ← parsePath
  let mut args := #[]
  while ← accept .comma do
    if (← peekKind) == .rightParen then break
    args := args.push (← parseGoalArg)
  discard (expect .rightParen)
  let ceiling ← if ← accept .lessEqual then some <$> parseExpr else pure none
  let span ← spanFrom start
  discard (expect .newline)
  return { span, pub, name, property, scheme, args, ceiling }

/-- `StaticName ::= [ "pub" ] "nat" Name "=" Size NEWLINE` -/
def parseStaticName (start : Token) (pub : Bool) : ParseM StaticName := do
  discard (expect .kwNat)
  let name ← parseName
  discard (expect .equals)
  let size ← parseStaticTerm
  let span ← spanFrom start
  discard (expect .newline)
  return { span, pub, name, size }

/-- `Use ::= [ "pub" ] "use" Path [ "as" Name | "::" "{" Name { "," Name } "}" ] NEWLINE` -/
def parseUse (start : Token) (pub : Bool) : ParseM Use := do
  discard (expect .kwUse)
  let path ← parsePath
  let tail ← if (← peekKind) == .colonColon then
      discard advance
      let namesStart ← expect .leftBrace
      let names ← commaList .rightBrace parseName
      discard (expect .rightBrace)
      pure (UseTail.names (← spanFrom namesStart) names)
    else if ← accept .kwAs then
      pure (UseTail.alias (← parseName))
    else pure UseTail.whole
  let span ← spanFrom start
  discard (expect .newline)
  return { span, pub, path, tail }

/-- Where an item stands: the file, a section, or the suite of a module (which also admits a
`ModuleMember` and a `MemberDef`). -/
inductive ItemPlace where
  | file
  | section
  | module
  deriving BEq

def functionRemovedMessage : String :=
  "function types and function literals are not part of the language: write a loop, a comprehension or a binder form"

/-- GR4: after `def Name (`, a `)` followed by `:` or `=`, or a name followed by `,` or `)`,
make a member definition. `offset` is the position of `def`. -/
def atMemberDef (offset : Nat) : ParseM Bool := do
  if (← peekKind offset) != .kwDef ∨ (← peekKind (offset + 1)) != .identifier
      ∨ (← peekKind (offset + 2)) != .leftParen then
    return false
  let first ← peekKind (offset + 3)
  let second ← peekKind (offset + 4)
  return (first == .rightParen ∧ (second == .colon ∨ second == .equals))
    ∨ (first == .identifier ∧ (second == .comma ∨ second == .rightParen))

/-- `MemberDef` (§5.11) after its kernel attribute. -/
def parseMemberDef (start : Token) (kernel : Option KernelAttr) : ParseM MemberDef := do
  let spec ← accept .kwSpec
  discard (expect .kwDef)
  let name ← parseName
  discard (expect .leftParen)
  let params ← commaList .rightParen parseName (allowEmpty := true)
  discard (expect .rightParen)
  let binding ← parseDefBinding spec
  return { span := ← spanFrom start, kernel, spec, name, params, binding }

def bindingHasBody : DefBinding → Bool
  | .body _ => true
  | _ => false

mutual
  /-- `Item` (§5.1), or in the suite of a module a `ModuleItem` (§5.11). -/
  partial def parseModuleItem (place : ItemPlace) : ParseM ModuleItem := do
    let start ← peek
    if start.kind == .hash then
      let kernel ← parseKernelAttr
      let offset := if (← peekKind) == .kwSpec then 1 else 0
      if place == .module ∧ (← atMemberDef offset) then
        let memberDef ← parseMemberDef start (some kernel)
        unless bindingHasBody memberDef.binding do
          failAt start "FN5" "a kernel is attached to a `def` with a body"
        return .memberDef memberDef
      let pub ← accept .kwPub
      let isDef := (← peekKind) == .kwDef ∨ (← peekKind 1) == .kwDef
      unless isDef do failAt start "FN5" kernelPlacementMessage
      let definition ← parseDef start (some kernel) pub
      unless bindingHasBody definition.binding do
        failAt start "FN5" "a kernel is attached to a `def` with a body"
      return .item (.«def» definition)
    if place == .module then
      if start.kind == .kwModule ∧ (← peekKind 1) == .identifier ∧ (← peekKind 2) == .equals
          ∧ (← peekKind 3) != .kwPrimitive ∧ (← peekKind 3) != .kwAsset then
        discard advance
        let name ← parseName
        discard advance
        let path ← parsePath
        let span ← spanFrom start
        discard (expect .newline)
        return .moduleMember { span, name, path }
      let offset := if start.kind == .kwSpec then 1 else 0
      if ← atMemberDef offset then
        return .memberDef (← parseMemberDef start none)
    return .item (← parseItem)

  /-- `Item` (§5.1) -/
  partial def parseItem : ParseM Item := do
    let start ← peek
    if start.kind == .hash then
      match ← parseModuleItem .file with
      | .item item => return item
      | _ => failAt start "FN5" kernelPlacementMessage
    match start.kind with
    | .kwSection => return .«section» (← parseSection)
    | .kwSpec =>
      if (← peekKind 1) == .kwFor then return .contract (← parseContract)
    | .identifier =>
      if ← atLaw then return .law (← parseLaw)
    | _ => pure ()
    let pub ← accept .kwPub
    let kind ← peekKind
    match kind with
    | .kwUse => return .use (← parseUse start pub)
    | .kwModule => return .«module» (← parseModule start pub)
    | .kwInterface => return .interface (← parseInterface start pub)
    | .kwType => return .typeDecl (← parseTypeDecl start pub)
    | .kwStruct => return .struct (← parseStruct start pub)
    | .kwEnum => return .enum (← parseEnum start pub)
    | .kwDef => return .«def» (← parseDef start none pub)
    | .kwProtocol => return .protocol (← parseProtocol start pub false)
    | .kwRelation => return .relation (← parseRelation start pub)
    | .kwScheme => return .scheme (← parseScheme start pub)
    | .kwGoal => return .goal (← parseGoal start pub)
    | .kwNat =>
      if (← peekKind 1) == .identifier ∧ (← peekKind 2) == .equals then
        return .staticName (← parseStaticName start pub)
      unexpected "a declaration"
    | .kwSpec =>
      match (← peekKind 1) with
      | .kwType => return .typeDecl (← parseTypeDecl start pub)
      | .kwDef => return .«def» (← parseDef start none pub)
      | .kwProtocol =>
        discard advance
        return .protocol (← parseProtocol start pub true)
      | _ => unexpected "`type`, `def`, `protocol` or `for` after `spec`"
    | .identifier =>
      let word ← peekText
      let next ← peekKind 1
      if word == "linear" ∧ next == .kwStruct then return .struct (← parseStruct start pub)
      if word == "entry" ∧ next == .kwDef then return .«def» (← parseDef start none pub)
      if word == "oracle" ∧ next == .kwDef then return .oracleDef (← parseOracleDef start pub)
      if word == "distribution" ∧ next == .identifier then
        fail "GR6" "`distribution` is not part of the language: sample or draw the bytes and apply the function"
      if word == "affine" ∧ next == .kwStruct then
        fail "GR6" "`affine` is not part of the language: a record is `linear` or freely copied"
      fail "GR" s!"`{word}` does not start a declaration"
    | _ => unexpected "a declaration"

  /-- `Section ::= "section" ( StaticParams [ Where ] | Where ) ":" Suite(Item)` -/
  partial def parseSection : ParseM Section := do
    let start ← expect .kwSection
    let staticParams ← parseStaticParams?
    let whereClause ← parseWhere?
    if staticParams.isNone ∧ whereClause.isNone then
      unexpected "static parameters or `where`"
    discard (expect .colon)
    let items ← suite parseItem
    return .«section» (← spanFrom start) staticParams whereClause items

  /-- `Module` (§5.1) after `pub`. After the name and the static parameters, `:` followed by
  the end of the line opens the suite; any other token after `:` starts a bound (§5.0). -/
  partial def parseModule (start : Token) (pub : Bool) : ParseM Module := do
    discard (expect .kwModule)
    let name ← parseName
    let staticParams ← parseStaticParams?
    let bound ← if (← peekKind) == .colon ∧ (← peekKind 1) != .newline then
        discard advance
        some <$> parseBound
      else pure none
    let whereClause ← parseWhere?
    if ← accept .equals then
      let body ← match (← peekKind) with
        | .kwPrimitive => ModuleBody.primitive <$> parsePrimitive
        | .kwAsset => ModuleBody.asset <$> parseAsset
        | _ => unexpected "`primitive` or `asset`"
      return .«module» (← spanFrom start) pub name staticParams bound whereClause body
    discard (expect .colon)
    let items ← suite (parseModuleItem .module)
    return .«module» (← spanFrom start) pub name staticParams bound whereClause (.suite items)
end

/-- `File ::= "module" ModulePath [ StaticParams ] [ Where ] NEWLINE { Item }` -/
def parseFile : ParseM File := do
  let start ← expect .kwModule
  let pathStart ← peek
  let mut names := #[← parseName]
  while ← accept .colonColon do
    names := names.push (← parseName)
  let path : ModulePath := { span := ← spanFrom pathStart, names }
  let staticParams ← parseStaticParams?
  let whereClause ← parseWhere?
  discard (expect .newline)
  let mut items := #[]
  while (← peekKind) != .endOfFile do
    items := items.push (← parseItem)
  return { span := ← spanFrom start, path, staticParams, whereClause, items }

end Zkc.Frontend.Syntax.Parser
