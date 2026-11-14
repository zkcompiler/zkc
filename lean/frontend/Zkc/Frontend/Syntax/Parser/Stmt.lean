module

public import Zkc.Frontend.Syntax.Parser.Expr

@[expose] public section

set_option autoImplicit false

/-!
# Statements and events (§5.8, §5.9)

A line of a suite of statements is decided by GR1: its first word, or else an expression read
first and the token after it.
-/

namespace Zkc.Frontend.Syntax.Parser

/-- A line of a suite: a statement, or an expression standing alone (which only the body of a
`def` admits, as its single line). -/
inductive Line where
  | statement (statement : Stmt)
  | expression (start : Token) (value : Expr)

/-- `Holders ::= Role | "(" Role { "," Role } ")"` -/
def parseHolders : ParseM Holders := do
  let start ← peek
  if start.kind == .leftParen then
    discard advance
    let roles ← commaList .rightParen parseName
    discard (expect .rightParen)
    return .roles (← spanFrom start) roles
  return .role (← parseName)

/-- `Placement ::= Holders [ "->" Holders ]` -/
def parsePlacement : ParseM Placement := do
  let start ← peek
  let holders ← parseHolders
  let readers ← if ← accept .rightArrow then some <$> parseHolders else pure none
  return { span := ← spanFrom start, holders, readers }

/-- `Role { "," Role }` after `to` and in a scheme line. -/
def parseRoleList : ParseM (Array Name) := do
  let mut roles := #[← parseName]
  while ← accept .comma do
    roles := roles.push (← parseName)
  return roles

/-- `"@" "(" Role "=" Role { "," Role "=" Role } ")"`; a role map by position has no production
(RM1). -/
def parseRoleMap : ParseM RoleMap := do
  let start ← expect .at
  discard (expect .leftParen)
  if (← peekKind) == .identifier ∧ (← peekKind 1) != .equals then
    fail "RM1" "roles are mapped by name: write `@(O = P, R = V)`"
  let entry : ParseM RoleMapEntry := do
    let entryStart ← peek
    let callee ← parseName
    discard (expect .equals)
    let caller ← parseName
    return { span := ← spanFrom entryStart, callee, caller }
  let entries ← commaList .rightParen entry
  discard (expect .rightParen)
  return { span := ← spanFrom start, entries }

/-- `Application ::= Path CallArgs [ "@" "(" Role "=" Role { "," Role "=" Role } ")" ]` -/
def parseApplication : ParseM Application := do
  let start ← peek
  let callee ← parsePath
  if (← peekKind) != .leftParen then
    fail "EV1" "after `<-` stands an event: send, draw, sample, query, attempt or an application"
  let args ← parseCallArgs
  let roleMap ← if (← peekKind) == .at ∧ (← peekKind 1) == .leftParen then
      some <$> parseRoleMap
    else pure none
  return { span := ← spanFrom start, callee, args, roleMap }

/-- `Event ::= Send | Draw | Sample | Query | Attempt | Application` -/
def parseEvent : ParseM Event := do
  let start ← peek
  match start.kind with
  | .kwSend =>
    discard advance
    let payload ← parseExpr
    let sender ← if ← atWord "from" then discard advance; some <$> parseName else pure none
    discard (expectWord "to")
    let receivers ← parseRoleList
    let oracle ← if (← peekKind) == .kwAs then
        discard advance
        discard (expectWord "oracle")
        discard (expect .staticOpen)
        let kind ← parseStaticTerm
        discard (expect .staticClose)
        if (← peekKind) == .leftParen then
          fail "OR3"
            "the shape of an oracle is in the static arguments of its kind: write `as oracle<table<T, n>>`"
        pure (some kind)
      else pure none
    return .send (← spanFrom start) payload sender receivers oracle
  | .kwDraw =>
    discard advance
    let type ← parseType
    discard (expectWord "from")
    let sender ← parseName
    discard (expectWord "to")
    let receivers ← parseRoleList
    return .draw (← spanFrom start) type sender receivers
  | .kwSample =>
    discard advance
    let type ← parseType
    return .sample (← spanFrom start) type
  | .kwQuery =>
    discard advance
    let handle ← parseExpr
    let opener ← if ← atWord "from" then discard advance; some <$> parseName else pure none
    discard (expectWord "at")
    let positions ← parseExpr
    let deferred ← if ← atWord "deferred" then discard advance; pure true else pure false
    return .query (← spanFrom start) handle opener positions deferred
  | .kwAttempt =>
    discard advance
    return .attempt (← spanFrom start)
  | .identifier => return .application (← parseApplication)
  | _ => fail "EV1" "after `<-` stands an event: send, draw, sample, query, attempt or an application"

/-- `Claim ::= Sum [ "at" Sum "==" Sum ]` -/
def parseClaim : ParseM Claim := do
  let start ← peek
  let handle ← parseSum
  let opening ← if ← atWord "at" then
      let openingStart ← advance
      let position ← parseSum
      discard (expect .equalEqual)
      let value ← parseSum
      pure (some { span := ← spanFrom openingStart, position, value : ClaimOpening })
    else pure none
  return { span := ← spanFrom start, handle, opening }

/-- `Open ::= [ SiteAttr ] "open" Claim { "," Claim } NEWLINE` -/
def parseOpen (start : Token) (site : Option SiteAttr) : ParseM Stmt := do
  discard (expect .kwOpen)
  let mut claims := #[← parseClaim]
  while ← accept .comma do
    claims := claims.push (← parseClaim)
  let span ← spanFrom start
  discard (expect .newline)
  return .«open» span site claims

def kernelPlacementMessage : String :=
  "`#[kernel(\"name\")]` stands on the line before a `def` with a body"

/-- `SiteAttr ::= "#" "[" "site" "(" Name ")" "]" NEWLINE` -/
def parseSiteAttr : ParseM SiteAttr := do
  let start ← expect .hash
  discard (expect .leftBracket)
  if ← atWord "kernel" then fail "FN5" kernelPlacementMessage
  discard (expectWord "site")
  discard (expect .leftParen)
  let name ← parseName
  discard (expect .rightParen)
  discard (expect .rightBracket)
  let span ← spanFrom start
  discard (expect .newline)
  return { span, name }

/-- Whether an expression that is not a pattern would be one but for a literal or an application
in it, which a refutable pattern would hold (TY13). -/
partial def isRefutableShape : Expr → Bool
  | .number _ | .trueLiteral _ | .falseLiteral _ | .call .. | .byteString _ => true
  | .tuple _ components => components.any fun
    | .component _ none value => isRefutableShape value
    | .component _ (some _) _ => false
  | .record _ _ fields => fields.any fun
    | .fieldInit _ _ (some value) => isRefutableShape value
    | .fieldInit _ _ none => false
  | _ => false

def notPatternError {α : Type} (start : Token) (value : Expr) : ParseM α :=
  if isRefutableShape value then
    failAt start "TY13" "a pattern outside `case` is irrefutable: a name, `_`, a tuple or a record pattern"
  else
    failAt start "GR1" "this is not a pattern"

def reasonOf? (text : String) (span : Span) : Option Reason :=
  match text with
  | "reject" => some (.reject span)
  | "abort" => some (.abort span)
  | "refused" => some (.refused span)
  | "exhausted" => some (.exhausted span)
  | _ => none

def isPatternContinuation (kind : TokenKind) : Bool :=
  kind == .equals ∨ kind == .colon ∨ kind == .at ∨ kind == .leftArrow

def expressionStatementMessage : String := "an expression is not a statement; bind it or return it"

def returnLastMessage : String := "`return` is the last line of a body"

mutual
  /-- One line of a suite of statements (GR1). `inProtocol` is true in the body of a protocol,
  where a call alone on its line is an application. The productions of a body admit every
  statement in a `def` as in a protocol; that a `def` has no event and no `@` is FN1, a rule of
  the checker. -/
  partial def parseLine (inProtocol : Bool) : ParseM Line := do
    let start ← peek
    match start.kind with
    | .hash =>
      let site ← parseSiteAttr
      if (← peekKind) == .kwOpen then
        return .statement (← parseOpen start (some site))
      match ← parseLine inProtocol with
      | .statement (.eventStmt (.bound _ none pattern type holders event)) =>
        return .statement (.eventStmt (.bound (← spanFrom start) (some site) pattern type holders event))
      | .statement (.eventStmt (.application _ none application)) =>
        return .statement (.eventStmt (.application (← spanFrom start) (some site) application))
      | _ => failAt start "EV3" "`#[site(…)]` stands on the line before an event"
    | .kwOpen => return .statement (← parseOpen start none)
    | .kwMut =>
      discard advance
      let name ← parseName
      let type ← if ← accept .colon then some <$> parseType else pure none
      let placement ← if ← accept .at then some <$> parsePlacement else pure none
      discard (expect .equals)
      let value ← parseExpr
      let span ← spanFrom start
      discard (expect .newline)
      return .statement (.mutDecl span name type placement value)
    | .kwGuard =>
      discard advance
      let holders ← if ← accept .at then some <$> parseHolders else pure none
      if (← peekKind) == .kwIf then
        fail "GR2" "parenthesize an `if` expression that is the condition of a guard"
      let condition ← parseOr
      let reason ← if ← accept .kwElse then
          let token ← peek
          let text ← peekText
          let file := (← get).file
          match (if token.kind == .identifier then reasonOf? text (tokenSpan file token) else none) with
          | some reason => discard advance; pure (some reason)
          | none =>
            fail "GU3" s!"`{← describe}` is not a reason; the reasons are reject, abort, refused, exhausted"
        else pure none
      let span ← spanFrom start
      discard (expect .newline)
      return .statement (.guard span holders condition reason)
    | .kwIf =>
      discard advance
      let condition ← parseExpr
      if (← peekKind) == .kwThen then
        -- GR1: after `if Expr`, `then` makes an expression
        discard advance
        let thenBranch ← parseExpr
        discard (expect .kwElse)
        let elseBranch ← parseExpr
        let value := Expr.ifExpr (← spanFrom start) condition thenBranch elseBranch
        return ← finishExpressionLine start value
      return .statement (← parseIfRest inProtocol start condition)
    | .kwMatch =>
      discard advance
      let scrutinee ← parseExpr
      discard (expect .colon)
      let cases ← suite (parseCase inProtocol)
      return .statement (.«match» (← spanFrom start) scrutinee cases)
    | .kwFor =>
      discard advance
      let pattern ← parsePattern
      discard (expect .kwIn)
      let domain ← parseDomain
      if (← peekKind) == .kwRoles then
        fail "CT1" "the roles of a loop are computed; `roles(…)` stands only in a protocol head"
      let collected ← if ← atWord "collect" then
          discard advance
          discard (expect .leftParen)
          let item : ParseM Collected := do
            let itemStart ← peek
            let name ← parseName
            discard (expect .equals)
            let value ← parseExpr
            return { span := ← spanFrom itemStart, name, value }
          let items ← commaList .rightParen item
          discard (expect .rightParen)
          pure (some items)
        else pure none
      discard (expect .colon)
      let body ← parseStatementSuite inProtocol
      return .statement (.«for» (← spanFrom start) pattern domain collected body)
    | .kwReturn => fail "CT5" returnLastMessage
    | .leftParen =>
      if (← peekKind 1) == .rightParen ∧ (← peekKind 2) == .newline then
        discard advance
        discard advance
        let span ← spanFrom start
        discard advance
        return .statement (.empty span)
      parsePatternOrExpressionLine inProtocol
    | .identifier =>
      if (← peekKind 1) == .colonEquals then
        let name ← parseName
        discard advance
        let value ← parseExpr
        let span ← spanFrom start
        discard (expect .newline)
        return .statement (.update span name value)
      parsePatternOrExpressionLine inProtocol
    | _ => parsePatternOrExpressionLine inProtocol

  /-- The rest of `If ::= "if" Expr ":" Suite(Stmt) [ "else" ( ":" Suite(Stmt) | If ) ]`. -/
  partial def parseIfRest (inProtocol : Bool) (start : Token) (condition : Expr) : ParseM Stmt := do
    discard (expect .colon)
    let thenSuite ← parseStatementSuite inProtocol
    let elseBranch ← if (← peekKind) == .kwElse then
        let elseStart ← advance
        if (← peekKind) == .kwIf then
          let ifStart ← advance
          let nested ← parseExpr
          pure (some (.elseIf (← parseIfRest inProtocol ifStart nested)))
        else
          discard (expect .colon)
          let statements ← parseStatementSuite inProtocol
          pure (some (.suite (← spanFrom elseStart) statements))
      else pure none
    return .«if» (← spanFrom start) condition thenSuite elseBranch

  /-- `Case ::= "case" CasePattern ":" Suite(Stmt)` -/
  partial def parseCase (inProtocol : Bool) : ParseM Case := do
    let start ← expect .kwCase
    let pattern ← parseCasePattern
    discard (expect .colon)
    let body ← parseStatementSuite inProtocol
    return .«case» (← spanFrom start) pattern body

  /-- `Suite(Stmt)` inside a control statement: every line is a statement. -/
  partial def parseStatementSuite (inProtocol : Bool) : ParseM (Array Stmt) := do
    discard (expect .newline)
    discard (expect .indent)
    let mut statements := #[]
    repeat
      match ← parseLine inProtocol with
      | .statement statement => statements := statements.push statement
      | .expression start _ => failAt start "GR1" expressionStatementMessage
      if (← peekKind) == .dedent then break
    discard advance
    return statements

  /-- The last case of GR1: a pattern followed by `=`, `:`, `@` or `<-`, or an expression. -/
  partial def parsePatternOrExpressionLine (inProtocol : Bool) : ParseM Line := do
    let start ← peek
    let pattern? ← attempt do
      let pattern ← parsePattern
      if isPatternContinuation (← peekKind) then pure pattern
      else throw { rule := "GR", message := "", span := default }
    match pattern? with
    | some pattern => return .statement (← parseBindingRest start pattern)
    | none =>
      let value ← parseExpr
      match value with
      | .call _ callee args =>
        if inProtocol then
          -- GR1: in a protocol body a call alone on its line is an application
          let next ← peekKind
          if next == .newline ∨ (next == .at ∧ (← peekKind 1) == .leftParen) then
            let roleMap ← if next == .at then some <$> parseRoleMap else pure none
            let applicationSpan ← spanFrom start
            discard (expect .newline)
            let application : Application := { span := applicationSpan, callee, args, roleMap }
            return .statement (.eventStmt (.application applicationSpan none application))
      | _ => pure ()
      finishExpressionLine start value

  /-- An expression has been read at the start of a line: it is the whole line, or the line is
  refused. -/
  partial def finishExpressionLine (start : Token) (value : Expr) : ParseM Line := do
    match (← peekKind) with
    | .newline =>
      discard advance
      return .expression start value
    | .colonEquals =>
      fail "GR3" "`:=` updates a `mut` name, not an element or a field; rebuild the value"
    | kind =>
      if isPatternContinuation kind then notPatternError start value
      unexpected "`=`, `<-` or the end of the line"

  /-- `Binding` or `EventStmt` after its pattern:
  `[ ":" Type ] [ "@" Holders ] ( "=" Expr | "<-" Event ) NEWLINE`. -/
  partial def parseBindingRest (start : Token) (pattern : Pattern) : ParseM Stmt := do
    let type ← if ← accept .colon then some <$> parseType else pure none
    let holders ← if ← accept .at then some <$> parseHolders else pure none
    if ← accept .leftArrow then
      let event ← parseEvent
      if (← peekKind) == .at then
        fail "HO3" "`@` never follows an event; place the role on the binder"
      let span ← spanFrom start
      discard (expect .newline)
      return .eventStmt (.bound span none pattern type holders event)
    discard (expect .equals)
    match (← peekKind) with
    | .kwSend | .kwDraw | .kwSample | .kwQuery | .kwAttempt =>
      fail "EV2" "an event stands on its own `<-` line: write `x <- …`"
    | _ => pure ()
    let value ← parseExpr
    if (← peekKind) == .at then
      fail "HO3" "`@` never follows an expression; place it on the binder"
    let span ← spanFrom start
    discard (expect .newline)
    return .binding span pattern type holders value
end

end Zkc.Frontend.Syntax.Parser
