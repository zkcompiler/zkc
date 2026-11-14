module

public import Zkc.Frontend.Syntax.Parser.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Expressions, types, paths and patterns (§5.2, §5.3, §5.6, §5.7)
-/

namespace Zkc.Frontend.Syntax.Parser

def compareOperator? : TokenKind → Option CompareOperator
  | .equalEqual => some .equal
  | .notEqual => some .notEqual
  | .less => some .less
  | .lessEqual => some .lessEqual
  | .greater => some .greater
  | .greaterEqual => some .greaterEqual
  | _ => none

def binderOperator? : TokenKind → Option BinderOperator
  | .sumSign => some .sum
  | .productSign => some .product
  | .forAllSign => some .all
  | .existsSign => some .any
  | _ => none

/-- The name of a binder form's function (§3.5). -/
def binderOperatorOfName? : String → Option BinderOperator
  | "sum" => some .sum
  | "product" => some .product
  | "all" => some .all
  | "any" => some .any
  | _ => none

def ifOperandMessage : String := "an `if` expression that is an operand is parenthesized"

mutual
  /-- `Path ::= Segment { "::" Segment }`. A `::` that is not followed by a name ends the path
  (the brace list of a `use`). -/
  partial def parsePath : ParseM Path := do
    let start ← peek
    let mut segments := #[← parseSegment]
    while (← peekKind) == .colonColon ∧ (← peekKind 1) == .identifier do
      discard advance
      segments := segments.push (← parseSegment)
    return .path (← spanFrom start) segments

  /-- `Segment ::= Name [ StaticArgs ]` -/
  partial def parseSegment : ParseM Segment := do
    let start ← peek
    let name ← parseName
    let staticArgs ← if (← peekKind) == .staticOpen then some <$> parseStaticArgs else pure none
    return .segment (← spanFrom start) name staticArgs

  /-- `StaticArgs ::= "<" StaticArg { "," StaticArg } ">"`. A refusal by `GR` inside is reported
  as LX5: the `<` touched a name, and was likely meant as a comparison. -/
  partial def parseStaticArgs : ParseM StaticArgs := do
    let start ← expect .staticOpen
    try
      let args ← commaList .staticClose parseStaticArg
      discard (expect .staticClose)
      -- SP11: a specification argument stands after the other static arguments
      let mut sawSpec := false
      for arg in args do
        match arg with
        | .spec .. => sawSpec := true
        | .term span .. | .inferred span .. =>
          if sawSpec then
            throw { rule := "SP11", span
                    message := "a specification argument stands after the other static arguments" }
      return .staticArgs (← spanFrom start) args
    catch error =>
      if error.rule == "GR" then
        failAt start "LX5"
          "write `a < b` for a comparison; `<` touching a name opens static arguments"
      else throw error

  /-- `StaticArg ::= [ Name "=" ] ( StaticTerm | "_" ) | "spec" Name "=" StaticTerm` -/
  partial def parseStaticArg : ParseM StaticArg := do
    let start ← peek
    if start.kind == .kwSpec ∧ (← peekKind 1) == .identifier ∧ (← peekKind 2) == .equals then
      discard advance
      let name ← parseName
      discard advance
      let term ← parseStaticTerm
      return .spec (← spanFrom start) name term
    let name ← if start.kind == .identifier ∧ (← peekKind 1) == .equals then
        let name ← parseName
        discard advance
        pure (some name)
      else pure none
    let next ← peekKind 1
    if (← peekKind) == .underscore ∧ (next == .comma ∨ next == .staticClose) then
      discard advance
      return .inferred (← spanFrom start) name
    let term ← parseStaticTerm
    return .term (← spanFrom start) name term

  /-- `StaticTerm ::= Sum`, with the primaries of GR5. -/
  partial def parseStaticTerm : ParseM Expr := withStatic parseSum

  /-- `Type` (§5.3) -/
  partial def parseType : ParseM TypeExpr := do
    let start ← peek
    match start.kind with
    | .kwBool => discard advance; return .bool (← spanFrom start)
    | .kwNat => discard advance; return .nat (← spanFrom start)
    | .kwRational => discard advance; return .rational (← spanFrom start)
    | .kwIndex =>
      discard advance
      discard (expectStaticOpen)
      let size ← parseStaticTerm
      discard (expect .staticClose)
      return .index (← spanFrom start) size
    | .kwNonzero =>
      discard advance
      discard (expectStaticOpen)
      let type ← parseType
      discard (expect .staticClose)
      return .nonzero (← spanFrom start) type
    | .leftBracket =>
      discard advance
      let element ← parseType
      let size ← if ← accept .semicolon then some <$> parseStaticTerm else pure none
      discard (expect .rightBracket)
      return .sequence (← spanFrom start) element size
    | .leftParen =>
      discard advance
      let fields ← commaList .rightParen parseTupleField (allowEmpty := true)
      discard (expect .rightParen)
      if fields.size == 1 then
        failAt start "GR" "a tuple type has no or at least two components"
      return .tuple (← spanFrom start) fields
    | .identifier =>
      if (← peekText) == "fn" ∧ (← peekKind 1) == .leftParen then
        fail "GR6"
          "function types and function literals are not part of the language: write a loop, a comprehension or a binder form"
      return .path (← spanFrom start) (← parsePath)
    | _ => unexpected "a type"

  /-- A `<` written apart from the word before it is a comparison (LX5); where static arguments
  must follow, it is refused by LX5. -/
  partial def expectStaticOpen : ParseM Token := do
    if (← peekKind) == .less then
      fail "LX5" "write `a < b` for a comparison; `<` touching a name opens static arguments"
    expect .staticOpen

  /-- `TupleField ::= [ Name ":" ] Type` -/
  partial def parseTupleField : ParseM TupleField := do
    let start ← peek
    let name ← if start.kind == .identifier ∧ (← peekKind 1) == .colon then
        let name ← parseName
        discard advance
        pure (some name)
      else pure none
    let type ← parseType
    return .tupleField (← spanFrom start) name type

  /-- `Expr ::= IfExpr | OrExpr` -/
  partial def parseExpr : ParseM Expr := do
    let start ← peek
    if start.kind == .kwIf then
      discard advance
      let condition ← parseExpr
      discard (expect .kwThen)
      let thenBranch ← parseExpr
      discard (expect .kwElse)
      let elseBranch ← parseExpr
      return .ifExpr (← spanFrom start) condition thenBranch elseBranch
    parseOr

  /-- `OrExpr ::= AndExpr { "or" AndExpr }` -/
  partial def parseOr : ParseM Expr := do
    let start ← peek
    let mut left ← parseAnd
    while (← peekKind) == .kwOr do
      discard advance
      let right ← parseAnd
      left := .orExpr (← spanFrom start) left right
    return left

  /-- `AndExpr ::= NotExpr { "and" NotExpr }` -/
  partial def parseAnd : ParseM Expr := do
    let start ← peek
    let mut left ← parseNot
    while (← peekKind) == .kwAnd do
      discard advance
      let right ← parseNot
      left := .andExpr (← spanFrom start) left right
    return left

  /-- `NotExpr ::= "not" NotExpr | Compare` -/
  partial def parseNot : ParseM Expr := do
    let start ← peek
    if start.kind == .kwNot then
      discard advance
      let operand ← parseNot
      return .notExpr (← spanFrom start) operand
    parseCompare

  /-- `Compare ::= Sum [ op Sum ]`; comparisons do not chain. -/
  partial def parseCompare : ParseM Expr := do
    let start ← peek
    let left ← parseSum
    match compareOperator? (← peekKind) with
    | some operator =>
      discard advance
      let right ← parseSum
      if (compareOperator? (← peekKind)).isSome then
        fail "GR" "comparisons do not chain; write `a < b and b < c`"
      return .compare (← spanFrom start) operator left right
    | none => return left

  /-- `Sum ::= Product { ( "+" | "-" | "++" ) Product }` -/
  partial def parseSum : ParseM Expr := do
    let start ← peek
    let mut left ← parseProduct
    repeat
      let operator? : Option SumOperator := match (← peekKind) with
        | .plus => some .add
        | .minus => some .subtract
        | .plusPlus => some .concatenate
        | _ => none
      match operator? with
      | some operator =>
        discard advance
        let right ← parseProduct
        left := .sum (← spanFrom start) operator left right
      | none => break
    return left

  /-- `Product ::= Unary { ( "*" | "/" | "%" ) Unary }` -/
  partial def parseProduct : ParseM Expr := do
    let start ← peek
    let mut left ← parseUnary
    repeat
      let operator? : Option ProductOperator := match (← peekKind) with
        | .star => some .multiply
        | .slash => some .divide
        | .percent => some .remainder
        | _ => none
      match operator? with
      | some operator =>
        discard advance
        let right ← parseUnary
        left := .product (← spanFrom start) operator left right
      | none => break
    return left

  /-- `Unary ::= "-" Unary | Power` -/
  partial def parseUnary : ParseM Expr := do
    let start ← peek
    if start.kind == .minus then
      discard advance
      let operand ← parseUnary
      return .unary (← spanFrom start) operand
    parsePower

  /-- `Power ::= Postfix [ "^" Unary ]` -/
  partial def parsePower : ParseM Expr := do
    let start ← peek
    let base ← parsePostfix
    if (← peekKind) == .caret then
      discard advance
      let exponent ← parseUnary
      return .power (← spanFrom start) base exponent
    return base

  /-- `Postfix ::= Primary { "." Name [ [ StaticArgs ] CallArgs ] | "." Number | "[" Expr "]"
  | "[" [ Expr ] ".." [ Expr ] "]" }` -/
  partial def parsePostfix : ParseM Expr := do
    let start ← peek
    let mut target ← parsePrimary
    repeat
      match (← peekKind) with
      | .dot =>
        if (← peekKind 1) == .number then
          discard advance
          let number ← parseNumber
          target := .position (← spanFrom start) target number
        else
          discard advance
          let name ← parseName
          if (← peekKind) == .staticOpen then
            let staticArgs ← parseStaticArgs
            if (← peekKind) != .leftParen then
              unexpected "`(`: static arguments after `.name` belong to a call"
            let args ← parseCallArgs
            target := .method (← spanFrom start) target name (some staticArgs) args
          else if (← peekKind) == .leftParen then
            let args ← parseCallArgs
            target := .method (← spanFrom start) target name none args
          else
            target := .field (← spanFrom start) target name
      | .leftBracket =>
        discard advance
        if ← accept .dotDot then
          let upper ← if (← peekKind) == .rightBracket then pure none else some <$> parseExpr
          discard (expect .rightBracket)
          target := .slice (← spanFrom start) target none upper
        else
          let lower ← parseExpr
          if ← accept .dotDot then
            let upper ← if (← peekKind) == .rightBracket then pure none else some <$> parseExpr
            discard (expect .rightBracket)
            target := .slice (← spanFrom start) target (some lower) upper
          else
            discard (expect .rightBracket)
            target := .index (← spanFrom start) target lower
      | _ => break
    return target

  partial def parseNumber : ParseM Number := do
    let token ← peek
    let text ← peekText
    discard (expect .number)
    return { span := tokenSpan (← get).file token, value := text.toNat! }

  partial def parseByteString : ParseM ByteString := do
    let token ← peek
    let text ← peekText
    let kind ← match token.kind with
      | .byteString => pure ByteStringKind.bytes
      | .hexString => pure ByteStringKind.hex
      | _ => unexpected "a byte string"
    discard advance
    return { span := tokenSpan (← get).file token, kind, content := text }

  /-- `Primary` (§5.6), with the primaries of GR5 in a static term. -/
  partial def parsePrimary : ParseM Expr := do
    let start ← peek
    match start.kind with
    | .number => return .number (← parseNumber)
    | .byteString | .hexString => return .byteString (← parseByteString)
    | .kwTrue => discard advance; return .trueLiteral (← spanFrom start)
    | .kwFalse => discard advance; return .falseLiteral (← spanFrom start)
    | .identifier => parsePathPrimary
    | .leftParen => parseParenthesized
    | .leftBracket => parseBracketed
    | .leftBrace =>
      discard advance
      let record ← parseExpr
      discard (expectWord "with")
      let fields ← commaList .rightBrace parseFieldUpdate
      discard (expect .rightBrace)
      return .recordUpdate (← spanFrom start) record fields
    | .sumSign | .productSign | .forAllSign | .existsSign =>
      discard advance
      let operator := (binderOperator? start.kind).getD .sum
      let pattern ← parsePattern
      discard (expect .elementSign)
      let domain ← parseDomain
      discard (expect .comma)
      let body ← parseExpr
      return .binderForm (← spanFrom start) operator .symbol pattern domain body
    | .innerOpen =>
      discard advance
      let left ← parseExpr
      discard (expect .comma)
      let right ← parseExpr
      discard (expect .innerClose)
      return .innerProduct (← spanFrom start) .symbol left right
    | .kwBool | .kwNat | .kwRational | .kwIndex | .kwNonzero =>
      if ← inStatic then
        match start.kind with
        | .kwBool => discard advance; return .boolType (← spanFrom start)
        | .kwNat => discard advance; return .natType (← spanFrom start)
        | .kwRational => discard advance; return .rationalType (← spanFrom start)
        | .kwIndex =>
          discard advance
          discard expectStaticOpen
          let size ← parseStaticTerm
          discard (expect .staticClose)
          return .indexType (← spanFrom start) size
        | _ =>
          discard advance
          discard expectStaticOpen
          let type ← parseType
          discard (expect .staticClose)
          return .nonzeroType (← spanFrom start) type
      else unexpected "an expression"
    | .kwIf => fail "GR2" ifOperandMessage
    | .underscore => fail "GR1" "`_` is a pattern, not an expression"
    | .kwSites => fail "EV4" "`sites.` stands only in a clause and in a line of a scheme"
    | .kwSend | .kwDraw | .kwSample | .kwQuery | .kwAttempt =>
      fail "EV2" "an event stands on its own `<-` line: write `x <- …`"
    | .newline =>
      fail "LX2" "the line ends inside an expression; a logical line continues only inside brackets"
    | .string =>
      fail "GR" "a string is not a value; it stands only where the grammar writes `String`"
    | kind =>
      -- a reserved word that begins no expression stands where a name could: it is never an
      -- identifier (LX9)
      if kind.isReservedWord then fail "LX9" s!"`{kind.spelling}` is a reserved word"
      unexpected "an expression"

  /-- A primary that starts with a path: the path, a call, or a record construction. The call
  of `sum`, `product`, `all` or `any` on one comprehension without a condition, and the call of
  `inner` on two arguments, are the named spellings of the mathematical forms (§3.5). -/
  partial def parsePathPrimary : ParseM Expr := do
    let start ← peek
    -- `fn` is a name (GR6); `fn(…)` followed by `=>` or `->` is a function literal or type
    if (← peekText) == "fn" ∧ (← peekKind 1) == .leftParen then
      if let some close ← matchingClose 1 then
        if (← atFatArrow (close + 1)) ∨ (← peekKind (close + 1)) == .rightArrow then
          fail "GR6"
            "function types and function literals are not part of the language: write a loop, a comprehension or a binder form"
    let path ← parsePath
    match (← peekKind) with
    | .leftParen =>
      let args ← parseCallArgs
      let span ← spanFrom start
      match path.plainName?, args with
      | some name, .callArgs _ #[.positional _ (.comprehension _ body pattern domain none)] none =>
        match binderOperatorOfName? name.text with
        | some operator => return .binderForm span operator .named pattern domain body
        | none => return .call span path args
      | some name, .callArgs _ #[.positional _ left, .positional _ right] none =>
        if name.text == "inner" then return .innerProduct span .named left right
        return .call span path args
      | _, _ => return .call span path args
    | .leftBrace =>
      discard advance
      let fields ← commaList .rightBrace parseFieldInit (allowEmpty := true)
      discard (expect .rightBrace)
      return .record (← spanFrom start) path fields
    | _ => return .path (← spanFrom start) path

  /-- `"(" ")" | "(" Expr ")" | "(" Expr "," Expr { "," Expr } ")"`; in a static term a
  component may be `Name ":" StaticTerm` (GR5). -/
  partial def parseParenthesized : ParseM Expr := do
    let start ← advance
    if ← accept .rightParen then return .unit (← spanFrom start)
    let static ← inStatic
    let component : ParseM TupleComponent := do
      let componentStart ← peek
      if static ∧ componentStart.kind == .identifier ∧ (← peekKind 1) == .colon then
        let name ← parseName
        discard advance
        let value ← parseStaticTerm
        return .component (← spanFrom componentStart) (some name) value
      let value ← parseExpr
      return .component (← spanFrom componentStart) none value
    let first ← component
    if (← peekKind) == .rightParen then
      discard advance
      match first with
      | .component _ none value => return .paren (← spanFrom start) value
      | .component _ (some _) _ => failAt start "GR" "a tuple has no or at least two components"
    let mut components := #[first]
    discard (expect .comma)
    if (← peekKind) == .rightParen then
      failAt start "GR" "a tuple has no or at least two components"
    components := components.push (← component)
    while (← peekKind) == .comma do
      discard advance
      if (← peekKind) == .rightParen then break
      components := components.push (← component)
    discard (expect .rightParen)
    return .tuple (← spanFrom start) components

  /-- The primaries that start with `[`: a list, a repetition, a comprehension. -/
  partial def parseBracketed : ParseM Expr := do
    let start ← advance
    if ← accept .rightBracket then return .list (← spanFrom start) #[]
    let first ← parseExpr
    match (← peekKind) with
    | .semicolon =>
      discard advance
      let count ← parseStaticTerm
      discard (expect .rightBracket)
      return .repetition (← spanFrom start) first count
    | .kwFor =>
      discard advance
      let pattern ← parsePattern
      discard (expect .kwIn)
      let domain ← parseDomain
      let filter ← if ← accept .kwIf then some <$> parseExpr else pure none
      discard (expect .rightBracket)
      return .comprehension (← spanFrom start) first pattern domain filter
    | _ =>
      let mut elements := #[first]
      while (← peekKind) == .comma do
        discard advance
        if (← peekKind) == .rightBracket then break
        elements := elements.push (← parseExpr)
      discard (expect .rightBracket)
      return .list (← spanFrom start) elements

  /-- `CallArgs ::= "(" [ Argument { "," Argument } ] [ ";" Argument { "," Argument } ] ")"` -/
  partial def parseCallArgs : ParseM CallArgs := do
    let start ← expect .leftParen
    let mut arguments := #[]
    if (← peekKind) != .rightParen ∧ (← peekKind) != .semicolon then
      arguments := arguments.push (← parseArgument)
      while (← peekKind) == .comma do
        discard advance
        if (← peekKind) == .rightParen then break
        arguments := arguments.push (← parseArgument)
    let witnesses ← if ← accept .semicolon then
        let mut witnesses := #[← parseArgument]
        while (← peekKind) == .comma do
          discard advance
          if (← peekKind) == .rightParen then break
          witnesses := witnesses.push (← parseArgument)
        pure (some witnesses)
      else pure none
    discard (expect .rightParen)
    return .callArgs (← spanFrom start) arguments witnesses

  /-- `Argument ::= Expr | Name "=" Expr | "spec" Name "=" Expr` -/
  partial def parseArgument : ParseM Argument := do
    let start ← peek
    if start.kind == .kwSpec ∧ (← peekKind 1) == .identifier ∧ (← peekKind 2) == .equals then
      discard advance
      let name ← parseName
      discard advance
      let value ← parseExpr
      return .spec (← spanFrom start) name value
    if start.kind == .identifier ∧ (← peekKind 1) == .equals then
      let name ← parseName
      discard advance
      let value ← parseExpr
      return .named (← spanFrom start) name value
    let value ← parseExpr
    return .positional (← spanFrom start) value

  /-- `FieldInit ::= Name [ "=" Expr ]` -/
  partial def parseFieldInit : ParseM FieldInit := do
    let start ← peek
    let name ← parseName
    let value ← if ← accept .equals then some <$> parseExpr else pure none
    return .fieldInit (← spanFrom start) name value

  /-- `Name "=" Expr` in a record update. -/
  partial def parseFieldUpdate : ParseM FieldUpdate := do
    let start ← peek
    let name ← parseName
    discard (expect .equals)
    let value ← parseExpr
    return .fieldUpdate (← spanFrom start) name value

  /-- `Domain ::= Sum [ ".." Sum ]` -/
  partial def parseDomain : ParseM Domain := do
    let start ← peek
    let first ← parseSum
    let stop ← if ← accept .dotDot then some <$> parseSum else pure none
    return .domain (← spanFrom start) first stop

  /-- `Pattern` (§5.7) -/
  partial def parsePattern : ParseM Pattern := do
    let start ← peek
    match start.kind with
    | .underscore => discard advance; return .wildcard (← spanFrom start)
    | .leftParen =>
      discard advance
      let first ← parsePattern
      discard (expect .comma)
      let mut items := #[first, ← parsePattern]
      while (← peekKind) == .comma do
        discard advance
        if (← peekKind) == .rightParen then break
        items := items.push (← parsePattern)
      discard (expect .rightParen)
      return .tuple (← spanFrom start) items
    | .identifier =>
      let path ← parsePath
      if (← peekKind) == .leftBrace then
        discard advance
        let fields ← commaList .rightBrace parseFieldPattern
        discard (expect .rightBrace)
        return .record (← spanFrom start) path fields
      match path.plainName? with
      | some name => return .name name
      | none => failAt start "GR1" "this is not a pattern"
    | _ => unexpected "a pattern"

  /-- `FieldPattern ::= Name [ "=" Pattern ]` -/
  partial def parseFieldPattern : ParseM FieldPattern := do
    let start ← peek
    let name ← parseName
    let pattern ← if ← accept .equals then some <$> parsePattern else pure none
    return .fieldPattern (← spanFrom start) name pattern
end

/-- `CasePattern` (§5.7) -/
partial def parseCasePattern : ParseM CasePattern := do
  let start ← peek
  match start.kind with
  | .number => return .number (← parseNumber)
  | .kwTrue => discard advance; return .trueLiteral (← spanFrom start)
  | .kwFalse => discard advance; return .falseLiteral (← spanFrom start)
  | .underscore => return .pattern (← parsePattern)
  | .leftParen =>
    discard advance
    let first ← parseCasePattern
    discard (expect .comma)
    let mut items := #[first, ← parseCasePattern]
    while (← peekKind) == .comma do
      discard advance
      if (← peekKind) == .rightParen then break
      items := items.push (← parseCasePattern)
    discard (expect .rightParen)
    return .tuple (← spanFrom start) items
  | .identifier =>
    let path ← parsePath
    match (← peekKind) with
    | .leftParen =>
      discard advance
      let payload ← commaList .rightParen parseCasePattern
      discard (expect .rightParen)
      return .variant (← spanFrom start) path (some payload)
    | .leftBrace =>
      discard advance
      let fields ← commaList .rightBrace parseFieldPattern
      discard (expect .rightBrace)
      return .pattern (.record (← spanFrom start) path fields)
    | _ =>
      -- a single name is the `Pattern` alternative; the checker decides whether it names an
      -- alternative of a variant
      match path.plainName? with
      | some name => return .pattern (.name name)
      | none => return .variant (← spanFrom start) path none
  | _ => unexpected "a pattern"

end Zkc.Frontend.Syntax.Parser
