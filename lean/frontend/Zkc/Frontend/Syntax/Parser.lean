module

public import Zkc.Frontend.Syntax.Parser.Decl

@[expose] public section

set_option autoImplicit false

namespace Zkc.Frontend.Syntax

/-- Parses the tokens of one source file. -/
def parseLexed (file : String) (lexed : Lexed) : Except SyntaxError SourceFile := do
  let state : Parser.State :=
    { tokens := lexed.tokens, texts := lexed.texts, file, index := 0
      lastLine := 1, lastColumn := 1, lastByte := 0, staticDepth := 0 }
  match Parser.parseFile.run state with
  | .ok tree _ => pure { tree, comments := lexed.comments }
  | .error error _ => throw error

/-- Lexes and parses one source file: its tree and comments, or the first refusal, with the rule
of the reference that refuses. -/
def parse (file : String) (source : ByteArray) : Except SyntaxError SourceFile := do
  return { (← parseLexed file (← lex file source)) with source }

/-- Parses a source given as text. -/
def parseString (file : String) (source : String) : Except SyntaxError SourceFile :=
  parse file source.toUTF8

/-- The expression that a piece of a source holds by itself, when it holds one: the text
between two bytes that a span gives. -/
def parseExprBytes (file : String) (source : ByteArray) : Except SyntaxError Expr := do
  let lexed ← lex file source
  let state : Parser.State :=
    { tokens := lexed.tokens, texts := lexed.texts, file, index := 0
      lastLine := 1, lastColumn := 1, lastByte := 0, staticDepth := 0 }
  match Parser.parseExpr.run state with
  | .ok expr _ => pure expr
  | .error error _ => throw error

end Zkc.Frontend.Syntax
