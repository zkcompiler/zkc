module

public import Zkc.Frontend.Syntax.Span

@[expose] public section

set_option autoImplicit false

namespace Zkc.Frontend.Syntax

/-- A refusal of the lexer or the parser: the identifier of the rule of the reference that
refuses (`LX4`, `GR1`, or `GR` alone for a token that no production admits), where, and the
message. Where the reference gives a message for the case, the message is its wording. -/
structure SyntaxError where
  rule : String
  span : Span
  message : String
  deriving Inhabited

namespace SyntaxError

def line (error : SyntaxError) : Nat := error.span.startLine.toNat

def column (error : SyntaxError) : Nat := error.span.startColumn.toNat

/-- `refuse <rule> <line>:<column> <message>`, the line that `zkc-syntax check` prints. -/
def render (error : SyntaxError) : String :=
  s!"refuse {error.rule} {error.line}:{error.column} {error.message}"

end SyntaxError

end Zkc.Frontend.Syntax
