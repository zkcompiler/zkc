module

public import Zkc.Frontend.Syntax.Parser
public import Zkc.Frontend.Syntax.Printer
public import Zkc.Frontend.Syntax.Canonical

@[expose] public section

set_option autoImplicit false

namespace Zkc.Frontend.Syntax

/-- The canonical text of a parsed source (§3.6): its canonical tree, printed with its
comments. -/
def formatSourceFile (parsed : SourceFile) : String :=
  printFile (canonicalize parsed.tree) parsed.comments

/-- The canonical text of a source, or the refusal of the lexer or the parser. -/
def format (file : String) (source : ByteArray) : Except SyntaxError String :=
  formatSourceFile <$> parse file source

end Zkc.Frontend.Syntax
