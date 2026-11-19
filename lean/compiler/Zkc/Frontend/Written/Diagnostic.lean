module

public import Zkc.Frontend.Syntax.Span

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Syntax

abbrev ExportM := Except String

def location (span : Span) := s!"{span.file}:{span.render}"

def refuse {α : Type} (span : Span) (rule message : String) : ExportM α :=
  .error s!"{location span}: {rule}: {message}"

end Zkc.Frontend.Written
