module

public import Zkc.Frontend.Syntax.Span

@[expose] public section

set_option autoImplicit false

/-!
# Refusals of the checker

A refusal names the rule of the reference that refuses, the place, and the message. A refusal
at an instance carries the chain of instantiations through which the instance was reached,
innermost first (SP7). The checker logs diagnostics (`Zkc.Frontend.Basic.Diagnostic`); a refusal
is a diagnostic as the tool prints it and the tests read it, made from the log at the end.
-/

namespace Zkc.Frontend

open Syntax

/-- One line of an instantiation chain: the instance as source writes it (`fold<k = 19>`) and
the place of the reference that asked for it. -/
structure Frame where
  description : String
  span : Span
  deriving Inhabited

/-- A refusal of the checker. -/
structure Refusal where
  /-- The identifier of the rule of the reference: `NL3`, `SP4`. -/
  rule : String
  span : Span
  message : String
  /-- The instantiations around the place, innermost first; empty outside an instance. -/
  chain : Array Frame := #[]
  deriving Inhabited

namespace Refusal

/-- `refuse <rule> <line>:<column> <message>` and one line per frame, as SP7 prints a chain. -/
def render (refusal : Refusal) : String :=
  let head :=
    s!"refuse {refusal.rule} {refusal.span.startLine}:{refusal.span.startColumn} {refusal.message}"
  refusal.chain.foldl (init := head) fun text frame =>
    s!"{text}\n      in {frame.description} ({frame.span.file}:{frame.span.startLine})"

end Refusal

end Zkc.Frontend
