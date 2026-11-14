module

public import Zkc.Frontend.Basic.Message
public import Zkc.Frontend.Basic.Options
public import Zkc.Frontend.Semantics.Refusal
public import Zkc.Frontend.Syntax.Error

@[expose] public section

set_option autoImplicit false

/-!
# Diagnostics

Every phase reports with one type: the rule of the reference that refuses, the place, the
message, the chain of instantiations around the place (SP7), and notes. A diagnostic is logged
when it is made; it is not an exception. What a later reader needs to decide whether to show it,
to sort it and to map it to an editor is in its fields, not in its text.

A check that runs out of a budget of the compiler is reported with a diagnostic of its own
severity, which carries the budget, its value and what was asked for: it is not a refusal.
-/

namespace Zkc.Frontend

open Syntax

inductive Severity where
  /-- The program is refused. -/
  | error
  /-- The program is accepted; the author is told something. -/
  | warning
  /-- A report without a judgement: a declaration without a default instance, a body that waits
  for a form of a later layer. -/
  | information
  /-- A check that did not finish: a budget of the compiler ran out. It refuses nothing and
  proves nothing (SP10). -/
  | incomplete
  deriving Inhabited, BEq, Hashable, Repr

/-- Which part of the pipeline made a diagnostic. A diagnostic of the core is what its admission
or its check of facts found in an emitted package, placed at the source it came from. -/
inductive DiagnosticOrigin where
  | syntax
  | names
  | instances
  | elaboration
  | analysis
  | emission
  | core
  deriving Inhabited, BEq, Repr

/-- One line of an instantiation chain: what was being instantiated, and the place of the
reference that asked for it. -/
structure ChainFrame where
  subject : Message
  span : Span
  deriving Inhabited

/-- A remark attached to a diagnostic, with a place of its own when it has one: the binder a
linear value came from, the earlier event of the same name. -/
structure Note where
  span : Option Span := none
  message : Message
  deriving Inhabited

/-- A budget of the compiler that ran out: which, at what value, and what was asked for when it
did. -/
structure Exhaustion where
  budget : Budget
  limit : Nat
  /-- What was asked for, as a line of a chain names it, with the place it was asked from. -/
  request : ChainFrame
  deriving Inhabited

/-- `<what the budget bounds> reaches its budget of <value> at `<request>``. -/
def Exhaustion.describe (exhaustion : Exhaustion) : String :=
  s!"{exhaustion.budget.describe} reaches its budget of {exhaustion.limit} at `{exhaustion.request.subject.renderWith Renderer.plain false}`"

structure Diagnostic where
  severity : Severity := .error
  origin : DiagnosticOrigin := .elaboration
  /-- The identifier of the rule of the reference: `NL3`, `SP4`. -/
  rule : String
  span : Span
  message : Message
  /-- The instantiations around the place, innermost first; empty outside an instance. -/
  chain : Array ChainFrame := #[]
  notes : Array Note := #[]
  /-- The budget that ran out, for an incomplete check. -/
  exhaustion : Option Exhaustion := none
  deriving Inhabited

namespace Diagnostic

/-- What makes two diagnostics one: the severity, the file, the first byte and the rule. A generic
declaration refused at several instances is shown once, with the chain of the first; an error is
never one with a warning. -/
abbrev Key := Severity × String × UInt32 × String

def key (diagnostic : Diagnostic) : Key :=
  (diagnostic.severity, diagnostic.span.file, diagnostic.span.startByte, diagnostic.rule)

def isError (diagnostic : Diagnostic) : Bool := diagnostic.severity == .error

def isIncomplete (diagnostic : Diagnostic) : Bool := diagnostic.severity == .incomplete

/-- The word a line of output starts with. -/
def verb : Severity → String
  | .error => "refuse"
  | .warning => "warn"
  | .information => "note"
  | .incomplete => "incomplete"

/-- `refuse <rule> <line>:<column> <message>`, one line per frame of the chain as SP7 prints
it, and one line per note. -/
def render (renderer : Renderer) (diagnostic : Diagnostic) : String :=
  let head := s!"{verb diagnostic.severity} {diagnostic.rule} {diagnostic.span.startLine}:{diagnostic.span.startColumn} {diagnostic.message.render renderer}"
  let chained := diagnostic.chain.foldl (init := head) fun text frame =>
    s!"{text}\n      in {frame.subject.renderWith renderer false} ({frame.span.file}:{frame.span.startLine})"
  diagnostic.notes.foldl (init := chained) fun text note =>
    match note.span with
    | some span => s!"{text}\n      note {span.startLine}:{span.startColumn} {note.message.render renderer}"
    | none => s!"{text}\n      note {note.message.render renderer}"

/-- The refusal of the lexer or the parser. -/
def ofSyntax (error : SyntaxError) : Diagnostic :=
  { origin := .syntax, rule := error.rule, span := error.span, message := .ofText error.message }

/-- A `Refusal` as a diagnostic: its message is one text. -/
def ofRefusal (refusal : Refusal) (origin : DiagnosticOrigin := .elaboration) : Diagnostic :=
  { origin, rule := refusal.rule, span := refusal.span, message := .ofText refusal.message
    chain := refusal.chain.map fun frame => { subject := .ofText frame.description, span := frame.span } }

/-- The diagnostic as a `Refusal`, with its message rendered, for a reader that takes one. -/
def toRefusal (renderer : Renderer) (diagnostic : Diagnostic) : Refusal :=
  { rule := diagnostic.rule, span := diagnostic.span, message := diagnostic.message.render renderer
    chain := diagnostic.chain.map fun frame =>
      { description := frame.subject.renderWith renderer false, span := frame.span } }

end Diagnostic

end Zkc.Frontend
