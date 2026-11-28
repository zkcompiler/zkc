module

public import Std.Data.HashSet
public import Zkc.Frontend.Basic.Diagnostic

@[expose] public section

set_option autoImplicit false

/-!
# The log of diagnostics

The log keeps the diagnostics in the order they were made and shows each once: a second
diagnostic of the same severity and rule at the same place is not kept, so a generic declaration
refused at several instances is shown once, with the chain of the first. What is kept for display
does not decide what was found: every error the log is given is counted, kept or not, so that
"was anything refused since this point" is a comparison of two numbers that a repeated refusal
still advances. The checks left incomplete, when a budget of the compiler ran out, are counted
apart from the errors: they refuse nothing (SP10).
-/

namespace Zkc.Frontend

/-- An incomplete depth check, including its structured budget. -/
def Diagnostic.isDepthIncomplete (diagnostic : Diagnostic) : Bool :=
  diagnostic.isIncomplete && diagnostic.exhaustion.any (·.budget == .instantiationDepth)

structure DiagnosticLog where
  /-- The diagnostics shown, each once, in the order they were made. -/
  entries : Array Diagnostic := #[]
  /-- The severity, file, first byte and rule of every diagnostic shown. -/
  seen : Std.HashSet Diagnostic.Key := {}
  /-- The number of errors given to the log, those not shown again included. -/
  errors : Nat := 0
  /-- The number of incomplete checks given to the log, those not shown again included. -/
  incomplete : Nat := 0
  /-- Instantiation-depth occurrences, including those deduplicated for display. -/
  depthIncomplete : Nat := 0
  deriving Inhabited

namespace DiagnosticLog

/-- The log with one more diagnostic. An error and an incomplete check are counted; the
diagnostic is shown unless one of its severity and rule stands at its place already. -/
def add (log : DiagnosticLog) (diagnostic : Diagnostic) : DiagnosticLog :=
  let errors := if diagnostic.isError then log.errors + 1 else log.errors
  let incomplete := if diagnostic.isIncomplete then log.incomplete + 1 else log.incomplete
  let depthIncomplete := if diagnostic.isDepthIncomplete then
    log.depthIncomplete + 1 else log.depthIncomplete
  if log.seen.contains diagnostic.key then { log with errors, incomplete, depthIncomplete }
  else
    { entries := log.entries.push diagnostic
      seen := log.seen.insert diagnostic.key
      errors, incomplete, depthIncomplete }

/-- Publish an isolated log, counting even the occurrences deduplicated for display. -/
def append (log observed : DiagnosticLog) : DiagnosticLog :=
  let merged := observed.entries.foldl add log
  { merged with
    errors := log.errors + observed.errors
    incomplete := log.incomplete + observed.incomplete
    depthIncomplete := log.depthIncomplete + observed.depthIncomplete }

end DiagnosticLog

/-- If default roots extend the module graph, its next validation replaces the preliminary
depth cutoffs. This projection contains all other occurrences, even at the same display key. -/
structure ModuleDepthRetry where
  retained : DiagnosticLog
  roots : Nat
  depth : Nat
  /-- Only the isolated program validation pass may publish provisional owner cutoffs. -/
  collecting : Bool := false
  deriving Inhabited

structure Log extends DiagnosticLog where
  moduleDepthRetry : Option ModuleDepthRetry := none
  /-- Advances only when the program validator supersedes its preliminary depth cutoffs. -/
  moduleDepthRevision : Nat := 0
  deriving Inhabited

namespace Log

def add (log : Log) (diagnostic : Diagnostic) : Log :=
  { log with toDiagnosticLog := log.toDiagnosticLog.add diagnostic
             moduleDepthRetry := log.moduleDepthRetry.map fun retry =>
               {retry with retained := retry.retained.add diagnostic} }

/-- Publish the local owner's log. Only a check that actually ended at the depth limit
has retryable depth occurrences. Its other observations, and every other local outcome,
remain in both projections. -/
def append (log : Log) (observed : DiagnosticLog) (ownerDepthFailure : Bool := false) : Log :=
  let retained (retry : ModuleDepthRetry) := Id.run do
    unless retry.collecting && ownerDepthFailure && observed.depthIncomplete != 0 do
      return retry.retained.append observed
    let stable := observed.entries.foldl (init := retry.retained) fun kept d =>
      if d.isDepthIncomplete then kept else kept.add d
    return {stable with
      errors := retry.retained.errors + observed.errors
      incomplete := retry.retained.incomplete + (observed.incomplete - observed.depthIncomplete)}
  { log with toDiagnosticLog := log.toDiagnosticLog.append observed
             moduleDepthRetry := log.moduleDepthRetry.map fun retry =>
               {retry with retained := retained retry} }

/-- Display offsets can differ when a provisional observation wins a display key. -/
structure Cursor where
  visible : Nat
  retained : Nat
  deriving Inhabited, BEq

def cursor (log : Log) : Cursor :=
  ⟨log.entries.size, (log.moduleDepthRetry.map (·.retained.entries.size)).getD log.entries.size⟩

def hasErrors (log : Log) : Bool := log.errors != 0

/-- Whether an error was logged since the log had `mark` errors. -/
def hasErrorsSince (log : Log) (mark : Nat) : Bool := mark < log.errors

/-- Whether a check was left incomplete because a budget of the compiler ran out. -/
def hasIncomplete (log : Log) : Bool := log.incomplete != 0

/-- The diagnostics in the order of output: by the rank of their file (the files given to the
tool first, in the order given), then line, column and rule. -/
def sorted (log : Log) (fileRank : String → Nat) : Array Diagnostic :=
  log.entries.qsort fun first second =>
    let a := [fileRank first.span.file, first.span.startLine.toNat, first.span.startColumn.toNat]
    let b := [fileRank second.span.file, second.span.startLine.toNat, second.span.startColumn.toNat]
    a < b || (a == b && first.rule < second.rule)

end Log

end Zkc.Frontend
