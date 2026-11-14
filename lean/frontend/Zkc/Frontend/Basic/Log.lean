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

structure Log where
  /-- The diagnostics shown, each once, in the order they were made. -/
  entries : Array Diagnostic := #[]
  /-- The severity, file, first byte and rule of every diagnostic shown. -/
  seen : Std.HashSet Diagnostic.Key := {}
  /-- The number of errors given to the log, those not shown again included. -/
  errors : Nat := 0
  /-- The number of incomplete checks given to the log, those not shown again included. -/
  incomplete : Nat := 0
  deriving Inhabited

namespace Log

/-- The log with one more diagnostic. An error and an incomplete check are counted; the
diagnostic is shown unless one of its severity and rule stands at its place already. -/
def add (log : Log) (diagnostic : Diagnostic) : Log :=
  let errors := if diagnostic.isError then log.errors + 1 else log.errors
  let incomplete := if diagnostic.isIncomplete then log.incomplete + 1 else log.incomplete
  if log.seen.contains diagnostic.key then { log with errors, incomplete }
  else
    { entries := log.entries.push diagnostic
      seen := log.seen.insert diagnostic.key
      errors, incomplete }

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
