import Zkc.Frontend

/-!
# The commands of `zkc-syntax`
-/

namespace Zkc.Tools.Frontend

open Zkc.Frontend.Syntax

def readSource (path : String) : IO ByteArray :=
  IO.FS.readBinFile path

/-- `check <files>`: one line per file, `accept` or `refuse <rule> <line>:<column> <message>`.
The exit code is 1 when a file is refused. -/
def check (paths : List String) : IO UInt32 := do
  let mut refused := false
  for path in paths do
    let source ← readSource path
    match parse path source with
    | .ok _ => IO.println s!"{path}: accept"
    | .error error =>
      refused := true
      IO.println s!"{path}: {error.render}"
  return if refused then 1 else 0

/-- `dump <file>`: the tree in its stable text form; `--no-spans` leaves the spans out. -/
def dump (path : String) (withSpans : Bool) : IO UInt32 := do
  let source ← readSource path
  match parse path source with
  | .ok parsed =>
    IO.print (dumpFile parsed.tree withSpans)
    return 0
  | .error error =>
    IO.eprintln s!"{path}: {error.render}"
    return 1

end Zkc.Tools.Frontend

namespace Zkc.Tools.Frontend

open Zkc.Frontend.Syntax

/-- `format <file>`: the canonical text (§3.6) on standard output. -/
def formatCommand (path : String) : IO UInt32 := do
  let source ← readSource path
  match format path source with
  | .ok text =>
    IO.print text
    return 0
  | .error error =>
    IO.eprintln s!"{path}: {error.render}"
    return 1

end Zkc.Tools.Frontend
