import Zkc.Tools.Frontend.Differential
import Zkc.Tools.Frontend.Trees
import Zkc.Tools.Frontend.Reading

open Zkc.Tools.Frontend

def usage : String :=
  "usage: zkc-check names [--library <dir>]… <files>…
       zkc-check resolutions [--library <dir>]… <files>…
       zkc-check instances [--library <dir>]… [--contents] <files>…
       zkc-check types [--library <dir>]… [--packages <dir> [--root <root>] [--scheme <name>]] <files>…
       zkc-check trees [--library <dir>]… [--contents] [--runs [--uninterpreted] [--seeds <n>]] [--count] <files>…
       zkc-check run [--library <dir>]… --root <root> [--function <name>] [--role <role>]… [--messages <json>] [--seed <n>] --inputs <json> <files>…
       zkc-check bench [--library <dir>]… [--repeat <n>] <files>…
       zkc-check measure [--library <dir>]… --root <root> (--inputs <json> | --inputs-file <path>) [--repeat <n>] [--no-run] <files>…
       zkc-check prove [--library <dir>]… --scheme <name> --statement <json> --witness <json> [--seed <n>] <files>…
       zkc-check verify [--library <dir>]… --scheme <name> --statement <json> --proof <hex> <files>…
       zkc-check compare [--library <dir>]… --baseline <dir> [--write] [--seeds <n>] [--budget <ms>] [--runs] [--uninterpreted] [--generator <root>=<function root>]… [--mutants <n>] <files>…
a module `zkc::a::b` that no given file has is read from `<dir>/zkc/a/b.zkc`"

/-- The options that each command takes; any other is a wrong command line. -/
def optionsOf : String → Array String
  | "names" | "resolutions" => #["--library"]
  | "instances" => #["--library", "--contents"]
  | "trees" => #["--library", "--contents", "--runs", "--uninterpreted", "--seeds", "--count"]
  | "types" => #["--library", "--packages", "--root", "--scheme"]
  | "run" => #["--library", "--root", "--function", "--inputs", "--role", "--messages", "--seed"]
  | "bench" => #["--library", "--repeat"]
  | "measure" => #["--library", "--root", "--inputs", "--inputs-file", "--repeat", "--no-run", "--seed"]
  | "prove" => #["--library", "--scheme", "--statement", "--witness", "--seed"]
  | "verify" => #["--library", "--scheme", "--statement", "--proof"]
  | "compare" => #["--library", "--baseline", "--write", "--seeds", "--budget", "--runs", "--uninterpreted", "--generator", "--mutants"]
  | _ => #[]

/-- A wrong command line, with the usage, exits with 2. -/
def main (args : List String) : IO UInt32 := do
  let wrong (message : String) : IO UInt32 := do
    unless message.isEmpty do IO.eprintln message
    IO.eprintln usage
    return 2
  let run (name : String) (command : Names.Options → IO UInt32) (rest : List String) : IO UInt32 :=
    match Names.readOptions rest {} with
    | .ok options =>
      match rest.find? fun word => word.startsWith "--" && !(optionsOf name).contains word with
      | some word => wrong s!"`{name}` takes no option `{word}`"
      | none => if options.files.isEmpty then wrong "no file is given" else command options
    | .error message => wrong message
  match args with
  | "names" :: rest => run "names" Names.names rest
  | "resolutions" :: rest => run "resolutions" Names.resolutions rest
  | "instances" :: rest => run "instances" Names.instances rest
  | "types" :: rest => run "types" Names.types rest
  | "trees" :: rest => run "trees" Reading.trees rest
  | "run" :: rest => run "run" Names.run rest
  | "bench" :: rest => run "bench" Names.bench rest
  | "measure" :: rest => run "measure" Names.measure rest
  | "prove" :: rest => run "prove" Names.prove rest
  | "verify" :: rest => run "verify" Names.verify rest
  | "compare" :: rest => run "compare" Differential.compare rest
  | [] => wrong ""
  | command :: _ => wrong s!"no command `{command}`"
