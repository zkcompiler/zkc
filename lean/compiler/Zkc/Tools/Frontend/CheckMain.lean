import Zkc.Tools.Frontend.Names

open Zkc.Tools.Frontend

def usage : String :=
  "usage: zkc-check names [--library <dir>]… <files>…
       zkc-check resolutions [--library <dir>]… <files>…
       zkc-check instances [--library <dir>]… [--contents] <files>…
       zkc-check types [--library <dir>]… <files>…
       zkc-check bench [--library <dir>]… [--repeat <n>] <files>…
a module `zkc::a::b` that no given file has is read from `<dir>/zkc/a/b.zkc`"

/-- The options that each command takes; any other is a wrong command line. -/
def optionsOf : String → Array String
  | "names" | "resolutions" => #["--library"]
  | "instances" => #["--library", "--contents"]
  | "types" => #["--library"]
  | "bench" => #["--library", "--repeat"]
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
  | "bench" :: rest => run "bench" Names.bench rest
  | [] => wrong ""
  | command :: _ => wrong s!"no command `{command}`"
