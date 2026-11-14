import Zkc.Tools.Frontend

open Zkc.Tools.Frontend

def usage : String :=
  "usage: zkc-syntax check <files>…
       zkc-syntax format <file>
       zkc-syntax dump [--no-spans] <file>
       zkc-syntax bench [--phase lex|parse|all] [--repeat <n>] <file>
       zkc-syntax generate <lines> <file>"

/-- `bench [--phase lex|parse|all] [--repeat <n>] <file>` -/
partial def benchCommand (args : List String) (phase : Bench.Phase := .all) (repetitions : Nat := 5) :
    IO UInt32 :=
  match args with
  | "--phase" :: "lex" :: rest => benchCommand rest .lex repetitions
  | "--phase" :: "parse" :: rest => benchCommand rest .parse repetitions
  | "--phase" :: "all" :: rest => benchCommand rest .all repetitions
  | "--repeat" :: count :: rest =>
    match count.toNat? with
    | some n => benchCommand rest phase n
    | none => do IO.eprintln usage; return 2
  | [path] => Bench.run path phase repetitions
  | _ => do IO.eprintln usage; return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: paths@(_ :: _) => check paths
  | ["format", path] => formatCommand path
  | ["dump", path] => dump path true
  | ["dump", "--no-spans", path] => dump path false
  | "bench" :: rest => benchCommand rest
  | ["generate", lines, path] =>
    match lines.toNat? with
    | some count =>
      IO.FS.writeFile path (Generate.program count)
      return 0
    | none =>
      IO.eprintln usage
      return 2
  | _ =>
    IO.eprintln usage
    return 2
