module

public import ZkcTools.CommonSource.Reference

@[expose] public section

def main (args : List String) : IO UInt32 := do
  let mode := args.headD ""
  let file := args[1]?.getD ""
  if (mode != "check" || args.length != 2) && (mode != "run" || args.length != 3) then
    return ← Zkc.Tools.refused "common-source-arguments"
  let input ← ZkcTools.CommonSource.read file
  let .ok json := input | return ← Zkc.Tools.refused (match input with | .error code => code | _ => "common-source-json")
  let decoded := Zkc.Source.Common.Native.Format.snapshot json
  let .ok snapshot := decoded | return ← Zkc.Tools.refused (match decoded with | .error code => code | _ => "common-source-format")
  match snapshot.check with
  | .error code => Zkc.Tools.refused code
  | .ok imported =>
      if mode == "check" then
        Zkc.Tools.emit (.arr #[.str "checked", .str snapshot.source, .str snapshot.symbol])
        return 0
      let .ok inputs ← ZkcTools.CommonSource.read args[2]!
        | return ← Zkc.Tools.refused "common-run-json"
      match ZkcTools.CommonSource.evaluate imported inputs with
      | .error code => Zkc.Tools.refused code
      | .ok result => Zkc.Tools.emit result; return 0
