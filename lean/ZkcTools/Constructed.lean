module

public import Zkc.Source.Constructed.Format
public import ZkcTools.Constructed.Replay

@[expose] public section

open Lean Zkc.Source.Constructed

def main (args : List String) : IO UInt32 := do
  let path :: rest := args | return ← Zkc.Tools.refused "constructed-source-arguments"
  if rest.length > 1 then return ← Zkc.Tools.refused "constructed-source-arguments"
  let input ← Zkc.Tools.readJson path
  let .ok json := input | return ← Zkc.Tools.refused (match input with | .error code => code | _ => "constructed-source-json")
  match Format.snapshot json with
  | .error e => Zkc.Tools.refused e.code
  | .ok snapshot =>
    match snapshot.check with
    | .error code => Zkc.Tools.refused code
    | .ok imported =>
      if let [runPath] := rest then
        let input ← Zkc.Tools.readJson runPath
        let evaluate := fun json => match json with
          | .arr #[.str "zkc.constructed-runs/0", .arr requests] => do
            let results ← requests.toList.mapM (Zkc.Tools.Constructed.evaluate imported)
            return Json.arr results.toArray
          | _ => Zkc.Tools.Constructed.evaluate imported json
        match input.bind evaluate with
        | .error code => return ← Zkc.Tools.refused code
        | .ok result => Zkc.Tools.emit result; return 0
      Zkc.Tools.emit <| Json.mkObj [("status", .str "admitted"),
        ("source", .str snapshot.source), ("candidate", .str snapshot.candidate),
        ("instructions", toJson snapshot.instructions.length),
        ("handlers", toJson snapshot.handlers.length)]
      return 0
