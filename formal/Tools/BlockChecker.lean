import Zkc.Compiler.Blocks.Rewriting
import Zkc.Protocols.BlockProfiles
import Tools.JsonSupport

set_option autoImplicit false

open Lean Zkc.Compiler.Blocks Zkc.Protocols.BlockProfiles
namespace Tools.BlockChecker

structure Literal where
  tag : String
  words : List Nat
  deriving DecidableEq, Repr

def index (j : Json) : Except String Nat := do
  let i ← j.getNat?
  if i >= 512 then throw "index-limit"
  pure i

def parseExpr : Nat → Json → Except String (Expr Literal)
  | 0, _ => .error "depth-limit"
  | fuel+1,j => do
    let a ← j.getArr?
    let tag ← (a.getD 0 Json.null).getStr?
    if tag == "input" && a.size == 2 then pure (.input (← index (a.getD 1 Json.null)))
    else if tag == "literal" && a.size == 3 then
      let t ← (a.getD 1 Json.null).getStr?
      let values ← (a.getD 2 Json.null).getArr?
      let xs ← values.toList.mapM Json.getNat?
      if !(t == "unit" && xs.isEmpty || t == "shift:u6" && xs.length == 1 && xs.all (· < 64) ||
          t == "scalar:q2305843009213697249" && xs.length == 1 && xs.all (· < 2305843009213697249)) then
        throw "unsupported-or-invalid-literal"
      pure (.literal ⟨t,xs⟩)
    else if tag == "apply" && a.size == 4 then
      pure (.apply (← (a.getD 1 Json.null).getStr?)
        (← parseExpr fuel (a.getD 2 Json.null)) (← parseExpr fuel (a.getD 3 Json.null)))
    else if tag == "choose" && a.size == 4 then
      pure (.choose (← parseExpr fuel (a.getD 1 Json.null))
        (← parseExpr fuel (a.getD 2 Json.null)) (← parseExpr fuel (a.getD 3 Json.null)))
    else throw "unsupported-expression-kind-or-arity"

def parseBlock (j : Json) : Except String (Block Literal) := do
  let rows ← j.getArr?
  if rows.size > 256 then throw "block-limit"
  rows.toList.mapM fun row => do
    let a ← row.getArr?
    if a.size != 2 then throw "assignment-arity"
    pure (← index (a.getD 0 Json.null), ← parseExpr 12 (a.getD 1 Json.null))

def parseExports (j : Json) : Except String (List (Nat × String)) := do
  let a ← j.getArr?
  if a.size == 0 || a.size > 32 then throw "export-count"
  a.toList.mapM fun row => do
    let r ← row.getArr?
    if r.size != 2 then throw "export-arity"
    pure (← index (r.getD 0 Json.null), ← (r.getD 1 Json.null).getStr?)

def runOne (j : Json) : Except String Json := do
  let profile ← j.getObjValAs? String "profile"
  if profile != "sumcheck:q2305843009213697249" && profile != "fri:babybear-r19" then
    throw "unresolved-profile"
  let inputs ← j.getObjValAs? (Array String) "input_types"
  if inputs.size > 128 then throw "input-limit"
  let ctx : Context String := fun i => inputs[i]?
  let source ← parseBlock (← j.getObjVal? "source")
  let target ← parseBlock (← j.getObjVal? "target")
  let ss ← parseExports (← j.getObjVal? "source_exports")
  let ts ← parseExports (← j.getObjVal? "target_exports")
  let sout ← match inferBlock (registry profile) Literal.tag "flag" source ctx with
    | some out => pure out
    | none => throw "source-formation-refused"
  let tout ← match inferBlock (registry profile) Literal.tag "flag" target ctx with
    | some out => pure out
    | none => throw "target-formation-refused"
  if !exportsCheck sout ss || !exportsCheck tout ts || ss.map Prod.snd != ts.map Prod.snd then
    throw "export-contract-refused"
  let sd := (ss.map Prod.fst).toFinset
  let td := (ts.map Prod.fst).toFinset
  -- Formation already ensures input coverage. Retain inferred demands as useful
  -- output for projected caches, not as an independent acceptance obligation.
  let mode ← j.getObjValAs? String "law"
  let semantic :=
    if mode == "horner-right-semiring" && profile == "sumcheck:q2305843009213697249" &&
        source.length <= 8 && target.length <= 8 then
      admission (registry profile) Literal.tag "flag" ctx source target ss ts .horner
    else if mode == "identity-plus-valid-cache" then
      admission (registry profile) Literal.tag "flag" ctx source target ss ts .identity
    else false
  pure (Json.mkObj [("status",toJson (if semantic then "admitted-conditional" else "semantic-law-refused")),
    ("formation",toJson "checked"),("law",toJson mode),
    ("source_required",toJson ((List.range 512).filter (· ∈ requiredInputs source sd))),
    ("target_required",toJson ((List.range 512).filter (· ∈ requiredInputs target td)))])

def report (j : Json) : Json :=
  let id := (j.getObjValAs? String "id").toOption.getD "unnamed"
  let result := match runOne j with
    | .ok r => r
    | .error e => Json.mkObj [("status",toJson "refused-or-malformed"),("reason",toJson e)]
  Json.mkObj [("id",toJson id),("result",result)]
end Tools.BlockChecker

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    match (← Zkc.Tools.readJson path) >>= Json.getArr? with
    | .error e => IO.eprintln e; pure 2
    | .ok a =>
      for j in a do IO.println (Tools.BlockChecker.report j).compress
      pure 0
  | _ => IO.eprintln "usage: block-checker CASES.json"; pure 2
