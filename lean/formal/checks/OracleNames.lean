module

meta import Zkc.Frontend.Driver.SourcePhases
meta import Zkc.Frontend.Syntax.Parser

meta section
open Zkc.Frontend

private def expectTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

/-- Resolve real source and inspect the information needed by a later oracle interpretation. -/
private def checkOracleEvents : IO Unit := do
  let lines := ["module oracle_names", "protocol Probe roles(P,V,W)(xs: [bool; 2] @P, i: nat @(P,V,W)):",
    "    h <- send xs from P to V,W as oracle<2>", "    a <- query h from W at i deferred",
    "    b <- query h from V at i", "    #[site(discharge)]", "    open a, h at i == b",
    "    bad <- query h from Unknown at i", ""]
  let file := "oracle_names.zkc"
  let input := fun (lines : List String) => (⟨file, Syntax.parseString file ("\n".intercalate lines)⟩ : SourceInput)
  let assembly ← assemble #[input lines] fun _ => pure none
  let resolved := resolveProgram assembly
  let some (_, id) := assembly.program.declarations.zipIdx.find? (fun (d, _) => d.name.any (·.text == "Probe"))
    | throw <| IO.userError "oracle event fixture did not parse"
  let some d := resolved.lowered[id]? | throw <| IO.userError "missing resolved oracle"
  let .protocol head body _ := d.content | throw <| IO.userError "expected oracle protocol"
  expectTrue (d.unknownRoles.toList.map (·.text) == ["Unknown"]) "query opener must resolve in the roster"
  expectTrue (head.events.map (fun e => (e.name, e.parts.toList)) == #[
    (some "h", ["value"]), (some "a", ["rows"]), (some "b", ["rows","opening"]),
    (some "discharge", ["opening"]), (some "bad", ["rows","opening"])]) "oracle sites or parts lost"
  let #[.event _ _ (some h) _ _ (.oracleSend _ (some 0) #[1,2] (.number _ 2)),
        .event _ _ (some a) _ _ (.query (.local _ h1) (some 2) (.local _ i1) true),
        .event _ _ (some b) _ _ (.query (.local _ h2) (some 1) (.local _ i2) false),
        .event _ _ none _ _ (.openClaims #[.pending _ (.local _ av),
          .opening _ (.local _ hv) (.local _ pos) (.local _ bv)]), _] := body
    | throw <| IO.userError "lost oracle role, mode, operands, or claim order"
  expectTrue (h.id == h1 && h1 == h2 && h2 == hv && i1 == i2 && i2 == pos &&
    a.id == av && b.id == bv) "oracle claims must retain their resolved operand binders"

#eval checkOracleEvents
