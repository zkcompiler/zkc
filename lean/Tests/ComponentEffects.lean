import Zkc.Source.Structured.ComponentChecking
import ZkcTools.SourceClaims.Components

/-! Focused effect-inventory controls. The supplied snapshots are admitted and
compared with actual native exports first. Synthetic mutations then exercise
only the bounded scanner, not whole-unit admission or mathematical laws. -/
open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.ComponentEffects

private def expect {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error code => throw (IO.userError code)

private def refuses {α : Type} (result : Except String α) (code : String) : Bool :=
  match result with | .error actual => actual == code | _ => false

private def instruction (descriptor : Descriptor) (regions : List WireRegion := []) : Instruction :=
  .instruction descriptor [] [] regions "inventory"

private def region (instructions : List Instruction) (end_ : Terminator := .yield []) : WireRegion :=
  .region [] [] (.block instructions end_)

private def localFunction (name : String) (body : Block) : Function :=
  ⟨name, .local, .privateDef, [], [], none, [], none, body⟩

private def scan (snapshot : Snapshot) (body : Block) : Except String Unit :=
  (ComponentRoutes.deterministic snapshot 65 (localFunction "inventory" body)).run' {}

private def controls (snapshot : Snapshot) : IO Nat := do
  let count ← IO.mkRef 0
  let test (name : String) (condition : Bool) : IO Unit := do
    count.modify (· + 1)
    unless condition do throw (IO.userError s!"component effects: {name}")
  let effects := [(Descriptor.draw "V" scalarDomain, "component-seam-sampling"),
    (.exchange "P" "V", "component-seam-message"),
    (.exec "oracle.query" "" [], "component-seam-oracle"),
    (.exec "unknown.effect" "" [], "component-seam-effect"),
    (.exec "exec.apply" "missing" [], "component-seam-effect"),
    (.apply "missing", "component-seam-call")]
  for control in [Descriptor.branch, .loop, .loopCondition] do
    test "nested Local control with stopped and condition paths" (scan snapshot
      (.block [instruction control [region [] (.stop .reject "stop"),
        region [instruction .branch [region [], region []]] (.condition [])]] (.ret []))).isOk
    for (effect, code) in effects do
      for arm in [false, true] do
        let hidden := region [instruction effect] (.stop .reject "stop")
        let arms := if arm then [region [], hidden] else [hidden, region []]
        test s!"hidden arm {repr control}, {code}" (refuses (scan snapshot
          (.block [instruction control arms] (.ret []))) code)
  let callbackName := "effect.callback"
  let predicateName := "effect.predicate"
  let domainName := "effect.domain"
  let body := localFunction callbackName (.block [] (.ret []))
  let predicate := localFunction predicateName (.block [] (.ret []))
  let domain : Domain := ⟨domainName, [], [], 0⟩
  let declarations := [Definition.realization ⟨"effect.realize", [], [], callbackName⟩,
    .map ⟨"effect.map", [], [], callbackName, []⟩,
    .finite ⟨"effect.finite", .privateDef, [], [], domainName, callbackName, predicateName⟩,
    .collect ⟨"effect.collect", .privateDef, [], [], domainName, callbackName, predicateName⟩]
  let withCallbacks : Snapshot := { snapshot with
    domains := snapshot.domains ++ [domain]
    definitions := snapshot.definitions ++ [.function body, .function predicate] ++ declarations }
  let routes := [Descriptor.call callbackName, .apply "effect.realize", .apply "effect.map",
    .apply "effect.finite", .apply "effect.collect", .fold domainName callbackName predicateName]
  for route in routes do
    test s!"actual callback {repr route}" (scan withCallbacks (.block [instruction route] (.ret []))).isOk
    for (effect, code) in effects do
      let changed := { withCallbacks with definitions := withCallbacks.definitions.map fun
        | .function func => .function (if func.name == callbackName then
            { func with body := .block [instruction .branch [region [], region [instruction effect]]] (.ret []) }
          else func)
        | other => other }
      test s!"hidden callback {repr route}, {code}" (refuses (scan changed
        (.block [instruction route] (.ret []))) code)
  for route in [Descriptor.apply "effect.finite", .apply "effect.collect",
      .fold domainName callbackName predicateName] do
    for (effect, code) in effects do
      let changed := { withCallbacks with definitions := withCallbacks.definitions.map fun
        | .function func => .function (if func.name == predicateName then
            { func with body := .block [instruction effect] (.ret []) } else func)
        | other => other }
      test s!"hidden predicate {repr route}, {code}" (refuses (scan changed
        (.block [instruction route] (.ret []))) code)
    test "missing finite domain" (refuses (scan { withCallbacks with domains := snapshot.domains }
      (.block [instruction route] (.ret []))) "component-seam-call")
  test "protocol helper is not Local" (refuses (scan { withCallbacks with
    definitions := withCallbacks.definitions ++ [.function { body with name := "effect.protocol", kind := .protocol }] }
    (.block [instruction (.call "effect.protocol")] (.ret []))) "component-seam-effect")
  test "Local control at depth bound" (scan snapshot ((List.range 64).foldl
    (fun nested _ => .block [instruction .branch [.region [] [] nested]] (.ret []))
    (.block [] (.ret [])))).isOk
  test "Local control depth bound" (refuses (scan snapshot ((List.range 65).foldl
    (fun nested _ => .block [instruction .branch [.region [] [] nested]] (.ret []))
    (.block [] (.ret [])))) "component-seam-depth")
  test "Local work bound" (refuses (scan snapshot
    (.block (List.replicate 100001 (instruction (.booleanConstant true))) (.ret []))) "component-seam-limit")
  return ← count.get

def main (args : List String) : IO Unit := do
  unless !args.isEmpty do throw (IO.userError "expected snapshot/claims pairs or --refused snapshot code")
  let mut remaining := args
  let mut count := 0
  while !remaining.isEmpty do
    let refused := remaining.head! == "--refused"
    if refused then remaining := remaining.drop 1
    unless remaining.length ≥ 2 do throw (IO.userError "incomplete snapshot arguments")
    let snapshotPath := remaining[0]!
    let claimPathOrCode := remaining[1]!
    remaining := remaining.drop 2
    let snapshot ← Tests.ComponentEffects.expect (Format.snapshot (← Tests.ComponentEffects.expect
      (Format.parse (← IO.FS.readFile snapshotPath))))
    let _ ← Tests.ComponentEffects.expect (check snapshot)
    if refused then
      unless Tests.ComponentEffects.refuses (ComponentRoutes.derive snapshot) claimPathOrCode do
        throw (IO.userError s!"expected actual route refusal: {snapshotPath}")
      IO.println s!"admitted actual snapshot; routes refused {claimPathOrCode}: {snapshotPath}"
    else
      let text ← IO.FS.readFile claimPathOrCode
      let _ ← Tests.ComponentEffects.expect (ZkcTools.SourceClaims.Components.check snapshot text)
      let _ ← Tests.ComponentEffects.expect (ComponentRoutes.derive snapshot)
      IO.println s!"associated actual native export: {snapshotPath}"
    let mut helpers := 0
    for definition in snapshot.definitions do
      if let .function owner := definition then
        if owner.kind == .local then
          let _ ← Tests.ComponentEffects.expect ((ComponentRoutes.deterministic snapshot 65 owner).run' {})
          helpers := helpers + 1
    IO.println s!"actual Local helper inventories passed: {helpers}"
    count := count + (← Tests.ComponentEffects.controls snapshot)
  IO.println s!"component effects: {count} checks passed"

end Tests.ComponentEffects
