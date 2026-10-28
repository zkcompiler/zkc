import Zkc.Source.Structured.ComponentChecking
import ZkcTools.SourceClaims.Components
import ZkcTools.StructuredSource.OpenEvaluation
import Zkc.Source.KernelRfl

/-! Actual source association and bounded continuation controls. Scanner-only
mutations below do not claim whole-unit admission or a mathematical law. -/
open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.ComponentContinuations

private def expect {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error code => throw (IO.userError code)

private def refuses {α : Type} (value : Except String α) (code : String) : Bool :=
  match value with | .error actual => actual == code | _ => false

private def routes (route : SeamRoute) : List SeamRoute :=
  route :: match route with
    | .pure _ _ _ _ args | .terminal _ _ _ _ args | .action _ _ _ _ args => args.flatMap routes
    | _ => []

-- Negation has no acceptance implication. A helper remains exact and opaque;
-- classification never traverses its arguments as if its body were conjunction.
example (args : List SeamRoute) : ComponentRoutes.acceptance
    65 (.pure .booleanEqual [2] 0 "V" args) = .pure .booleanEqual [2] 0 "V" args := by kernel_rfl

example (arg : SeamRoute) : ComponentRoutes.acceptance
    65 (.pure (.localCall "identity" "V") [2] 0 "V" [arg]) =
    .terminal (.localCall "identity" "V") [2] 0 "V" [arg] := by kernel_rfl

example : ((InstantiationSource.math "repack" 1 [.parameter ⟨.input, 0, "V", false⟩,
    .math "constant" 0 []]) == .math "repack" 1 [.parameter ⟨.input, 0, "V", false⟩,
    .math "constant" 0 []]) = true := by kernel_rfl

private def changeProtocols (snapshot : Snapshot) (change : Function → Function) : Snapshot :=
  { snapshot with definitions := snapshot.definitions.map fun
    | .function func => .function (if func.kind == .protocol then change func else func)
    | other => other }

private def run (snapshot : Snapshot) (text : String) (fixture : Bool) : IO Nat := do
  let count ← IO.mkRef 0
  let test (name : String) (condition : Bool) : IO Unit := do
    count.modify (· + 1)
    unless condition do throw (IO.userError s!"component continuation: {name}")
  let program ← expect (check snapshot)
  let exported ← expect (ZkcTools.SourceClaims.Components.parse text >>= ZkcTools.SourceClaims.Components.decode snapshot)
  test "actual native source export agrees exactly" (ZkcTools.SourceClaims.Components.check snapshot text).isOk
  let leaves := exported.seams.flatMap fun row => row.routes.flatMap routes
  test "actual acceptance keeps an exact helper" (leaves.any fun
    | .terminal (.localCall ..) .. | .terminal (.call ..) .. => true | _ => false)
  test "handoffs contain no early terminal" (exported.seams.all fun row =>
    match row.endpoint with
    | .output .. => true
    | _ => (row.routes.flatMap routes).all fun
      | .terminal .. => false | _ => true)
  let repeats := exported.seams.filter fun row =>
    match row.endpoint with | .repeatResult .. => true | _ => false
  test "zero-iteration alternatives are complete" (repeats.all (·.routes.length == 2))
  if fixture then test "multi-field fixture retains both carried alternatives" (repeats.length == 2)
  for variant in [0, 1, 2, 3] do
    let change := fun route => match route with
      | .pure op pos port role args | .terminal op pos port role args =>
        match variant with
        | 0 => SeamRoute.pure (.localCall "wrong-body" role) pos port role args
        | 1 => .pure op pos port "wrong-role" args
        | 2 => .pure op pos port role (args ++ [.input 999 "captured"])
        | _ => .pure op (pos ++ [999]) port role args
      | _ => .input 999 "wrong-source"
    let changed := { exported with seams := exported.seams.map fun row =>
      { row with routes := row.routes.map change } }
    test s!"wrong helper, role, capture or body position {variant}"
      (refuses (ComponentExport.check snapshot changed) "component-seam-association")
  let changed := { exported with seams := exported.seams.map fun row =>
    match row.endpoint with
    | .repeatResult .. => { row with routes := row.routes.take 1 }
    | _ => row }
  unless repeats.isEmpty do
    test "missing zero-iteration alternative refuses"
      (refuses (ComponentExport.check snapshot changed) "component-seam-association")
  if exported.seams.any (·.kind == .method) then
    let changed := { exported with seams := exported.seams.map fun row =>
      if row.kind == .method then { row with kind := .pure } else row }
    test "method body cannot be relabeled as a pure seam"
      (refuses (ComponentExport.check snapshot changed) "component-seam-association")
    test "method action provenance is explicit" (leaves.any fun | .action .. => true | _ => false)
  for blocked in ["component-seam-oracle", "component-seam-effect"] do
    for admitted in ["component-seam-sampling", "component-seam-message"] do
      let bad : ComponentRoutes.Flow := { route := .input 0 "V", effect := some blocked }
      let action : ComponentRoutes.Flow := { route := .input 1 "V", effect := some admitted }
      for operands in [[bad, action], [action, bad]] do
        test "an admitted action cannot mask an unadmitted effect"
          (refuses (ComponentRoutes.pureFlow (ComponentRoutes.aggregate operands) true) blocked)
  if fixture then
    for maximum in [0, 2] do
      let changed := changeProtocols snapshot fun func =>
        if func.name != snapshot.entry then func else
          let .block instructions end_ := func.body
          { func with body := .block (.instruction
              (.protocolRepeat 0 maximum ["role00000000"] []) [1] []
              [.region [.index] [] (.block [] (.yield []))] "empty" :: instructions) end_ }
      test "empty repeat retains unrelated ownership, including maximum zero"
        (ComponentRoutes.derive changed).isOk
    for variant in List.range 7 do
      let changed := changeProtocols snapshot fun func =>
        let .block instructions end_ := func.body
        if func.name != snapshot.entry then
          let end_ := match end_ with
            | .ret [first, second, ok] => .ret [first, if variant == 0 then first else
                if variant == 1 then ok else second, ok]
            | other => other
          { func with body := .block instructions end_ }
        else
          let instructions := instructions.map fun instruction =>
            let .instruction descriptor args types regions site := instruction
            match descriptor with
            | .protocolRepeat carried maximum roles scopes =>
              if variant == 6 then
                .instruction descriptor args types
                  (regions.map fun
                    | .region inputs outputs _ =>
                      .region inputs outputs (.block [] (.stop .abort "stopped callback"))) site
              else
                .instruction (.protocolRepeat (if variant == 3 then 1 else carried) maximum roles scopes)
                  (if variant == 2 then args.set 2 (args[1]?.getD 0) else args) types regions site
            | .localCall name role => .instruction (.localCall name (if variant == 4 then "absent" else role))
                args types regions site
            | _ => instruction
          let instructions := if variant == 5 then
            instructions.modify (instructions.length - 1) fun
              | .instruction _ args types regions site =>
                .instruction .booleanEqual args types regions site
            else instructions
          { func with body := .block instructions end_ }
      test s!"ownership/control/BooleanNot refusal {variant}" (refuses (ComponentRoutes.derive changed)
        (if variant < 3 then "component-seam-coverage" else if variant == 3 || variant == 6 then
          "component-seam-control" else if variant == 4 then "component-seam-role" else "component-seam-acceptance"))
    for rounds in [0, 1, 2] do
      for value in [false, true] do
        let observed ← expect (ZkcTools.StructuredSource.evaluateOpen program (.arr #[
          .str "zkc.structured-open-request/0", .str "role00000000", .arr #[.bool value, .str (toString rounds)],
          .arr #[], toJson (100000 : Nat)]))
        let status ← expect ((observed.getArr?).mapError id)
        let actual ← expect ((status[1]!).getArr?.mapError id)
        test "guarded Local conversion is defined on its actual scope and stops outside it"
          (if !value && rounds > 0 then actual[0]? == some (.str "stopped") && actual[1]? == some (.str "reject")
           else status[1]? == some (.arr #[.str "returned", .arr #[.bool value]]))
  return ← count.get

def main (args : List String) : IO Unit := do
  let mut remaining := args
  let mut count := 0
  while !remaining.isEmpty do
    let fixture := remaining.head! == "--fields"
    if fixture then remaining := remaining.drop 1
    unless remaining.length ≥ 2 do throw (IO.userError "expected snapshot/claims pairs")
    let snapshot ← Tests.ComponentContinuations.expect (Format.parse (← IO.FS.readFile remaining[0]!) >>= Format.snapshot)
    count := count + (← Tests.ComponentContinuations.run snapshot (← IO.FS.readFile remaining[1]!) fixture)
    IO.println s!"associated continuation export: {remaining[0]!}"
    remaining := remaining.drop 2
  IO.println s!"component continuations: {count} checks passed"

end Tests.ComponentContinuations
