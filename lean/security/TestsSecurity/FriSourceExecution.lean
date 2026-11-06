import ZkcExamples.Structured.FriSource
import ZkcSecurity.Bindings.Models.KoalaBearModel

/-! Actual verifier executions on the zero and degree-seven codewords, using the
installed octic arithmetic. The deterministic draws exercise the schedule;
they make no distributional assertion. -/
namespace TestsSecurity.FriSourceExecution
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured.FriSource
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)

structure History where
  actions : List String := []
  samples : Nat := 0

def positions := [31, 4, 4, 11, 27, 0, 3, 15]

def ordinary (coefficient : Nat) (invalidQuery : Bool) : PublishedWords.Table model →
    PIR.MonadHandler Id (participantInterfaceOn model.toCarriers) History String :=
  fun _ op h ↦
    match op with
    | .send .. => ⟨.returned (), h, []⟩
    | .receive (.vector d) _ _ => ⟨.returned [(coefficient : model.Field d)],
        {h with actions := h.actions ++ ["terminal"]}, []⟩
    | .query _ (.draw d) _ => ⟨.returned (2 : model.Field d),
        {h with actions := h.actions ++ ["fold"]}, []⟩
    | .query _ (.sampleIndex _) (.cons _ (.cons bound .nil)) =>
        ⟨.returned (if invalidQuery then bound else positions[h.samples]?.getD bound),
          ⟨h.actions ++ ["index"], h.samples + 1⟩, []⟩
    | _ => ⟨.stopped .refused, h, ["unknown operation"]⟩

/-- The honest words for X⁷ on the unit coset under three challenges of 2
are X⁷, 2X³ and 4X. The last polynomial is the constant 8. -/
def layer (d : String) (rows round : Nat) : Option (List (model.Field d)) := do
  let points ← (Numerical.points model.toFieldModel d 1 rows).toOption
  let power ← [7, 3, 1][round]?
  return points.map (fun x ↦ (2 ^ round : model.Field d) * x ^ power)

def chooser (short : Bool) (degreeSeven := false) : PublishedWords.Chooser Id model History String :=
  fun req words h ↦ match req with
    | ⟨.table (.field d) _, _, rows, _, _, _, _⟩ =>
      ⟨(if degreeSeven then (layer d rows words.length).elim (.stopped .refused) .returned
        else .returned (List.replicate (rows - (if short then 1 else 0)) (0 : model.Field d))),
        {h with actions := h.actions ++ ["publish"]}, []⟩
    | _ => ⟨.stopped .refused, h, ["unexpected word sort"]⟩

def run (shift : Octic := 1) (rounds := 3) (queries := 8)
    (coefficient := 0) (short := false) (invalidQuery := false) (degreeSeven := false) : Execution model History String :=
  verifier (model := model) (m := Id) shift rounds queries 0 {} (ordinary coefficient invalidQuery)
    (chooser short degreeSeven)

def result (e : Execution model History String) : PIR.Outcome (Option Bool) :=
  match e.outcome with
  | .stopped reason => .stopped reason
  | .returned outputs => .returned ((outputs.get .here).bind ProtocolValue.toConcrete)

def held (input : List Octic) : Execution model History String :=
  let ordinary : PublishedWords.Table model →
      PIR.MonadHandler Id (participantInterfaceOn model.toCarriers) History String :=
    fun _ op h ↦ match op with
    | .receive (.field d) _ _ => ⟨.returned (2 : model.Field d), h, []⟩
    | .receive .index _ _ => ⟨.returned (positions[h.samples]?.getD 32),
        {h with samples := h.samples + 1}, []⟩
    | .send .. => ⟨.returned (), h, []⟩
    | _ => ⟨.stopped .refused, h, []⟩
  PublishedWords.sourceRunM (start 0 input (1 : Octic) 3 8 0 {}) ordinary (chooser false)

def controls : IO Unit := do
  let sequence := ["publish", "fold", "publish", "fold", "publish", "fold", "terminal"]
  let allActions := sequence ++ List.replicate 8 "index"
  let inspectCase (name : String) (execution : Execution model History String)
      (expected : PIR.Outcome (Option Bool)) (rows : List Nat) (actions : List String)
      (reads : Nat) : IO Unit := do
    let state := execution.state
    unless result execution == expected && state.oracle.queries == reads &&
        (state.oracle.provider.words.map (·.2.rows)) == rows &&
        state.oracle.provider.auxiliary.actions == actions do
      throw (IO.userError (name ++ ": outcome " ++ reprStr (result execution) ++
        ", reads " ++ toString state.oracle.queries ++ ", actions " ++
        toString state.oracle.provider.auxiliary.actions))
  for degreeSeven in [false, true] do
    let coefficient := if degreeSeven then 8 else 0
    let runHonest := run (coefficient := coefficient) (degreeSeven := degreeSeven)
    inspectCase "honest verifier" runHonest (.returned (some true)) [8, 16, 32] allActions 96
    let some first := runHonest.state.oracle.provider.words.getLast? | throw (IO.userError "first word")
    let some input := (if degreeSeven then layer extension 32 0 else some (List.replicate 32 0))
      | throw (IO.userError "input")
    let .field d := first.1 | throw (IO.userError "row sort")
    unless d == extension do throw (IO.userError "nominal row sort")
    let holder := held input
    unless result holder == .returned none && holder.state.parents.isEmpty &&
        holder.state.oracle.provider.auxiliary.samples == 8 do
      throw (IO.userError ("holder: " ++ reprStr (result holder)))
    let some published := PublishedWords.find runHonest.state.oracle.provider.words
        (.field extension) first.2.anchor | throw (IO.userError "first word nominal lookup")
    unless published.cells == input && runHonest.state.parents.isEmpty do
      throw (IO.userError "first publication or verifier frame")
    for entry in runHonest.state.oracle.provider.words do
      let some localWord := PublishedWords.find holder.state.oracle.provider.words
        (.field extension) entry.2.anchor | throw (IO.userError "holder anchor")
      let some received := PublishedWords.find runHonest.state.oracle.provider.words
        (.field extension) entry.2.anchor | throw (IO.userError "verifier anchor")
      unless localWord.cells == received.cells do throw (IO.userError "different role publications")
  inspectCase "round count" (run (rounds := 2)) (.stopped .reject) [] [] 0
  inspectCase "zero shift" (run (shift := 0)) (.stopped .refused) [] [] 0
  inspectCase "short private input" (held (List.replicate 31 0)) (.stopped .reject) [] [] 0
  inspectCase "short published word" (run (short := true)) (.stopped .refused) [] ["publish"] 0
  inspectCase "terminal value" (run (coefficient := 1)) (.stopped .reject)
    [8, 16, 32] allActions 12
  inspectCase "query count" (run (queries := 7)) (.stopped .reject) [8, 16, 32] sequence 0
  inspectCase "out-of-range position" (run (invalidQuery := true)) (.stopped .refused)
    [8, 16, 32] (sequence ++ ["index"]) 0
  IO.println "FRI: both roles, zero and degree-seven words, three folds, eight draws, seven mutations"

#eval controls

end TestsSecurity.FriSourceExecution
