import Zkc.Tests.Frontend.DifferentialRuns
import Zkc.Tools.Frontend.Trees
import Zkc.Tools.Frontend.Reading

/-!
# The typed trees of the corpus's protocols

For every program of the corpus, and of a directory of probes when one is given: what became of
the body of each protocol instance, the invariants of the trees, and the second reading. The
second reading evaluates the tree of a protocol root role by role, from the tables of the
passes, and compares what each role does with the run of the emitted package, by the keys of
the events: it is the check that the emitter keeps what each role does.
-/

set_option autoImplicit false

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax (parse)
open Zkc.Tools.Frontend

/-- The trees of the corpus. -/
def treeSuite (reference : System.FilePath) (independent : Option System.FilePath)
    (probes : Option System.FilePath := none) (arithmetic : Bool := false) : TestM Unit := do
  let start ← IO.monoMsNow
  let mut outcomes : Array (String × Nat) := #[]
  let mut violations : Array (String × Nat × String) := #[]
  let mut readAgree := 0
  let mut readDiffer : Array String := #[]
  let mut readIncomplete : Array (String × Nat) := #[]
  let mut corpus ← corpusPrograms reference independent
  -- the probes: every `.zkc` file one directory below the directory given
  if let some directory := probes then
    let library ← cachedLoader #[reference / "lib"]
    for group in (← directory.readDir).qsort (·.fileName < ·.fileName) do
      unless ← group.path.isDir do continue
      for path in ← sortedFiles group.path "zkc" do
        let name := path.toString
        corpus := corpus.push { id := s!"probes/{group.fileName}/{path.fileStem.getD ""}"
                                inputs := #[{ name, parsed := parse name (← IO.FS.readBinFile path) }]
                                load := fun names => library names }
  for program in corpus do
    let .ok trees ← Trees.treesOf program.inputs program.load | continue
    for (_, _, outcome) in Trees.protocolOutcomes trees do
      let key := (outcome.splitOn ":").headD outcome
      outcomes := match outcomes.findIdx? (·.1 == key) with
        | some index => outcomes.modify index fun (key, count) => (key, count + 1)
        | none => outcomes.push (key, 1)
    -- the second reading of each protocol root against the run of its package
    for uninterpreted in (if arithmetic then [true, false] else [true]) do
      let seeds := List.range (if uninterpreted then 16 else 4)
      for (description, verdict) in Reading.compareProgram trees uninterpreted seeds do
        let provider := if uninterpreted then "uninterpreted rows" else "the model that computes"
        match verdict with
        | .agree _ => readAgree := readAgree + 1
        | .differ .. =>
          readDiffer := readDiffer.push
            s!"{program.id}: reading of {description} under {provider}: {Reading.describeVerdict verdict}"
        | .incomplete why =>
          let text := Reading.describeVerdict (.incomplete why)
          if (text.splitOn "the reading breaks off").length > 1 then
            readDiffer := readDiffer.push s!"{program.id}: reading of {description} under {provider}: {text}"
          let key := s!"{provider}: {text.take 110}"
          readIncomplete := match readIncomplete.findIdx? (·.1 == key) with
            | some index => readIncomplete.modify index fun (key, count) => (key, count + 1)
            | none => readIncomplete.push (key, 1)
    for line in Trees.violationsOf trees do
      -- the kind of a violation: its message without the numbers of binders
      let message := (line.splitOn ": ").getLastD line
      let kind := String.ofList (message.toList.filter fun char => !char.isDigit)
      violations := match violations.findIdx? (·.1 == kind) with
        | some index => violations.modify index fun (kind, count, first) => (kind, count + 1, first)
        | none => violations.push (kind, 1, s!"{program.id}: {line}")
  note s!"protocol instances: {", ".intercalate (outcomes.map fun (key, count) => s!"{count} {key}").toList}"
  note s!"second reading against the run of the package: {readAgree} observed to agree, {readDiffer.size} to differ, {readIncomplete.foldl (fun sum (_, count) => sum + count) 0} incomplete"
  for (key, count) in readIncomplete do note s!"  {count} {key}"
  note s!"invariants of the trees: {violations.foldl (fun sum (_, count, _) => sum + count) 0} violations of {violations.size} kinds"
  for (kind, count, first) in violations do note s!"  {count} × {kind}; first: {first}"
  note s!"time: {(← IO.monoMsNow) - start} ms"
  for line in readDiffer do failure line
  for (kind, _, first) in violations do failure s!"an invariant of the trees is violated: {kind}: {first}"
  if readDiffer.isEmpty && violations.isEmpty then pass

end Zkc.Tests.Frontend
