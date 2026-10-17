import ZkcExamples.Structured.SumcheckHonestExecution
import Mathlib.Data.ZMod.Basic

/-! A prover that skips its fold breaks completeness.

The mutant keeps the retained callback's fold call but yields the incoming table
slots instead of the folded ones, so the prover resends the original half sums
in every round. The mutant is admitted by the maintained checker; both
participants run the maintained participant semantics under the same honest
delivery and challenge tape as the completeness theorem. With one round the
first message is correct regardless of the fold and the verifier accepts; from
the second round the verifier's guard rejects. The original export accepts in
both cases. -/
namespace Tests.SumcheckFoldMutations
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open ZkcExamples.Structured.SumcheckHonestExecution

/-- In the Reduce repeat callback, yield the incoming entries, dimension and
width (callback inputs at 22, 23 and 24) instead of the fold's results. -/
def skipFold : Instruction → Instruction
  | .instruction descriptor@(.protocolRepeat ..) operands results
      [.region inputs outputs (.block instructions (.yield [7, 8, 9, 6, 5, 0]))] site =>
      .instruction descriptor operands results
        [.region inputs outputs (.block instructions (.yield [22, 23, 24, 6, 5, 0]))] site
  | instruction => instruction

def mutateFunction (function : Zkc.Source.Structured.Function) : Zkc.Source.Structured.Function :=
  let .block instructions terminator := function.body
  if function.kind == .protocol then
    { function with body := .block (instructions.map skipFold) terminator }
  else function

def mutate (snapshot : Snapshot) : Snapshot :=
  { snapshot with definitions := snapshot.definitions.map fun
      | .function function => .function (mutateFunction function)
      | definition => definition }

abbrev F := ZMod 5

/-- Run the verifier against the prover of one root invocation, both from the
same program and inputs, and report the verifier's outcome. -/
def coupled (program : Program) (raw : List F) (count : Nat) (tape : List F) :
    Except String String := do
  if hin : program.payload.entry.inputs = SumcheckSourceBodies.runSignature.inputs then
    if hout : program.payload.entry.outputs = SumcheckSourceBodies.runSignature.outputs then
      let inputs := SumcheckSourceVerifier.sourceRootInputs (G := F) (some raw) (some raw.sum)
        (some count) (some 7)
      let verifier := (program.participant F F 1 (hin.symm ▸ inputs)).bind
        fun values => .done (hout ▸ values)
      let prover := program.participant F F 0 (hin.symm ▸ inputs)
      let execution := verifier.run (network SumcheckSourceVerifier.childContext) ⟨prover, tape⟩
      return match execution.outcome with
        | .returned values => s!"returned {repr (values.get .here)}"
        | .stopped reason => s!"stopped {repr reason}"
    else throw "mutant output ABI changed"
  else throw "mutant input ABI changed"

private def admitted (snapshot : Snapshot) : IO Program :=
  match check snapshot with
  | .ok program => pure program
  | .error message => throw (IO.userError ("unexpected mutant admission failure: " ++ message))

private def result (value : Except String String) : IO String :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let test (name : String) (ok : Bool) : IO Unit :=
    unless ok do failures.modify (name :: ·)
  let original := SumcheckSourceViews.program
  let mutant ← admitted (mutate SumcheckSourceData.snapshot)
  let changed := mutant.payload.protocols.find? (·.name == SumcheckSourceBodies.reduceSignature.name)
  match changed with
  | none => throw (IO.userError "mutant lost the retained Reduce definition")
  | some definition =>
      test "mutant: Reduce signature unchanged" (definition.signature == SumcheckSourceBodies.reduceSignature)
  let source := (SumcheckSourceData.snapshot.definitions.map fun definition => toString (repr definition))
  let mutated := ((mutate SumcheckSourceData.snapshot).definitions.map fun definition =>
    toString (repr definition))
  test "mutant: exactly one retained definition changed"
    (((source.zip mutated).filter fun pair => pair.1 != pair.2).length == 1)
  let two : List F := [0, 1, 2, 4]
  let one : List F := [3, 4]
  let originalTwo ← result (coupled original two 2 [2, 3])
  let mutantTwo ← result (coupled mutant two 2 [2, 3])
  let originalOne ← result (coupled original one 1 [2])
  let mutantOne ← result (coupled mutant one 1 [2])
  test s!"original accepts two rounds: {originalTwo}" (originalTwo == "returned some true")
  test s!"skipped fold rejects two rounds: {mutantTwo}" (mutantTwo == "stopped PIR.Stop.reject")
  test s!"original accepts one round: {originalOne}" (originalOne == "returned some true")
  test s!"skipped fold still accepts one round: {mutantOne}" (mutantOne == "returned some true")
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError (String.intercalate "\n" errors.reverse))
  IO.println "skipped-fold completeness controls passed"

#eval run
end Tests.SumcheckFoldMutations
