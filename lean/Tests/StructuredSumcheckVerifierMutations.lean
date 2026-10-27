import Tests.StructuredSumcheckVerifierBodies
import Tests.StructuredSumcheckVerifierSupport

/-! Complete source mutants retain names and signatures. Admission and execution
use the maintained checker and participant semantics. The source captures remain
immutable; these are separately authored controls with explicit edits. -/
namespace Tests.StructuredSumcheckVerifierMutations
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open Tests.StructuredSumcheckVerifierSupport

inductive Mutation where
  | guard | evaluation | append | returnPoint
  deriving DecidableEq, Repr

/-- Change instructions only inside the retained repeat callback. -/
def mutateRound (mutation : Mutation) : Instruction → Instruction
  | .instruction (.fieldEqual field) [13, 0] results regions site =>
      .instruction (.fieldEqual field)
        (if mutation == .guard then [0, 0] else [13, 0]) results regions site
  | .instruction (.fieldMultiply field) [0, 14] results regions site =>
      .instruction (.fieldMultiply field)
        (if mutation == .evaluation then [0, 12] else [0, 14]) results regions site
  | .instruction (.fieldMultiply field) [10, 13] results regions site =>
      .instruction (.fieldMultiply field)
        (if mutation == .evaluation then [10, 15] else [10, 13]) results regions site
  | instruction => instruction

def mutateRepeat (mutation : Mutation) : Instruction → Instruction
  | .instruction descriptor@(.protocolRepeat ..) operands results
      [.region inputs outputs (.block instructions terminator)] site =>
      .instruction descriptor operands results
        [.region inputs outputs (.block (instructions.map (mutateRound mutation)) terminator)] site
  | instruction => instruction

/-- Select the append primitive structurally, never by a helper's name. -/
def mutateFunction (bindings : List Binding) (mutation : Mutation) (function : Zkc.Source.Structured.Function) :
    Zkc.Source.Structured.Function :=
  let .block instructions terminator := function.body
  if function.kind == .protocol then
    { function with body := (.block (instructions.map (mutateRepeat mutation))
        (if mutation == .returnPoint && terminator == .ret [5, 2, 3, 4, 0, 1]
          then .ret [5, 2, 3, 4, 5, 1] else terminator)) }
  else if mutation == .append then
    match instructions with
    | [.instruction (.exec "exec.apply" binding []) [0, 1] results [] site] =>
        if bindings.any (fun b => b.name == binding && b.contract == "vector.append") then
        { function with body := (.block
            [.instruction (.exec "exec.apply" binding []) [0, 1] results [] site]
            (.ret [1])) }
        else function
    | _ => function
  else function

def mutate (mutation : Mutation) (snapshot : Snapshot) : Snapshot :=
  { snapshot with definitions := snapshot.definitions.map fun
      | .function function => .function (mutateFunction snapshot.bindings mutation function)
      | definition => definition }

/- A syntax projection sufficient to refute equality of complete raw trees.
It supplies no evaluation or helper semantics. -/
mutual
  def rawOperands {T O : Type} : RawRegion T O → List (List Nat)
    | .ret operands => [operands]
    | .stop _ => []
    | .letOp _ operands _ bodies next => operands :: (rawRegionOperands bodies ++ rawOperands next)
    | .bind _ body next => rawOperands body ++ rawOperands next
  def rawRegionOperands {T O : Type} : RawRegions T O → List (List Nat)
    | .nil => []
    | .cons _ _ body rest => rawOperands body ++ rawRegionOperands rest
end

theorem distinct_operands_refute_raw {T O : Type} (left right : RawRegion T O)
    (different : rawOperands left ≠ rawOperands right) : left ≠ right :=
  fun same => different (congrArg rawOperands same)

/- The corresponding raw mutations refute the *complete* original tree
associations in the kernel, independently of the executable admission tests. -/
def changedOperands (mutation : Mutation) (op : ProtocolOp) (operands : List Nat) : List Nat :=
  match mutation, op, operands with
  | .guard, .calculate (.fieldEqual _) _, [13, 0] => [0, 0]
  | .evaluation, .calculate (.fieldMultiply _) _, [0, 14] => [0, 12]
  | .evaluation, .calculate (.fieldMultiply _) _, [10, 13] => [10, 15]
  | _, _, _ => operands

mutual
  def changedRaw (mutation : Mutation) : RawRegion Ty ProtocolOp → RawRegion Ty ProtocolOp
    | .ret operands => .ret
        (if mutation == .returnPoint && operands == [5, 2, 3, 4, 0, 1]
          then [5, 2, 3, 4, 5, 1] else operands)
    | .stop reason => .stop reason
    | .letOp op operands results bodies next =>
        .letOp op (changedOperands mutation op operands) results
          (changedRawRegions mutation bodies) (changedRaw mutation next)
    | .bind types body next => .bind types (changedRaw mutation body) (changedRaw mutation next)
  def changedRawRegions (mutation : Mutation) : RawRegions Ty ProtocolOp → RawRegions Ty ProtocolOp
    | .nil => .nil
    | .cons inputs outputs body rest =>
        .cons inputs outputs (changedRaw mutation body) (changedRawRegions mutation rest)
end

theorem guard_mutation_refutes_complete_source_body :
    changedRaw .guard SumcheckSourceViews.reduceDefinition.raw ≠
      (SumcheckVerifierBodies.reduceBody 2).erase := by
  apply distinct_operands_refute_raw
  decide +kernel

theorem evaluation_mutation_refutes_complete_reduction_body :
    changedRaw .evaluation SumcheckReduceViews.reduceDefinition.raw ≠
      (SumcheckVerifierBodies.reduceBody 4).erase := by
  apply distinct_operands_refute_raw
  decide +kernel

theorem return_mutation_refutes_complete_reduction_body :
    changedRaw .returnPoint SumcheckReduceViews.reduceDefinition.raw ≠
      (SumcheckVerifierBodies.reduceBody 4).erase := by
  apply distinct_operands_refute_raw
  decide +kernel

/-- Dynamic signature checks only adapt typed test inputs; execution is the
existing Program.participant, with no alternative source interpreter. -/
def execute {F A : Type} [CommRing F] [DecidableEq F]
    {inputs outputs : List Ty} (program : Program)
    (args : Values (Component (assignment F F)) inputs)
    (project : Values (Component (assignment F F)) outputs → A) (state : State F) :
    Except String (PIR.Execution (State F) (Event F) A) := do
  if hin : program.payload.entry.inputs = inputs then
    if hout : program.payload.entry.outputs = outputs then
      let process := (program.participant F F 1 (hin.symm ▸ args)).bind
        fun values => .done (project (hout ▸ values))
      return process.run handler state
    else throw "mutant output ABI changed"
  else throw "mutant input ABI changed"

def reductionInputs {F : Type} (claim : F) :
    Values (Component (assignment F F)) SumcheckReduceBodies.runSignature.inputs :=
  .cons none (.cons none (.cons (some claim) (.cons (some 1) (.cons (some 7) .nil))))

def reductionOutput {F : Type}
    (values : Values (Component (assignment F F)) SumcheckReduceBodies.runSignature.outputs) :
    Option (List F) × Option F :=
  (values.get (.there (.there .here)), values.get (.there (.there (.there .here))))

def sourceInputs {F : Type} (raw : List F) (claim : F) :
    Values (Component (assignment F F)) SumcheckSourceBodies.runSignature.inputs :=
  .cons (some raw) (.cons (some claim) (.cons (some 1) (.cons (some 7) .nil)))

def sourceOutput {F : Type}
    (values : Values (Component (assignment F F)) SumcheckSourceBodies.runSignature.outputs) :
    Option Bool := values.get .here

private def admitted (snapshot : Snapshot) : IO Program :=
  match check snapshot with
  | .ok program => pure program
  | .error message => throw (IO.userError ("unexpected mutant admission failure: " ++ message))

private def result {A : Type} (value : Except String A) : IO A :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let test (name : String) (ok : Bool) : IO Unit :=
    unless ok do failures.modify (name :: ·)
  let original := SumcheckReduceViews.program
  let guarded ← admitted (mutate .guard SumcheckReduceData.snapshot)
  let swapped ← admitted (mutate .evaluation SumcheckReduceData.snapshot)
  let sourceSwapped ← admitted (mutate .evaluation SumcheckSourceData.snapshot)
  let oldAppend ← admitted (mutate .append SumcheckReduceData.snapshot)
  let sourceOldAppend ← admitted (mutate .append SumcheckSourceData.snapshot)
  for (name, program) in [("guard", guarded), ("evaluation", swapped)] do
    let actual := program.payload.protocols.find? (·.name == SumcheckReduceBodies.reduceSignature.name)
    match actual with
    | none => throw (IO.userError "mutant lost the retained Reduce definition")
    | some definition =>
        test (name ++ ": complete raw association fails")
          (rawOperands definition.raw != rawOperands SumcheckReduceViews.reduceDefinition.raw)
        test (name ++ ": complete signature unchanged")
          (definition.signature == SumcheckReduceBodies.reduceSignature)
  let appendDefinition := oldAppend.payload.definitions.find?
    (·.name == SumcheckHelperBodies.appendHelper.name)
  match appendDefinition with
  | none => throw (IO.userError "mutant lost append definition")
  | some definition =>
      test "append: raw association fails"
        (rawOperands definition.raw != rawOperands SumcheckReduceViews.appendDefinition.raw)
      test "append: ABI unchanged" (definition.helper == SumcheckHelperBodies.appendHelper)
  let falseBoundary : State (ZMod 5) := ⟨[.value 0, .value 0, .value 1, .ack], 0⟩
  let originalGuard ← result (execute original (reductionInputs (1 : ZMod 5)) reductionOutput falseBoundary)
  let mutantGuard ← result (execute guarded (reductionInputs (1 : ZMod 5)) reductionOutput falseBoundary)
  test "guard: original rejects before query" (originalGuard.outcome == .stopped .reject &&
    originalGuard.state.consumed == 2)
  test "guard: mutant reaches query and delivery" (mutantGuard.state.consumed == 4 &&
    mutantGuard.outcome == .returned (some [1], some 0))
  let evaluationReplies : State (ZMod 2) := ⟨[.value 0, .value 1, .value 0, .ack], 0⟩
  let originalEval ← result (execute original (reductionInputs (1 : ZMod 2)) reductionOutput evaluationReplies)
  let mutantEval ← result (execute swapped (reductionInputs (1 : ZMod 2)) reductionOutput evaluationReplies)
  test "evaluation: original endpoint is zero in characteristic two"
    (originalEval.outcome == .returned (some [0], some 0))
  test "evaluation: swapped weights give one"
    (mutantEval.outcome == .returned (some [0], some 1))
  let originalTerminal ← result (execute SumcheckSourceViews.program
    (sourceInputs ([0, 0] : List (ZMod 2)) 1) sourceOutput evaluationReplies)
  let swappedTerminal ← result (execute sourceSwapped
    (sourceInputs ([0, 0] : List (ZMod 2)) 1) sourceOutput evaluationReplies)
  test "evaluation: actual Source checker distinguishes the swapped result"
    (originalTerminal.outcome == .returned (some true) &&
      swappedTerminal.outcome == .returned (some false))
  let appendReplies : State (ZMod 5) := ⟨[.value 0, .value 1, .value 1, .ack], 0⟩
  let originalAppend ← result (execute original (reductionInputs (1 : ZMod 5)) reductionOutput appendReplies)
  let mutantAppend ← result (execute oldAppend (reductionInputs (1 : ZMod 5)) reductionOutput appendReplies)
  test "append: actual cv retained" (originalAppend.outcome == .returned (some [1], some 1))
  test "append: returning the old point loses cv" (mutantAppend.outcome == .returned (some [], some 1))
  let sourceOriginal ← result (execute SumcheckSourceViews.program
    (sourceInputs ([0, 1] : List (ZMod 5)) 1) sourceOutput appendReplies)
  let sourceMutant ← result (execute sourceOldAppend
    (sourceInputs ([0, 1] : List (ZMod 5)) 1) sourceOutput appendReplies)
  test "append: actual Source terminal accepts" (sourceOriginal.outcome == .returned (some true))
  test "append: mutated Source terminal rejects by false" (sourceMutant.outcome == .returned (some false))
  test "return map: foreign point violates admission"
    (!(check (mutate .returnPoint SumcheckReduceData.snapshot)).isOk)
  let permuted ← admitted { SumcheckReduceData.snapshot with
    definitions := SumcheckReduceData.snapshot.definitions.reverse }
  let permutedRun ← result (execute permuted (reductionInputs (1 : ZMod 5)) reductionOutput appendReplies)
  test "complete declaration permutation preserves result and events"
    (permutedRun.outcome == originalAppend.outcome && permutedRun.state == originalAppend.state &&
      permutedRun.events == originalAppend.events)
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError (String.intercalate "\n" errors.reverse))
  IO.println "structured Sumcheck source mutation controls passed"

#eval run
end Tests.StructuredSumcheckVerifierMutations
