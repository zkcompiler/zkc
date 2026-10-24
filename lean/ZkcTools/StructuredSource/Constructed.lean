module

public import Zkc.Construction.Participant
public import Lean

@[expose] public section

/-! Lean-owned syntax printing for exact constructed Process views.

The printer reads retained artifact constructors, never executes their program,
and has no protocol or helper-name registry. Its proposed views are accepted
only by the generated kernel-checked structural correspondence proofs.
-/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.Constructed
open Zkc.Construction

def app (head : String) (arguments : List String) : String :=
  "(" ++ " ".intercalate (head :: arguments) ++ ")"
def literal {A : Type} [Repr A] (value : A) : String := "(" ++ (reprStr value).replace "\n" " " ++ ")"

structure Output where
  moduleName : String
  artifactModule : String
  artifactExpression : String

def binders :=
  " (model : Structured.DomainModel) (program : Structured.Program) (context : Context)"
def arguments := ["model", "program", "context"]

/-- Print one independent action and the corresponding generic proof rule. -/
def action (instruction : Instruction) (bodyName : String) : Except String (String × String) :=
  let declared := literal instruction.results
  let references := literal instruction.operands
  let rule (name : String) (args : List String) : Except String (String × String) :=
    .ok (app ("View." ++ name) args, app ("Correspondence." ++ name) args)
  match instruction.operation, instruction.operands, instruction.body with
  | .receive site schema peer ty, [], [] =>
      rule "receive" [literal site, literal schema, literal peer, literal ty, declared]
  | .send site schema peer, [reference], [] =>
      rule "send" [literal site, literal schema, literal peer, toString reference, declared]
  | .indicesEmpty, [], [] => rule "indicesEmpty" [declared]
  | .indicesAppend, [coordinates, index], [] =>
      rule "indicesAppend" [toString coordinates, toString index, declared]
  | .observe suite template, [state, value, coordinates], [] =>
      let args := [literal suite, literal template, toString state, toString value,
        toString coordinates, declared]
      .ok (app "View.observe" ("context" :: args), app "Correspondence.observe" args)
  | .challenge suite field template, [state, coordinates], [] =>
      let args := [literal suite, literal field, literal template, toString state,
        toString coordinates, declared]
      .ok (app "View.challenge" ("context" :: args), app "Correspondence.challenge" args)
  | .localService port request template coordinates, _, [] =>
      let args := [literal port, literal request, literal template, literal coordinates,
        references, declared]
      .ok (app "View.localService" ("context" :: args), app "Correspondence.localService" args)
  | .calculate operation, _, [] =>
      let args := [literal operation, references, declared]
      .ok (app "View.calculation" ("model" :: args), app "Correspondence.calculation" args)
  | .call name, _, [] =>
      let args := [literal name, references, declared]
      .ok (app "View.helper" (["model", "program"] ++ args), app "Correspondence.helper" args)
  | .guard site, [condition], [] =>
      .ok (app "View.guard" [toString condition, declared],
       app "Correspondence.guard" [literal site, toString condition, declared])
  | .loop site maximum yielded, count :: initial, _ =>
      .ok (app "View.loop" [toString maximum, literal yielded, toString count,
        literal initial, declared, app bodyName arguments],
       app "Correspondence.loop" [literal site, toString maximum, literal yielded,
        toString count, literal initial, declared, app (bodyName ++ "_eq") arguments])
  | _, _, _ => throw ("constructed-view-unsupported-shape: operation=" ++
      literal instruction.operation ++ "; operands=" ++ references ++ "; results=" ++
      declared ++ "; body-instructions=" ++ toString instruction.body.length)

/-- A block is emitted as named actions and bind composition. Nested loops
remain named, parameterized blocks, never an unrolled trace. -/
def block (fuel : Nat) (instructions : List Instruction) (name path : String)
    (inputs : List ValueSort := []) (inputPath : String := "([] : List ValueSort)") :
    Except String String := do
  let fuel + 1 := fuel | throw ("constructed-view-depth: path=" ++ path)
  let mut text := ""
  let mut names : List String := []
  let mut sorts := inputs
  for (instruction, index) in instructions.zipIdx do
    let stepName := name ++ "Step" ++ toString index
    let stepPath := "(" ++ path ++ ")[" ++ toString index ++ "]'(by decide +kernel)"
    match instruction.operation with
    | .loop .. =>
        let outerPath := "((" ++ path ++ ").take " ++ toString index ++
          ").foldl (fun frame instruction => frame ++ instruction.results) (" ++ inputPath ++ ")"
        let bodyInputPath := "((" ++ outerPath ++ ") ++ ValueSort.data Structured.Ty.index :: (" ++
          stepPath ++ ").results)"
        text := text ++ (← block fuel instruction.body (stepName ++ "Body")
          ("(" ++ stepPath ++ ").body")
          (sorts ++ .data .index :: instruction.results) bodyInputPath)
    | _ => pure ()
    let (view, proof) ← (action instruction (stepName ++ "Body")).mapError
      (fun error => error ++ "; path=" ++ stepPath)
    text := text ++ "def " ++ stepName ++ binders ++ " : View.Block model.toCarriers :=\n  " ++
      view ++ "\n\n" ++
      "theorem " ++ stepName ++ "_eq" ++ binders ++ " :\n" ++
      "    Correspondence.Step (program := program) (context := context)\n" ++
      "      (" ++ stepPath ++ ") " ++ app stepName arguments ++ " :=\n  " ++ proof ++ "\n\n"
    names := names ++ [stepName]
    sorts := sorts ++ instruction.results
  let view := names.foldr (fun name rest => app "View.sequence" [app name arguments, rest]) "View.empty"
  let proof := names.foldr (fun name rest => app "Correspondence.sequence"
    [app (name ++ "_eq") arguments, rest]) "Correspondence.empty"
  let results := instructions.map (·.results)
  pure (text ++ "def " ++ name ++ "SlotInputs : List ValueSort := " ++ literal inputs ++
    "\n\ntheorem " ++ name ++ "SlotInputs_eq : " ++ name ++ "SlotInputs =\n" ++
    "    (" ++ inputPath ++ ") := by kernel_rfl\n\n" ++
    "def " ++ name ++ "SlotResults : List (List ValueSort) := " ++ literal results ++
    "\n\ntheorem " ++ name ++ "SlotResults_eq : " ++ name ++ "SlotResults =\n" ++
    "    (" ++ path ++ ").map (fun instruction => instruction.results) := by kernel_rfl\n\n" ++
    "def " ++ name ++ "SlotSorts : List (List ValueSort) :=\n  " ++ name ++
    "SlotResults.scanl (fun frame results => frame ++ results) " ++ name ++ "SlotInputs" ++
    "\n\ntheorem " ++ name ++ "SlotSorts_eq : " ++ name ++ "SlotSorts =\n" ++
    "    (" ++ path ++ ").scanl (fun frame instruction => frame ++ instruction.results)\n" ++
    "      (" ++ inputPath ++ ") := by\n" ++
    "  unfold " ++ name ++ "SlotSorts\n" ++
    "  rw [" ++ name ++ "SlotInputs_eq, " ++ name ++ "SlotResults_eq, List.scanl_map]\n\n" ++
    "def " ++ name ++ binders ++ " : View.Block model.toCarriers :=\n  " ++ view ++
    "\n\ntheorem " ++ name ++ "_eq" ++ binders ++ " :\n" ++
    "    Correspondence.Block (program := program) (context := context)\n" ++
    "      (" ++ path ++ ") " ++ app name arguments ++ " :=\n  " ++ proof ++ "\n\n")
termination_by fuel

def source (artifact : Participant) (output : Output) : Except String String := do
  let body ← block 1024 artifact.instructions "body" "artifact.instructions"
    artifact.inputs "artifact.inputs"
  pure ("module\n\npublic import " ++ output.artifactModule ++
    "\npublic import Zkc.Construction.DomainBinding\n\n@[expose] public section\n\n" ++
    "/-! Generated by ZkcTools.StructuredSource.Constructed. Kernel-checked whole\n" ++
    "open Process views of the actual retained artifact, with all runtime checks.\n" ++
    "No authored mathematical evidence is imported. Regenerate; do not hand edit. -/\n" ++
    "set_option autoImplicit false\nset_option smartUnfolding false\n" ++
    "set_option maxRecDepth 10000\nset_option maxHeartbeats 8000000\n" ++
    "set_option linter.unusedVariables false\n" ++
    "namespace " ++ output.moduleName ++ "\nopen Zkc.Source Zkc.Construction Zkc.Construction.Domain\n\n" ++
    "abbrev artifact : Participant := " ++ output.artifactExpression ++ "\n\n" ++
    "def inputSorts : List ValueSort := " ++ literal artifact.inputs ++ "\n" ++
    "def outputSorts : List ValueSort := " ++ literal artifact.outputs ++ "\n" ++
    "def returned : List Nat := " ++ literal artifact.returned ++ "\n\n" ++ body ++
    "def view" ++ binders ++ " (inputs : Environment model.toCarriers) :\n" ++
    "    PIR.Process (effects model.toCarriers) (Result model.toCarriers) :=\n" ++
    "  View.participant inputSorts outputSorts returned " ++ app "body" arguments ++ " inputs\n\n" ++
    "theorem participant_eq" ++ binders ++ " (inputs : Environment model.toCarriers) :\n" ++
    "    Domain.participant model program context artifact inputs = view model program context inputs :=\n" ++
    "  Correspondence.participant artifact (body_eq model program context) inputs\n\n" ++
    "end " ++ output.moduleName ++ "\n")

end ZkcTools.StructuredSource.Constructed
