module

public import Zkc.Construction.DomainExecution

@[expose] public section

/-! Closed Math regions: all-arm formation and selected-only execution. -/
set_option autoImplicit false
namespace Tests.MathRegions
open Zkc.Construction Zkc.Source

private def field : ValueSort := .data (.field "test-field")
private def captures : List ValueSort := [.data (.vector "test-field"), .data .index, field]
private def immediate : InstructionRegion := ⟨captures, [], [2]⟩
private def checkedRead : InstructionRegion :=
  ⟨captures, [⟨.calculate (.boundedAt "test-field"), [0, 1], [field], []⟩], [3]⟩
private def selection : Instruction :=
  ⟨.mathBranch, [0, 1, 2, 3], [field], [immediate, checkedRead]⟩

example : checkMathStep (fun _ _ _ => true) (.data .boolean :: captures) selection =
    .ok (.data .boolean :: captures ++ [field]) := by rfl

/-- A dormant arm still cannot issue a protocol guard. -/
example : checkMathStep (fun _ _ _ => true) [.data .boolean]
    ⟨.mathBranch, [0], [], [⟨[], [], []⟩,
      ⟨[], [⟨.guard "hidden", [0], [], []⟩], []⟩]⟩ =
    .error "construction-math-operation" := by rfl

/-- Out-of-frame yields in a dormant arm are formation failures. -/
example : checkMathStep (fun _ _ _ => true) [.data .boolean]
    ⟨.mathBranch, [0], [], [⟨[], [], []⟩, ⟨[], [], [1]⟩]⟩ =
    .error "construction-math-yields" := by rfl

/-- The unused checked read would fail on the empty vector. It is not executed. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context)
    (value : model.Field "test-field") :
    Domain.step model program context selection
      [.data (.boolean true), .data (.vector "test-field" []), .data (.index 0),
        .data (.field "test-field" value)] =
      .done [.data (.boolean true), .data (.vector "test-field" []), .data (.index 0),
        .data (.field "test-field" value), .data (.field "test-field" value)] := by rfl

/-- Linking validates a dormant call's complete source signature. -/
private def knownCall (name : String) (inputs outputs : List ValueSort) : Bool :=
  name == "predicate" && inputs == [field] && outputs == [.data .boolean]

private def callSelection (name : String) (argument : Nat) (results : List ValueSort) : Instruction :=
  ⟨.mathBranch, [0, 0, 1], [.data .boolean],
    [⟨[.data .boolean, field], [], [0]⟩,
     ⟨[.data .boolean, field], [⟨.call name, [argument], results, []⟩], [2]⟩]⟩

example : (checkMathStep knownCall [.data .boolean, field]
    (callSelection "predicate" 1 [.data .boolean])).isOk = true := by rfl

example : checkMathStep knownCall [.data .boolean, field]
    (callSelection "missing" 1 [.data .boolean]) =
    .error "construction-math-call" := by rfl

example : checkMathStep knownCall [.data .boolean, field]
    (callSelection "predicate" 0 [.data .boolean]) =
    .error "construction-math-call" := by rfl

example : checkMathStep knownCall [.data .boolean, field]
    (callSelection "predicate" 1 [field]) =
    .error "construction-math-call" := by rfl

/-- A reached failure keeps the caller and exact local frame at its checkpoint. -/
example {carriers : Structured.Carriers} (caller localFrame : Domain.Environment carriers) :
    ((PIR.Process.call (.checkpoint localFrame) (fun _ => .halt .refused) :
        PIR.Process (Domain.effects carriers) Unit).interpret (Domain.withCallerFrame caller)) =
      .call (.checkpoint (caller ++ localFrame)) (fun _ => .halt .refused) := by rfl

/-- Closed arm references remain local even though checkpoints retain the caller. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context)
    (value : model.Field "test-field") :
    Domain.step model program context selection
      [.data (.boolean false), .data (.vector "test-field" []), .data (.index 0),
        .data (.field "test-field" value)] =
      .call (.checkpoint
        ([.data (.boolean false), .data (.vector "test-field" []), .data (.index 0),
          .data (.field "test-field" value)] ++
         [.data (.vector "test-field" []), .data (.index 0), .data (.field "test-field" value)]))
        (fun _ => .halt .refused) := by rfl

end Tests.MathRegions
