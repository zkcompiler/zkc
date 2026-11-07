module

public import Zkc.Construction.DomainCorrespondence
public import Zkc.Construction.LayoutPermutation

@[expose] public section

/-! Local interval semantics: exact carry/capture frames, zero trips, early
completion, stopped bodies and dormant-body admission. -/
namespace Tests.LocalRanges
open Zkc.Source Zkc.Construction

/-- The induction becomes the next state; the immutable Boolean decides whether
another iteration runs. No source sampling coordinate is introduced. -/
def region : InstructionRegion :=
  ⟨[.data .index, .data .index, .data .boolean], [], [2, 0]⟩

def interval : Instruction := ⟨.localRange true, [0, 1, 2, 3], [.data .index], [region]⟩

def frame (model : Structured.DomainModel) (lower upper : Nat) (continuing : Bool) :
    Domain.Environment model.toCarriers :=
  [.data (.index lower), .data (.index upper), .data (.index 42), .data (.boolean continuing)]

example : checkClosedStep .local (fun _ _ _ _ => true)
    [.data .index, .data .index, .data .index, .data .boolean] interval =
      .ok [.data .index, .data .index, .data .index, .data .boolean, .data .index] := rfl

example : checkClosedStep .math (fun _ _ _ _ => true)
    [.data .index, .data .index, .data .index, .data .boolean] interval =
      .error "construction-math-operation" := rfl

/-- The upper bound is exclusive and the induction starts at the lower bound. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context interval (frame model 3 6 true) =
      .done (frame model 3 6 true ++ [.data (.index 5)]) := rfl

/-- False retains the new state, without executing any later body. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context interval (frame model 3 6 false) =
      .done (frame model 3 6 false ++ [.data (.index 3)]) := rfl

example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context interval (frame model 6 6 true) =
      .done (frame model 6 6 true ++ [.data (.index 42)]) := rfl

example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context interval (frame model 7 6 true) =
      .done (frame model 7 6 true ++ [.data (.index 42)]) := rfl

/-- An unconditional range has no continuation result. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context
      ⟨.localRange false, [0, 1, 2], [.data .index], [⟨[.data .index, .data .index], [], [0]⟩]⟩
      [.data (.index 2), .data (.index 4), .data (.index 42)] =
        .done [.data (.index 2), .data (.index 4), .data (.index 42), .data (.index 3)] := rfl

/-- A malformed yield refuses before an empty traversal. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context
      { interval with regions := [{ region with yielded := [0, 2] }] }
      (frame model 0 0 true) = .halt .refused := rfl

/-- A local traversal cannot smuggle in a service or communication effect. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context
      { interval with regions := [{ region with instructions :=
        [⟨.receive "m" "m" "peer" .index, [], [.data .index], []⟩] }] }
      (frame model 0 0 true) = .halt .refused := rfl

/-- A stopped reached body keeps the outer frame in its checkpoint. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context
      { interval with regions := [{ region with instructions := [⟨.guard "body", [2], [], []⟩] }] }
      (frame model 3 6 false) =
        .call (.checkpoint (frame model 3 6 false ++
          [.data (.index 3), .data (.index 42), .data (.boolean false)])) (fun _ => .halt .reject) := rfl

/-- Zero trips do not execute a well-formed stopping body. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context
      { interval with regions := [{ region with instructions := [⟨.guard "body", [2], [], []⟩] }] }
      (frame model 3 3 false) = .done (frame model 3 3 false ++ [.data (.index 42)]) := rfl

/-- Closed range-local references do not move with the outer SSA frame. -/
example : LayoutPermutation.reindexInstructions (· + 1) 1 [interval] =
    [{ interval with operands := [1, 2, 3, 4] }] := by decide +kernel

example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.Correspondence.Step (model := model) (program := program) (context := context) interval
      (Domain.View.localRange program true 0 1 [2, 3] [.data .index] region Domain.View.empty) :=
  Domain.Correspondence.localRange true 0 1 [2, 3] [.data .index] region
    Domain.Correspondence.empty

end Tests.LocalRanges
