module

public import Zkc.Construction.DomainExecution
public import Zkc.Construction.LayoutPermutation

@[expose] public section

/-! Closed local control preserves selected rejection and dormant-arm formation.
No local branch can acquire transcript or service interactions. -/
namespace Tests.LocalRegions
open Zkc.Source Zkc.Construction

def selection : Instruction :=
  ⟨.localBranch, [0, 1], [.data .boolean],
    [⟨[.data .boolean], [], [0]⟩,
     ⟨[.data .boolean], [⟨.guard "require", [0], [], []⟩], [0]⟩]⟩

example : checkClosedStep .local (fun _ _ _ _ => true)
    [.data .boolean, .data .boolean] selection =
      .ok [.data .boolean, .data .boolean, .data .boolean] := by rfl

example : checkClosedStep .math (fun _ _ _ _ => true)
    [.data .boolean, .data .boolean] selection = .error "construction-math-operation" := by rfl

/-- A false guard in the dormant arm is well formed and never executed. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context selection
      [.data (.boolean true), .data (.boolean false)] =
        .done [.data (.boolean true), .data (.boolean false), .data (.boolean false)] := by rfl

/-- A reached guard rejects, preserving its caller and closed local checkpoint. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context selection
      [.data (.boolean false), .data (.boolean false)] =
        .call (.checkpoint [.data (.boolean false), .data (.boolean false), .data (.boolean false)])
          (fun _ => .halt .reject) := by rfl

example : checkClosedStep .local (fun _ _ _ _ => true) [.data .boolean]
    ⟨.localBranch, [0], [], [⟨[], [], []⟩, ⟨[], [⟨.guard "bad", [0], [], []⟩], []⟩]⟩ =
      .error "construction-local-operation" := by rfl

example : checkClosedStep .local (fun _ _ _ _ => true) [.data .boolean]
    ⟨.localBranch, [0], [], [⟨[], [], []⟩,
      ⟨[], [⟨.receive "message" "message" "peer" .index, [], [.data .index], []⟩], []⟩]⟩ =
      .error "construction-local-operation" := by rfl

example : checkClosedStep .local (fun _ _ _ _ => true) [.data .boolean, .transcript "suite"]
    ⟨.localBranch, [0, 1], [], [⟨[.transcript "suite"], [], []⟩, ⟨[.transcript "suite"], [], []⟩]⟩ =
      .error "construction-local-captures" := by rfl

def localCall (kind : Structured.HelperKind) (name : String)
    (inputs outputs : List ValueSort) : Bool :=
  kind == .local && name == "local-only" && inputs == [.data .boolean] && outputs == [.data .boolean]

def callingArm : InstructionRegion :=
  ⟨[.data .boolean], [⟨.call "local-only", [0], [.data .boolean], []⟩], [1]⟩

example : checkClosedArms .local localCall [.data .boolean]
    ⟨[.data .boolean], [], [0]⟩ callingArm = .ok () := by rfl

/-- Nesting Math inside Local does not grant that Math arm local helper rights. -/
example : checkClosedStep .local localCall [.data .boolean]
    ⟨.localBranch, [0, 0], [.data .boolean],
      [⟨[.data .boolean], [], [0]⟩,
       ⟨[.data .boolean],
         [⟨.mathBranch, [0, 0], [.data .boolean], [⟨[.data .boolean], [], [0]⟩, callingArm]⟩], [1]⟩]⟩ =
      .error "construction-math-call" := by rfl
/-- The backend requirement has a different failed outcome from a source guard. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Domain.step model program context ⟨.require "bound", [0], [], []⟩
      [.data (.boolean false)] = .halt .refused ∧
    Domain.step model program context ⟨.guard "bound", [0], [], []⟩
      [.data (.boolean false)] = .halt .reject := by constructor <;> rfl

/-- Local frames remain zero based under an outer SSA layout perturbation. -/
example : LayoutPermutation.reindexInstructions (· + 1) 1 [selection] =
    [{ selection with operands := [1, 2] }] := by decide +kernel

/-- A service request carries evaluated bounds, distinct from SSA coordinates. -/
example (port : ServicePort) (template : Template) :
    LayoutPermutation.reindexInstructions (· + 1) 1
      [⟨.localService port (.sampleIndex 8) template [2], [0], [.data .index], []⟩] =
      [⟨.localService port (.sampleIndex 8) template [3], [1], [.data .index], []⟩] := rfl

end Tests.LocalRegions
