module

public import Zkc.Construction.AuthoredPairProducer

@[expose] public section

/-! Shared producer/validator formation of repeats whose carried values do not
include a transcript. These controls do not assume that the loop executes. -/
namespace Tests.ConstructionLocalLoops
open Zkc.Source Zkc.Construction

def context : Context := .fiatShamir "entry" ["P", "V"] 0 1 2
  "random.F/0" (some (.draw "F")) "suite" []

def state : CheckState := ⟨[.data .index, .data .index, .transcript "suite"], 2,
  .none, [], [], []⟩

def body : InstructionRegion := ⟨[.data .index, .data .index],
  [⟨.calculate .indexWrappingAdd, [4, 3], [.data .index], []⟩], [5]⟩

def localLoop : Instruction := ⟨.loop "local" 8, [0, 1], [.data .index], [body]⟩

def final : CheckState := { state with sorts := state.sorts ++ [.data .index] }

example : checkStep context state localLoop = .ok final := rfl

example (program : Structured.Program) :
    AuthoredPair.checkProducerStep program context state localLoop = .ok final := rfl

/-- A nested local repeat contributes its own induction and leaves no aliases
in the outer coordinate map. -/
def nested : InstructionRegion := ⟨[.data .index, .data .index],
  [⟨.loop "inner" 2, [0, 4], [.data .index],
    [⟨[.data .index, .data .index],
      [⟨.calculate .indexWrappingAdd, [6, 5], [.data .index], []⟩], [7]⟩]⟩], [5]⟩

example : checkStep context state { localLoop with regions := [nested] } = .ok final := rfl

example (program : Structured.Program) : AuthoredPair.checkProducerStep program context state
    { localLoop with regions := [nested] } = .ok final := rfl

example : checkStep context state { localLoop with operands := [2, 1] } =
    .error "construction-local-loop" := rfl

example : checkStep context state { localLoop with regions := [{ body with yielded := [2] }] } =
    .error "construction-local-loop-yield" := rfl

example : checkStep context state { localLoop with regions := [{ body with yielded := [] }] } =
    .error "construction-local-loop-yield" := rfl

/-- A zero maximum does not suppress checking of malformed dormant code. -/
example : checkStep context state
    { localLoop with
      operation := .loop "local" 0
      regions := [{ body with instructions := [⟨.unsupported "bad", [], [], []⟩] }] } =
    .error "construction-unsupported" := rfl

example : checkStep context { state with pending := .deliver 1 "delivery" } localLoop =
    .error "construction-pending" := rfl

/-- A message cannot be received and then silently discarded at the boundary. -/
def received : InstructionRegion := ⟨[.data .index, .data .index],
  [⟨.receive "message" "message" "P" .index, [], [.data .index], []⟩], [4]⟩

example : checkStep context state { localLoop with regions := [received] } =
    .error "construction-local-loop-yield" := rfl

/-- Even a correctly observed message requires returning its changed transcript. -/
def observed : InstructionRegion := ⟨[.data .index, .data .index],
  received.instructions ++ [
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.indicesAppend, [6, 3], [.indices], []⟩,
    ⟨.observe "suite" ⟨"entry", [.repeat "entry" "local"],
      ["message", "entry", "message", "message", "P", "V"]⟩,
      [2, 5, 7], [.transcript "suite"], []⟩], [4]⟩

example : checkStep context state { localLoop with regions := [observed] } =
    .error "construction-local-loop-yield" := rfl

/-- The shared output rule independently refuses invented challenge progress. -/
example : localLoopOutput state { state with seen := ["new-draw"] } [] [] =
    .error "construction-local-loop-yield" := rfl

end Tests.ConstructionLocalLoops
