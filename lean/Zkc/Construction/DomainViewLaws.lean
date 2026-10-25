module

public import Zkc.Construction.DomainCorrespondence

@[expose] public section

/-! Exact reductions of generated SSA views. A caller supplies the actual slot
lookups and outcome laws. These rules preserve every effect, checkpoint and
returned frame, and quantify every typed receive/query reply. They introduce
neither an instruction evaluator nor a mathematical interpretation of helpers.
-/
set_option autoImplicit false
namespace Zkc.Construction.Domain.View
open Zkc.Source
variable {carriers : Structured.Carriers}

@[simp] theorem read_nil (env : Environment carriers) : read env [] = some [] := rfl

theorem read_cons (env : Environment carriers) (reference : Nat) (references : List Nat)
    (head : Value carriers) (tail : Environment carriers)
    (found : env[reference]? = some head) (rest : read env references = some tail) :
    read env (reference :: references) = some (head :: tail) := by
  simp only [read] at rest
  simp [read, found, rest]

theorem append_eq (declared : List ValueSort) (env results : Environment carriers)
    (matched : sortsMatch declared results = true) :
    append declared env results = .done (env ++ results) := by
  simp only [append, matched, ite_true]

theorem append_refused (declared : List ValueSort) (env results : Environment carriers)
    (mismatched : sortsMatch declared results = false) :
    append declared env results = .halt .refused := by
  simp only [append, mismatched, Bool.false_eq_true, ite_false]

/-- The pre/post checkpoints are retained even for a pure successful action. -/
theorem sequence_return (first rest : Block carriers) (env next : Environment carriers)
    (returned : first env = .done next) :
    sequence first rest env = .call (.checkpoint env) (fun _ =>
      .call (.checkpoint next) (fun _ => rest next)) := by
  simp only [sequence, returned, PIR.Process.bind]

theorem sequence_stop (first rest : Block carriers) (env : Environment carriers)
    (reason : PIR.Stop) (stopped : first env = .halt reason) :
    sequence first rest env = .call (.checkpoint env) (fun _ => .halt reason) := by
  simp only [sequence, stopped, PIR.Process.bind]

theorem receive_eq (site peer : String) (ty : Structured.Ty) (env : Environment carriers)
    (supported : dataType ty = true) :
    receive site site peer ty [.data ty] env = .call (.receive ty site site peer) (fun reply =>
      match Value.encode ty reply with
      | some encoded => append [.data ty] env [encoded]
      | none => .halt .refused) := by
  simp only [receive, supported, and_self, ite_true]
  kernel_rfl

theorem send_eq (site peer : String) (reference : Nat) (env : Environment carriers)
    (payload : Payload carriers) (found : env[reference]? = some (.data payload)) :
    send site site peer reference [] env =
      .call (.send site site peer payload) (fun _ => .done env) := by
  simp only [send, found, and_self, ite_true]

theorem guard_eq (reference : Nat) (env : Environment carriers) (value : Bool)
    (found : env[reference]? = some (.data (.boolean value))) :
    guard reference [] env = if value then .done env else .halt .reject := by
  cases value <;> simp only [guard, found, ite_true, Bool.false_eq_true, ite_false]

theorem calculation_eq (model : Structured.DomainModel) (operation : Calculation)
    (references : List Nat) (declared : List ValueSort)
    (env arguments results : Environment model.toCarriers)
    (found : read env references = some arguments)
    (returned : calculate model operation arguments = .returned results) :
    calculation model operation references declared env = append declared env results := by
  simp only [calculation, found, returned]

theorem calculation_stop (model : Structured.DomainModel) (operation : Calculation)
    (references : List Nat) (declared : List ValueSort)
    (env arguments : Environment model.toCarriers) (reason : PIR.Stop)
    (found : read env references = some arguments)
    (stopped : calculate model operation arguments = .stopped reason) :
    calculation model operation references declared env = .halt reason := by
  simp only [calculation, found, stopped]

theorem helper_eq (model : Structured.DomainModel) (program : Structured.Program) (name : String)
    (references : List Nat) (declared : List ValueSort)
    (env arguments results : Environment model.toCarriers)
    (found : read env references = some arguments)
    (returned : callHelper model program name declared arguments = .returned results) :
    helper model program name references declared env = append declared env results := by
  simp only [helper, found, returned]

theorem helper_stop (model : Structured.DomainModel) (program : Structured.Program) (name : String)
    (references : List Nat) (declared : List ValueSort)
    (env arguments : Environment model.toCarriers) (reason : PIR.Stop)
    (found : read env references = some arguments)
    (stopped : callHelper model program name declared arguments = .stopped reason) :
    helper model program name references declared env = .halt reason := by
  simp only [helper, found, stopped]

theorem indicesAppend_eq (coordinates index : Nat) (env : Environment carriers)
    (path : List Nat) (value : Nat)
    (foundPath : env[coordinates]? = some (.indices path))
    (foundIndex : env[index]? = some (.data (.index value))) :
    indicesAppend coordinates index [.indices] env = .done (env ++ [.indices (path ++ [value])]) := by
  simp only [indicesAppend, foundPath, foundIndex, append, sortsMatch, List.map_cons,
    Value.sort, List.map_nil, beq_self_eq_true, ite_true]

theorem observe_eq (context : Context) (template : Template) (state value coordinates : Nat)
    (env : Environment carriers) (history : History carriers) (payload : Payload carriers)
    (path : List Nat) (origin : Origin)
    (foundState : env[state]? = some (.transcript context.suite history))
    (foundValue : env[value]? = some (.data payload))
    (foundCoordinates : env[coordinates]? = some (.indices path))
    (resolved : templateOrigin context template path = some origin)
    (message : origin.request = none) :
    observe context context.suite template state value coordinates [.transcript context.suite] env =
      .call (.observe (.message origin payload)) (fun _ =>
        append [.transcript context.suite] env
          [.transcript context.suite (history ++ [.message origin payload])]) := by
  simp only [observe, foundState, foundValue, foundCoordinates, and_self, ite_true,
    resolved, message]

/-- The original history and dependent reply type are explicit binding data. -/
theorem challenge_eq (context : Context) (suite field : String) (template : Template)
    (state coordinates : Nat) (env : Environment carriers) (history : History carriers)
    (path : List Nat) (origin : Origin)
    (foundState : env[state]? = some (.transcript suite history))
    (foundCoordinates : env[coordinates]? = some (.indices path))
    (resolved : queryOrigin context suite field template path = some origin)
    (request : origin.request = some (.draw field)) :
    challenge context suite field template state coordinates [.data (.field field), .transcript suite]
      env = .call (.query history origin) (fun reply =>
        let value : carriers.Field field := by
          simpa only [Raw, request, Request.draw] using reply
        append [.data (.field field), .transcript suite] env
          [.data (.field field value), .transcript suite (history ++ [.challenge origin])]) := by
  simp only [challenge, foundState, foundCoordinates, and_self, ite_true, resolved,
    request, ↓reduceDIte]

end Zkc.Construction.Domain.View
