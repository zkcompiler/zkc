module

public import Zkc.Construction.DomainExecution

@[expose] public section

/-! Compositional views of constructed programs. These are ordinary Process
combinators, not an instruction interpreter. Each primitive exposes its exact
operands, result checks and partiality. Helpers remain the actual admitted
helpers until the client supplies their checked mathematical laws. -/
set_option autoImplicit false
namespace Zkc.Construction.Domain.View
open Zkc.Source

abbrev Block (carriers : Structured.Carriers) :=
  Environment carriers → PIR.Process (effects carriers) (Environment carriers)
variable {carriers : Structured.Carriers}

def empty : Block carriers := .done

/-- Both checkpoints remain, including the environment before failure. -/
def sequence (first rest : Block carriers) : Block carriers := fun env =>
  .call (.checkpoint env) fun _ =>
    (first env).bind fun next =>
      .call (.checkpoint next) fun _ => rest next

def append (declared : List ValueSort) (env results : Environment carriers) :
    PIR.Process (effects carriers) (Environment carriers) :=
  if sortsMatch declared results then .done (env ++ results) else .halt .refused

def receive (site schema peer : String) (ty : Structured.Ty) (declared : List ValueSort) :
    Block carriers := fun env =>
  if schema = site ∧ dataType ty = true ∧ declared = [.data ty] then
    .call (.receive ty site schema peer) fun value =>
      match Value.encode ty value with
      | some encoded => append declared env [encoded]
      | none => .halt .refused
  else .halt .refused

def send (site schema peer : String) (reference : Nat) (declared : List ValueSort) :
    Block carriers := fun env =>
  match env[reference]? with
  | some (.data payload) =>
      if schema = site ∧ declared = [] then
        .call (.send site schema peer payload) fun _ => .done env
      else .halt .refused
  | _ => .halt .refused

def indicesEmpty (declared : List ValueSort) : Block carriers := fun env =>
  append declared env [.indices []]

def indicesAppend (coordinates index : Nat) (declared : List ValueSort) :
    Block carriers := fun env =>
  match env[coordinates]?, env[index]? with
  | some (.indices path), some (.data (.index value)) =>
      append declared env [.indices (path ++ [value])]
  | _, _ => .halt .refused

def observe (context : Context) (suite : String) (template : Template)
    (state value coordinates : Nat) (declared : List ValueSort) : Block carriers := fun env =>
  match env[state]?, env[value]?, env[coordinates]? with
  | some (.transcript actual history), some (.data payload), some (.indices path) =>
      if suite = actual ∧ suite = context.suite ∧ declared = [.transcript suite] then
        match templateOrigin context template path with
        | some origin =>
            if origin.request = none then
              let event := Event.message origin payload
              .call (.observe event) fun _ =>
                append declared env [.transcript suite (history ++ [event])]
            else .halt .refused
        | none => .halt .refused
      else .halt .refused
  | _, _, _ => .halt .refused

def challenge (context : Context) (suite field : String) (template : Template)
    (state coordinates : Nat) (declared : List ValueSort) : Block carriers := fun env =>
  match env[state]?, env[coordinates]? with
  | some (.transcript actual history), some (.indices path) =>
      if actual = suite ∧ declared = [.data (.field field), .transcript suite] then
        match queryOrigin context suite field template path with
        | some origin =>
            if request : origin.request = some (.draw field) then
              .call (.query history origin) fun answer =>
                let value : carriers.Field field := by
                  simpa only [Raw, request, Request.draw] using answer
                append declared env [.data (.field field value),
                  .transcript suite (history ++ [.challenge origin])]
            else .halt .refused
        | none => .halt .refused
      else .halt .refused
  | _, _ => .halt .refused

/-- Nominal arithmetic includes bounded-index failure and refused decoding. -/
def calculation (model : Structured.DomainModel) (operation : Calculation)
    (references : List Nat) (declared : List ValueSort) : Block model.toCarriers := fun env =>
  match read env references with
  | some arguments =>
      match calculate model operation arguments with
      | .returned results => append declared env results
      | .stopped reason => .halt reason
  | none => .halt .refused

/-- Exact program, signature and operand order remain binding indices. -/
def helper (model : Structured.DomainModel) (program : Structured.Program) (name : String)
    (references : List Nat) (declared : List ValueSort) : Block model.toCarriers := fun env =>
  match read env references with
  | some arguments =>
      match callHelper model program name declared arguments with
      | .returned results => append declared env results
      | .stopped reason => .halt reason
  | none => .halt .refused

def guard (condition : Nat) (declared : List ValueSort) : Block carriers := fun env =>
  if declared = [] then
    match env[condition]? with
    | some (.data (.boolean true)) => .done env
    | some (.data (.boolean false)) => .halt .reject
    | _ => .halt .refused
  else .halt .refused

/-- Immutable captures, induction coordinates and explicit yields use the
existing generic loop. The body is an independently bound Process view. -/
def loop (maximum : Nat) (yielded : List Nat) (count : Nat) (initial : List Nat)
    (declared : List ValueSort) (body : Block carriers) : Block carriers := fun env =>
  match env[count]?, read env initial with
  | some (.data (.index bound)), some carried =>
      if bound ≤ maximum ∧ sortsMatch declared carried then
        (iterate body env yielded declared (List.range bound) carried).bind (append declared env)
      else .halt .refused
  | _, _ => .halt .refused

/-- Full ABI and return map, including private values and final SSA frame. -/
def participant (inputs outputs : List ValueSort) (returned : List Nat) (body : Block carriers)
    (env : Environment carriers) : PIR.Process (effects carriers) (Result carriers) :=
  .call (.checkpoint env) fun _ =>
    if sortsMatch inputs env then
      (body env).bind fun final =>
        match read final returned with
        | some values =>
            if sortsMatch outputs values then .done ⟨values, final⟩ else .halt .refused
        | none => .halt .refused
    else .halt .refused

end Zkc.Construction.Domain.View
