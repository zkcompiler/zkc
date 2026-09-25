import Tools.Interactive.TypedLocal

set_option autoImplicit false

namespace Tests.TypedLocal
open Tools.Interactive Zkc.Source

private def fr := "bls12-381.fr"
private def field := "field:" ++ fr
private def rng := "rng:" ++ fr

private def bindings : List OperationBinding :=
  [⟨"draw", "random.draw", [fr], ""⟩,
   ⟨"guard", "control.require", [], ""⟩,
   ⟨"add", "field.add", [fr], ""⟩]

private def source : Explicit.Function :=
  ⟨⟨"GuardedDraw", [("rng", rng), ("allowed", "bool")], [rng, field], some
    [.op "draw_site" "draw" [] ["rng"] ["value", "next"],
     .op "guard_site" "guard" [] ["allowed"] [], .ret ["next", "value"]]⟩,
   some ⟨"Guarded", [("F", fr)]⟩⟩

private def numbers {Ty : Type} {types : List Ty} : Values (fun _ => Nat) types → List Nat
  | .nil => []
  | .cons value rest => value :: numbers rest

private def values {Ty : Type} : (types : List Ty) → List Nat → Option (Values (fun _ => Nat) types)
  | [], [] => some .nil
  | _ :: types, n :: rest => do return .cons n (← values types rest)
  | _, _ => none

-- This abstract service tests reification, ordering and stopping. It is not
-- field arithmetic, a random distribution or a cryptographic implementation.
private abbrev Event := String × String × List Nat
private abbrev interface : PIR.Signature := ⟨Event, fun _ => List Nat⟩

private def meaning : ResultBundle.Meaning Tools.Interactive.TypedLocal.signature interface where
  Value _ := Nat
  condition n := n != 0
  operation request args := .call (request.site, request.contract, numbers args) fun reply =>
    match values request.signature.outputs reply with
    | some result => .done result
    | none => .halt .refused

private def handler : PIR.Handler interface Nat Event := fun request state =>
  match request.2 with
  | ("random.draw", [generation]) =>
      ⟨if generation == state then .returned [17 + generation, generation + 1] else .stopped .exhausted,
        state + 1, [request]⟩
  | ("control.require", [allowed]) =>
      ⟨if allowed == 0 then .stopped .reject else .returned [], state, [request]⟩
  | ("field.add", [a, b]) => ⟨.returned [a + b], state, [request]⟩
  | _ => ⟨.stopped .refused, state, [request]⟩

private def run (source : Explicit.Function) (inputs : List Nat)
    (selected : List OperationBinding := bindings) :
    Result (PIR.Execution Nat Event (List Nat)) := do
  let function ← Tools.Interactive.TypedLocal.elaborate selected source
  let some inputs := values (function.arguments.map Prod.snd) inputs | throw "test-argument-arity"
  let some code := function.code | throw "test-structured-function"
  let result := (code.denote meaning.interpretation
    (ResultBundle.singletons inputs).get).run handler 0
  return ⟨match result.outcome with
    | .returned values => .returned (numbers values)
    | .stopped reason => .stopped reason,
    result.state, result.events⟩

private def observed (source : Explicit.Function) (inputs : List Nat)
    (selected : List OperationBinding := bindings) :
    Option (PIR.Outcome (List Nat) × Nat × List Event) :=
  (run source inputs selected).toOption.map fun result => (result.outcome, result.state, result.events)

example : observed source [0, 1] = some (.returned [1, 17], 1,
    [("draw_site", "random.draw", [0]), ("guard_site", "control.require", [1])]) := by native_decide
example : observed source [0, 0] = some (.stopped .reject, 1,
    [("draw_site", "random.draw", [0]), ("guard_site", "control.require", [0])]) := by native_decide
example : observed source [3, 1] = some (.stopped .exhausted, 1,
    [("draw_site", "random.draw", [3])]) := by native_decide

private def sameTypes : Explicit.Function :=
  ⟨⟨"Order", [("left", field), ("right", field)], [field, field, field], some
    [.op "sum" "add" [] ["right", "left"] ["sum"], .ret ["right", "sum", "left"]]⟩, none⟩
example : observed sameTypes [3, 8] = some (.returned [8, 11, 3], 0,
    [("sum", "field.add", [8, 3])]) := by native_decide

private def reusedAuthority : Explicit.Function :=
  { source with code := { source.code with body := some [
     .op "draw_site" "draw" [] ["rng"] ["value", "next"],
     .op "again" "draw" [] ["rng"] ["other", "last"], .ret ["last", "other"]] } }
private def refusal (function : Explicit.Function) : Option String :=
  match Tools.Interactive.TypedLocal.elaborate bindings function with
  | .ok _ => none
  | .error code => some code
example : refusal reusedAuthority = some "interactive-resource-reuse" := by native_decide

private def empty : Explicit.Function := ⟨⟨"Empty", [], [], some [.ret []]⟩, none⟩
example : observed empty [] = some (.returned [], 0, []) := by native_decide

private def renamed : Explicit.Function :=
  { sameTypes with code := { sameTypes.code with body := some [
    .op "sum" "private_add_binding" [] ["right", "left"] ["sum"], .ret ["right", "sum", "left"]] } }
private def selected : List OperationBinding :=
  [⟨"private_add_binding", "field.add", [fr], "arkworks/field.add"⟩]
example : observed renamed [3, 8] selected = observed sameTypes [3, 8] := by native_decide

private def chained : Explicit.Function :=
  { source with code := { source.code with results := [rng, field, field], body := some [
    .op "before" "guard" [] ["allowed"] [],
    .op "first" "draw" [] ["rng"] ["x", "r1"],
    .op "between" "guard" [] ["allowed"] [],
    .op "second" "draw" [] ["r1"] ["y", "r2"], .ret ["r2", "y", "x"]] } }
example : observed chained [0, 1] = some (.returned [2, 18, 17], 2,
    [("before", "control.require", [1]), ("first", "random.draw", [0]),
     ("between", "control.require", [1]), ("second", "random.draw", [1])]) := by native_decide
example : observed chained [0, 0] = some (.stopped .reject, 0,
    [("before", "control.require", [0])]) := by native_decide

example : ((Tools.Interactive.TypedLocal.elaborate bindings source).toOption.map
    Tools.Interactive.TypedLocal.Function.origin == some source.origin) = true := by native_decide

end Tests.TypedLocal
