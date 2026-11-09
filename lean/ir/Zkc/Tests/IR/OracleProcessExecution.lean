import Zkc.Tests.IR.OracleProcessData

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured
open Tests.OracleProcessData
namespace Tests.OracleProcessExecution

private def test (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError name)

private def queries (events : List (OracleProtocol.Event ProviderEvent)) : List OracleRead :=
  events.filterMap fun event ↦ match event with
    | .logical (.query request) => some request
    | _ => none

private def providerEvents (events : List (OracleProtocol.Event ProviderEvent)) :
    List ProviderEvent :=
  events.filterMap fun event ↦ match event with
    | .logical (.provider event) | .ordinary event => some event
    | _ => none

private def run (failure : Option (Nat × PIR.Stop) := none) (stopAfter : Bool := false) :=
  OracleProcess.runM (m := Id) model [checked] (ordinary false) (base failure)
    (process stopAfter) state

private def controls : IO Unit := do
  let count ← IO.mkRef (0 : Nat)
  let test (name : String) (condition : Bool) : IO Unit := do
    test name condition
    count.modify (· + 1)
  test "actual checked declaration" (checkOracle snapshot [] math associated 1).isOk
  let result := run
  let reference := (process false).run
    (OracleProtocol.handler model [checked] (ordinary false) (base none)) state
  have exactLaw := OracleProcess.protocol_represents model [checked] (ordinary false) (base none)
    (process false) state
  let _ := exactLaw
  have perAction := OracleProcess.runM_actions (m := Id) model [checked]
    (ordinary false) (base none) (process false) state
  let _ := perAction
  test "complete returned outcome" (result.outcome == .returned 17)
  test "shared provider state" (result.state.oracle.provider == reference.state.oracle.provider)
  test "every provider event and order"
    (providerEvents result.events == providerEvents reference.events)
  test "complete event log" (result.events == reference.events)
  test "all expanded query records" (queries result.events == queries reference.events)
  test "two nested expansions, repeated outer queries" (result.state.oracle.queries == 14)
  test "cache reused across ordinary requests"
    (result.state.oracle.provider.calls == 8 && result.state.oracle.provider.hits == 7 &&
      result.state.oracle.provider.cache == [(anchor 0, 0)] &&
      result.state.oracle.provider.ordinaryCalls == 2)
  test "ordinary and base requests share order"
    (result.state.oracle.provider.order ==
      [true, false, false, false, false, true, false, false, false, false])
  test "expanded stack depths"
    ((queries result.events).map (·.expansion.length) == [0, 1, 2, 2, 1, 2, 2, 0, 1, 2, 2, 1, 2, 2])
  test "expanded invocation stays the actual source invocation"
    ((queries result.events).all
      (fun request ↦ request.location.invocation == state.frame.invocation))
  let child : OracleRead := ⟨kind, anchor 1, 0,
    {location 0 with invocation := state.frame.invocation}, [(anchor 2, location 9)]⟩
  let leaf : OracleRead := ⟨kind, anchor 0, 0,
    {location 0 with invocation := state.frame.invocation},
    [(anchor 2, location 9), (anchor 1, child.location)]⟩
  test "exact child location and expansion ancestry" ((queries result.events)[1]? == some child)
  test "exact leaf location and expansion ancestry" ((queries result.events)[2]? == some leaf)
  for reason in [PIR.Stop.abort, .refused, .incomplete, .reject, .exhausted] do
    let stopped := run (some (2, reason))
    test "child stop reason survives" (stopped.outcome == .stopped reason)
    test "failed child retains post-state and cache"
      (stopped.state.oracle.provider.calls == 2 && stopped.state.oracle.provider.hits == 1 &&
        stopped.state.oracle.provider.cache == [(anchor 0, 0)])
    test "failed child retains log and suppresses all later continuations"
      (stopped.state.oracle.queries == 4 && (queries stopped.events).length == 4 &&
        (providerEvents stopped.events).length == 3 &&
        stopped.state.oracle.provider.order == [true, false, false])
  let halted := run none true
  test "explicit source halt keeps full reached prefix"
    (halted.outcome == .stopped .reject &&
      halted.state.oracle.provider == result.state.oracle.provider &&
      queries halted.events == queries result.events)
  let ordinaryStop := OracleProcess.runM (m := Id) model [checked] (ordinary true) (base none)
    (process false) state
  test "ordinary stop retains state/events and prevents all base queries"
    (ordinaryStop.outcome == .stopped .reject && ordinaryStop.state.oracle.queries == 0 &&
      ordinaryStop.state.oracle.provider.order == [true] && providerEvents ordinaryStop.events ==
        [.ordinary "ordinary"])
  let skipped := OracleProcess.runM (m := Id) model [checked] (ordinary false) (base none)
    (PIR.Process.call (.oracle {request 1 with arguments := .cons none (.cons none .nil)})
      fun _ ↦ .done ()) state
  test "role invisible query skips with no provider or query event"
    (skipped.outcome == .returned () && skipped.state.oracle.queries == 0 &&
      skipped.state.oracle.provider == state.oracle.provider && skipped.events.isEmpty)
  let outside := {request 0 with location := location 8}
  let misplaced := OracleProcess.runM (m := Id) model [checked] (ordinary false) (base none)
    (PIR.Process.call (.oracle outside) fun _ ↦ .done ()) state
  test "wrong source cursor refuses before external operations"
    (misplaced.outcome == .stopped .refused && misplaced.events.isEmpty &&
      misplaced.state.oracle.provider == state.oracle.provider)
  let missing := {state with oracle.entries := []}
  let notFound := OracleProcess.runM (m := Id) model [checked] (ordinary false) (base none)
    (PIR.Process.call (.oracle (request 0)) fun _ ↦ .done ()) missing
  test "missing table refuses with exact query count"
    (notFound.outcome == .stopped .refused && notFound.state.oracle.queries == 1 &&
      (queries notFound.events).length == 1 && notFound.state.oracle.provider.calls == 0)
  let outcomes := OracleProcess.runM (m := List) model [checked]
    (fun action current ↦ [ordinary false action current])
    (fun request current ↦
      if current.calls == 0 then
        [base none request current, base (some (1, .abort)) request current]
      else [base none request current]) (process false) state
  test "genuine outer monad branches on a base request"
    (outcomes.map (·.outcome) == [.returned 17, .stopped .abort])
  test "monadic failed branch retains attempted provider state/log"
    (outcomes[1]?.any fun failed ↦ failed.state.oracle.provider.calls == 1 &&
      failed.state.oracle.queries == 3 && (providerEvents failed.events).length == 2)
  let sampled := OracleProcess.runM (m := List) model [checked]
    (fun action current ↦ [ordinaryChoice 0 action current, ordinaryChoice 1 action current,
      ordinaryChoice 2 action current])
    (fun request current ↦ [base none request current]) adaptiveProcess state
  test "sampled ordinary reply selects the later actual Oracle read"
    (sampled.map (·.outcome) == [.returned (some 10), .returned (some 11), .stopped .refused])
  test "each sampled branch retains its own coherent provider cache"
    (sampled[0]?.any (fun result ↦ result.state.oracle.provider.cache == [(anchor 0, 0)]) &&
      sampled[1]?.any (fun result ↦ result.state.oracle.provider.cache == [(anchor 0, 1)]))
  test "sampled out-of-domain reply stops before any base read"
    (sampled[2]?.any fun result ↦ result.state.oracle.queries == 1 &&
      result.state.oracle.provider.calls == 0 && result.state.oracle.provider.order == [true])
  let virtualView : OracleDataView (.singleton kind) :=
    ⟨0, [1], ⟨anchor 2, .cons 2 .nil⟩⟩
  let demand := OracleProcess.runM (m := Id) model [checked] (ordinary true) (base none)
    (PIR.Process.call (.demand ⟨0, .singleton kind, virtualView⟩) fun _ ↦ .done ()) state
  test "effect-free virtual demand retains its exact located refusal" (match demand.events with
    | [.logical (.refusal location "oracle-virtual-concrete-demand")] =>
      location == ⟨state.frame.invocation, state.frame.definition, state.frame.row⟩ &&
        demand.outcome == .stopped .refused && demand.state.oracle.provider == state.oracle.provider
    | _ => false)
  let baseView : OracleDataView (.singleton kind) :=
    ⟨0, [1], ⟨anchor 0, .cons 2 .nil⟩⟩
  let concrete := OracleProcess.runM (m := Id) model [checked] (ordinary true) (base none)
    (PIR.Process.call (.demand ⟨0, .singleton kind, baseView⟩)
      fun values ↦ .done (values : List Nat)) state
  test "effect-free base demand uses immutable stored data"
    (@BEq.beq (PIR.Outcome (List Nat)) inferInstance concrete.outcome (.returned [10, 20]) &&
      concrete.events.isEmpty &&
      concrete.state.oracle.provider == state.oracle.provider)
  let exception := OracleProcess.runM (m := Except String) model [checked]
    (fun action current ↦ .ok (ordinary false action current))
    (fun _ _ ↦ .error "outer-provider-error") (process false) state
  test "outer exception remains an outer exception" (match exception with
    | .error "outer-provider-error" => true | _ => false)
  IO.println s!"oracle-process-execution: {← count.get} controls passed"

#eval controls

end Tests.OracleProcessExecution
