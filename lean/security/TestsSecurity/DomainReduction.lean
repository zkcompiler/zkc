module

public import ZkcSecurity.Bindings.Transcript.DomainReduction

@[expose] public section

/-! Explicit-history bridge controls over the actual Domain handlers. -/
set_option autoImplicit false
namespace TestsSecurity.DomainReduction
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir
open ZkcSecurity.FiatShamir.DomainReduction

abbrev carriers := Structured.uniformCarriers Bool Unit
abbrev State := Domain.History carriers × Bool

def context : Context :=
  Context.fiatShamir "entry" (["producer", "validator"]) 0 1 0 "random.scalar/0" (some (.draw "scalar")) "suite" ([])

def message (site : String) (value : Bool) : Domain.Event carriers :=
  .message (context.message site 0 1) (.field "scalar" value)
def delivery (value : Bool) : Domain.Event carriers :=
  .message (context.message "delivery" 1 0) (.field "scalar" value)
abbrev origin := context.query "draw" (.draw "scalar")

def actualRound (state : State) : PIR.Process (Domain.effects carriers) State :=
  .call (.checkpoint [.transcript "suite" state.1]) fun _ =>
  .call (.receive (.field "scalar") "low" "low" "producer") fun low =>
  .call (.observe (message "low" low)) fun _ =>
  .call (.receive (.field "scalar") "high" "high" "producer") fun high =>
  .call (.observe (message "high" high)) fun _ =>
  if low = high then
    let history := (state.1 ++ [message "low" low]) ++ [message "high" high]
    .call (.query history origin) fun answer =>
    .call (.observe (delivery answer)) fun _ =>
      .done (((history ++ [.challenge origin]) ++ [delivery answer]), answer)
  else .halt .reject

def presentedRound (state : State) : PIR.Process (Domain.Actions carriers) State :=
  .call (.receive (.field "scalar") "low" 0) fun low =>
  .call (.receive (.field "scalar") "high" 0) fun high =>
  if low = high then
    let history := (state.1 ++ [message "low" low]) ++ [message "high" high]
    .call (.query "draw" "scalar" (.cons 0 .nil)) fun answer =>
    .call (.send (ty := .field "scalar") "delivery" 0 answer) fun _ =>
      .done (((history ++ [.challenge origin]) ++ [delivery answer]), answer)
  else .halt .reject

theorem read_round (history : Domain.History carriers) (state : State) (same : state.1 = history) :
    ReadingTo (Domain.interface context) (fun reached result => result.1 = reached)
      history (actualRound state) (presentedRound state) := by
  subst history
  apply ReadingTo.checkpoint
  apply ReadingTo.receive (I := Domain.Actions carriers) (.field "scalar") "low" "low" "producer" _
    (.receive (.field "scalar") "low" 0) _ _ _ id rfl
      (by intro payload; simp [Domain.receivedValue])
  intro payload low decoded
  have encoded := Domain.Payload.ofValue_value decoded
  have same : payload = .field "scalar" low := by
    simpa [Domain.Payload.ofValue, Structured.Ty.isHandle] using encoded.symm
  subst payload
  apply ReadingTo.observe
  apply ReadingTo.receive (I := Domain.Actions carriers) (.field "scalar") "high" "high" "producer" _
    (.receive (.field "scalar") "high" 0) _ _ _ id rfl
      (by intro payload; simp [Domain.receivedValue])
  intro payload high decoded
  have encoded := Domain.Payload.ofValue_value decoded
  have same : payload = .field "scalar" high := by
    simpa [Domain.Payload.ofValue, Structured.Ty.isHandle] using encoded.symm
  subst payload
  apply ReadingTo.observe
  change ReadingTo _ _ _ (if low = high then _ else _) (if low = high then _ else _)
  split
  · apply ReadingTo.query (I := Domain.Actions carriers) _ origin _ (.query "draw" "scalar" (.cons 0 .nil)) _ id rfl
      (by rfl)
    intro answer
    apply ReadingTo.absorbSend (I := Domain.Actions carriers) (.send (ty := .field "scalar") "delivery" 0 answer) _
      (delivery answer) () rfl
    apply ReadingTo.observe
    exact .done _ _ rfl
  · exact .halt _ .reject

theorem coherent_round (history : Domain.History carriers) (state : State) (same : state.1 = history) :
    CoherentTo (fun reached result => result.1 = reached) history (actualRound state) := by
  subst history
  apply CoherentTo.checkpoint
  apply CoherentTo.receive
  intro low
  apply CoherentTo.observe
  apply CoherentTo.receive
  intro high
  apply CoherentTo.observe
  change CoherentTo _ _ (if low = high then _ else _)
  split
  · apply CoherentTo.query _ origin _ rfl
    intro answer
    apply CoherentTo.observe
    exact .done _ _ rfl
  · exact .halt _ .reject

/-- Reached histories survive zero, partial and full loops. No future reply is
restricted, and the reject branch remains in the actual Process. -/
theorem read_loop (count : Nat) (history : Domain.History carriers) (value : Bool) :
    ReadingTo (Domain.interface context) (fun reached result => result.1 = reached)
      history (PIR.repeatN count actualRound (history, value))
        (PIR.repeatN count presentedRound (history, value)) :=
  ReadingTo.repeatN (fun reached _ result => result.1 = reached) actualRound presentedRound
    (fun reached _ result holds => read_round reached result holds) count history (history, value) rfl

theorem coherent_loop (count : Nat) (history : Domain.History carriers) (value : Bool) :
    CoherentTo (fun reached result => result.1 = reached)
      history (PIR.repeatN count actualRound (history, value)) :=
  CoherentTo.repeatN (fun reached _ result => result.1 = reached) actualRound
    (fun reached _ result holds => coherent_round reached result holds) count history (history, value) rfl

/-- One bridge supplies the returned-history fact to both sides of a
continuation, including the zero-round case and every received value. -/
theorem bridge_loop_copy (count : Nat) (history : Domain.History carriers) (value : Bool) :
    Bridge (Domain.interface context) (fun reached result => result.1 = reached)
      history
      ((PIR.repeatN count actualRound (history, value)).bind (fun result => .done result))
      ((PIR.repeatN count presentedRound (history, value)).bind (fun result => .done result)) := by
  have bridge : Bridge (Domain.interface context) (fun reached result => result.1 = reached)
      history (PIR.repeatN count actualRound (history, value))
        (PIR.repeatN count presentedRound (history, value)) :=
    ⟨read_loop count history value, coherent_loop count history value⟩
  exact bridge.bind _ _ (fun reached result holds => .done reached result holds)

/-- A stale carried key cannot satisfy actual observation coherence. -/
theorem stale_query_refused (event : Domain.Event carriers) :
    ¬ Coherent ([] : Domain.History carriers)
      (.call (.observe event) fun _ => .call (.query [] origin) fun _ => .done ()) := by
  intro coherent
  have bad := coherent.observe_next.query_history
  simp at bad

/-- A checkpoint changes the failure environment but emits no event. -/
theorem checkpoint_stop {m : Type → Type} [Monad m] [LawfulMonad m]
    (query : Domain.History carriers → (event : Domain.Event carriers) → m (Domain.Raw event))
    (environment : Domain.Environment carriers) (event : Domain.Event carriers)
    (state : Domain.RuntimeState carriers Unit) :
    Domain.run .validator (ZkcSecurity.Endpoint.Domain.Compiled.oracle query)
      (.call (.checkpoint environment) fun _ =>
        .call (.observe event) fun _ => (.halt .reject : PIR.Process (Domain.effects carriers) Unit)) state =
      pure ⟨.stopped .reject, { state with environment := environment }, [event]⟩ := by
  simp [Domain.run, PIR.Process.runM, Domain.handler, PIR.Execution.followM]

end TestsSecurity.DomainReduction

namespace TestsSecurity.DomainReduction
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir

/-- Host carrier equality does not authorize another nominal field's payload. -/
theorem wrong_nominal_payload :
    (Domain.Payload.field (carriers := carriers) "other" false).value (.field "scalar") = none := by
  decide +kernel

/-- Successful reception consumes a payload but emits no observation. A stop
before .observe therefore has an empty event prefix and the exact unread tail. -/
theorem receive_stop_without_observation {m : Type → Type} [Monad m] [LawfulMonad m]
    (query : Domain.History carriers → (event : Domain.Event carriers) → m (Domain.Raw event))
    (unread : Domain.Proof carriers) (state : Domain.RuntimeState carriers Unit) :
    Domain.run .validator (ZkcSecurity.Endpoint.Domain.Compiled.oracle query)
      (.call (.receive (.field "scalar") "low" "low" "producer") fun _ =>
        (.halt .reject : PIR.Process (Domain.effects carriers) Unit))
      { state with proof := .field "scalar" false :: unread } =
      pure ⟨.stopped .reject, { state with proof := unread }, []⟩ := by
  simp [Domain.run, PIR.Process.runM, Domain.handler, PIR.Execution.followM, Domain.Payload.value]

end TestsSecurity.DomainReduction
