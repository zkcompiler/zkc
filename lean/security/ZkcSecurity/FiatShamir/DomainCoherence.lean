module

public import Zkc.Construction.DomainExecutionLaws

@[expose] public section

/-! Coherence of explicit query keys with actual observation prefixes.
This is a derivation on the existing Process, not an evaluator. Receives and
checkpoints never observe. Only actual observations and supported queries
advance the history. The returned-value index supports state-carrying loops. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.DomainReduction
open Zkc.Source Zkc.Construction
variable {carriers : Structured.Carriers} {A B : Type}

inductive CoherentTo (Post : Domain.History carriers → A → Prop) :
    Domain.History carriers → PIR.Process (Domain.effects carriers) A → Prop
  | done (history) (value : A) : Post history value → CoherentTo Post history (.done value)
  | halt (history) (reason : PIR.Stop) : CoherentTo Post history (.halt reason)
  | checkpoint {history next} (environment : Domain.Environment carriers) :
      CoherentTo Post history next →
      CoherentTo Post history (.call (.checkpoint environment) (fun _ => next))
  | observe {history next} (event : Domain.Event carriers) :
      CoherentTo Post (history ++ [event]) next →
      CoherentTo Post history (.call (.observe event) (fun _ => next))
  | send {history next} (site schema peer : String) (payload : Domain.Payload carriers) :
      CoherentTo Post history next →
      CoherentTo Post history (.call (.send site schema peer payload) (fun _ => next))
  | receive {history} (ty : Structured.Ty) (site schema peer : String)
      (next : carriers.Value ty → PIR.Process (Domain.effects carriers) A) :
      (∀ value, CoherentTo Post history (next value)) →
      CoherentTo Post history (.call (.receive ty site schema peer) next)
  | query (history : Domain.History carriers) (origin : Origin)
      (next : Domain.Raw (.challenge origin : Domain.Event carriers) →
        PIR.Process (Domain.effects carriers) A)
      (supported : Domain.drawRequest origin = true) :
      (∀ raw, CoherentTo Post (history ++ [.challenge origin]) (next raw)) →
      CoherentTo Post history (.call (.query history origin) next)

abbrev Coherent := CoherentTo (carriers := carriers) (A := A) (fun _ _ => True)

namespace CoherentTo
variable {Post : Domain.History carriers → A → Prop}

/-- A checked return fact can be weakened without changing any effect. -/
theorem weaken {Next : Domain.History carriers → A → Prop}
    {history : Domain.History carriers} {process : PIR.Process (Domain.effects carriers) A}
    (coherent : CoherentTo Post history process)
    (implies : ∀ reached value, Post reached value → Next reached value) :
    CoherentTo Next history process := by
  induction coherent with
  | done history value holds => exact .done history value (implies history value holds)
  | halt history reason => exact .halt history reason
  | checkpoint env _ ih => exact .checkpoint env ih
  | observe event _ ih => exact .observe event ih
  | send site schema peer payload _ ih => exact .send site schema peer payload ih
  | receive ty site schema peer after _ ih => exact .receive ty site schema peer _ ih
  | query history origin after supported _ ih => exact .query history origin _ supported ih

/-- Bind uses the actual reached history and the full returned value. -/
theorem bind {history : Domain.History carriers}
    {process : PIR.Process (Domain.effects carriers) A} (coherent : CoherentTo Post history process)
    {PostNext : Domain.History carriers → B → Prop}
    (next : A → PIR.Process (Domain.effects carriers) B)
    (continuation : ∀ reached value, Post reached value → CoherentTo PostNext reached (next value)) :
    CoherentTo PostNext history (process.bind next) := by
  induction coherent with
  | done history value holds => exact continuation history value holds
  | halt history reason => exact .halt history reason
  | checkpoint env _ ih => exact .checkpoint env ih
  | observe event _ ih => exact .observe event ih
  | send site schema peer payload _ ih => exact .send site schema peer payload ih
  | receive ty site schema peer after _ ih => exact .receive ty site schema peer _ ih
  | query history origin after supported _ ih => exact .query history origin _ supported ih

theorem repeatN (invariant : Domain.History carriers → Nat → A → Prop)
    (body : A → PIR.Process (Domain.effects carriers) A)
    (step : ∀ history remaining value, invariant history (remaining + 1) value →
      CoherentTo (fun reached => invariant reached remaining) history (body value))
    (count : Nat) (history : Domain.History carriers) (value : A)
    (holds : invariant history count value) :
    CoherentTo (fun reached => invariant reached 0) history (PIR.repeatN count body value) := by
  induction count generalizing history value with
  | zero => exact .done history value holds
  | succ count ih => exact (step history count value holds).bind _ ih

/-- Actual constructed loops preserve the caller's immutable frame and exact
yield/sort checks. Invariants concern every adaptive returned state. -/
theorem iterate
    (body : Domain.Environment carriers →
      PIR.Process (Domain.effects carriers) (Domain.Environment carriers))
    (outer : Domain.Environment carriers) (yielded : List Nat) (declared : List ValueSort)
    (invariant : Domain.History carriers → List Nat → Domain.Environment carriers → Prop)
    (step : ∀ history index rest carried, invariant history (index :: rest) carried →
      CoherentTo (fun reached final => ∀ next, Domain.read final yielded = some next →
        Domain.sortsMatch declared next = true → invariant reached rest next)
        history (body (outer ++ .data (.index index) :: carried)))
    (indices : List Nat) (history : Domain.History carriers) (carried : Domain.Environment carriers)
    (holds : invariant history indices carried) :
    CoherentTo (fun reached => invariant reached []) history
      (Domain.iterate body outer yielded declared indices carried) := by
  induction indices generalizing history carried with
  | nil => exact .done history carried holds
  | cons index rest ih =>
    apply (step history index rest carried holds).bind
    intro reached final preserved
    cases found : Domain.read final yielded with
    | none => exact .halt reached .refused
    | some next =>
      dsimp only
      split
      · exact ih reached next (preserved next found (by assumption))
      · exact .halt reached .refused

/-- An actual observation advances coherence at its continuation. -/
theorem observe_next {history : Domain.History carriers} {event : Domain.Event carriers}
    {next : Unit → PIR.Process (Domain.effects carriers) A}
    (coherent : CoherentTo Post history (.call (.observe event) next)) :
    CoherentTo Post (history ++ [event]) (next ()) := by
  cases coherent
  assumption

/-- Inspecting a coherent query exposes its exact actual prefix. -/
theorem query_history {history stored : Domain.History carriers} {origin : Origin}
    {next : Domain.Raw (.challenge origin : Domain.Event carriers) →
      PIR.Process (Domain.effects carriers) A}
    (coherent : CoherentTo Post history (.call (.query stored origin) next)) :
    stored = history := by
  cases coherent
  rfl

/-- Altering oracle cells outside extensions of the actual observed prefix
preserves the ENTIRE execution, including checkpoint environment, private
returns, unread proof and ordered observations on stopped paths. Oracle state
is arbitrary and is transported through each actual query. -/
theorem run_congr {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    {history : Domain.History carriers} {process : PIR.Process (Domain.effects carriers) A}
    (coherent : CoherentTo Post history process)
    (first second : Domain.Oracle m carriers S)
    (same : ∀ suffix origin state,
      first (history ++ suffix) (.challenge origin) state =
        second (history ++ suffix) (.challenge origin) state)
    (state : Domain.RuntimeState carriers S) :
    Domain.run .validator first process state = Domain.run .validator second process state := by
  rw [Domain.validator_eq_direct, Domain.validator_eq_direct]
  induction coherent generalizing state with
  | done => rfl
  | halt => rfl
  | checkpoint env _ ih => exact ih same _
  | send site schema peer payload _ ih => exact ih same _
  | @observe reached next event _ ih =>
      simp only [Domain.validateDirect]
      have extended : ∀ suffix origin state,
          first ((reached ++ [event]) ++ suffix) (.challenge origin) state =
            second ((reached ++ [event]) ++ suffix) (.challenge origin) state := by
        intro suffix origin state
        simpa only [List.append_assoc] using same ([event] ++ suffix) origin state
      rw [ih extended]
  | receive ty site schema peer next _ ih =>
      simp only [Domain.validateDirect]
      cases hp : state.proof with
      | nil => rfl
      | cons payload unread =>
        cases decoded : payload.value ty with
        | none => simp only [decoded]
        | some value => simpa only [hp, decoded] using ih value same { state with proof := unread }
  | query history origin next supported _ ih =>
      simp only [Domain.validateDirect, supported, ite_true]
      have cell := same [] origin state.oracle
      simp only [List.append_nil] at cell
      rw [cell]
      congr 1
      funext answer
      rcases answer with ⟨outcome, final⟩
      cases outcome with
      | stopped reason => rfl
      | returned raw =>
        simp only [PIR.Execution.followM]
        have extended : ∀ suffix origin' state',
            first ((history ++ [.challenge origin]) ++ suffix) (.challenge origin') state' =
              second ((history ++ [.challenge origin]) ++ suffix) (.challenge origin') state' := by
          intro suffix origin' state'
          simpa only [List.append_assoc] using same ([.challenge origin] ++ suffix) origin' state'
        rw [ih raw extended]

end CoherentTo
end ZkcSecurity.FiatShamir.DomainReduction
