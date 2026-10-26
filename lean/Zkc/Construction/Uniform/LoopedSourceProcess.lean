module

public import Zkc.Construction.Uniform.SourceProcess
public import Zkc.Construction.OriginProjection

@[expose] public section

/-! The retained scalar oracle reads static source sites. Dynamic occurrence
coordinates are erased before that oracle is called. This is a projection of
an existing oracle interface, not an identification of random-oracle games.
Only Process effects are translated; constructed instructions are never read.
-/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.LoopedSourceProcess
open Zkc.Source
open Zkc.Construction.Uniform.DomainAdapter

def event {carriers : Structured.Carriers} : Domain.Event carriers → Domain.Event carriers
  | .message origin payload => .message (Origin.withoutCoordinates origin) payload
  | .challenge origin => .challenge (Origin.withoutCoordinates origin)
  | .publicBinding row => .publicBinding row

def history {carriers : Structured.Carriers} (events : Domain.History carriers) : Domain.History carriers :=
  events.map event

def value {carriers : Structured.Carriers} : Domain.Value carriers → Domain.Value carriers
  | .transcript suite events => .transcript suite (history events)
  | other => other

/-- Retain every protocol effect while projecting its oracle key. Physical
checkpoints are erased only for the returned-value/unread-proof observation. -/
def operations {carriers : Structured.Carriers} :
    PIR.OperationInterpretation (Domain.effects carriers) (Domain.effects carriers)
  | .checkpoint _ => .done ()
  | .observe observed => .call (.observe (event observed)) .done
  | .query events origin => .call (.query (history events) (Origin.withoutCoordinates origin)) .done
  | .localService port origin => .call (.localService port (Origin.withoutCoordinates origin)) .done
  | operation => .call operation .done

theorem readback_history {F G : Type} (events : Domain.History (Structured.uniformCarriers F G)) :
    readbackHistory SourceProcess.legacyOrigin (history events) =
      readbackHistory Origin.withoutCoordinates events := by
  induction events with
  | nil => rfl
  | cons first rest ih =>
      cases first <;>
        simp only [history, List.map_cons, readbackHistory, List.mapM_cons, event,
          readbackEvent, SourceProcess.legacyOrigin] at *
      all_goals rw [ih]

section Handler
variable {F G A R : Type} {m : Type → Type} [Monad m]

theorem query_eq (initial : History F G) (challenge : History F G → m F)
    (events : Domain.History (Structured.uniformCarriers F G)) (origin : Origin) :
    query SourceProcess.legacyOrigin initial challenge (history events) (Origin.withoutCoordinates origin) =
      query Origin.withoutCoordinates initial challenge events origin := by
  rcases origin with ⟨entry, site, request⟩
  cases request with
  | none => rfl
  | some request =>
      rcases request with ⟨method, operands, sort⟩
      cases sort <;> try rfl
      simp only [query, Origin.withoutCoordinates, readback_history, SourceProcess.legacyOrigin]

/-- The key projection precedes the existing challenge action, preserving
its cache and its opaque initial history, every stop and malformed proof head. -/
theorem runK_operations (initial : History F G) (challenge : History F G → m F)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (next : A → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK SourceProcess.legacyOrigin initial challenge (process.interpret operations) proof next =
      runK Origin.withoutCoordinates initial challenge process proof next := by
  induction process generalizing proof with
  | done => rfl
  | halt => rfl
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => rfl
          | cons payload unread =>
              cases decoded : Value.decode ty (.data payload) <;>
                simp only [PIR.Process.interpret, operations, PIR.Process.bind, runK, decoded]
              exact ih _ unread
      | send | observe | checkpoint =>
          simpa only [PIR.Process.interpret, operations, PIR.Process.bind, runK] using ih () proof
      | localService => rfl
      | query events origin =>
          simp only [PIR.Process.interpret, operations, PIR.Process.bind, runK]
          have draw : Domain.drawRequest (Origin.withoutCoordinates origin) = Domain.drawRequest origin := by
            rcases origin with ⟨entry, sites, request⟩
            cases request with
            | none => rfl
            | some request =>
                rcases request with ⟨method, arguments, ty⟩
                by_cases methodEq : method = "draw"
                · subst method
                  cases arguments <;> cases ty <;> rfl
                · cases arguments <;> cases ty <;>
                    simp [Domain.drawRequest, Origin.withoutCoordinates, methodEq]
          rw [draw]
          split
          · rw [query_eq]
            congr 1
            funext answer
            cases answer with
            | stopped => rfl
            | returned reply => exact ih reply proof
          · rfl

end Handler

section Composition
variable {F G A B : Type}

/-- Use an explicitly proved history equality at a component boundary. The
nominal suffix is recovered from the reached physical read, rather than by
inverting the noninjective coordinate projection. -/
def at_history {C : Type} {context : Context} {process : PIR.Process (Actions F G) A}
    {suffix : Domain.History (Structured.uniformCarriers F G)}
    {relation : (A × Domain.History (Structured.uniformCarriers F G)) → C → Prop}
    {live : PIR.Process (Domain.effects (Structured.uniformCarriers F G))
      (A × Domain.History (Structured.uniformCarriers F G)) →
      Domain.Environment (Structured.uniformCarriers F G) → Prop}
    {target : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) C}
    (law : Original.Simulation relation live (SourceProcess.sourceView context process (history suffix)) target)
    (events : Domain.History (Structured.uniformCarriers F G))
    (equal : events = history suffix) :
    Original.Simulation relation live (SourceProcess.sourceView context process events) target := by
  rw [equal]
  exact law

theorem sourceView_bind (context : Context) (process : PIR.Process (Actions F G) A)
    (next : A → PIR.Process (Actions F G) B)
    (events : Domain.History (Structured.uniformCarriers F G)) :
    SourceProcess.sourceView context (process.bind next) events =
      (SourceProcess.sourceView context process events).bind fun result =>
        SourceProcess.sourceView context (next result.1) result.2 := by
  induction process generalizing events with
  | done => rfl
  | halt => rfl
  | call operation continuation ih =>
      cases operation <;>
        simp only [PIR.Process.bind, SourceProcess.sourceView, PIR.Process.bind_assoc]
      all_goals congr 1; funext result; exact ih _ result.2

theorem sourceView_finite {Item : Type} (context : Context)
    (step : A → Item → PIR.Process (Actions F G) A) (items : List Item) (initial : A)
    (events : Domain.History (Structured.uniformCarriers F G)) :
    SourceProcess.sourceView context (Finite.fold step items initial) events =
      Finite.fold (fun state item => SourceProcess.sourceView context (step state.1 item) state.2)
        items (initial, events) := by
  induction items generalizing initial events with
  | nil => rfl
  | cons item rest ih => simp only [Finite.fold, sourceView_bind, ih]

variable {m : Type → Type} [Monad m]

/-- Consume a structural certificate using the already installed Process
handler. Every related return gets its own continuation obligation. -/
theorem simulation_runK {R : Type} {relation : A → B → Prop}
    {live : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A →
      Domain.Environment (Structured.uniformCarriers F G) → Prop}
    {source : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A}
    {target : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) B}
    (law : Original.Simulation relation live source target)
    (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
    (proof : Proof F G)
    (left : A → Proof F G → m (PIR.Outcome R × Proof F G))
    (right : B → Proof F G → m (PIR.Outcome R × Proof F G))
    (agree : ∀ a b unread, relation a b → left a unread = right b unread) :
    runK key initial challenge source proof left =
      runK key initial challenge target proof right := by
  have one := congrArg (fun process => runK key initial challenge process proof left) law.source
  rw [runK_forgetCheckpoints, runK_forgetCheckpoints, runK_bind] at one
  have two := congrArg (fun process => runK key initial challenge process proof right) law.target
  rw [runK_bind] at two
  rw [← one, ← two]
  apply runK_congr_yields _ _ _ _ _ law.paired_yields
  intro result unread related
  exact agree result.1 result.2 unread related

end Composition
end Zkc.Construction.Uniform.LoopedSourceProcess
