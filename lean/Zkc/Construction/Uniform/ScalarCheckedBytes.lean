module

public import Zkc.Construction.ScalarConnection
public import Zkc.Executable.DomainSuccessRules

@[expose] public section

/-! Honest-success transport through the same complete connection used by
scalar execution. Success remains a property-layer premise about the source;
source/compiler correspondence is unrestricted. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.ScalarCheckedBytes
open Zkc.Source Zkc.Source.Structured Zkc.Executable Zkc.Executable.DomainVM
open DomainAdapter
variable {F G A B : Type}

theorem passes_of_run (key : Origin → Origin) (initial : History F G) (oracle : History F G → F)
    (process : PIR.Process (Domain.effects (uniformCarriers F G)) A) (proof : Proof F G)
    (value : A) (unread : Proof F G)
    (executed : run (m := Id) key initial oracle process proof = (.returned value, unread)) :
    Passes key initial oracle process proof (fun result rest => result = value ∧ rest = unread) := by
  induction process generalizing proof with
  | done result => cases executed; exact ⟨rfl, rfl⟩
  | halt => cases executed
  | call operation next ih =>
    cases operation with
    | receive ty site schema peer =>
      cases proof with
      | nil => cases executed
      | cons payload rest =>
        cases decoded : Value.decode ty (.data payload) with
        | none =>
          simp only [DomainAdapter.run, DomainAdapter.runK, decoded, pure] at executed
          cases executed
        | some answer =>
          simpa only [Passes, decoded] using ih answer rest (by simpa only [DomainAdapter.run, DomainAdapter.runK, decoded] using executed)
    | send | observe | checkpoint => exact ih () proof executed
    | localService => cases executed
    | query history origin =>
      simp only [Passes]
      by_cases drawn : Domain.drawRequest origin = true
      · cases replied : query (m := Id) key initial oracle history origin with
        | stopped reason =>
          simp only [DomainAdapter.run, DomainAdapter.runK, drawn, ite_true, replied, bind, pure] at executed
          cases executed
        | returned answer =>
          refine ⟨drawn, ?_⟩
          simpa only [replied] using ih answer proof (by
            simpa only [DomainAdapter.run, DomainAdapter.runK, drawn, ite_true, replied, bind, Id.instMonad] using executed)
      · simp only [DomainAdapter.run, DomainAdapter.runK, drawn, pure] at executed
        cases executed

theorem passes_transport {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects (uniformCarriers F G)) A → Domain.Environment (uniformCarriers F G) → Prop}
    {source : PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {target : PIR.Process (Domain.effects (uniformCarriers F G)) B}
    (connection : Original.Simulation returns live source target)
    (key : Origin → Origin) (initial : History F G) (oracle : History F G → F)
    (proof : Proof F G) (property : A → Proof F G → Prop) (post : B → Proof F G → Prop)
    (passes : Passes key initial oracle source proof property)
    (returned : ∀ a b unread, returns a b → property a unread → post b unread) :
    Passes key initial oracle target proof post := by
  induction connection generalizing proof with
  | done related => exact returned _ _ _ related passes
  | halt => exact False.elim passes
  | checkpoint frame related next ih => exact ih proof passes
  | call operation next ih =>
    cases operation with
    | receive ty site schema peer =>
      cases proof with
      | nil => exact False.elim passes
      | cons payload unread =>
        cases decoded : Value.decode ty (.data payload) with
        | none => simp only [Passes, decoded] at passes
        | some value => simpa only [Passes, decoded] using ih value unread (by simpa only [Passes, decoded] using passes)
    | send | observe | checkpoint => exact ih () proof passes
    | localService => exact False.elim passes
    | query history origin =>
      simp only [Passes] at passes ⊢
      obtain ⟨drawn, passes⟩ := passes
      refine ⟨drawn, ?_⟩
      cases replied : query (m := Id) key initial oracle history origin with
      | stopped reason => simp only [replied] at passes
      | returned value => simpa only [replied] using ih value proof (by simpa only [replied] using passes)

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Full returns and readable nominal histories are transported together.
The scalar presentation's history projection is fixed by the actual artifact. -/
theorem connected {program : Program} {routing : Original.Routing} {role : Nat}
    {abi : Original.InputABI} {artifact : Participant}
    (connection : SourceConnection.Connected program routing role abi artifact)
    (mode : routing.mode = .validator) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement) (noLocal : routing.locals = [])
    (physical : Domain.Environment (uniformCarriers F G))
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs)
    (decoded : abi.read physical program.payload.entry.inputs = some inputs)
    (emptyHistory : ConnectionInputs.inputHistory routing.context artifact.inputs physical = [])
    (supported : ScalarSupport.Supported (ScalarProjection.iterations artifact)
      (Occurrence.participant (ringModel F G) program role inputs))
    (initial : History F G) (oracle : History F G → F) (proof : Proof F G)
    (property : (Values (Component (assignment F G)) program.payload.entry.outputs ×
      Domain.History (uniformCarriers F G)) → Proof F G → Prop)
    (post : Domain.Result (uniformCarriers F G) → Proof F G → Prop)
    (passes : Passes SourceProcess.legacyOrigin initial oracle
      (SourceProcess.sourceView routing.context
        ((program.participant F G role inputs).interpret CommonAdapter.project) []) proof property)
    (returned : ∀ scalar actual target unread,
      scalar.1 = actual.1 → scalar.2 = ScalarProjection.history (ScalarProjection.iterations artifact) actual.2.history →
      Original.CompleteReturns program.payload.entry.signature routing.context role artifact actual target →
      property scalar unread → post target unread) :
    Passes (ScalarVerifier.origin artifact) initial oracle
      (Domain.participant (ringModel F G) program routing.context artifact physical) proof post := by
  have occurrence : SourceConnection.occurrence program role abi (ringModel F G) physical =
      Occurrence.participant (ringModel F G) program role inputs := by simp only [SourceConnection.occurrence, decoded]
  have covered := Classical.choice (connection.coverage (ringModel F G) physical)
  rw [occurrence] at covered
  have observed := Classical.choice (ScalarObservation.simulation mode replacement profile noLocal covered supported
    (by intro _; rfl) [])
  have presented := passes
  rw [← ScalarConnection.scalar_participant] at presented
  have projected := passes_transport observed SourceProcess.legacyOrigin initial oracle proof _
    (fun actual unread => ∃ scalar, scalar.1 = actual.1 ∧
      scalar.2 = ScalarProjection.history (ScalarProjection.iterations artifact) actual.2.history ∧ property scalar unread)
    presented (by intro scalar actual unread related good; exact ⟨scalar, related.1, related.2.2, good⟩)
  obtain ⟨actual, unread, good, executed⟩ := Passes.run _ _ _ _ _ _ projected
  have executed' := executed
  change DomainAdapter.runK (m := Id) SourceProcess.legacyOrigin initial oracle _ proof _ = _ at executed'
  rw [ScalarProjection.runK_operations, ScalarProjection.key_artifact] at executed'
  have actualPasses := passes_of_run (ScalarVerifier.origin artifact) initial oracle _ proof actual unread executed'
  have source : SourceConnection.source program routing role abi artifact (ringModel F G) physical =
      Original.fold routing (Occurrence.participant (ringModel F G) program role inputs) ⟨[], []⟩ := by
    rw [connection.source_eq_fold, occurrence]
    congr 1
    simp only [SourceConnection.initial, emptyHistory]
  apply passes_transport (Classical.choice (connection.simulation (ringModel F G) physical))
    (ScalarVerifier.origin artifact) initial oracle proof _ post
  · rw [source]
    exact actualPasses
  · intro original target rest related same
    obtain ⟨rfl, rfl⟩ := same
    obtain ⟨scalar, result, history, property⟩ := good
    exact returned scalar original target rest result history related property

end Zkc.Construction.Uniform.ScalarCheckedBytes
