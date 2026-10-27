module

public import ZkcExamples.Construction.GkrOriginalOutput
public import ZkcSecurity.Realizations.Gkr.HonestProducerSource

@[expose] public section

/-! Parametric GKR output correspondence and full repeat law. This is reusable
library work, independent of any selected participant or physical frame. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OriginalOutput
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting GkrOriginalOutput
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The callback uses the actual occurrence interpreter's helper fold and
iteration observations. The parent-owned source theorem only identifies this
body with its checked plain callback; it supplies no compiled simulation. -/
abbrev Certificate (mode : Domain.Mode) (handle offset index : Nat)
    (captured : Domain.Environment (uniformCarriers F G))
    (point : List F) (history : Domain.History (uniformCarriers F G))
    (compiled : Domain.View.Block (uniformCarriers F G)) :=
    Original.Simulation
      (Original.IterationReturns (Returns mode) [] "s37" index
        [offset + 10, offset + 9] [.data (.vector scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle mode)
        (outputBody.denote
          (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
            HonestProducerSource.observedHelpers (role mode) [] {} Occurrence.iterations)
          ((Values.cons (some index) ((values mode point).append
            (.cons (service mode handle) .nil))) :
            Values (Component (assignment F G)) (.index :: (outputState ++ outputCaptures))).get)
        ⟨[⟨"s37", index⟩], history⟩)
      (compiled (captured ++ .data (.index index) :: carried point history))

def observedCallback (mode : Domain.Mode) (handle offset index : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (point : List F) (history : Domain.History (uniformCarriers F G))
    (routes : Routes mode handle index) :
    Certificate mode handle offset index captured point history (body (ringModel F G) offset) := by
  unfold Certificate
  rw [HonestProducerSource.output_callback]
  exact callback mode handle offset index captured size point history routes

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem values_masked (mode : Domain.Mode) (point : List F) :
    maskValues (role mode) (({} : ProtocolContext).mapScopes outputSpec.stateScopes)
      (values (G := G) mode point) = values mode point := by
  cases mode <;> rfl

/-- The complete original occurrence repeat, with the real source role masks,
source callback and bounds, is related to its ordinary compiled loop. The only
routing premises concern individual original effects, independently resolved. -/
abbrev RepeatCertificate (mode : Domain.Mode) (handle : Nat)
    (captured : Domain.Environment (uniformCarriers F G))
    (point : List F) (history : Domain.History (uniformCarriers F G))
    (count : Nat) (compiled : Domain.View.Block (uniformCarriers F G)) :=
    Original.Simulation
      (fun original final => ∃ next, Returns mode original next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle mode)
        (denoteRepeatOn outputSpec {} (role mode) (some count) (values mode point)
          (.cons (service mode handle) .nil)
          (fun args => outputBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              HonestProducerSource.observedHelpers (role mode) [] {} Occurrence.iterations) args.get)
          Occurrence.iterations "s37") ⟨[], history⟩)
      (compiled captured)

def outputRepeat (mode : Domain.Mode) (handle offset : Nat)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (point : List F) (history : Domain.History (uniformCarriers F G))
    (count countReference : Nat) (initialReferences : List Nat)
    (countRead : captured[countReference]? = some (.data (.index count)))
    (initialRead : Domain.read captured initialReferences = some (carried point history))
    (routes : ∀ index, Routes mode handle index) :
    RepeatCertificate mode handle captured point history count
      (Domain.View.loop outputSpec.maximum [offset + 10, offset + 9] countReference initialReferences
        [.data (.vector scalarDomain), .transcript context.suite]
        (body (ringModel F G) offset)) := by
  unfold RepeatCertificate
  apply Original.Simulation.occurrenceRepeat (routing handle mode) outputSpec {} (role mode)
    (captures := .cons (service mode handle) .nil)
    (sourceBody := fun args => outputBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        HonestProducerSource.observedHelpers (role mode) [] {} Occurrence.iterations) args.get)
    (site := "s37") (relation := Returns mode)
  · cases mode <;> rfl
  · intro original frame related
    obtain ⟨next, history, rfl, rfl⟩ := related
    rw [values_masked]
    exact ⟨next, history, rfl, rfl⟩
  · intro value state frame index related
    apply Classical.choice
    obtain ⟨next, history, pair, rfl⟩ := related
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    rw [values_masked]
    exact ⟨observedCallback mode handle offset index captured size next history (routes index)⟩
  · intro original frame related
    obtain ⟨next, history, rfl, rfl⟩ := related
    rfl
  · exact countRead
  · exact initialRead
  · rfl
  · rw [values_masked]
    exact ⟨point, history, rfl, rfl⟩


end ZkcSecurity.Realizations.Gkr.OriginalOutput
