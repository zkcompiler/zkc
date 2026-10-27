module

public import Zkc.Construction.ArtifactBinding
public import Zkc.Construction.OriginalABI

@[expose] public section

/-! Structural certificates for nested occurrence loops. A callback must close
the exact source frame and justify every compiled yield and its nominal sort.
The rules use the existing source fold and compiled iteration implementation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers} {A : Type}

theorem fold_done (routing : Routing) (value : A) (state : State carriers) :
    fold routing (.done value) state = .done (value, state) := rfl

/-- A callback retains its entire original result and reached history. Its
physical return map is checked before relating the next carried state. -/
def IterationReturns
    (relation : (A × State carriers) → Domain.Environment carriers → Prop)
    (outer : Frames) (site : String) (index : Nat)
    (yielded : List Nat) (declared : List ValueSort)
    (source : A × State carriers) (final : Domain.Environment carriers) : Prop :=
  source.2.frames = outer ++ [⟨site, index⟩] ∧
    ∃ carried, Domain.read final yielded = some carried ∧
      Domain.sortsMatch declared carried = true ∧
      relation (source.1, ⟨outer, source.2.history⟩) carried

/-- Closing a nested callback requires its actual last frame. No ordinary-action
restriction is imposed: an inner certified loop can establish the same law. -/
def Simulation.occurrenceStep
    (routing : Routing) (site : String) (index : Nat)
    (source : PIR.Process (Structured.Occurrence.signature carriers) A)
    (initial : State carriers)
    (body : PIR.Process (Domain.effects carriers) (Domain.Environment carriers))
    (captured : Domain.Environment carriers) (yielded : List Nat) (declared : List ValueSort)
    (relation : (A × State carriers) → Domain.Environment carriers → Prop)
    (certificate : Simulation
      (IterationReturns relation initial.frames site index yielded declared)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing source { initial with frames := initial.frames ++ [⟨site, index⟩] }) body) :
    Simulation relation (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing (Structured.Occurrence.iterations.within site index source) initial)
      (body.bind fun final =>
        match Domain.read final yielded with
        | none => .halt .refused
        | some carried =>
            if Domain.sortsMatch declared carried then .done carried else .halt .refused) := by
  rw [fold_within]
  apply certificate.bind (fun _ _ retained => retained)
  intro original final returned
  apply Classical.choice
  obtain ⟨frames, carried, read, sorts, related⟩ := returned
  refine ⟨?_⟩
  simp only [frames, List.getLast?_concat, List.dropLast_concat, ↓reduceIte,
    read, sorts]
  exact .done related

/-- A single symbolic callback certificate composes over any ordered index
list, with arbitrary outer source frames and arbitrary provider replies. -/
def Simulation.occurrenceIterate
    (routing : Routing) (site : String)
    (step : A → Nat → PIR.Process (Structured.Occurrence.signature carriers) A)
    (body : Domain.View.Block carriers)
    (captured : Domain.Environment carriers) (yielded : List Nat) (declared : List ValueSort)
    (relation : (A × State carriers) → Domain.Environment carriers → Prop)
    (callback : ∀ value state carried index, relation (value, state) carried →
      Simulation (IterationReturns relation state.frames site index yielded declared)
        (fun _ frame => ArtifactBinding.Captures captured frame)
        (fold routing (step value index) { state with frames := state.frames ++ [⟨site, index⟩] })
        (body (captured ++ .data (.index index) :: carried)))
    (indices : List Nat) (value : A) (state : State carriers)
    (carried : Domain.Environment carriers) (related : relation (value, state) carried) :
    Simulation relation (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing (Finite.fold
        (fun value index => Structured.Occurrence.iterations.within site index (step value index))
        indices value) state)
      (Domain.iterate body captured yielded declared indices carried) := by
  rw [fold_finite]
  apply Simulation.iterate
  · intro source carried index related
    exact Simulation.occurrenceStep routing site index (step source.1 index) source.2
      (body (captured ++ .data (.index index) :: carried)) captured yielded declared relation
      (callback source.1 source.2 carried index related)
  · exact fun _ _ _ retained => retained
  · exact related

/-- Complete bounded compiled-loop wrapper. Source and target both refuse an
excessive count; the successful branch retains the whole immutable capture. -/
def Simulation.occurrenceLoop
    (routing : Routing) (site : String)
    (step : A → Nat → PIR.Process (Structured.Occurrence.signature carriers) A)
    (body : Domain.View.Block carriers)
    (captured : Domain.Environment carriers) (yielded : List Nat) (declared : List ValueSort)
    (relation : (A × State carriers) → Domain.Environment carriers → Prop)
    (callback : ∀ value state carried index, relation (value, state) carried →
      Simulation (IterationReturns relation state.frames site index yielded declared)
        (fun _ frame => ArtifactBinding.Captures captured frame)
        (fold routing (step value index) { state with frames := state.frames ++ [⟨site, index⟩] })
        (body (captured ++ .data (.index index) :: carried)))
    (sortInvariant : ∀ source carried, relation source carried →
      Domain.sortsMatch declared carried = true)
    (maximum count countReference : Nat) (initialReferences : List Nat)
    (countRead : captured[countReference]? = some (.data (.index count)))
    (value : A) (state : State carriers) (carried : Domain.Environment carriers)
    (initialRead : Domain.read captured initialReferences = some carried)
    (initialSorts : Domain.sortsMatch declared carried = true)
    (related : relation (value, state) carried) :
    Simulation
      (fun source final => ∃ next, relation source next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (if count ≤ maximum then fold routing (Finite.fold
        (fun value index => Structured.Occurrence.iterations.within site index (step value index))
        (List.range count) value) state else .halt .refused)
      (Domain.View.loop maximum yielded countReference initialReferences declared body captured) := by
  simp only [Domain.View.loop, countRead, initialRead, initialSorts, and_true]
  by_cases bound : count ≤ maximum
  · simp only [bound, ↓reduceIte]
    have head := Simulation.occurrenceIterate routing site step body captured yielded declared relation
      callback (List.range count) value state carried related
    have tail : ∀ original final, relation original final →
        Simulation (fun source final => ∃ next, relation source next ∧ final = captured ++ next)
          (fun _ frame => ArtifactBinding.Captures captured frame)
          (.done original) (Domain.View.append declared captured final) := by
      intro original final returned
      have sorts := sortInvariant original final returned
      simp only [Domain.View.append, sorts, ↓reduceIte]
      exact .done ⟨final, returned, rfl⟩
    simpa only [PIR.Process.bind_done] using
      head.bind (fun _ _ retained => retained) tail
  · simp only [bound, ↓reduceIte]
    exact .halt .refused

/-- Bind the actual structured repeat, including its input and output role
masks. The relation must survive the real mask, rather than assuming that all
optional components are present. Nested callbacks use the same frame rule. -/
def Simulation.occurrenceRepeat
    (routing : Routing) (spec : Structured.RepeatSpec)
    (context : Structured.ProtocolContext) (self : Nat)
    (active : (spec.roles.map context.roles).contains self = true)
    (captures : Values (Component carriers.Value) spec.captures)
    (sourceBody : RegionFunction (Component carriers.Value)
      (Structured.Occurrence.signature carriers)
      (.index :: (spec.state ++ spec.captures), spec.state))
    (site : String) (body : Domain.View.Block carriers)
    (captured : Domain.Environment carriers) (yielded : List Nat) (declared : List ValueSort)
    (relation : (Values (Component carriers.Value) spec.state × State carriers) →
      Domain.Environment carriers → Prop)
    (maskClosed : ∀ original carried, relation original carried →
      relation (Structured.maskValues self (context.mapScopes spec.stateScopes) original.1,
        original.2) carried)
    (callback : ∀ value state carried index, relation (value, state) carried →
      Simulation (IterationReturns relation state.frames
        (Structured.qualifyProtocolSite context.applicationPrefix site) index yielded declared)
        (fun _ frame => ArtifactBinding.Captures captured frame)
        (fold routing
          (sourceBody (.cons (some index)
            ((Structured.maskValues self (context.mapScopes spec.stateScopes) value).append captures)))
          { state with frames := state.frames ++
            [⟨Structured.qualifyProtocolSite context.applicationPrefix site, index⟩] })
        (body (captured ++ .data (.index index) :: carried)))
    (sortInvariant : ∀ original carried, relation original carried →
      Domain.sortsMatch declared carried = true)
    (count countReference : Nat) (initialReferences : List Nat)
    (countRead : captured[countReference]? = some (.data (.index count)))
    (value : Values (Component carriers.Value) spec.state) (state : State carriers)
    (carried : Domain.Environment carriers)
    (initialRead : Domain.read captured initialReferences = some carried)
    (initialSorts : Domain.sortsMatch declared carried = true)
    (related : relation
      (Structured.maskValues self (context.mapScopes spec.stateScopes) value, state) carried) :
    Simulation
      (fun original final => ∃ next, relation original next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing (Structured.denoteRepeatOn spec context self (some count) value
        captures sourceBody Structured.Occurrence.iterations site) state)
      (Domain.View.loop spec.maximum yielded countReference initialReferences declared body captured) := by
  rw [fold_repeat]
  simp only [active, ↓reduceIte, Domain.View.loop, countRead, initialRead, initialSorts, and_true]
  by_cases bound : count ≤ spec.maximum
  · simp only [bound, ↓reduceIte]
    have head : Simulation relation (fun _ frame => ArtifactBinding.Captures captured frame)
        (Finite.fold (fun original index => fold routing
          (Structured.Repeat.stepOn spec context self captures sourceBody original.1 index
            Structured.Occurrence.iterations site) original.2)
          (List.range count)
          (Structured.maskValues self (context.mapScopes spec.stateScopes) value, state))
        (Domain.iterate body captured yielded declared (List.range count) carried) := by
      apply Simulation.iterate
      · intro original carried index related
        simp only [Structured.Repeat.stepOn, fold_bind, fold_done]
        have inside := Simulation.occurrenceStep routing
          (Structured.qualifyProtocolSite context.applicationPrefix site) index _ original.2
          _ captured yielded declared relation (callback original.1 original.2 carried index related)
        have after : ∀ next final, relation next final →
            Simulation relation (fun _ frame => ArtifactBinding.Captures captured frame)
              (fold routing (.done (Structured.maskValues self
                (context.mapScopes spec.stateScopes) next.1)) next.2) (.done final) := by
          intro next final returned
          rw [fold_done]
          exact .done (maskClosed next final returned)
        have finished := inside.bind (fun _ _ retained => retained) after
        simp only [PIR.Process.bind_done, fold_done] at finished
        convert finished using 1
      · exact fun _ _ _ retained => retained
      · exact related
    have tail : ∀ original final, relation original final →
        Simulation (fun source final => ∃ next, relation source next ∧ final = captured ++ next)
          (fun _ frame => ArtifactBinding.Captures captured frame)
          (.done original) (Domain.View.append declared captured final) := by
      intro original final returned
      simp only [Domain.View.append, sortInvariant original final returned, ↓reduceIte]
      exact .done ⟨final, returned, rfl⟩
    simpa only [PIR.Process.bind_done] using head.bind (fun _ _ retained => retained) tail
  · simp only [bound, ↓reduceIte]
    exact .halt .refused

end Zkc.Construction.Original
