module

public import Zkc.Construction.OriginalLoop

@[expose] public section
/-! Structural loop controls independent of the GKR template. -/
set_option autoImplicit false
noncomputable section
namespace Tests.OriginalNestedLoops
open Zkc.Source Zkc.Construction Zkc.Construction.Original
variable {carriers : Structured.Carriers}

def preserved (frames : Frames) (history : Domain.History carriers)
    (source : Nat × State carriers) (frame : Domain.Environment carriers) : Prop :=
  source.2 = ⟨frames, history⟩ ∧ frame = [.data (.index source.1)]

/-- A client with arbitrary outer source frames and a nonempty physical capture.
All ordered induction indices are checked symbolically, including zero trips. -/
def unchanged (routing : Routing) (site : String)
    (frames : Frames) (history : Domain.History carriers)
    (capture : Domain.Environment carriers) (indices : List Nat) (value : Nat) :
    Simulation (preserved frames history)
      (fun _ frame => ArtifactBinding.Captures capture frame)
      (fold routing (Finite.fold
        (fun value index => Structured.Occurrence.iterations.within site index (.done value))
        indices value) ⟨frames, history⟩)
      (Domain.iterate .done capture [capture.length + 1] [.data .index]
        indices [.data (.index value)]) := by
  apply Simulation.occurrenceIterate
  · intro value state carried index related
    apply Classical.choice
    obtain ⟨rfl, rfl⟩ := related
    refine ⟨Simulation.done ?_⟩
    refine ⟨rfl, [.data (.index value)], ?_, rfl, rfl, rfl⟩
    simp [Domain.read]
  · exact ⟨rfl, rfl⟩

/-- Two nested loops really close in order. The inner loop runs under the
outer induction frame and restores that frame before the outer close. -/
theorem nested_close (routing : Routing) (outer inner : String) (i j : Nat)
    (frames : Frames) (history : Domain.History carriers) (value : Nat) :
    fold routing (Structured.Occurrence.iterations.within outer i
      (Structured.Occurrence.iterations.within inner j (.done value))) ⟨frames, history⟩ =
      .done (value, ⟨frames, history⟩) := by
  rw [fold_within, fold_within]
  simp [fold, PIR.Process.interpretState, PIR.Process.bind]

/-- A stopped inner callback cannot execute either closing operation. -/
theorem nested_stop (routing : Routing) (outer inner : String) (i j : Nat)
    (state : State carriers) (reason : PIR.Stop) :
    fold routing (Structured.Occurrence.iterations.within outer i
      (Structured.Occurrence.iterations.within inner j (.halt reason : PIR.Process _ Nat))) state =
      .halt reason := by
  rw [fold_within, fold_within]
  simp [fold, PIR.Process.interpretState, PIR.Process.bind]

/-- An unclosed inner frame cannot be silently popped as the outer frame. -/
theorem mismatched_close (routing : Routing) (outer inner : String) (i j : Nat)
    (state : State carriers) (different : (⟨outer, i⟩ : Structured.Occurrence.Frame) ≠ ⟨inner, j⟩) :
    fold routing (Structured.Occurrence.iterations.within outer i
      (.call (.enter ⟨inner, j⟩) (fun _ => .done (0 : Nat)))) state = .halt .refused := by
  rw [fold_within]
  simp [fold, PIR.Process.interpretState, PIR.Process.bind, operations, Ne.symm different]

/-- Exact yield decoding and nominal sorts are obligations even when a
callback has no actions. Missing physical outputs cannot certify a return. -/
theorem missing_yield (relation : (Nat × State carriers) → Domain.Environment carriers → Prop)
    (frames : Frames) (site : String) (index : Nat) (source : Nat × State carriers) :
    ¬ IterationReturns relation frames site index [0] [.data .index] source [] := by
  rintro ⟨_, carried, read, _, _⟩
  simp [Domain.read] at read

theorem changed_sort (relation : (Nat × State carriers) → Domain.Environment carriers → Prop)
    (frames : Frames) (site : String) (index : Nat) (source : Nat × State carriers) :
    ¬ IterationReturns relation frames site index [0] [.data .boolean] source [.data (.index 0)] := by
  rintro ⟨_, carried, read, sorts, _⟩
  have found : carried = [.data (.index 0)] := by simpa [Domain.read] using read.symm
  subst carried
  contradiction

def maskedSpec (maximum : Nat) : Structured.RepeatSpec :=
  ⟨[.index, .index], [], [0], [[0], []], maximum⟩

def maskedReturns (frames : Frames) (history : Domain.History carriers)
    (original : Values (Component carriers.Value) [.index, .index] × State carriers)
    (compiled : Domain.Environment carriers) : Prop :=
  ∃ value, original = (.cons (some value) (.cons none .nil), ⟨frames, history⟩) ∧
    compiled = [.data (.index value)]

/-- A separate actual structured-repeat client. Its second original slot is
masked away although supplied initially; the complete optional result remains
in the relation. Counts above the declared maximum refuse on both sides. -/
def maskedRepeat (routing : Routing) (maximum count value hidden : Nat)
    (frames : Frames) (history : Domain.History carriers) :
    Simulation
      (fun original final => ∃ next, maskedReturns frames history original next ∧
        final = [.data (.index count), .data (.index value)] ++ next)
      (fun _ frame => ArtifactBinding.Captures [.data (.index count), .data (.index value)] frame)
      (fold routing
        (Structured.denoteRepeatOn (maskedSpec maximum) {} 0 (some count)
          (.cons (some value) (.cons (some hidden) .nil)) .nil
          (fun args => .done (.cons (args.get (.there .here))
            (.cons (args.get (.there (.there .here))) .nil)))
          Structured.Occurrence.iterations "repeat") ⟨frames, history⟩)
      (Domain.View.loop maximum [3] 0 [1] [.data .index] .done
        [.data (.index count), .data (.index value)]) := by
  apply Simulation.occurrenceRepeat routing (maskedSpec maximum) {} 0
    (captures := .nil)
    (sourceBody := fun args => .done (.cons (args.get (.there .here))
      (.cons (args.get (.there (.there .here))) .nil)))
    (site := "repeat") (relation := maskedReturns frames history)
  · rfl
  · intro original carried related
    obtain ⟨next, rfl, rfl⟩ := related
    exact ⟨next, rfl, rfl⟩
  · intro original state carried index related
    apply Classical.choice
    obtain ⟨next, pair, rfl⟩ := related
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    exact ⟨.done ⟨rfl, [.data (.index next)], rfl, rfl, next, rfl, rfl⟩⟩
  · intro original carried related
    obtain ⟨next, _, rfl⟩ := related
    rfl
  · rfl
  · rfl
  · rfl
  · exact ⟨value, rfl, rfl⟩

end Tests.OriginalNestedLoops
