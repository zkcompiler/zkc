module

public import ZkcProgram.MonadExecution
public import ZkcProgram.Interaction
public import ProtocolProof.Semantics.EventLog

/-! Canonical measurable structures on the shared, complete execution carrier. -/

public section

set_option autoImplicit false

open MeasureTheory PIR

namespace PIR

instance : Countable Stop := Function.Injective.countable
  (f := fun reason : Stop ↦ match reason with
    | .reject => (0 : ℕ) | .abort => 1 | .exhausted => 2 | .incomplete => 3 | .refused => 4)
  (by intro a b h; cases a <;> cases b <;> simp_all)
instance : MeasurableSpace Stop := ⊤
instance : MeasurableSingletonClass Stop := ⟨fun _ ↦ trivial⟩

/-- The sum representation includes every terminal reason. -/
@[expose] def Outcome.equiv (A : Type) : Outcome A ≃ A ⊕ Stop where
  toFun | .returned value => .inl value | .stopped reason => .inr reason
  invFun | .inl value => .returned value | .inr reason => .stopped reason
  left_inv outcome := by cases outcome <;> rfl
  right_inv value := by cases value <;> rfl

instance {A : Type} [Countable A] : Countable (Outcome A) :=
  (Outcome.equiv A).injective.countable
instance {A : Type} [MeasurableSpace A] : MeasurableSpace (Outcome A) :=
  MeasurableSpace.comap (Outcome.equiv A) inferInstance

/-- The outcome measurable structure retains the returned value or the exact stop reason. -/
@[expose] def Outcome.measurableEquiv {A : Type} [MeasurableSpace A] : Outcome A ≃ᵐ A ⊕ Stop where
  toEquiv := equiv A
  measurable_toFun := comap_measurable _
  measurable_invFun := measurable_comap_iff.mpr (by
    simpa only [Equiv.self_comp_symm] using (measurable_id : Measurable (id : A ⊕ Stop → _)))

instance {A : Type} [MeasurableSpace A] [MeasurableSingletonClass A] :
    MeasurableSingletonClass (Outcome A) where
  measurableSet_singleton outcome := by
    have hs : MeasurableSet ({Outcome.equiv A outcome} : Set (A ⊕ Stop)) := by
      cases outcome with
      | returned value =>
        change MeasurableSet ({Sum.inl value} : Set (A ⊕ Stop))
        rw [← Set.image_singleton]
        exact (measurableSet_singleton value).inl_image
      | stopped reason =>
        change MeasurableSet ({Sum.inr reason} : Set (A ⊕ Stop))
        rw [← Set.image_singleton]
        exact (measurableSet_singleton reason).inr_image
    have preimage := (comap_measurable (Outcome.equiv A)) hs
    rwa [← Set.image_singleton, (Outcome.equiv A).injective.preimage_image] at preimage

theorem Outcome.measurable_returned {A : Type} [MeasurableSpace A] :
    Measurable (Outcome.returned : A → Outcome A) :=
  Outcome.measurableEquiv.symm.measurable.comp measurable_inl

theorem Outcome.measurable_stopped {A : Type} [MeasurableSpace A] :
    Measurable (Outcome.stopped : Stop → Outcome A) :=
  Outcome.measurableEquiv.symm.measurable.comp measurable_inr

/-- Packing is a bijection, so no outcome, state or event is forgotten. -/
@[expose] def Execution.equiv (S L A : Type) :
    Execution S L A ≃ Outcome A × (S × List L) where
  toFun result := (result.outcome, result.state, result.events)
  invFun result := ⟨result.1, result.2.1, result.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {S L A : Type} [Countable S] [Countable L] [Countable A] :
    Countable (Execution S L A) :=
  (Execution.equiv S L A).injective.countable
instance {S L A : Type} [MeasurableSpace S] [MeasurableSpace L] [MeasurableSpace A] :
    MeasurableSpace (Execution S L A) :=
  MeasurableSpace.comap (Execution.equiv S L A) inferInstance
instance {S L A : Type} [MeasurableSpace S] [MeasurableSpace L] [MeasurableSpace A]
    [MeasurableSingletonClass S] [MeasurableSingletonClass L] [MeasurableSingletonClass A] :
    MeasurableSingletonClass (Execution S L A) where
  measurableSet_singleton result := by
    have preimage := (comap_measurable (Execution.equiv S L A))
      (measurableSet_singleton (Execution.equiv S L A result))
    rwa [← Set.image_singleton, (Execution.equiv S L A).injective.preimage_image] at preimage

namespace Execution
variable {S L A : Type} [MeasurableSpace S] [MeasurableSpace L] [MeasurableSpace A]

/-- The measurable equivalence between records and the backend's full product. -/
@[expose] def measurableEquiv : Execution S L A ≃ᵐ Outcome A × (S × List L) where
  toEquiv := equiv S L A
  measurable_toFun := comap_measurable _
  measurable_invFun := measurable_comap_iff.mpr (by
    simpa only [Equiv.self_comp_symm] using
      (measurable_id : Measurable (id : Outcome A × (S × List L) → _)))

theorem measurable_outcome : Measurable (Execution.outcome : Execution S L A → _) :=
  measurable_fst.comp measurableEquiv.measurable
theorem measurable_state : Measurable (Execution.state : Execution S L A → _) :=
  measurable_fst.comp (measurable_snd.comp measurableEquiv.measurable)
theorem measurable_events : Measurable (Execution.events : Execution S L A → _) :=
  measurable_snd.comp (measurable_snd.comp measurableEquiv.measurable)

end Execution
end PIR
