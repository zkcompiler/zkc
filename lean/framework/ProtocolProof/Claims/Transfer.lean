module

public import ProtocolProof.Claims.Request

/-!
# Property-preserving security steps

A security transformation is a separate proof boundary from exact component installation.
It can change the game and the admissible environment, but its reduction, loss, and requested
budget remain explicit. A protocol author should reuse such a theorem; this interface does
not turn a whole-game inequality into an automatically solved local obligation.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProtocolProof

universe u v w x y z

/-- Statistical upper-bound transport. `translate` is chosen before either experiment runs.
Computational security additionally needs a separately proved resource/cost interpretation. -/
structure UpperTransfer {E : Type u} {O : Type v} [MeasurableSpace O]
    {F : Type w} {P : Type x} [MeasurableSpace P]
    (actual : UpperRequest E O) (model : UpperRequest F P) where
  translate : E → F
  admitted : ∀ e, actual.admissible e → model.admissible (translate e)
  loss : E → ℝ≥0∞
  compare : ∀ e, actual.admissible e →
    actual.experiment.run e actual.event ≤
      model.experiment.run (translate e) model.event + loss e
  budget : ∀ e, actual.admissible e → model.bound (translate e) + loss e ≤ actual.bound e

namespace UpperTransfer

variable {E : Type u} {O : Type v} [MeasurableSpace O]
  {F : Type w} {P : Type x} [MeasurableSpace P]
  {G : Type y} {Q : Type z} [MeasurableSpace Q]
  {actual : UpperRequest E O} {middle : UpperRequest F P} {model : UpperRequest G Q}

/-- A proved stage transfer preserves exactly the source request's meaning. -/
theorem establish (transfer : UpperTransfer actual middle) (proof : middle.Holds) :
    actual.Holds := by
  intro e he
  exact (transfer.compare e he).trans
    ((add_le_add (proof _ (transfer.admitted e he)) le_rfl).trans (transfer.budget e he))

/-- Consecutive security steps compose their environment translations and explicit losses. -/
def comp (first : UpperTransfer actual middle) (second : UpperTransfer middle model) :
    UpperTransfer actual model where
  translate e := second.translate (first.translate e)
  admitted e he := second.admitted _ (first.admitted e he)
  loss e := second.loss (first.translate e) + first.loss e
  compare e he := by
    calc
      actual.experiment.run e actual.event ≤
          middle.experiment.run (first.translate e) middle.event + first.loss e :=
        first.compare e he
      _ ≤ (model.experiment.run (second.translate (first.translate e)) model.event +
          second.loss (first.translate e)) + first.loss e :=
        add_le_add (second.compare _ (first.admitted e he)) le_rfl
      _ = _ := add_assoc _ _ _
  budget e he := by
    rw [← add_assoc]
    exact (add_le_add (second.budget _ (first.admitted e he)) le_rfl).trans (first.budget e he)

/-- Identity changes no experiment and charges no loss. -/
def identity (request : UpperRequest E O) : UpperTransfer request request where
  translate := id
  admitted _ h := h
  loss _ := 0
  compare _ _ := by simp
  budget _ _ := by simp

end UpperTransfer

/-- Exact equality of each permitted view establishes the statistical request at any nonnegative error.
The same simulator is fixed outside the private-witness quantifier. -/
theorem ViewRequest.establish_exact {P : Type u} {W : Type v} {V : Type w}
    [MeasurableSpace V] (request : ViewRequest P W V)
    (equalViews : ∀ publicInput witness, request.valid publicInput witness →
      request.real.run (publicInput, witness) = request.simulated.run publicInput) :
    request.Holds := by
  intro publicInput witness hvalid event _
  rw [equalViews publicInput witness hvalid]
  exact ⟨le_add_right le_rfl, le_add_right le_rfl⟩

end ProtocolProof
