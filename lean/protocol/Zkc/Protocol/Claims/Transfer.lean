module

public import Zkc.Protocol.Claims.Request

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

end ProtocolProof

namespace ProtocolProof

universe u v w x y z

/-- Lower-bound transport keeps lost mass explicit. Truncated subtraction is intentional:
loss greater than the guaranteed mass yields no positive completeness guarantee. -/
structure LowerTransfer {E : Type u} {O : Type v} [MeasurableSpace O]
    {F : Type w} {P : Type x} [MeasurableSpace P]
    (actual : LowerRequest E O) (model : LowerRequest F P) where
  translate : E → F
  admitted : ∀ e, actual.admissible e → model.admissible (translate e)
  loss : E → ℝ≥0∞
  compare : ∀ e, actual.admissible e →
    model.experiment.run (translate e) model.event - loss e ≤
      actual.experiment.run e actual.event
  budget : ∀ e, actual.admissible e → actual.bound e ≤ model.bound (translate e) - loss e

namespace LowerTransfer

variable {E : Type u} {O : Type v} [MeasurableSpace O]
  {F : Type w} {P : Type x} [MeasurableSpace P]
  {G : Type y} {Q : Type z} [MeasurableSpace Q]
  {actual : LowerRequest E O} {middle : LowerRequest F P} {model : LowerRequest G Q}

/-- Close exactly the requested unconditional lower bound. -/
theorem establish (transfer : LowerTransfer actual middle) (proof : middle.Holds) :
    actual.Holds := by
  intro e he
  exact (transfer.budget e he).trans
    ((tsub_le_tsub_right (proof _ (transfer.admitted e he)) _).trans (transfer.compare e he))

/-- Compose lower-bound losses without cancelling a possibly infinite quantity. -/
def comp (first : LowerTransfer actual middle) (second : LowerTransfer middle model) :
    LowerTransfer actual model where
  translate e := second.translate (first.translate e)
  admitted e he := second.admitted _ (first.admitted e he)
  loss e := second.loss (first.translate e) + first.loss e
  compare e he := by
    rw [← tsub_tsub]
    exact (tsub_le_tsub_right (second.compare _ (first.admitted e he)) _).trans
      (first.compare e he)
  budget e he := by
    rw [← tsub_tsub]
    exact (first.budget e he).trans
      (tsub_le_tsub_right (second.budget _ (first.admitted e he)) _)

/-- Identity preserves the initial and terminal probability mass. -/
def identity (request : LowerRequest E O) : LowerTransfer request request where
  translate := id
  admitted _ h := h
  loss _ := 0
  compare _ _ := by simp
  budget _ _ := by simp

end LowerTransfer
end ProtocolProof
