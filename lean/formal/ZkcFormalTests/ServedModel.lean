import ZkcFormal.Written.StandardInterpretation

/-!
What a served model is.

A receipt of written soundness (`Soundness.Witnessed`) says that its model is served: some
conforming service with a state answers every effect that has a sampler as the sampler draws.
Conformance alone does not say that. The service that never answers conforms to every samplers
and every permission, so a receipt that asked for a conforming service asked for nothing. It is
no service of a served model wherever an effect has a sampler, here at the standard
interpretation's draw of a position below four. The service of the laws is one.
-/

open Zkc.Core ZkcFormal ZkcFormal.ProbabilisticProcess ZkcFormal.Written OracleComp ProbComp

namespace ZkcFormalTests.ServedModel

variable {S : Sig}

/-- The service that never answers. -/
def silent : Service S Unit := fun _ s => pure (none, s)

/-- The silent service conforms, whatever the samplers and the permission. -/
theorem silent_conforms (samplers : Samplers S) (allowed : ∀ op, S.Reply op → Prop) :
    (silent : Service S Unit).Conforms samplers allowed :=
  ⟨fun _ _ _ _ _ => by simp [silent], fun _ _ _ _ h => by simp [silent] at h⟩

/-- The silent service does not answer as a sampler draws. -/
theorem silent_not_draws (samplers : Samplers S) (op : S.Op) (draw : ProbComp (S.Reply op))
    (has : samplers op = some draw) : ¬ (silent : Service S Unit).Draws samplers := by
  intro draws
  have same := draws op draw has () (fun _ => True)
  have never : Pr{let out ← (silent : Service S Unit) op ()}[∃ v, out.1 = some v ∧ True] = 0 := by
    simp [silent]
  have sometimes : 0 < Pr{let v ← draw}[True] := by
    rw [prEvent_pos_iff]
    obtain ⟨v, drawn⟩ := OracleComp.support_nonempty draw
    exact ⟨v, drawn, trivial⟩
  rw [never] at same
  exact sometimes.ne same

open StandardInterpretation in
/-- At the standard interpretation the silent service is no service of a served model. -/
example : ¬ (silent : Service (RSig model) Unit).Draws samplers :=
  silent_not_draws _ (.own (.coin (.uniform (.fin 4))) [0] ⟨[], ⟨0⟩⟩ [] .nil (.fin 4)) _ rfl

open StandardInterpretation in
/-- The standard interpretation is served, and what its samplers draw is permitted. -/
example (op : ROp model) (draw : ProbComp ((RSig model).Reply op)) (has : samplers op = some draw)
    (v : (RSig model).Reply op) (drawn : v ∈ support draw) : Permitted model op v :=
  served.allowed_of_drawn op draw has v drawn

end ZkcFormalTests.ServedModel
