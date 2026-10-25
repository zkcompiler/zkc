module

public import Zkc.Executable.Soundness

@[expose] public section

/-! Host validation at every budget.

Below the total charge of a reading with loops or helper calls, the metered
meaning is not a fixed function of the budget, but it is always the ideal
meaning with some continuations replaced by stops. `Prunes rejects first
second` states this shape: `first` is `second` with some continuations replaced
by results that `rejects` holds of, and the two computations otherwise make the
same calls in the same order (`metered_prunes`). Host validation therefore
prunes the ideal acceptance of the decoded proof by rejections, at every budget
and with every framing header (`validate_prunes`), so it accepts no more often
than the ideal acceptance does in every probability model of the challenge
function.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

/-- `Prunes rejects first second`: `first` is `second` with some continuations
replaced by a result that `rejects` holds of. -/
inductive Prunes {m : Type → Type} [Monad m] {α : Type} (rejects : α → Prop) : m α → m α → Prop
  | refl (computation : m α) : Prunes rejects computation computation
  | stop (result : α) (rejected : rejects result) (computation : m α) :
      Prunes rejects (pure result) computation
  | bind {β : Type} (first : m β) (pruned original : β → m α)
      (step : ∀ value, Prunes rejects (pruned value) (original value)) :
      Prunes rejects (first >>= pruned) (first >>= original)

theorem Prunes.map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {rejects : α → Prop}
    {rejects' : β → Prop} (f : α → β) (preserves : ∀ result, rejects result → rejects' (f result))
    {first second : m α} (pruned : Prunes rejects first second) :
    Prunes rejects' (f <$> first) (f <$> second) := by
  induction pruned with
  | refl computation => exact .refl _
  | stop result rejected computation =>
      rw [map_pure]
      exact .stop _ (preserves result rejected) _
  | bind first pruned original step ih =>
      rw [map_bind, map_bind]
      exact .bind _ _ _ ih

/-- A stopped result. -/
def Stopped {F G R : Type} (result : PIR.Outcome R × Proof F G) : Prop :=
  ∃ stop, result.1 = .stopped stop

theorem stopped_pure {F G R : Type} {m : Type → Type} [Monad m] (stop : PIR.Stop) (proof : Proof F G)
    (computation : m (PIR.Outcome R × Proof F G)) :
    Prunes Stopped (pure (.stopped stop, proof)) computation :=
  .stop _ ⟨stop, rfl⟩ _

section PruningIdeal
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]
variable (context : Context) (challenge : History F G → m F)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem iterateM_prunes {R : Type}
    (body : List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G))
    (bodyPrunes : ∀ start proof (next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, Prunes Stopped (next env unread) (next' env unread)) →
      Prunes Stopped (body start proof next) (body start proof next'))
    (env : List (Value F G)) (yielded : List Nat) :
    ∀ (items : List Nat) (carried : List (Value F G)) (proof : Proof F G)
      (next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, Prunes Stopped (next env unread) (next' env unread)) →
      Prunes Stopped (iterateM body env yielded items carried proof next)
        (iterateM body env yielded items carried proof next')
  | [], carried, proof, next, next', continues => continues carried proof
  | index :: rest, carried, proof, next, next', continues => by
      simp only [iterateM]
      apply bodyPrunes
      intro final unread
      split
      · exact iterateM_prunes body bodyPrunes env yielded rest _ _ next next' continues
      · exact .refl _

mutual
/-- The ideal meaning prunes as its continuation does. -/
theorem idealK_prunes {R : Type} :
    ∀ (instructions : List Instruction) (env : List (Value F G)) (proof : Proof F G)
      (next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, Prunes Stopped (next env unread) (next' env unread)) →
      Prunes Stopped (idealK context challenge table instructions env proof next)
        (idealK context challenge table instructions env proof next')
  | [], env, proof, next, next', continues => by simpa only [idealK] using continues env proof
  | instruction :: rest, env, proof, next, next', continues => by
      simp only [idealK]
      exact idealStep_prunes instruction env proof _ _
        (fun env' unread => idealK_prunes rest env' unread next next' continues)

theorem idealStep_prunes {R : Type} :
    ∀ (instruction : Instruction) (env : List (Value F G)) (proof : Proof F G)
      (next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, Prunes Stopped (next env unread) (next' env unread)) →
      Prunes Stopped (idealStep context challenge table instruction env proof next)
        (idealStep context challenge table instruction env proof next')
  | ⟨operation, operands, results, body⟩, env, proof, next, next', continues => by
      cases operation with
      | loop site maximum yielded =>
          cases operands with
          | nil => exact .refl _
          | cons count initial =>
              simp only [idealStep]
              split
              · split
                · exact iterateM_prunes _
                    (fun start unread continuation continuation' bodyContinues =>
                      idealK_prunes body start unread continuation continuation' bodyContinues)
                    env yielded _ _ proof _ _ (fun final unread => continues _ _)
                · exact .refl _
              · exact .refl _
      | _ =>
          rcases operands with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp only [idealStep]
          all_goals repeat' split
          all_goals first
            | exact .refl _
            | exact continues _ _
            | exact .bind _ _ _ (fun answer => continues _ _)
end

end PruningIdeal


section PruningMetered
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]
variable (context : Context) (challenge : History F G → m F)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

/-- The metered meaning of a reading prunes the ideal meaning of its
constructed instructions, at every budget. -/
theorem meteredK_prunes {R : Type} :
    ∀ (code : List Code) (env : List (Value F G)) (proof : Proof F G) (used : Nat)
      (next : List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G))
      (next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread used, Prunes Stopped (next env unread used) (next' env unread)) →
      Prunes Stopped (meteredK context challenge table cost budget code env proof used next)
        (idealK context challenge table (Code.instructions code) env proof next')
  | [], env, proof, used, next, next', continues => by
      simpa only [meteredK, Code.instructions, idealK] using continues env proof used
  | .charge count :: rest, env, proof, used, next, next', continues => by
      simp only [meteredK, meteredStep, Code.instructions]
      split
      · exact meteredK_prunes rest env proof (used + count) next next' continues
      · exact stopped_pure _ _ _
  | .step instruction charged :: rest, env, proof, used, next, next', continues => by
      simp only [meteredK, meteredStep, Code.instructions, idealK]
      split
      · exact idealStep_prunes context challenge table instruction env proof _ _
          (fun env' unread => meteredK_prunes rest env' unread _ next next' continues)
      · exact stopped_pure _ _ _
  | .helper instruction :: rest, env, proof, used, next, next', continues => by
      simp only [meteredK, meteredStep, Code.instructions, idealK]
      split
      · split
        · split
          · exact idealStep_prunes context challenge table instruction env proof _ _
              (fun env' unread => meteredK_prunes rest env' unread _ next next' continues)
          · exact stopped_pure _ _ _
        · exact stopped_pure _ _ _
      · exact stopped_pure _ _ _
  | .loop site maximum yielded operands results body :: rest, env, proof, used, next, next', continues => by
      simp only [meteredK, meteredStep, Code.instructions, idealK]
      cases operands with
      | nil => exact stopped_pure _ _ _
      | cons count initial =>
          simp only [idealStep]
          cases countEq : indexAt env count with
          | none => exact stopped_pure _ _ _
          | some bound =>
              cases initialEq : Construction.read env initial with
              | none => exact stopped_pure _ _ _
              | some carried =>
                  simp only
                  by_cases bounded : bound ≤ maximum
                  · simp only [bounded, ite_true]
                    by_cases fits : used + 1 ≤ budget
                    · simp only [fits, ite_true]
                      -- Iterations prune as their bodies and yields do.
                      have iterations : ∀ (items : List Nat) (values : List (Value F G)) (unread : Proof F G)
                          (charged : Nat),
                          Prunes Stopped
                            (meteredIterate budget (fun start unread' used' continuation =>
                                meteredK context challenge table cost budget body start unread' used' continuation)
                              env yielded items values unread charged fun final unread' used' =>
                                meteredK context challenge table cost budget rest (env ++ final) unread' used' next)
                            (iterateM (fun start unread' continuation =>
                                idealK context challenge table (Code.instructions body) start unread' continuation)
                              env yielded items values unread fun final unread' =>
                                idealK context challenge table (Code.instructions rest) (env ++ final) unread' next') := by
                        intro items
                        induction items with
                        | nil =>
                            intro values unread charged
                            exact meteredK_prunes rest (env ++ values) unread charged next next' continues
                        | cons index indices ih =>
                            intro values unread charged
                            simp only [meteredIterate, iterateM]
                            apply meteredK_prunes body
                            intro final unread' used'
                            by_cases fits' : used' + 1 ≤ budget
                            · simp only [fits', ↓reduceIte]
                              cases Construction.read final yielded with
                              | none => exact .refl _
                              | some carried' => exact ih _ _ _
                            · simp only [fits', ↓reduceIte]
                              exact stopped_pure _ _ _
                      exact iterations _ _ _ _
                    · simp only [fits, ↓reduceIte]
                      exact stopped_pure _ _ _
                  · simp only [bounded, ite_false]
                    exact .refl _

/-- The metered meaning of a reading prunes the ideal meaning of its
constructed instructions and returned references. -/
theorem metered_prunes (lowered : Lowered) (env : List (Value F G)) (proof : Proof F G) :
    Prunes Stopped (metered context challenge table cost budget lowered env proof)
      (ideal context challenge table lowered.returned (Code.instructions lowered.code) env proof) := by
  unfold metered ideal
  apply meteredK_prunes
  intro final unread used
  by_cases fits : used + 1 ≤ budget
  · simp only [fits, ite_true]
    exact .refl _
  · simp only [fits, ite_false]
    exact stopped_pure _ _ _

end PruningMetered


section PruningValidation
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)

/-- Host validation prunes the ideal acceptance of the decoded proof, at every
budget and with every framing header: where it does not reject outright, it is
that acceptance with some continuations replaced by a rejection. -/
theorem validate_prunes (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator table name) {L : Lowered}
    (reading : validator.read vocabulary helpers = .ok L) (binding : List UInt8) (acceptance : Nat)
    (data : List (Value F G)) (history : History F G) (bytes : List UInt8)
    (admitted : validator.admits data = true) :
    Prunes (fun accepted => accepted = false)
      (validate vocabulary validator context challenge decode budget binding acceptance data history bytes)
      ((fun result => Accepts acceptance (idealObservation result)) <$>
        ideal context challenge table L.returned (Code.instructions L.code) (data ++ [.transcript history])
          (decodeProof decode (Plan.types data L.plan) (bytes.drop 40))) := by
  by_cases header : bytes.take 40 = magic ++ binding
  · rw [validate_metered vocabulary validator context challenge table decode budget helpers prepared reading
      binding acceptance data history bytes admitted header]
    exact (metered_prunes context challenge table (helperCost vocabulary validator) budget L _ _).map _
      (fun result ⟨stop, stopped⟩ => by simp [Accepts, idealObservation, observation, stopped, Decision])
  · unfold validate
    simp only [header, ↓reduceIte]
    refine .stop _ ?_ _
    rfl

end PruningValidation

end Zkc.Executable
