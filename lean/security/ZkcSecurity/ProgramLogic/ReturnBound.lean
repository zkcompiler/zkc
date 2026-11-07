module

public import Zkc.Semantics.ReturnedPostcondition
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.CanReturn
public import VCVio.EvalDist.ProbabilityBounds

@[expose] public section

/-! Quantitative return postconditions on the original stateful execution.
Stops contribute no mass to a bad return. Each step can choose its next
postcondition using the value and store at the reached boundary. -/

namespace ZkcSecurity
open OracleComp
variable {A B S E : Type}

/-- A violation is observable only on a returned record. -/
def violates (post : A → S → Prop) (record : PIR.Execution S E A) : Prop :=
  match record.outcome with
  | .returned a => ¬ post a record.state
  | .stopped _ => False

def ReturnBound (run : ProbComp (PIR.Execution S E A)) (post : A → S → Prop) (error : ENNReal) : Prop :=
  Pr{let record ← run}[violates post record] ≤ error

namespace ReturnBound
variable {run : ProbComp (PIR.Execution S E A)} {post : A → S → Prop} {error : ENNReal}

theorem ofLaw (law : Std.Do.Internal.Ensures (fun r ↦ ∀ a, r.outcome = .returned a → post a r.state) run) :
    ReturnBound run post 0 := by
  apply le_of_eq
  apply prEvent_eq_zero_of_forall_mem_support
  intro record supported
  have holds := Zkc.MonadicPostcondition.iff_forall_canReturn.mp law record
    ((OracleComp.canReturn_iff_mem_support _ _).mpr supported)
  cases eq : record.outcome with
  | stopped => simp [violates, eq]
  | returned a => simpa only [violates, eq, not_not] using holds a eq

/-- A pathwise law and a charged postcondition refer to the very same
record, even when the provider has auxiliary randomness. -/
theorem withLaw {fact : A → S → Prop} (paid : ReturnBound run post error)
    (law : Std.Do.Internal.Ensures (fun r ↦ ∀ a, r.outcome = .returned a → fact a r.state) run) :
    ReturnBound run (fun a s ↦ post a s ∧ fact a s) error := by
  refine (prEvent_mono_of_support run _ _ ?_).trans paid
  intro record supported
  have holds := Zkc.MonadicPostcondition.iff_forall_canReturn.mp law record
    ((OracleComp.canReturn_iff_mem_support _ _).mpr supported)
  cases eq : record.outcome with
  | stopped => simp [violates, eq]
  | returned a =>
    simp only [violates, eq]
    exact fun bad ok ↦ bad ⟨ok, holds a eq⟩

theorem weaken {weaker : A → S → Prop} (paid : ReturnBound run post error)
    (implies : ∀ a s, post a s → weaker a s) : ReturnBound run weaker error :=
  (prEvent_mono run _ _ fun record ↦ by
    cases eq : record.outcome with
    | stopped => simp [violates, eq]
    | returned a =>
      simp only [violates, eq]
      exact fun bad ok ↦ bad (implies a record.state ok)).trans paid

private theorem follow (head : PIR.Execution S E A) (next : A → S → ProbComp (PIR.Execution S E B))
    (goal : B → S → Prop) :
    Pr{let r ← head.followM next}[violates goal r] =
      match head.outcome with
      | .stopped _ => 0
      | .returned a => Pr{let r ← next a head.state}[violates goal r] := by
  cases head with
  | mk outcome state trace =>
    cases outcome <;> simp [PIR.Execution.followM, violates]
    rfl

/-- Charge each reached step once. A later step sees the post-state and
can rely on the earlier good return. -/
theorem bind {next : A → S → ProbComp (PIR.Execution S E B)} {goal : B → S → Prop} {later : ENNReal}
    (head : ReturnBound run post error)
    (tail : ∀ a state, post a state → ReturnBound (next a state) goal later) :
    ReturnBound (run >>= fun r ↦ r.followM next) goal (error + later) := by
  refine (prEvent_bind_le_prEvent_add_of_support run _ (violates post) _ ?_).trans (add_le_add_left head _)
  intro record _ good
  rw [follow]
  cases eq : record.outcome with
  | stopped => exact bot_le
  | returned a => exact tail a record.state (by simpa only [violates, eq, not_not] using good)

variable {I : PIR.Signature} {handler : PIR.MonadHandler ProbComp I S E} {before : S}
  {first : PIR.Process I A} {next : A → PIR.Process I B} {goal : B → S → Prop}

theorem ofOnReturn (law : PIR.Process.OnReturn handler before first post) :
    ReturnBound (first.runM handler before) post 0 := ofLaw law

theorem processBind {later : ENNReal} (head : ReturnBound (first.runM handler before) post error)
    (tail : ∀ a state, post a state → ReturnBound ((next a).runM handler state) goal later) :
    ReturnBound ((first.bind next).runM handler before) goal (error + later) := by
  rw [PIR.runM_bind]
  exact head.bind tail

theorem afterExact (head : PIR.Process.OnReturn handler before first post)
    (tail : ∀ a state, post a state → ReturnBound ((next a).runM handler state) goal error) :
    ReturnBound ((first.bind next).runM handler before) goal error := by
  simpa only [zero_add] using processBind (ofOnReturn head) tail

theorem beforeExact (head : ReturnBound (first.runM handler before) post error)
    (tail : ∀ a state, post a state → PIR.Process.OnReturn handler state (next a) goal) :
    ReturnBound ((first.bind next).runM handler before) goal error := by
  simpa only [add_zero] using head.processBind (fun a state valid ↦ ofOnReturn (tail a state valid))

end ReturnBound
end ZkcSecurity
