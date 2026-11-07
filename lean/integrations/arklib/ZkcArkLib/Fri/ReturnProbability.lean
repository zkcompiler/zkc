module

public import ZkcArkLib.Fri.PhasesCausal
public import Zkc.Semantics.ReturnedPostcondition
public import VCVio.OracleComp.CanReturn

@[expose] public section

/-! Transfer conditional source return laws to bounds in the same
probabilistic execution, keeping the original mass of stopped runs. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.Phases
open OracleComp
variable {I : PIR.Signature} {S E A B : Type} {handler : PIR.MonadHandler ProbComp I S E} {before : S}
  {first : PIR.Process I A} {next : A → PIR.Process I B} {middle : A → S → Prop} {post : B → Prop}

/-- A prefix with no obligations can also stop before its continuation. -/
theorem boundAfterPrefix {upper : ENNReal}
    (bound : ∀ a state, Pr{let result ← (next a).runM handler state}[returned post result] ≤ upper) :
    Pr{let result ← (first.bind next).runM handler before}[returned post result] ≤ upper := by
  rw [PIR.runM_bind]
  apply prEvent_bind_le_of_forall_le
  intro head
  exact prEvent_followM_le head _ post upper bound

/-- An exit action may stop after the child returned. It contributes no
additional mass to an event of that child's value. -/
theorem boundWithExit {event : A → Prop} (exit : A → PIR.Process I Unit) :
    Pr{let result ← (first.bind fun a ↦ (exit a).bind fun _ ↦ .done a).runM handler before}[returned event result] ≤
      Pr{let result ← first.runM handler before}[returned event result] := by
  rw [PIR.runM_bind]
  apply prEvent_bind_le_prEvent_of_forall_eq_zero
  intro head outside
  rw [prEvent_followM]
  cases eq : head.outcome with
  | stopped => rfl
  | returned a =>
    have absent : ¬ event a := by simpa only [returned, eq] using outside
    change Pr{let result ← ((exit a).bind (fun _ ↦ .done a)).runM handler head.state}[returned event result] = 0
    rw [prEvent_runM_repack (exit a) handler head.state (fun _ ↦ a) event]
    apply prEvent_eq_zero_of_forall_not
    intro record
    cases out : record.outcome <;> simp [returned, out, absent]

theorem returnOnSupport (law : PIR.Process.OnReturn handler before first middle)
    (result : PIR.Execution S E A) (supported : result ∈ support (first.runM handler before)) :
    ∀ a, result.outcome = .returned a → middle a result.state :=
  Zkc.MonadicPostcondition.iff_forall_canReturn.mp law result ((OracleComp.canReturn_iff_mem_support _ _).mpr supported)

theorem boundAfterReturn {upper : ENNReal} (law : PIR.Process.OnReturn handler before first middle)
    (bound : ∀ a state, middle a state → Pr{let result ← (next a).runM handler state}[returned post result] ≤ upper) :
    Pr{let result ← (first.bind next).runM handler before}[returned post result] ≤ upper := by
  rw [PIR.runM_bind]
  apply prEvent_bind_le_of_forall_le_of_support
  intro head member
  rw [prEvent_followM]
  cases eq : head.outcome with
  | stopped => exact bot_le
  | returned a => exact bound a head.state (returnOnSupport law head member a eq)

/-- A successful continuation can only suppress an event of the earlier
draw. The local proof may use facts about its exact value and post-state. -/
theorem boundByEarlierEvent (earlier : A → Prop) (law : PIR.Process.OnReturn handler before first middle)
    (necessary : ∀ a state, middle a state → PIR.Process.OnReturn handler state (next a) (fun b _ ↦ post b → earlier a)) :
    Pr{let result ← (first.bind next).runM handler before}[returned post result] ≤
      Pr{let head ← first.runM handler before}[returned earlier head] := by
  rw [PIR.runM_bind]
  apply prEvent_bind_le_prEvent_of_support
  intro head member outside
  rw [prEvent_followM]
  cases eq : head.outcome with
  | stopped => rfl
  | returned a =>
    have rejected : ¬ earlier a := by simpa only [returned, eq] using outside
    apply prEvent_eq_zero_of_forall_mem_support
    intro result supported
    have tail := returnOnSupport (necessary a head.state (returnOnSupport law head member a eq)) result supported
    cases out : result.outcome with
    | stopped => simp [returned, out]
    | returned b => exact fun yes ↦ rejected (tail b out (by simpa only [returned, out] using yes))

end ZkcSecurity.ArkLib.Fri.Phases
