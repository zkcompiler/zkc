module

public import ZkcSecurity.Families.Sumcheck.Composition

@[expose] public section

/-! Finite short-circuit conjunction over existing open components. Composition
threads the reached history and handler state; it infers no independence or
uniform probability price from the number of calls. -/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.FiniteCalls
open Zkc.Transcript Zkc.Obligations ZkcSecurity.Obligations
variable {I : PIR.Signature} {Input : Type}

/-- A false answer returns false immediately. Stops and unread suffixes keep
the selected component's operational meaning. -/
def all (call : Input → PIR.Process I Bool) : List Input → PIR.Process I Bool
  | [] => .done true
  | input :: rest => (call input).bind fun accepted =>
    if accepted then all call rest else .done false

theorem binding (actual view : Input → PIR.Process I Bool)
    (inputs : List Input) (equations : ∀ input ∈ inputs, actual input = view input) :
    all actual inputs = all view inputs := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    simp only [all, equations input List.mem_cons_self,
      ih (fun entry member => equations entry (List.mem_cons_of_mem input member))]

variable {E P : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]
  {absorb : Interface I E P Raw} {charge : List E → E → ENNReal}

/-- A false conjunct suffices, at its actual reached history, even when earlier
calls received arbitrary adversarial messages and used the same oracle. -/
noncomputable def rejected (call : Input → PIR.Process I Bool) (falseInput : Input → Prop)
    (inputs : List Input)
    (localRejection : ∀ input ∈ inputs, falseInput input → ∀ history,
      Derivation absorb (boundedEscape charge) (fun _ accepted => accepted = false) history (call input))
    (wrong : ∃ input ∈ inputs, falseInput input) (history : List E) :
    Derivation absorb (boundedEscape charge) (fun _ accepted => accepted = false)
      history (all call inputs) := by
  induction inputs generalizing history with
  | nil => simp at wrong
  | cons input rest ih =>
    classical
    rw [all]
    by_cases bad : falseInput input
    · exact (localRejection input List.mem_cons_self bad history).bind _ (fun _ accepted no => by
        subst accepted
        exact .done rfl)
    · have tail : ∃ input ∈ rest, falseInput input := by
        obtain ⟨selected, member, falseSelected⟩ := wrong
        rcases List.mem_cons.mp member with same | member
        · exact False.elim (bad (same ▸ falseSelected))
        · exact ⟨selected, member, falseSelected⟩
      exact (unrestricted (call input) history).bind _ (fun reached accepted _ => by
        cases accepted with
        | false => exact .done rfl
        | true => exact ih (fun entry member => localRejection entry (List.mem_cons_of_mem input member)) tail reached)

/-- Successful execution retains the complete handler poststate and ordered
events. The local premise is total success, not a vacuous partial-return law. -/
theorem honest_run {H O : Type} (call : Input → PIR.Process I Bool)
    (handler : PIR.Handler I H O) (inputs : List Input)
    (localSuccess : ∀ input ∈ inputs, ∀ h, ∃ final events,
      (call input).run handler h = ⟨.returned true, final, events⟩) (h : H) :
    ∃ final events, (all call inputs).run handler h = ⟨.returned true, final, events⟩ := by
  induction inputs generalizing h with
  | nil => exact ⟨h, [], rfl⟩
  | cons input rest ih =>
    obtain ⟨next, events, head⟩ := localSuccess input List.mem_cons_self h
    obtain ⟨final, tailEvents, tail⟩ := ih
      (fun entry member => localSuccess entry (List.mem_cons_of_mem input member)) next
    refine ⟨final, events ++ tailEvents, ?_⟩
    simp only [all, PIR.run_bind, head, PIR.Execution.follow, ite_true, tail]

/-- Resource-sensitive delivery across calls. The invariant describes the
remaining calls and actual handler state, including a finite proof buffer. -/
theorem honest_run_invariant {H O : Type} (call : Input → PIR.Process I Bool)
    (handler : PIR.Handler I H O) (invariant : List Input → H → Prop)
    (step : ∀ input rest h, invariant (input :: rest) h → ∃ next events,
      (call input).run handler h = ⟨.returned true, next, events⟩ ∧ invariant rest next)
    (inputs : List Input) (h : H) (initial : invariant inputs h) :
    ∃ final events, (all call inputs).run handler h = ⟨.returned true, final, events⟩ ∧
      invariant [] final := by
  induction inputs generalizing h with
  | nil => exact ⟨h, [], rfl, initial⟩
  | cons input rest ih =>
    obtain ⟨next, events, head, nextInvariant⟩ := step input rest h initial
    obtain ⟨final, tailEvents, tail, finalInvariant⟩ := ih next nextInvariant
    refine ⟨final, events ++ tailEvents, ?_, finalInvariant⟩
    simp only [all, PIR.run_bind, head, PIR.Execution.follow, ite_true, tail]

end ZkcSecurity.Families.Sumcheck.FiniteCalls
