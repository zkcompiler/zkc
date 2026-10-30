module

public import Zkc.Construction.OriginalFold
public import ZkcSecurity.Bindings.Transcript.DomainReduction

public section

/-! Lift installed operation interpretations to a source reading and observation
coherence together. The source is the actual occurrence Process and the target
of the reading is the existing Original.fold. No whole-source equality or
reading is an installation premise. Full source results and construction states
are returned identically by the two interpretations.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.SourceReading
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open DomainReduction
variable {carriers : Carriers} {I : PIR.Signature} {A B : Type}

/-- The explicit construction history equals the actual observation prefix.
The result includes the complete source value and occurrence frames, rather
than an acceptance-only projection. -/
@[expose] def Post (history : Domain.History carriers) (result : A × Original.State carriers) : Prop :=
  result.2.history = history

/-- A property adapter installs laws for individual operations at every reached
state and every typed reply. The law uses the exact routing and Original
operation; it cannot substitute a protocol reference computation. -/
structure Interpretation (routing : Original.Routing)
    (absorb : Typed.Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw) where
  operations : PIR.StateOperationInterpretation (Occurrence.signature carriers) I (Original.State carriers)
  law : ∀ operation state, Bridge absorb Post state.history
    (Original.operations routing operation state) (operations operation state)

namespace Interpretation
variable {routing : Original.Routing}
variable {absorb : Typed.Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}

/-- This presentation reuses Process.interpretState; it introduces neither a
source evaluator nor a new probabilistic semantics. -/
@[expose] def presentation (adapter : Interpretation routing absorb)
    (source : PIR.Process (Occurrence.signature carriers) A) (state : Original.State carriers) :
    PIR.Process I (A × Original.State carriers) :=
  source.interpretState adapter.operations state

/-- Operation-level laws automatically compose through the actual source,
including calls, arbitrary reply-dependent continuations and stopped prefixes. -/
theorem reading (adapter : Interpretation routing absorb)
    (source : PIR.Process (Occurrence.signature carriers) A) (state : Original.State carriers) :
    Bridge absorb Post state.history (Original.fold routing source state)
      (adapter.presentation source state) := by
  induction source generalizing state with
  | done value => exact .done _ _ rfl
  | halt reason => exact .halt _ _
  | call operation next ih =>
    apply (adapter.law operation state).bind
    intro reached result agrees
    simp only [Post] at agrees
    subst reached
    exact ih result.1 result.2

/-- Component seams use the entire returned value, reached history and frames.
No occurrence rebasing or history equation is an instance obligation. -/
theorem bind (adapter : Interpretation routing absorb)
    (source : PIR.Process (Occurrence.signature carriers) A)
    (next : A → PIR.Process (Occurrence.signature carriers) B) (state : Original.State carriers) :
    adapter.presentation (source.bind next) state =
      (adapter.presentation source state).bind fun (value, reached) =>
        adapter.presentation (next value) reached :=
  PIR.Process.interpretState_bind _ _ _ _

/-- Arbitrary symbolic loop counts use the same installed operation laws. The
source loop is retained; this theorem does not unroll its bound in a proof. -/
theorem repeatN (adapter : Interpretation routing absorb)
    (count : Nat) (body : A → PIR.Process (Occurrence.signature carriers) A)
    (value : A) (state : Original.State carriers) :
    Bridge absorb Post state.history (Original.fold routing (PIR.repeatN count body value) state)
      (adapter.presentation (PIR.repeatN count body value) state) :=
  adapter.reading _ _

end Interpretation
end ZkcSecurity.FiatShamir.SourceReading

namespace ZkcSecurity.FiatShamir.DomainReduction.Bridge
open Zkc.Source Zkc.Construction
variable {carriers : Structured.Carriers} {I : PIR.Signature} {A : Type}

/-- Installed component bridges compose through a symbolic loop with one
history-indexed invariant. Reading and coherence share each reached-state law.
This is a relational rule; it does not identify successful completeness with
the rejection-oriented property of a component. -/
theorem repeatN
    {absorb : Zkc.Transcript.Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
    (invariant : Domain.History carriers → Nat → A → Prop)
    (actual : A → PIR.Process (Domain.effects carriers) A)
    (presented : A → PIR.Process I A)
    (step : ∀ history remaining value, invariant history (remaining + 1) value →
      Bridge absorb (fun reached => invariant reached remaining) history (actual value) (presented value))
    (count : Nat) (history : Domain.History carriers) (value : A)
    (holds : invariant history count value) :
    Bridge absorb (fun reached => invariant reached 0) history
      (PIR.repeatN count actual value) (PIR.repeatN count presented value) :=
  ⟨ReadingTo.repeatN invariant actual presented
      (fun history remaining value holds => (step history remaining value holds).reading)
      count history value holds,
    CoherentTo.repeatN invariant actual
      (fun history remaining value holds => (step history remaining value holds).coherent)
      count history value holds⟩

end ZkcSecurity.FiatShamir.DomainReduction.Bridge
