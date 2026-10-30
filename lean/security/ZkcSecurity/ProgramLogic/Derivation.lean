module

public import Zkc.Obligations.Derivation
public import Zkc.Claims.Capability
public import ZkcSecurity.ProgramLogic.Transcript.Reduction

public section

/-! Probabilistic interpretation into the existing typed reduction engine.
At each fixed history/key, escape is measured under the engine's fresh raw
sample. Conditioning/locality and shared-key replay belong to the selected
model and its existing endpoint theorem. This module adds no experiment.
-/

set_option autoImplicit false
namespace ZkcSecurity.Obligations
open OracleComp OracleSpec Zkc.Transcript Zkc.Obligations
open ZkcSecurity.FiatShamir.Typed

variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type}
  [∀ event, SampleableType (Raw event)]

@[expose] def boundedEscape (charge : List E → E → ENNReal) : EscapeJudgment E Raw :=
  fun history event bad => Pr{let raw ← $ᵗ (Raw event)}[bad raw] ≤ charge history event

theorem boundedEscape_antitone (charge : List E → E → ENNReal) :
    (boundedEscape (Raw := Raw) charge).Antitone :=
  fun _ _ _ _ included bounded => (prEvent_mono _ _ _ included).trans bounded

theorem chargedStepTo_iff_escapeStep (absorb : Interface I E P Raw)
    (doomed : List E → PIR.Process I A → Prop) (Post : List E → A → Prop)
    (charge : List E → E → ENNReal) (history : List E) (process : PIR.Process I A) :
    ChargedStepTo absorb doomed Post charge history process ↔
      absorb.EscapeStep (boundedEscape charge) doomed Post history process := by
  cases process with
  | done value => exact Iff.rfl
  | halt reason => exact Iff.rfl
  | call operation next =>
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _ <;>
        simp only [ChargedStepTo, Interface.EscapeStep, absorbed, Absorption.ChargedNode, boundedEscape]

/-- Arbitrary stages preserve the trivial return fact, including all typed
receives and every stop. This is partial safety, never successful execution. -/
noncomputable def unrestricted {absorb : Interface I E P Raw} {charge : List E → E → ENNReal}
    (process : PIR.Process I A) (history : List E) :
    Derivation absorb (boundedEscape charge) (fun _ _ => True) history process := by
  induction process generalizing history with
  | done value => exact .done trivial
  | halt reason => exact .halt reason
  | call operation next ih =>
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · exact .receive absorbed fun m value _ => ih value _
      · exact .send absorbed (ih value _)
      · refine .query absorbed (fun _ => False) ?_ (fun _ value _ _ => ih value _)
        change Pr{let _ ← $ᵗ (Raw event)}[False] ≤ charge history event
        simp
      · exact .refuse absorbed

/-- The reading supplies an ordinary `Typed.Reduction` with the same indices. -/
@[expose] def reduction (absorb : Interface I E P Raw) (Post : List E → A → Prop)
    (charge : List E → E → ENNReal) : Reduction absorb Post charge where
  doomed history process := absorb.Charged (boundedEscape charge) Post process history
  step history process member :=
    (chargedStepTo_iff_escapeStep absorb _ Post charge history process).mpr
      ((absorb.charged_iff_escapeStep (boundedEscape charge) Post process history).mp member)

/-- Membership, rather than construction of the maximal reduction alone, is
the substantive derivation-to-contract theorem. -/
theorem derived_doomed {absorb : Interface I E P Raw} {Post : List E → A → Prop}
    {charge : List E → E → ENNReal} {history : List E} {process : PIR.Process I A}
    (derivation : Derivation absorb (boundedEscape charge) Post history process) :
    (reduction absorb Post charge).doomed history process :=
  derivation.charged (boundedEscape_antitone charge)

theorem interpret {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}
    {Post : List E → A → Prop} {charge : List E → E → ENNReal}
    (conditionalBound : ∀ history event bad,
      escape history event bad → Pr{let raw ← $ᵗ (Raw event)}[bad raw] ≤ charge history event)
    {history : List E} {process : PIR.Process I A}
    (derivation : Derivation absorb escape Post history process) :
    (reduction absorb Post charge).doomed history process :=
  derived_doomed (derivation.mapEscape conditionalBound)

/-- Every existing reduction yields a derivation, relative to the same local
probability semantics. This does not assert a terminating search procedure. -/
theorem nonempty_iff_reduction {absorb : Interface I E P Raw} {Post : List E → A → Prop}
    {charge : List E → E → ENNReal} {history : List E} {process : PIR.Process I A} :
    Nonempty (Derivation absorb (boundedEscape charge) Post history process) ↔
      ∃ contract : Reduction absorb Post charge, contract.doomed history process := by
  constructor
  · rintro ⟨derivation⟩
    exact ⟨reduction absorb Post charge, derived_doomed derivation⟩
  · rintro ⟨contract, member⟩
    apply Derivation.of_charged process history
    exact absorb.le_charged (boundedEscape_antitone charge) contract.doomed
      (fun reached residual inside =>
        (chargedStepTo_iff_escapeStep absorb contract.doomed Post charge reached residual).mp
          (contract.step reached residual inside)) history process member

/-- A separate capability export over a fixed history/process meaning.
The postcondition (including residual No/frame links) and exact occurrence
charge are parameters. Canonical subject association is a caller obligation. -/
@[expose] def chargedCapability (absorb : Interface I E P Raw) (Post : List E → A → Prop)
    (charge : List E → E → ENNReal) : Zkc.Claims.Capability (List E × PIR.Process I A) where
  Payload := Reduction absorb Post charge
  Valid contract meaning := contract.doomed meaning.1 meaning.2

def exportCapability {absorb : Interface I E P Raw} {Post : List E → A → Prop}
    {charge : List E → E → ENNReal} {history : List E} {actual : PIR.Process I A}
    (derivation : Derivation absorb (boundedEscape charge) Post history actual) :
    (chargedCapability absorb Post charge).Export (history, actual) :=
  ⟨reduction absorb Post charge, derived_doomed derivation⟩

/-- Terminal adequacy is supplied explicitly, independently of membership. -/
def certificate {absorb : Interface I E P Raw} {Post : List E → A → Prop}
    {charge : List E → E → ENNReal} (accepts : A → Prop)
    (terminal : ∀ history value, Post history value → ¬ accepts value) :
    ChargedCertificate absorb accepts charge :=
  (reduction absorb Post charge).toCertificate absorb terminal

end ZkcSecurity.Obligations
