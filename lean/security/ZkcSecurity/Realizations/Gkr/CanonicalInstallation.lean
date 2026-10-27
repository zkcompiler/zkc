module

public import ZkcSecurity.Realizations.Gkr.CanonicalReading
public import ZkcSecurity.Realizations.Gkr.Generated.ABI
public import ZkcSecurity.FiatShamir.LosslessPresentationClaims
public import ZkcSecurity.Realizations.Gkr.OriginalCertificates

@[expose] public section

/-! Installation of the current nominal validator. The actual complete compiled
certificate retains all typed replies, stops, physical returns and histories. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalInstallation
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir Generated.Subject
abbrev Scalar := ZMod blsModulus
abbrev model := subject.domainModel
abbrev Statement := validatorArtifacts.Statement model

def returns (source : CanonicalReading.Result Scalar Scalar)
    (actual : Domain.Result model.toCarriers) : Prop :=
  ∃ value : Bool, source.1 = .cons (some value) .nil ∧
    actual.values = [.data (.boolean value), .transcript subject.selection.context.suite source.2.history] ∧
    actual.environment[43]? = some (.data (.boolean value)) ∧
    actual.environment[42]? = some (.transcript subject.selection.context.suite source.2.history) ∧
    source.2.frames = []

def live (statement : Statement) (history : Domain.History model.toCarriers)
    (_ : PIR.Process (Domain.effects model.toCarriers) (CanonicalReading.Result Scalar Scalar))
    (frame : Domain.Environment model.toCarriers) : Prop :=
  ArtifactBinding.Captures (Domain.inputFrame subject.selection.context
    ((Domain.encodeValues statement).getD []) history) frame

/-- The current generated ABI and the full nominal validator certificate use
exactly the same seven public inputs and initial transcript. -/
def certificate (statement : Statement) (history : Domain.History model.toCarriers) :
  Original.Simulation returns (live statement history)
    (CanonicalReading.source (Canonical.invocation model statement 0) history)
    (Domain.participant model validatorCompiled.imported.program validatorCompiled.selection.context
      validatorArtifacts.participant (Domain.inputFrame validatorCompiled.selection.context
        ((Domain.encodeValues statement).getD []) history)) := by
  apply Classical.choice
  obtain ⟨initial, outputs, add, mul, layers, selector, width, rfl⟩ :=
    Generated.ABI.statement_surjective statement
  refine ⟨?_⟩
  have root := OriginalCertificates.validator (F := Scalar) (G := Scalar)
    0 initial outputs add mul layers selector width history
  apply root.mapRelations
  · intro source actual related
    obtain ⟨⟨captured, point, claim, finalHistory, value, sourceEq, size, _, frameEq⟩,
      returned, valueEq, valuesEq⟩ := related
    have same : value = returned := by
      have same := congrArg (fun values => values.get .here) valueEq
      rw [sourceEq] at same
      exact Option.some.inj same
    subst returned
    refine ⟨value, valueEq, valuesEq, ?_, ?_, ?_⟩
    · simp (disch := omega) only [frameEq, List.getElem?_append_right, size,
        List.getElem?_cons_zero, List.getElem?_cons_succ]
    · simp (disch := omega) only [frameEq, List.getElem?_append_right, size,
        List.getElem?_cons_zero, List.getElem?_cons_succ]
      rw [sourceEq]
      rfl
    · rw [sourceEq]
  · intro process frame retained
    exact retained.2.1

def installation : Original.Claims.Installation validatorSubject where
  result := CanonicalReading.Result Scalar Scalar
  signature := OccurrenceReading.signature Scalar
  absorb := OccurrenceReading.interface
  inputs statement := (Domain.encodeValues statement).getD []
  encoded statement := Domain.encodeValues_getD statement (by rfl)
  source statement := CanonicalReading.source (Canonical.invocation model statement 0)
  presented statement := CanonicalReading.presented (Canonical.invocation model statement 0)
  Post := OccurrenceReading.Post []
  returns := returns
  live := live
  acceptance := CanonicalReading.acceptance
  bridge statement history := ⟨CanonicalReading.reading _ _, certificate statement history⟩
  agrees := by
    intro source actual related
    obtain ⟨value, sourceEq, valuesEq, _⟩ := related
    change source.1.get .here = Domain.acceptanceAt 0 actual.values
    rw [sourceEq, valuesEq]
    rfl
end ZkcSecurity.Realizations.Gkr.CanonicalInstallation
