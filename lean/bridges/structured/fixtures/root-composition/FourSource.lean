module

public import ZkcExamples.Structured.Generated.Bindings.FourSumsInputs
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyRoots
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyPair
public meta import ZkcTools.StructuredSource.ReferenceInstallation
public meta import ZkcTools.StructuredSource.InferReferenceInstallation
public meta import ZkcTools.StructuredSource.NormalizedRoot

@[expose] public section

/-! A fresh admitted client of the checked two-value Sumcheck family. All
associations and both root normal forms are proposed by shared tools. The
source checks run independently; the endpoint modules consume these same roots. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace TestsSecurity.RootComposition.Four.Source
open Zkc.Source Zkc.Source.Structured NormalForm ReferenceLibrary
open ZkcExamples.Structured SumcheckReferenceInstallation
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
abbrev program := Generated.Bindings.FourSumsInputs.program

/-- Both the static bound and whole declaration identity are discovered from
and checked against the admitted typed reduction body. -/
def reduction : (bound : Nat) × (name : String) ×
    Zkc.Source.Structured.Template.Association program.payload
      (SourceFamily.reductionSignature name) (SumcheckVerifierBodies.reduceBody bound) := by
  infer_source_template

def installation : SourceFamily.Installation program where
  maximum := reduction.fst
  maximum_small := by decide +kernel
  reductionName := reduction.snd.fst
  reduction := reduction.snd.snd
  roundBodies := by
    constructor
    · select_reference_bodies
    · bind_structured_bodies
  admissionBodies := by
    constructor
    · select_reference_bodies
    all_goals bind_structured_bodies
  validatorBodies := by intro model; constructor <;> bind_structured_bodies
  producerBodies := by intro model; constructor <;> bind_structured_bodies
  initial := by intro model; bind_structured_bodies

def validator : Zkc.Source.Structured.NormalizedRoot.Checked program 1
    (SourceFamily.validatorSignature installation) := by
  derive_normalized_source_root

def producer : Zkc.Source.Structured.NormalizedRoot.Checked program 0
    (SourceFamily.producerSignature installation) := by
  derive_normalized_source_root

/-- Concrete input rows are ordinary public ABI data, not internal source slots.
All four malformed tables remain in the adversarial validator domain. -/
def malformedArguments : Binders (ringModel Rat Rat)
    (Zkc.Source.Structured.NormalizedRoot.pattern program 1).scope :=
  .cons (some []) (.cons (some []) (.cons (some []) (.cons (some [])
    (.cons (some 0) (.cons (some 0) (.cons (some 0) (.cons (some 0)
      (.cons (some 1) (.cons (some 0) .nil)))))))))

inductive Event where
  | receive
  | query (site : String)
  | deliver
  deriving DecidableEq

def zeroReplies : PIR.Handler (Occurrence.signature (ringModel Rat Rat).toCarriers) Unit Event
  | .enter _, _ => ⟨.returned (), (), []⟩
  | .leave _, _ => ⟨.returned (), (), []⟩
  | .action (.receive (.field _) _ _), _ => ⟨.returned 0, (), [.receive]⟩
  | .action (.receive ..), _ => ⟨.stopped .refused, (), []⟩
  | .action (.query site _ _), _ => ⟨.returned (0 : Rat), (), [.query site]⟩
  | .action (.send ..), _ => ⟨.returned (), (), [.deliver]⟩

def malformedRun :=
  (Occurrence.participant (ringModel Rat Rat) program 1
    (Zkc.Source.Structured.NormalizedRoot.inputs (ringModel Rat Rat) malformedArguments)).run zeroReplies ()

def querySites (events : List Event) : List String :=
  events.filterMap fun event => match event with | .query site => some site | _ => none

/-- False first results do not discard later source calls. This checks an
actual complete source execution, including the balanced terminal conjunction. -/
theorem malformed_four_calls :
    malformedRun.events.length = 16 ∧
    (querySites malformedRun.events).length = 4 ∧
    (querySites malformedRun.events).Nodup ∧
    malformedRun.outcome = .returned (.cons (some false) .nil) := by
  unfold malformedRun
  rw [SourceFamily.validator_equation installation _ validator]
  constructor
  · kernel_rfl
  constructor
  · kernel_rfl
  constructor
  · decide +kernel
  · kernel_rfl

#print axioms installation
#print axioms SourceFamily.validator_equation
#print axioms SourceFamily.producer_equation
#print axioms SourceFamily.pair
#print axioms SourceFamily.one_no
#print axioms SourceFamily.one_cost
end TestsSecurity.RootComposition.Four.Source
