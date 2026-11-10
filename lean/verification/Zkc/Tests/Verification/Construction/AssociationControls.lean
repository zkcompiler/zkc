module

public import Zkc.Tests.Verification.Construction.ActualCalls

/-! Lookup identity is not law applicability. An admitted body edit under the same key and
source digest rejects the old association, while a newly proved law remains installable. -/

@[expose] public section
set_option experimental.vcgen true
open PIR Zkc.Source Zkc.Source.Structured ProtocolProof Std.WP
namespace ActualSourceConstruction.AssociationControls
open Twice

def replaceSubtract : Instruction → Instruction
  | .instruction (.fieldSubtract field) operands results regions site =>
    .instruction (.fieldAdd field) operands results regions site
  | other => other

def changeHelper : Definition → Definition
  | .function definition =>
    if definition.name = difference.signature.name then
      let .block instructions terminator := definition.body
      .function { definition with body := .block (instructions.map replaceSubtract) terminator }
    else .function definition
  | other => other

def changedSource : Snapshot :=
  { actual.source with definitions := actual.source.definitions.map changeHelper }

def checked : Imported changedSource :=
  Zkc.Verification.Imported.ofIsOk check changedSource (by decide +kernel)

def program : Program := source_value% checked.program

theorem programExact : checked.program = program := by kernel_rfl

def changed : Imported changedSource :=
  ⟨program, checked.admitted.trans (congrArg Except.ok programExact)⟩

bind_source_helper addition from changed named "s12h61637475616c5f63616c6c7310h646966666572656e6365"
bind_source_protocol twice from changed named "s12h61637475616c5f63616c6c735h5477696365"

theorem same_lookup_key : addition.helper = difference.signature := by kernel_rfl

/-- The caller's own tree is unchanged; dependency meaning still changes its law. -/
theorem same_caller_body : twice.body = Twice.twice.body := by kernel_rfl

theorem same_digest : changedSource.source = actual.source.source := rfl

theorem stale_body_refused : ¬ BodyIn program.payload.definitions
    difference.signature difference.body := by
  rintro ⟨definition, member, _, body⟩
  have only : program.payload.definitions = [addition] := by kernel_rfl
  rw [only, List.mem_singleton] at member
  subst definition
  have operations := congrArg RawRegion.operations body
  change [Op.fieldAdd "bls12-381.fr"] = [Op.fieldSubtract "bls12-381.fr"] at operations
  cases operations

variable (model : DomainModel) {I : Signature} {Pred EPred : Type}
  [Assertion Pred] [Assertion EPred] [WPMonad (Process I) Pred EPred]

@[spec high] theorem addition_law (observations : SiteObservations I)
    (table : Evaluation.MeaningsOn model.toCarriers I)
    (arguments : Values model.Value addition.signature.inputs)
    (post : Values model.Value addition.signature.outputs → Pred) (stopped : EPred) :
    ⦃post (.singleton (arguments.get .here + arguments.get (.there .here)))⦄
      addition.body.denote (Evaluation.meaningOn model observations table) arguments.get
      ⦃post; stopped⦄ := by
  construct_region

/-- Correct rebinding remains possible; a changed body does not invalidate all mathematics. -/
theorem rebound_law [WPMonad (Process (participantInterfaceOn model.toCarriers)) Pred EPred]
    (x y : model.Field "bls12-381.fr")
    (post : Values (Component model.Value) twice.signature.outputs → Pred) (stopped : EPred) :
    ⦃post (.cons (some (x + y)) (.cons (some (y + x)) .nil))⦄
      program.participantOn model 0 (.cons (some x) (.cons (some y) .nil))
      ⦃post; stopped⦄ := by
  construct_region

#print axioms stale_body_refused
#print axioms rebound_law
end ActualSourceConstruction.AssociationControls
