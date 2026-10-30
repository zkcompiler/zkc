module

public import ZkcSecurityExamples.Components.KoalaBearSumcheckRootSource
public import ZkcSecurityExamples.Components.KoalaBearSumcheckGenerated.Pair
public import ZkcSecurityExamples.Components.KoalaBearSumcheckGenerated.Identity
public import ZkcSecurity.Bindings.Subjects.Domain
public import Zkc.Source.Structured.ContractElaboration

@[expose] public section

/-! Exact association of the actual constructed root with the nominal endpoint.
These admission, target and stage links precede any security evidence. They do
not supply the separate compiled execution bridge or a canonical property. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiled
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Domains.KoalaBearModel (model baseIdentity)
open ZkcSecurity.Domains.KoalaBear (Base)

abbrev snapshot := KoalaBearSumcheckGenerated.Data.snapshot
abbrev imported := KoalaBearSumcheckGenerated.Inputs.imported
abbrev artifact := KoalaBearSumcheckGenerated.Pair.Validator.participant
abbrev publics : List Ty := [.field baseIdentity, .field baseIdentity, .field baseIdentity]

def artifacts : ZkcSecurity.Endpoint.Domain.Artifacts := ⟨snapshot, artifact, publics⟩

def selection : Selection imported.program.payload.entry.outputs :=
  (select imported artifact).get (by decide +kernel)

def compiled : ZkcSecurity.Endpoint.Domain.Compiled artifacts where
  imported := imported
  compiled := by decide +kernel
  selection := selection
  selected := by kernel_rfl
  checked := by decide +kernel
  publics := by kernel_rfl
  occurrences := by kernel_rfl

def owner : ContractBinding imported := by bind_contract
def clauseIndex : Fin owner.contract.clauses.length := owner.namedClause "sum"
def application : ApplicationBinding owner (owner.clause clauseIndex).subject := by bind_contract
def formula : FormulaBinding imported application.relation := by bind_contract

def target : RetainedTarget imported artifact.policy publics where
  owner := owner
  entry := rfl
  clauseIndex := clauseIndex
  target := by kernel_rfl
  noResidual := by kernel_rfl
  decision := by kernel_rfl
  application := application
  booleanOutput := rfl
  publicTypes := rfl
  publicArity := rfl
  supported := by decide +kernel

def subject : ZkcSecurity.Claims.Domain.Subject model artifacts where
  compiled := compiled
  target := target
  relations := KoalaBearSumcheckRelations.installed
  meaning := .formula formula
  originalExport := KoalaBearSumcheckGenerated.Identity.sourceExport
  participantExport := KoalaBearSumcheckGenerated.Identity.validatorExport

def statement (a b claim : Base) : artifacts.Statement model :=
  .cons a (.cons b (.cons claim .nil))

theorem target_read (a b claim : Base) (witness : subject.Witness) :
    subject.target.application.read {} (subject.boundary (statement a b claim))
      (subject.assignments (statement a b claim) witness) = some (.cons a (.cons b (.cons claim .nil))) := by
  kernel_rfl

theorem target_formula (a b claim : Base) :
    formula.invokeRelationOn model (.cons a (.cons b (.cons claim .nil))) =
      .done (.cons (decide (claim = a + b)) .nil) := by
  kernel_rfl

/-- The retained target selects the exact source relation helper. -/
theorem target_helper_link :
    formula.definition.helper = KoalaBearSumcheckGenerated.Inputs.helper0Helper := by
  kernel_rfl

theorem holds_iff (a b claim : Base) (witness : subject.Witness) :
    subject.Holds (statement a b claim) witness ↔ KoalaBearSumcheckSource.sumRelation a b claim := by
  rw [subject.holds_formula_iff formula]
  constructor
  · rintro ⟨arguments, read, holds⟩
    rw [target_read] at read
    cases Option.some.inj read
    change formula.invokeRelationOn model (.cons a (.cons b (.cons claim .nil))) =
      .done (.cons true .nil) at holds
    rw [target_formula] at holds
    change claim = a + b
    exact of_decide_eq_true (Values.cons.inj (PIR.Process.done.inj holds)).1
  · intro truth
    change claim = a + b at truth
    refine ⟨.cons a (.cons b (.cons claim .nil)), target_read a b claim witness, ?_⟩
    change formula.invokeRelationOn model _ = .done (.cons true .nil)
    rw [target_formula, decide_eq_true truth]

theorem falseStatement_iff (a b claim : Base) :
    subject.FalseStatement (statement a b claim) ↔ ¬ KoalaBearSumcheckSource.sumRelation a b claim := by
  constructor
  · intro wrong yes
    exact wrong ⟨fun _ _ => none, (holds_iff a b claim _).mpr yes⟩
  · rintro wrong ⟨witness, yes⟩
    exact wrong ((holds_iff a b claim witness).mp yes)

/-- The actual stage obligation retains all five construction checks. -/
theorem construction_links : subject.ConstructionChecked := subject.constructionChecked

def stage_links := subject.stageLinkProofs

end ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiled
