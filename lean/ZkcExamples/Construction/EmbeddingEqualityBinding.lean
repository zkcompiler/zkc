module

public import ZkcExamples.Construction.EmbeddingEqualityData
public import ZkcExamples.Construction.EmbeddingEqualityParticipant
public import ZkcExamples.Construction.EmbeddingEqualityBodies
public import Zkc.Source.Structured.UnitViews
public import Zkc.Construction.Compiled
public import Zkc.Construction.SourceOccurrences
public import Zkc.Construction.RetainedTarget
public import Zkc.Source.Structured.ContractElaboration

@[expose] public section

/-! Kernel admission and exact policy/body association for the actual exported
embedding equality fixture. The data modules are generated from native exports;
names and hashes alone do not discharge these checks. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

noncomputable section

namespace ZkcExamples.Construction.EmbeddingEqualityBinding
open Zkc.Source Zkc.Source.Structured Zkc.Construction

abbrev snapshot := EmbeddingEqualityData.snapshot
abbrev artifact := EmbeddingEqualityParticipant.participant

structured_views snapshot
  helpers [formulaBodyView := ZkcExamples.Construction.EmbeddingEqualityBodies.formula,
    embeddingBodyView := ZkcExamples.Construction.EmbeddingEqualityBodies.embedding]
  protocols [proof := ZkcExamples.Construction.EmbeddingEqualityBodies.proof]

theorem admitted : Structured.check snapshot = .ok program := kernel_admission

theorem compiled : checkCompiled imported artifact = .ok () := by decide +kernel

def selection : Selection program.payload.entry.outputs :=
  ⟨Context.fiatShamir snapshot.entry ["role00000000", "role00000001"] 0 1 2
    "random.koala-bear.ext8-binomial3/0" (some (.draw "koala-bear.ext8-binomial3"))
    "merlin3.koala-bear.ext8-binomial3.rejection31le/0"
    [("label_6368616c6c656e6765", "label_64656c6976657279_0")],
    0, [.field "koala-bear", .field "koala-bear"], [.held 0, .held 1, .service], .here⟩

theorem selected : select imported artifact = some selection := by kernel_rfl

theorem selection_checked : selection.check imported artifact = true := by decide +kernel

abbrev context : Context := selection.context

theorem source_occurrences : SourceOccurrences.check snapshot context artifact = .ok () := by
  kernel_rfl

theorem public_shape : selection.publics = [.field "koala-bear", .field "koala-bear"] := by
  decide +kernel

theorem acceptance_position : selection.position = 0 := by decide +kernel

def owner : ContractBinding imported := by bind_contract
def clauseIndex : Fin owner.contract.clauses.length := owner.namedClause "equality"
def clause : ContractClause := owner.clause clauseIndex
def application : ApplicationBinding owner clause.subject := by bind_contract
def formula : FormulaBinding imported application.relation := by bind_contract

theorem target_exact : owner.contract.clauses = [clause] ∧
    clause.name = "equality" ∧ clause.residual = none ∧
    clause.decision = some ⟨.output, 0, "role00000001"⟩ := by decide +kernel

def retained : RetainedTarget imported artifact.policy [.field "koala-bear", .field "koala-bear"] where
  owner := owner
  entry := rfl
  clauseIndex := clauseIndex
  target := by decide +kernel
  noResidual := by decide +kernel
  decision := by decide +kernel
  application := application
  formula := formula
  booleanOutput := rfl
  publicTypes := rfl
  publicArity := rfl
  supported := by decide +kernel

end ZkcExamples.Construction.EmbeddingEqualityBinding
