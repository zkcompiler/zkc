import Zkc.Source.Structured.ContractElaboration
import ZkcExamples.Structured.SchnorrBinding
import ZkcExamples.Structured.SumcheckContractBindings

open Zkc.Source Zkc.Source.Structured

namespace Tests.ContractElaborationSources

set_option smartUnfolding false

namespace Schnorr
open ZkcExamples.Structured

set_option maxRecDepth 20000 in
noncomputable def owner : ContractBinding SchnorrInteractive.imported := by bind_contract
set_option maxRecDepth 20000 in
theorem owner_eq : owner = SchnorrBinding.owner := rfl

set_option maxRecDepth 20000 in
noncomputable def clauseIndex := owner.namedClause "knowledge"
set_option maxRecDepth 20000 in
theorem clause_eq : owner.clause clauseIndex = SchnorrBinding.clause := rfl

set_option maxRecDepth 20000 in
noncomputable def application : ApplicationBinding owner (owner.clause clauseIndex).subject := by
  bind_contract
set_option maxRecDepth 20000 in
theorem application_eq : application = SchnorrBinding.application := rfl

set_option maxRecDepth 20000 in
noncomputable def formula : FormulaBinding SchnorrInteractive.imported application.relation := by
  bind_contract
set_option maxRecDepth 20000 in
theorem formula_eq : formula = SchnorrBinding.formulaBinding := rfl

set_option maxRecDepth 20000 in
theorem formula_law {F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] (base key : G) (witness : F) :
    formula.process (.cons base (.cons key (.cons witness .nil))) =
      .done (.cons (decide (key = witness • base)) .nil) := by rfl

end Schnorr

namespace Sumcheck
open ZkcExamples.Structured

noncomputable def owner : ContractBinding SumcheckSourceViews.imported := by bind_contract
theorem owner_eq : owner = SumcheckContractBindings.publicOwner := rfl

noncomputable def clauseIndex := owner.namedClause "public_sum"
theorem clause_eq : owner.clause clauseIndex = SumcheckContractBindings.publicClause := rfl

noncomputable def application : ApplicationBinding owner (owner.clause clauseIndex).subject := by
  bind_contract
theorem application_eq : application = SumcheckContractBindings.publicApplication := rfl

noncomputable def formula : FormulaBinding SumcheckSourceViews.imported application.relation := by
  bind_contract
theorem formula_eq : formula = SumcheckContractBindings.publicFormula := rfl

noncomputable def reductionApplication : ApplicationBinding SumcheckContractBindings.reductionOwner
    SumcheckContractBindings.reductionClause.subject := by bind_contract
theorem reduction_application_eq : reductionApplication = SumcheckContractBindings.reductionApplication := rfl

noncomputable def reductionFormula : FormulaBinding SumcheckReduceViews.imported
    reductionApplication.relation := by bind_contract
theorem reduction_formula_eq : reductionFormula = SumcheckContractBindings.reductionFormula := rfl

end Sumcheck
end Tests.ContractElaborationSources
