module

public import ZkcSecurity.Claims.AuthoredPair
public import Zkc.Construction.TargetElaboration
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Source-driven structural assembly for an already selected authored pair.
The tactic proves only admission and metadata associations. The retained input
clauses and export identities fix the subject; no success or security law is inferred.
-/
set_option autoImplicit false

namespace ZkcSecurity.Tools
open Zkc.Source.Structured Zkc.Construction

/-- Enumerate the retained finite clause index with the computational `Fin`
recursor. A proof of list membership cannot eliminate into `FormulaClause`,
which contains data as well as proofs. Every generated branch is checked. -/
elab "bind_input_formulas" : tactic => Lean.Elab.Tactic.withMainContext do
  let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
  let .forallE _ domain _ _ := target
    | Lean.throwError "bind_input_formulas: expected a finite clause function"
  let domain ← Lean.Meta.whnf domain
  unless domain.getAppFn.constName? == some ``Fin do
    Lean.throwError "bind_input_formulas: expected a Fin clause index"
  let count ← Lean.Meta.reduce domain.getAppArgs[0]!
  let some count := count.rawNatLit?
    | Lean.throwError "bind_input_formulas: clause count is not closed"
  let mut term ← `(fun index => Fin.elim0 index)
  for _ in [:count] do
    term ← `(Fin.cases (by
      intro isInput
      first
        | solve | cases isInput
        | exact { binding := by bind_contract
                  formula := by bind_contract
                  booleanOutput := by rfl }) $term)
  let generated ← Lean.Elab.Term.elabTermEnsuringType term target
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.instantiateMVars generated)
  Lean.Elab.Tactic.replaceMainGoal []

elab "bind_authored_subject " name:str
    " exports " originalExport:term ", " producerExport:term ", " validatorExport:term : tactic =>
    Lean.Elab.Tactic.withMainContext do
  let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
  unless target.getAppFn.constName? == some ``Claims.HonestPair.Subject do
    Lean.throwError "bind_authored_subject: expected HonestPair.Subject"
  let arguments := target.getAppArgs
  unless arguments.size == 4 do
    Lean.throwError "bind_authored_subject: unexpected Subject parameters"
  let original ← Lean.Elab.Term.exprToSyntax arguments[1]!
  let imported ← Lean.Elab.Term.exprToSyntax arguments[2]!
  let selected ← Lean.Elab.Term.exprToSyntax arguments[3]!
  let term ← `(let selection : Selection ($imported).program.payload.entry.outputs :=
                 (select $imported ($selected).artifacts.validator).get (by decide +kernel)
               have selectionExact : select $imported ($selected).artifacts.validator = some selection :=
                 (Option.some_get _).symm
               have admitted : AuthoredPair.Admitted $imported $selected ($selected).artifacts :=
                 ⟨by decide +kernel⟩
               have occurrences :
                   SourceOccurrences.check $original selection.context ($selected).artifacts.producer = .ok () ∧
                   SourceOccurrences.check $original selection.context ($selected).artifacts.validator = .ok () := by
                 obtain ⟨context, found, producer, validator⟩ := AuthoredPair.admitted_occurrences admitted
                 have same := (select_sound $imported ($selected).artifacts.validator selectionExact).1
                 rw [same] at found
                 cases found
                 exact ⟨producer, validator⟩
               let target : RetainedTarget $imported ($selected).policy selection.publics := by
                 bind_target $name
               { originalExport := $originalExport
                 producerExport := $producerExport
                 validatorExport := $validatorExport
                 admitted := admitted
                 selection := selection
                 selectionExact := selectionExact
                 selectionChecked := by decide +kernel
                 producerOccurrences := occurrences.1
                 validatorOccurrences := occurrences.2
                 target := target
                 targetExact := by decide +kernel
                 inputContractExact := by decide +kernel
                 inputClausesExact := by decide +kernel
                 preconditionsEmpty := by decide +kernel
                 inputFormulas := by bind_input_formulas })
  let generated ← Lean.Elab.Term.elabTermEnsuringType term target
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.instantiateMVars generated)
  Lean.Elab.Tactic.replaceMainGoal []

end ZkcSecurity.Tools
