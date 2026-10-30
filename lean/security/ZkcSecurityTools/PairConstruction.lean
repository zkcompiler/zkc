module

public import ZkcSecurity.Bindings.Subjects.HonestPair
public import Zkc.Construction.TargetElaboration
public import ZkcTools.ConstructionBindings.Admission
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
recursor. A proof of list membership cannot eliminate into `RetainedClause`,
which contains data as well as proofs. Every generated branch is checked. -/
elab "bind_input_meanings" : tactic => Lean.Elab.Tactic.withMainContext do
  let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
  let .forallE _ domain _ _ := target
    | Lean.throwError "bind_input_meanings: expected a finite clause function"
  let domain ← Lean.Meta.whnf domain
  unless domain.getAppFn.constName? == some ``Fin do
    Lean.throwError "bind_input_meanings: expected a Fin clause index"
  let count ← Lean.Meta.reduce domain.getAppArgs[0]!
  let some count := count.rawNatLit?
    | Lean.throwError "bind_input_meanings: clause count is not closed"
  let mut term ← `(fun index => Fin.elim0 index)
  for _ in [:count] do
    term ← `(Fin.cases (by
      intro isInput
      first
        | solve | cases isInput
        | exact { binding := by bind_contract
                  meaning := by bind_retained_meaning
                  booleanOutput := by rfl }) $term)
  let generated ← Lean.Elab.Term.elabTermEnsuringType term target
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.instantiateMVars generated)
  Lean.Elab.Tactic.replaceMainGoal []

private meta def bindAuthoredSubject (name : Lean.TSyntax `str)
    (registry originalExport producerExport validatorExport : Lean.TSyntax `term)
    (connections : Option (Lean.TSyntax `term × Lean.TSyntax `term)) : Lean.Elab.Tactic.TacticM Unit :=
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
  let producerProof ← match connections.map Prod.fst with
    | some root => `(some ⟨by derive_source_connection using $root⟩)
    | none => `(by first | exact some ⟨by derive_source_connection⟩ | exact none)
  let validatorProof ← match connections.map Prod.snd with
    | some root => `(some ⟨by derive_source_connection using $root⟩)
    | none => `(by first | exact some ⟨by derive_source_connection⟩ | exact none)
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
               let relations : RegisteredRelations _ ($original).relations :=
                 .ofChecked $registry (by kernel_rfl)
               { originalExport := $originalExport
                 producerExport := $producerExport
                 validatorExport := $validatorExport
                 admitted := admitted
                 selection := selection
                 selectionExact := selectionExact
                 selectionChecked := by decide +kernel
                 producerOccurrences := occurrences.1
                 validatorOccurrences := occurrences.2
                 producerConnection := $producerProof
                 validatorConnection := $validatorProof
                 target := target
                 relations := relations
                 meaning := by bind_retained_meaning
                 targetExact := by decide +kernel
                 inputContractExact := by decide +kernel
                 inputClausesExact := by decide +kernel
                 preconditionsEmpty := by decide +kernel
                 inputMeanings := by bind_input_meanings })
  let generated ← Lean.Elab.Term.elabTermEnsuringType term target
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.instantiateMVars generated)
  Lean.Elab.Tactic.replaceMainGoal []

elab "bind_authored_subject " name:str " with_registry " registry:term
    " exports " originalExport:term ", " producerExport:term ", " validatorExport:term : tactic =>
  bindAuthoredSubject name registry originalExport producerExport validatorExport none

elab "bind_authored_subject " name:str " with_registry " registry:term
    " connections " producer:term ", " validator:term
    " exports " originalExport:term ", " producerExport:term ", " validatorExport:term : tactic =>
  bindAuthoredSubject name registry originalExport producerExport validatorExport (some (producer, validator))

/-- Formula-only subjects use the same builder with the empty registry. The
whole relation table must still pass admission; this is not a fallback. -/
macro "bind_authored_subject " name:str
    " exports " originalExport:term ", " producerExport:term ", " validatorExport:term : tactic =>
  `(tactic| bind_authored_subject $name with_registry OpaqueRegistry.empty exports
    $originalExport, $producerExport, $validatorExport)

/-- Large roots reuse checked certificate declarations; an invalid supplied
certificate refuses rather than falling back to an unresolved link. -/
macro "bind_authored_subject " name:str " connections " producer:term ", " validator:term
    " exports " originalExport:term ", " producerExport:term ", " validatorExport:term : tactic =>
  `(tactic| bind_authored_subject $name with_registry OpaqueRegistry.empty
    connections $producer, $validator exports $originalExport, $producerExport, $validatorExport)

end ZkcSecurity.Tools
