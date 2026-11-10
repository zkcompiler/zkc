module

public import Zkc.Verification.Core.Steps
public import Zkc.Verification.Core.Transcript
public import Zkc.Tools.Protocol.Readings

/-! Source proof construction over the core language.

Importing this module lets `construct_region` walk the meaning of a core definition for a
literal side, one operation at a time. The steps are the equations of
`Zkc.Verification.Core.Steps`. This module registers what the constructor needs beside them:

- the transports along the membership of a role in a literal side, and the control definitions
  of the meaning, are evaluated (`construction_eval`): a held value becomes the value or the
  unit value, an agreement becomes the agreed count or condition, and a bounded iteration
  reaches the rule for `PIR.repeatN`;
- the transcript interface of a side exposes the absorption of each effect, and the
  obligation of a receive names the received value alone.

`open_core_definition` opens the definition whose meaning the goal names: the meaning becomes
the body of the definition over the table of the earlier definitions. An author opens the
definition being proved and no other, so that a callee stays named and a law about it is
applied where it is called or applied.

`register_core_entries package` makes the entry equations of an imported package available to
the constructor, so that the table entry of a `call` or an `apply` becomes the callee's own
meaning. No proof unfolds the table.
-/

public meta section
open Lean Meta Elab Tactic Command

-- Transports along a membership, the control of the meaning and the abbreviations of the laws.
attribute [construction_eval] Zkc.Core.Held.of Zkc.Core.Held.value Zkc.Core.Held.absent
  Zkc.Core.Held.elim Zkc.Core.holdValues Zkc.Core.presentValues Zkc.Core.absentValues
  Zkc.Core.absentHeldValues Zkc.Core.unmapValues Zkc.Core.remapValues Zkc.Core.broadcast
  Zkc.Core.heldCopies Zkc.Core.absentOutputs Zkc.Core.Reason.stop Zkc.Core.agreed
  Zkc.Core.agreeWith Zkc.Core.repeatProcess Zkc.Core.loopProcess Zkc.Core.partialProcess
  Zkc.Core.repeatBody Zkc.Core.repeatInitial Zkc.Core.repeatCounts Zkc.Core.Step.branchRegion
  Zkc.Core.branchConditions Zkc.Core.loopBody Zkc.Core.Step.roleValues Zkc.Core.Step.heldValues
  Zkc.Core.Step.definitionRow Zkc.Core.Step.collect Zkc.Source.Values.tail Zkc.Source.Values.split
  Zkc.Source.Values.append

-- The absorption of each effect of a side, and the obligation of a receive.
attribute [construction_simp] Zkc.Core.Transcript.interface Zkc.Core.Transcript.forall_recovered
  Zkc.Core.Transcript.received_mk

-- Access to a carried tuple that is a variable, and a Boolean choice between two processes.
attribute [construction_simp] Zkc.Source.Values.get_append Bool.cond_eq_ite

-- A position of the tail of a tuple is the next position of the tuple. The equation is applied
-- before the tail is visited, since the structural normalization unfolds a tail on its own.
run_cmd liftTermElabM do
  addSimpTheorem ProtocolProof.Tools.Construction.constructionSimp ``Zkc.Core.tail_get
    (post := false) (inv := false) AttributeKind.global (eval_prio default)

namespace Zkc.Tools.Verification

/-- Open the definition whose meaning the goal names. The meaning of an imported protocol for a
side, or of an imported function, becomes its body over the table of the earlier definitions.
The step is a definitional unfolding of the program's constant and of its definition; the table
stays closed. -/
elab "open_core_definition" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let some meaning := target.find? fun part =>
        part.isAppOf ``Zkc.Core.Program.meaning && part.getAppNumArgs ≥ 6
      | throwError "the goal names no meaning of a core definition applied to its arguments"
    let some definition ← ProtocolProof.Tools.Construction.evaluateDecided meaning
      | throwError "the program is not an imported definition:\n{meaning}"
    let some body ← ProtocolProof.Tools.Construction.evaluateDecided definition
      | throwError "the definition is not a literal function or protocol:\n{definition}"
    replaceMainGoal [← goal.replaceTargetDefEq (target.replace fun part =>
      if part == meaning then some body else none)]

/-- Register the entry equations of an imported package with the structural normalization of
the constructor, for the current section or file. The importer names them
`package.definition.entry.callee`. -/
elab "register_core_entries " package:ident : command => do
  let prefixName := package.getId
  let environment ← getEnv
  let entries := environment.constants.fold (init := #[]) fun found name _ =>
    if prefixName.isPrefixOf name && name.getPrefix.components.getLast? == some `entry then
      found.push name
    else found
  if entries.isEmpty then
    throwError "no entry equation of a package {prefixName} is in scope"
  liftTermElabM do
    for entry in entries.qsort Name.lt do
      addSimpTheorem ProtocolProof.Tools.Construction.constructionSimp entry (post := true)
        (inv := false) AttributeKind.local (eval_prio default)

end Zkc.Tools.Verification
