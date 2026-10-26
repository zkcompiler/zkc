/- This standalone audit deliberately omits the module header: Lean must load
opaque proof bodies transitively, rather than exported theorem signatures. -/
import Tests.SumcheckCanonicalCompleteness
import Lean.Util.FoldConsts
set_option maxHeartbeats 0
set_option pp.universes true

open Lean in
private def dependencyClosure (root : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut order : Array Name := #[]
  let mut pending : List Name := [root]
  repeat
    match pending with
    | [] => break
    | name :: rest =>
      pending := rest
      unless visited.contains name do
        visited := visited.insert name
        order := order.push name
        let some info := env.find? name | throwError "unresolved dependency: {name}"
        do
          -- Lean.Util.FoldConsts uses the union of type constants and
          -- value? (allowOpaque := true), including theorem proof bodies.
          for used in info.getUsedConstantsAsSet do
            unless visited.contains used do pending := used :: pending
  return order

private theorem dependencyMarker : True := True.intro
private theorem bodyWitness : True := dependencyMarker

open Lean in
run_cmd Lean.Elab.Command.liftTermElabM do
  let witness ← dependencyClosure ``bodyWitness
  unless witness.contains ``dependencyMarker do
    throwError "proof-body traversal failed its marker control"
  let refusedMissing ← try
    let _ ← dependencyClosure `Tests.SumcheckCanonicalAudit.intentionallyAbsent
    pure false
  catch _ => pure true
  unless refusedMissing do throwError "dependency traversal accepted an unresolved name"

open Lean in
run_cmd Lean.Elab.Command.liftTermElabM do
  let roots := #[
    `Zkc.Executable.DomainVM.Continues.bind,
    `Zkc.Executable.DomainVM.Continues.of_yields,
    `Zkc.Executable.DomainVM.Continues.of_yields_all_proofs,
    `Zkc.Executable.DomainVM.Continues.of_forall,
    `Zkc.Executable.DomainVM.FitsK.of_static,
    `Zkc.Executable.DomainVM.FitsK.append,
    `Zkc.Executable.DomainVM.FitsK.mono,
    `Zkc.Executable.DomainVM.FitsK.helper,
    `Zkc.Executable.DomainVM.FitsK.loop_invariant,
    `Zkc.Executable.DomainVM.FitsStep.mono,
    `Zkc.Executable.DomainVM.FitsIterate.mono,
    `Zkc.Executable.DomainVM.FitsIterate.invariant,
    `Zkc.Executable.DomainVM.Passes.mono,
    `Zkc.Executable.DomainVM.Passes.bind,
    `Zkc.Executable.DomainVM.Passes.fold,
    `Zkc.Executable.DomainVM.Passes.forgetCheckpoints,
    `Zkc.Executable.DomainVM.Passes.participant_observation,
    `ZkcExamples.Executable.SumcheckDomainFamily.round_charge,
    `ZkcExamples.Executable.SumcheckDomainFamily.charge_eq,
    `ZkcExamples.Executable.SumcheckDomainFamily.round_fits,
    `ZkcExamples.Executable.SumcheckDomainFamily.sufficient_family,
    `ZkcExamples.Executable.SumcheckDomainFamily.sufficient,
    `ZkcExamples.Executable.SumcheckDomainCharges.sufficient,
    `ZkcExamples.Executable.SumcheckDomainHonest.honest_step,
    `ZkcExamples.Executable.SumcheckDomainHonest.reduce_passes,
    `ZkcExamples.Executable.SumcheckDomainHonest.root_passes,
    `ZkcExamples.Executable.SumcheckDomainHonest.of_root_passes,
    `ZkcExamples.Executable.SumcheckDomainHonest.observation_passes,
    `ZkcExamples.Executable.SumcheckDomainCompleteness.honest_metered,
    `ZkcExamples.Executable.SumcheckDomainCompleteness.honest_header,
    `ZkcExamples.Executable.SumcheckDomainCompleteness.honest_decoded,
    `ZkcExamples.Executable.SumcheckDomainCompleteness.honest_metered_bytes,
    `Tests.SumcheckCanonicalCompleteness.variable_honest,
    `Tests.SumcheckCanonicalCompleteness.zero_honest,
    `Tests.SumcheckCanonicalCompleteness.one_honest,
    `Tests.SumcheckCanonicalCompleteness.two_honest,
    `Tests.SumcheckCanonicalCompleteness.variable_budget,
    `Tests.SumcheckCanonicalCompleteness.zero_budget,
    `Tests.SumcheckCanonicalCompleteness.false_claim,
    `Tests.SumcheckCanonicalCompleteness.wrong_shape]
  let banned := #[`Zkc.Construction.specK, `Zkc.Construction.specStep,
    `Zkc.Construction.idealK, `Zkc.Construction.idealStep,
    `Zkc.Construction.spec, `Zkc.Construction.ideal,
    `Zkc.Executable.meteredK, `Zkc.Executable.meteredStep, `Zkc.Executable.metered,
    `Zkc.Executable.meteredIterate, `Zkc.Executable.FitsIterate,
    `Zkc.Executable.FitsK, `Zkc.Executable.FitsStep, `Zkc.Executable.Sufficient,
    `Zkc.Executable.Succeeds, `Zkc.Construction.Uniform.compiled_selected, `sorryAx]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for root in roots do
    unless (env.find? root).isSome do throwError "missing root {root}"
    let closure ← dependencyClosure root
    let hits := closure.filter fun name => banned.any fun retired =>
      retired.isPrefixOf name || name.toString.startsWith (retired.toString ++ "_")
    let axioms := closure.filter fun name => match env.find? name with
      | some (.axiomInfo _) => true
      | _ => false
    let some info := env.find? root | throwError "missing stored type for {root}"
    logInfo m!"STORED TYPE {root}: {info.type}"
    logInfo m!"ROOT {root}: {closure.size} stored type/body dependencies; banned={hits}; axioms={axioms}"
    unless hits.isEmpty do throwError "retired dependency in {root}"
    unless (axioms.filter fun name => !allowed.contains name).isEmpty do throwError "nonstandard axiom in {root}"
