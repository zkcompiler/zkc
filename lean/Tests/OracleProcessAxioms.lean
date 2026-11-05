import Tests.OracleProcessData
import Lean

set_option autoImplicit false
open Lean Zkc.Source.Structured

run_cmd do
  let selected := [
    ``Tests.OracleProcessData.associated,
    ``Tests.OracleProcessData.checked,
    ``OracleProcess.represents_present,
    ``OracleProcess.answer_represents,
    ``OracleProcess.read_represents,
    ``OracleProcess.operation_independent,
    ``OracleProcess.control_independent,
    ``OracleProcess.operation_represents,
    ``OracleProcess.protocol_represents,
    ``OracleProcess.executeM_initial_irrelevant,
    ``OracleProcess.executeM_bind,
    ``OracleProcess.executeM_sequence,
    ``OracleProcess.executeM_present,
    ``OracleProcess.runM_actions,
    ``OracleProcess.runM_envelope,
    ``OracleProcess.runM_pure,
    ``OracleProcess.source_represents,
    ``OracleProcess.sourceRunM_pure,
    ``OracleProcess.sourceRunM_envelope,
    ``OracleProcess.sourceRunM_reachable]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in selected do
    let axioms ← Lean.collectAxioms declaration
    for dependency in axioms do
      unless allowed.contains dependency do
        throwError "unexpected axiom in {declaration}: {dependency}"
    logInfo m!"{declaration}: {axioms}"
  logInfo m!"ORACLE-PROCESS-AXIOMS-PASS: {selected.length} selected declarations"

set_option pp.universes true in
#check OracleProcess.Interface
#check OracleProcess.source
#check OracleProcess.sourceRunM
#check OracleProcess.answer_represents
#check OracleProcess.operation_independent
#check OracleProcess.control_independent
#check OracleProcess.protocol_represents
#check OracleProcess.runM_envelope
#check OracleProcess.runM_pure
#check OracleProcess.runM_interpret
#check OracleProcess.executeM_envelope
#check OracleProcess.source_represents
#check OracleProcess.sourceRunM_pure
#check OracleProcess.sourceRunM_envelope
#check OracleProcess.sourceRunM_reachable
