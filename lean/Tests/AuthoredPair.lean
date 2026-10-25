import Zkc.Construction.AuthoredPairExecution
import Mathlib.Algebra.Ring.Int.Defs

set_option autoImplicit false
namespace Tests.AuthoredPair
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.AuthoredPair

private def digest := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def target : ContractClause :=
  ⟨.target, "truth", ⟨"Truth", [⟨.input, 0, "V"⟩]⟩, none, some ⟨.output, 0, "V"⟩⟩
private def inputClause : ContractClause :=
  ⟨.input, "honest", ⟨"Truth", [⟨.input, 0, "P"⟩]⟩, none, none⟩
private def original : Snapshot :=
  ⟨digest, "main", [],
    [⟨"Truth", .publicDef, "zkc.language.formula/0", "truth", "0", [.boolean], [.boolean],
      ["statement"], some "identity"⟩], [],
    [.function ⟨"identity", .math, .privateDef, [.boolean], [.boolean], none, [], none,
      .block [] (.ret [0])⟩,
     .function ⟨"main", .protocol, .publicDef, [.boolean, .service scalarServiceContract], [.boolean],
      some ⟨["P", "V"], [["P", "V"], ["V"]], [["V"]]⟩, [], none, .block [] (.ret [0])⟩],
    [⟨"main", [inputClause, target]⟩], blsRows⟩
private def importChecked (snapshot : Snapshot)
    (accepted : (Structured.check snapshot).isOk = true) : Imported snapshot := by
  cases found : Structured.check snapshot with
  | error error => simp_all [Except.isOk, Except.toBool]
  | ok program => exact ⟨program, found⟩
private def imported : Imported original := importChecked original (by decide +kernel)
private def program : Program := imported.program
private def policy : Policy :=
  ⟨"main", "P", "V", 0, "suite", [1], [0], [], "zkc.framed/0", ""⟩
private def producer : Participant :=
  { source := digest, candidate := digest, policy, symbol := "producer",
    inputs := [.data .boolean, .transcript "suite"],
    outputs := [.transcript "suite"], instructions := [], returned := [1] }
private def validator : Participant :=
  { source := digest, candidate := digest, policy, symbol := "validator",
    inputs := [.data .boolean, .transcript "suite"],
    outputs := [.data .boolean, .transcript "suite"], instructions := [], returned := [0, 1] }
private def artifacts : Artifacts := ⟨producer, validator⟩
private def context : Context :=
  ⟨"main", ["P", "V"], 0, 1, 1, scalarServiceContract, none, "suite", []⟩
private def selected : Zkc.Construction.AuthoredPair.Selection original :=
  ⟨artifacts, policy, "producer", "validator", ⟨[], [inputClause]⟩, target⟩

example : select original artifacts "truth" = .ok selected := by decide +kernel
example : Zkc.Construction.AuthoredPair.check imported selected artifacts = .ok () := by decide +kernel
example : Admitted imported selected artifacts := ⟨by decide +kernel⟩
example : (select original artifacts "missing").isOk = false := by decide +kernel

-- Unchanged digest/name labels cannot authorize a changed producer body.
private def stoppedProducer : Participant :=
  { producer with instructions := [⟨.guard "stop", [0], [], []⟩] }
example : Zkc.Construction.AuthoredPair.check imported selected ⟨stoppedProducer, validator⟩ =
    .error "authored-pair-artifacts" := by decide +kernel
example : Zkc.Construction.AuthoredPair.check imported selected ⟨validator, producer⟩ =
    .error "authored-pair-artifacts" := by decide +kernel
example : selectionValid (original := original) { selected with inputs := ⟨[], []⟩ } = false := by decide +kernel
example : selectionValid (original := original)
    { selected with target := { target with subject := ⟨"Truth", []⟩ } } = false :=
  by decide +kernel
example : selectionValid (original := original)
    { selected with policy := { policy with publicInputs := [] } } = false :=
  by decide +kernel
example : selectionValid (original := original) { selected with producerSymbol := "validator" } = false :=
  by decide +kernel
example : checkProducer program context
    { producer with instructions := [⟨.receive "m" "m" "V" .boolean, [], [.data .boolean], []⟩] } =
    .error "construction-producer-receive" := by decide +kernel
example : checkProducer program context
    { producer with instructions := [⟨.call "unknown", [], [], []⟩] } =
    .error "construction-producer-helper" := by decide +kernel

private def model : DomainModel := ringModel Int Int
private def oracle : Domain.Oracle Id model.toCarriers Nat :=
  fun _ _ counter => (.stopped .refused, counter + 1)
private def environment (value : Bool) : Domain.Environment model.toCarriers :=
  [.data (.boolean value), .transcript "suite" []]
private def run (actual : Artifacts) (value : Bool) :=
  executePrepared model program context actual (environment value) (environment value) oracle 0

example : Domain.PairExecution.succeeds 0 (run artifacts true) = true := by rfl
example : Domain.PairExecution.succeeds 0 (run artifacts false) = false := by rfl
example : (run artifacts true).producer.state.oracle = 0 := by rfl
example : observations (run artifacts true) = [] := by rfl

-- A source-related stopped producer remains failed and validation is skipped.
example : (run ⟨stoppedProducer, validator⟩ false).validator = none := by rfl
example : Domain.PairExecution.succeeds 0 (run ⟨stoppedProducer, validator⟩ false) = false := by rfl

private def extraProof : Participant := { producer with instructions :=
  [⟨.send "m" "m" "V", [0], [], []⟩] }
example : (run ⟨extraProof, validator⟩ true).producer.state.proof = [.boolean true] := by rfl
example : Domain.PairExecution.succeeds 0 (run ⟨extraProof, validator⟩ true) = false := by rfl

-- All-reply artifact transport uses actual instruction equality, not a name.
#print axioms Zkc.Construction.AuthoredPair.admitted_producer_process
#print axioms Zkc.Construction.AuthoredPair.admitted_validator
#print axioms Zkc.Construction.AuthoredPair.leftover_fails
end Tests.AuthoredPair
