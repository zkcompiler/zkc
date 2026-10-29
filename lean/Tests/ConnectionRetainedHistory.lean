import Tests.SourceConnectionPilot
import ZkcTools.ConstructionBindings.Root
import Zkc.Construction.ConnectionRootRoutes
import Zkc.Construction.ConnectionRouteCoverageRoot

/-! A pure checked callee retains the caller's current transcript. Both roles
use the ordinary library/root proposer and independent coverage theorem. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.ConnectionRetainedHistory
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open ZkcTools.ConstructionBindings

def keepSignature : ProtocolSignature :=
  ⟨"keep", ["P", "V"], [.boolean], [.boolean], [[0,1]], [[0,1]]⟩
def runSignature : ProtocolSignature := { keepSignature with name := "main" }
def keepBody : Region protocolDialect [.boolean] [.boolean] := .ret (.cons .here .nil)
def runBody : Region protocolDialect [.boolean] [.boolean] :=
  .letOp (.mark "keep") .nil .nil <|
  .letOp (.protocolApply keepSignature [0,1] "keep") (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

private def protocol (name : String) (body : Block) : Definition :=
  .function ⟨name, .protocol, .publicDef, [.boolean], [.boolean],
    some ⟨["P", "V"], [["P", "V"]], [["P", "V"]]⟩,
    [], some (.protocol ⟨name, []⟩), body⟩

def snapshot : Snapshot := { Tests.SourceConnectionPilot.snapshot with
  definitions := [protocol "keep" (.block [] (.ret [0])),
    protocol "main" (.block [
      .instruction (.protocolApply "keep" ["P", "V"]) [0] [.boolean] [] "keep"] (.ret [0]))]
  contracts := [⟨"keep", []⟩, ⟨"main", []⟩] }
structured_views snapshot helpers [] protocols [keep, run]
example : Structured.check snapshot = .ok program := kernel_admission

def context : Context := .fiatShamir "main" ["P", "V"] 0 1 0 "random.field/0"
  (some (.draw "field")) "suite" []
def policy : Policy := ⟨"main", "P", "V", 0, "", [], [0], [], "zkc.framed/0", ""⟩
def artifact : Participant :=
  ⟨snapshot.source, snapshot.source, policy, "main.V", [.data .boolean, .transcript "suite"],
    [.data .boolean, .transcript "suite"], [], [0,1], []⟩
def producerRouting : Original.Routing := ⟨snapshot, context, .producer, 0, [], [], [], []⟩
def validatorRouting : Original.Routing := { producerRouting with mode := .validator }
def target : ConnectionCertificate.Block := fun _ => Domain.View.empty

theorem target_eq (model : DomainModel) : Domain.Correspondence.Block
    (model := model) (program := program) (context := context) artifact.instructions (target model) :=
  Domain.Correspondence.empty

def library : ConnectionLibrary.Bundle program.payload := by
  derive_connection_library roles [0,1]

def producer : RootCertificate program producerRouting 0 artifact := by
  derive_root_connection_with_library target target correspondence target_eq services [] library library

def validator : RootCertificate program validatorRouting 1 artifact := by
  derive_root_connection_with_library target target correspondence target_eq services [] library library

def producerFacts := producer.facts
def validatorFacts := validator.facts

-- Neither a stale/untracked cell nor a transcript of another suite can stand
-- for the current history. Output aliasing and out-of-extent data also refuse.
example : True := by
  fail_if_success
    have : ConnectionCertificate.HistoryReadback
        ([.history "other"] : ConnectionFrame.Layout []) "suite" (some 0) := by
      exact .transcript 0 (by rfl)
  trivial
example : True := by
  fail_if_success
    have : ConnectionCertificate.HistoryReadback
        ([.unused, .history "suite"] : ConnectionFrame.Layout []) "suite" (some 0) := by
      exact .transcript 0 (by rfl)
  trivial
example : ¬ ((Original.Location.data 1) ∉ [.data 1]) := by decide +kernel
example : ¬ ConnectionFrame.applicationAdmitted 2 2 [.data 2] none := by decide +kernel
example : ¬ ConnectionFrame.applicationAdmitted 2 1 [] none := by decide +kernel
example : ¬ ConnectionFrame.applicationAdmitted 2 2 [.data 0] (some 1) := by decide +kernel

example : True := by
  fail_if_success
    have : RootCertificate program validatorRouting 1 { artifact with returned := [0,0] } := by
      derive_root_connection_with_library target target correspondence target_eq services [] library library
  trivial

#print axioms producer
#print axioms validator
#print axioms producerFacts
#print axioms validatorFacts
end Tests.ConnectionRetainedHistory
