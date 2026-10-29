import ZkcTools.ConstructionBindings.Alignment
import Zkc.Source.Structured.UnitViews
import Zkc.Source.Structured.DomainProtocolLinking

/-! One checked body per symbolic repeat, including nested ordered occurrence
coordinates and profile history. The certificates do not unroll either count. -/
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.ConnectionSymbolicRepeat
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate

def innerSpec : RepeatSpec := ⟨[.index], [], [0,1], [[0,1]], 4⟩
def outerSpec : RepeatSpec := ⟨[.index], [.index], [0,1], [[0,1]], 3⟩
def innerBody : Region protocolDialect [.index, .index] [.index] :=
  .letOp (.mark "message") .nil .nil <|
  .letOp (.exchange .index 0 1 "message") (.cons (.there .here) .nil) .nil <|
  .ret (.cons .here .nil)
def outerBody : Region protocolDialect [.index, .index, .index] [.index] :=
  .letOp (.mark "inner") .nil .nil <|
  .letOp (.repeat innerSpec "inner") (.cons (.there (.there .here)) (.cons (.there .here) .nil))
    (.cons innerBody .nil) <|
  .ret (.cons .here .nil)
def nestedSignature : ProtocolSignature :=
  ⟨"nested", ["P", "V"], [.index, .index, .index], [.index],
    [[0,1], [0,1], [0,1]], [[0,1]]⟩
def nestedBody : Region protocolDialect nestedSignature.inputs nestedSignature.outputs :=
  .letOp (.mark "outer") .nil .nil <|
  .letOp (.repeat outerSpec "outer") (.cons .here (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
    (.cons outerBody .nil) <|
  .ret (.cons .here .nil)
def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "nested"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"nested", .protocol, .publicDef, [.index, .index, .index], [.index],
    some ⟨["P", "V"], [["P", "V"], ["P", "V"], ["P", "V"]], [["P", "V"]]⟩,
    [], some (.protocol ⟨"nested", []⟩), .block [
      .instruction (.protocolRepeat 1 3 ["P", "V"] [["P", "V"]]) [0,2,1] [.index]
        [.region [.index, .index, .index] [.index] (.block [
          .instruction (.protocolRepeat 1 4 ["P", "V"] [["P", "V"]]) [2,1] [.index]
            [.region [.index, .index] [.index] (.block [
              .instruction (.exchange "P" "V") [1] [.index] [] "message"] (.yield [0]))]
            "inner"] (.yield [0]))] "outer"] (.ret [0])⟩]
  contracts := [⟨"nested", []⟩]
  catalogue := blsCatalogue
structured_views snapshot helpers [] protocols [nested]
theorem admitted : check snapshot = .ok program := kernel_admission

def message : Template := ⟨"nested", [⟨"repeat", "nested", "outer"⟩, ⟨"repeat", "nested", "inner"⟩],
  ["message", "nested", "message", "message", "P", "V"]⟩
def plainContext : Context := .plain "nested" ["P", "V"] 0 1
def fsContext : Context := .fiatShamir "nested" ["P", "V"] 0 1 0 "random.bls12-381.fr/0"
  (some (.draw "bls12-381.fr")) "suite" []
def routing (context : Context) (mode : Domain.Mode := .validator) : Original.Routing :=
  ⟨snapshot, context, mode, 0, [message], [], [], []⟩
def pattern : InputPattern nestedSignature.inputs := .cons .present (.cons .present (.cons .present .nil))
def plainLayout : Layout pattern.scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here))),
    .data (.present (.var (.there (.there .here))))]
def fsLayout : Layout pattern.scope := plainLayout ++ [.history "suite"]

def plainInner : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.receive "message" "message" "P" .index [.data .index]) Domain.View.empty
def plainOuter : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 4 [7] 1 [4] [.data .index] (plainInner model)) Domain.View.empty
def plainView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 3 [5] 0 [2] [.data .index] (plainOuter model)) Domain.View.empty

def plainAccepted : Certificate (routing plainContext) {} [] 1 2 nestedDefinition pattern
    [.data 3] none [] plainLayout plainView := by derive_connection_alignment

def plainProducerInner : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.send "message" "message" "V" 6 []) Domain.View.empty
def plainProducerOuter : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 4 [6] 1 [4] [.data .index] (plainProducerInner model)) Domain.View.empty
def plainProducerView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 3 [5] 0 [2] [.data .index] (plainProducerOuter model)) Domain.View.empty
def plainProducerAccepted : Certificate (routing plainContext .producer) {} [] 0 2 nestedDefinition pattern
    [.data 3] none [] plainLayout plainProducerView := by derive_connection_alignment

def fsInner (reversed : Bool := false) : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend 10 (if reversed then 7 else 4) [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend 11 (if reversed then 4 else 7) [.indices]) <|
  Domain.View.sequence (Domain.View.receive "message" "message" "P" .index [.data .index]) <|
  Domain.View.sequence (Domain.View.observe fsContext "suite" message 9 13 12 [.transcript "suite"]) Domain.View.empty

def fsOuter (reversed : Bool := false) : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 4 [13,14] 1 [5,6] [.data .index, .transcript "suite"]
    (fsInner reversed model)) Domain.View.empty
def fsView (reversed : Bool := false) : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 3 [7,8] 0 [2,3] [.data .index, .transcript "suite"]
    (fsOuter reversed model)) Domain.View.empty

def fsAccepted : Certificate (routing fsContext) {} [] 1 2 nestedDefinition pattern
    [.data 4] (some 5) [] fsLayout (fsView false) := by derive_connection_alignment

def fsProducerInner : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend 10 4 [.indices]) <|
  Domain.View.sequence (Domain.View.indicesAppend 11 7 [.indices]) <|
  Domain.View.sequence (Domain.View.send "message" "message" "V" 8 []) <|
  Domain.View.sequence (Domain.View.observe fsContext "suite" message 9 8 12 [.transcript "suite"]) Domain.View.empty
def fsProducerOuter : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 4 [8,13] 1 [5,6] [.data .index, .transcript "suite"]
    (fsProducerInner model)) Domain.View.empty
def fsProducerView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 3 [7,8] 0 [2,3] [.data .index, .transcript "suite"]
    (fsProducerOuter model)) Domain.View.empty
def fsProducerAccepted : Certificate (routing fsContext .producer) {} [] 0 2 nestedDefinition pattern
    [.data 4] (some 5) [] fsLayout fsProducerView := by derive_connection_alignment

-- Two finite body certificates suffice; sizes do not depend on runtime counts.
example : plainAccepted.alignment.size = 6 := rfl
example : plainProducerAccepted.alignment.size = 7 := rfl
example : fsAccepted.alignment.size = 9 := rfl
example : fsProducerAccepted.alignment.size = 10 := rfl

/-- Counts, input data, initial history and all provider replies remain arbitrary.
In particular, this one proof includes zero counts and excessive-count refusal. -/
def plainSimulation (model : DomainModel) (outer inner seed : Nat)
    (history : Domain.History model.toCarriers) :=
  plainAccepted.simulation (RosterDistinct.root 1 2) model (Occurrence.helpers model program.payload)
    (fun entry => entry.elim0) (Occurrence.table model program.payload) ⟨[],history⟩
    (.cons outer (.cons inner (.cons seed .nil))) rfl
    ⟨[.data .index, .data .index, .data .index], [.data 0, .data 1, .data 2]⟩
    [.data (.index outer), .data (.index inner), .data (.index seed)] rfl
    (by intro reference member; simp at member
        rcases member with rfl | rfl | rfl <;> simp)
    ⟨⟨outer,rfl,rfl⟩, ⟨inner,rfl,rfl⟩, ⟨seed,rfl,rfl⟩, trivial⟩
    [.data (.index outer), .data (.index inner), .data (.index seed)]
    (.cons ⟨outer,rfl,rfl⟩ (.cons ⟨inner,rfl,rfl⟩ (.cons ⟨seed,rfl,rfl⟩ .nil)))
    (by simp [ArtifactBinding.Captures])

def fsSimulation (model : DomainModel) (outer inner seed : Nat)
    (history : Domain.History model.toCarriers) :=
  fsAccepted.simulation (RosterDistinct.root 1 2) model (Occurrence.helpers model program.payload)
    (fun entry => entry.elim0) (Occurrence.table model program.payload) ⟨[],history⟩
    (.cons outer (.cons inner (.cons seed .nil))) rfl
    ⟨[.data .index, .data .index, .data .index, .transcript "suite"], [.data 0, .data 1, .data 2]⟩
    [.data (.index outer), .data (.index inner), .data (.index seed), .transcript "suite" history] rfl
    (by intro reference member; simp at member
        rcases member with rfl | rfl | rfl <;> simp)
    ⟨⟨outer,rfl,rfl⟩, ⟨inner,rfl,rfl⟩, ⟨seed,rfl,rfl⟩, trivial⟩
    [.data (.index outer), .data (.index inner), .data (.index seed), .transcript "suite" history]
    (.cons ⟨outer,rfl,rfl⟩ (.cons ⟨inner,rfl,rfl⟩ (.cons ⟨seed,rfl,rfl⟩ (.cons rfl .nil))))
    (by simp [ArtifactBinding.Captures])

-- Failures below retain finite, actionable diagnostics. None executes a count.
example : True := by
  fail_if_success
    have : Certificate (routing fsContext) {} [] 1 2 nestedDefinition pattern
        [.data 4] (some 5) [] fsLayout (fsView true) := by derive_connection_alignment
  trivial

example : True := by
  fail_if_success
    have : Certificate (routing plainContext .producer) {} [] 0 2 nestedDefinition pattern
        [.data 3] none [] plainLayout plainView := by derive_connection_alignment
  trivial

example : True := by
  fail_if_success
    have : Certificate (routing fsContext) {} [] 1 2 nestedDefinition pattern
        [.data 3] none [] plainLayout plainView := by derive_connection_alignment
  trivial

example : True := by
  fail_if_success
    have : Certificate (routing plainContext) {} [] 1 2 nestedDefinition pattern
        [.data 2] none [] plainLayout plainView := by derive_connection_alignment
  trivial

-- A duplicate static route cannot establish the exact occurrence binding.
example : True := by
  fail_if_success
    have : Certificate {routing fsContext with messages := [message, message]} {} [] 1 2 nestedDefinition pattern
        [.data 4] (some 5) [] fsLayout (fsView false) := by derive_connection_alignment
  trivial

def wrongCountView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 3 [5] 1 [2] [.data .index] (plainOuter model)) Domain.View.empty
example : True := by
  fail_if_success
    have : Certificate (routing plainContext) {} [] 1 2 nestedDefinition pattern
        [.data 3] none [] plainLayout wrongCountView := by derive_connection_alignment
  trivial

def wrongYieldOuter : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 4 [6] 1 [4] [.data .index] (plainInner model)) Domain.View.empty
def wrongYieldView : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.loop 3 [5] 0 [2] [.data .index] (wrongYieldOuter model)) Domain.View.empty
example : True := by
  fail_if_success
    have : Certificate (routing plainContext) {} [] 1 2 nestedDefinition pattern
        [.data 3] none [] plainLayout wrongYieldView := by derive_connection_alignment
  trivial

end Tests.ConnectionSymbolicRepeat
