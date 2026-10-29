import ZkcTools.ConstructionBindings.Alignment
import Zkc.Source.Structured.UnitViews
import Zkc.Source.Structured.DomainProtocolLinking

/-! A symbolic repeat whose body can reject. Successful body guards refine
the carried state readback, including the unmodified physical output cell.
The public soundness wrappers include zero counts and arbitrary guard inputs. -/
set_option autoImplicit false
set_option maxRecDepth 12000
noncomputable section
namespace Tests.ConnectionRepeatGuard
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate

def spec : RepeatSpec := ⟨[.boolean], [], [0,1], [[0,1]], 2⟩
def callback : Region protocolDialect [.index, .boolean] [.boolean] :=
  .letOp (.mark "check") .nil .nil <|
  .letOp (.guard 1 "check") (.cons (.there .here) .nil) .nil <|
  .ret (.cons (.there .here) .nil)
def guardedSignature : ProtocolSignature :=
  ⟨"guarded", ["P", "V"], [.index, .boolean], [.boolean], [[0,1], [0,1]], [[0,1]]⟩
def guardedBody : Region protocolDialect guardedSignature.inputs guardedSignature.outputs :=
  .letOp (.mark "loop") .nil .nil <|
  .letOp (.repeat spec "loop") (.cons .here (.cons (.there .here) .nil)) (.cons callback .nil) <|
  .ret (.cons .here .nil)
def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "guarded"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"guarded", .protocol, .publicDef, [.index, .boolean], [.boolean],
    some ⟨["P", "V"], [["P", "V"], ["P", "V"]], [["P", "V"]]⟩,
    [], some (.protocol ⟨"guarded", []⟩), .block [
      .instruction (.protocolRepeat 1 2 ["P", "V"] [["P", "V"]]) [0,1] [.boolean]
        [.region [.index, .boolean] [.boolean] (.block [
          .instruction (.guard "V") [1] [] [] "check"] (.yield [1]))] "loop"] (.ret [0])⟩]
  contracts := [⟨"guarded", []⟩]
  catalogue := blsCatalogue
structured_views snapshot helpers [] protocols [guarded]
theorem admitted : check snapshot = .ok program := kernel_admission
def plainContext : Context := .plain "guarded" ["P", "V"] 0 1
def fsContext : Context := .fiatShamir "guarded" ["P", "V"] 0 1 0 "random.bls12-381.fr/0"
  (some (.draw "bls12-381.fr")) "suite" []
def routing (context : Context) : Original.Routing := ⟨snapshot, context, .validator, 0, [], [], [], []⟩
def pattern : InputPattern guardedSignature.inputs := .cons .present (.cons .present .nil)
def plainLayout : Layout pattern.scope := [.data (.present (.var .here)), .data (.present (.var (.there .here)))]
def fsLayout : Layout pattern.scope := plainLayout ++ [.history "suite"]
def plainView (guardReference : Nat := 3) : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.loop 2 [3] 0 [1] [.data .boolean]
    (Domain.View.sequence (Domain.View.guard guardReference []) Domain.View.empty)) Domain.View.empty
def fsView : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.loop 2 [4,5] 0 [1,2] [.data .boolean, .transcript "suite"]
    (Domain.View.sequence (Domain.View.guard 4 []) Domain.View.empty)) Domain.View.empty
def plainAccepted : Certificate (routing plainContext) {} [] 1 2 guardedDefinition pattern
    [.data 2] none [] plainLayout (plainView 3) := by derive_connection_alignment
def fsAccepted : Certificate (routing fsContext) {} [] 1 2 guardedDefinition pattern
    [.data 3] (some 4) [] fsLayout fsView := by derive_connection_alignment

def plainSimulation (model : DomainModel) (count : Nat) (condition : Bool)
    (history : Domain.History model.toCarriers) :=
  plainAccepted.simulation (RosterDistinct.root 1 2) model (Occurrence.helpers model program.payload)
    (fun entry => entry.elim0) (Occurrence.table model program.payload) ⟨[],history⟩
    (.cons count (.cons condition .nil)) rfl
    ⟨[.data .index, .data .boolean], [.data 0, .data 1]⟩
    [.data (.index count), .data (.boolean condition)] rfl
    (by intro reference member; simp at member; rcases member with rfl | rfl <;> simp)
    ⟨⟨count,rfl,rfl⟩,⟨condition,rfl,rfl⟩,trivial⟩ [.data (.index count), .data (.boolean condition)]
    (.cons ⟨count,rfl,rfl⟩ (.cons ⟨condition,rfl,rfl⟩ .nil)) (by simp [ArtifactBinding.Captures])

def fsSimulation (model : DomainModel) (count : Nat) (condition : Bool)
    (history : Domain.History model.toCarriers) :=
  fsAccepted.simulation (RosterDistinct.root 1 2) model (Occurrence.helpers model program.payload)
    (fun entry => entry.elim0) (Occurrence.table model program.payload) ⟨[],history⟩
    (.cons count (.cons condition .nil)) rfl
    ⟨[.data .index, .data .boolean, .transcript "suite"], [.data 0, .data 1]⟩
    [.data (.index count), .data (.boolean condition), .transcript "suite" history] rfl
    (by intro reference member; simp at member; rcases member with rfl | rfl <;> simp)
    ⟨⟨count,rfl,rfl⟩,⟨condition,rfl,rfl⟩,trivial⟩
    [.data (.index count), .data (.boolean condition), .transcript "suite" history]
    (.cons ⟨count,rfl,rfl⟩ (.cons ⟨condition,rfl,rfl⟩ (.cons rfl .nil))) (by simp [ArtifactBinding.Captures])

-- The outer captured condition and the carried condition can agree on a
-- particular run, but cannot replace one another in the checked body frame.
example : True := by
  fail_if_success
    have : Certificate (routing plainContext) {} [] 1 2 guardedDefinition pattern
        [.data 2] none [] plainLayout (plainView 1) := by derive_connection_alignment
  trivial

end Tests.ConnectionRepeatGuard
