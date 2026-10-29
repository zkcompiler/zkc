import ZkcTools.ConstructionBindings.Root
import Zkc.Source.Structured.UnitViews
import Tests.StructuredDomainModels

/-! A complete connection with distinct field carriers and two non-Boolean
outputs. This is a synthetic typed admission control, not a native export or
an assertion of algebraic laws for an installed extension field. -/
set_option autoImplicit false
noncomputable section
namespace Tests.MixedDomainRootConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot

abbrev types : List Ty := [.field "koala-bear", .field "koala-bear.ext8-binomial3"]

def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "mixed"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"mixed", .protocol, .publicDef, types, types,
    some ⟨["P", "V"], [["P", "V"], ["P", "V"]], [["P", "V"], ["P", "V"]]⟩,
    [], some (.protocol ⟨"mixed", []⟩),
    .block [.instruction (.fieldAdd "koala-bear") [0, 0] [.field "koala-bear"] [] "",
      .instruction (.fieldAdd "koala-bear.ext8-binomial3") [2, 2] [.field "koala-bear.ext8-binomial3"] [] ""] (.ret [1, 0])⟩]
  contracts := [⟨"mixed", []⟩]
  catalogue := koalaBearCatalogue

def rootSignature : ProtocolSignature :=
  ⟨"mixed", ["P", "V"], types, types, [[0, 1], [0, 1]], [[0, 1], [0, 1]]⟩
def rootBody : Region protocolDialect types types :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "koala-bear") rfl) (.cons .here (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "koala-bear.ext8-binomial3") rfl)
    (.cons (.there (.there .here)) (.cons (.there (.there .here)) .nil)) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))
structured_views snapshot helpers [] protocols [root]

abbrev context : Context := .plain "mixed" ["P", "V"] 0 1
def routing : Original.Routing := ⟨snapshot, context, .validator, 0, [], [], [], []⟩
def artifact : Participant where
  source := snapshot.source
  candidate := "mixed-domain-control"
  symbol := "validator"
  policy := ⟨"mixed", "P", "V", 0, "", [], [0, 1], [], "zkc.framed/0", ""⟩
  inputs := [.data (.field "koala-bear"), .data (.field "koala-bear.ext8-binomial3")]
  outputs := [.data (.field "koala-bear"), .data (.field "koala-bear.ext8-binomial3")]
  instructions := [
    ⟨.calculate (.fieldAdd "koala-bear"), [0, 0], [.data (.field "koala-bear")], []⟩,
    ⟨.calculate (.fieldAdd "koala-bear.ext8-binomial3"), [1, 1], [.data (.field "koala-bear.ext8-binomial3")], []⟩]
  returned := [2, 3]

def body (model : DomainModel) : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.calculation model (.fieldAdd "koala-bear") [0, 0] [.data (.field "koala-bear")])
    (Domain.View.sequence (Domain.View.calculation model (.fieldAdd "koala-bear.ext8-binomial3") [1, 1] [.data (.field "koala-bear.ext8-binomial3")])
      Domain.View.empty)

def connected : RootCertificate program routing 1 artifact := by
  derive_root_connection target body
    correspondence (fun _ => Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _)
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _) Domain.Correspondence.empty))
    services []

/-- Deliberately operational test data. The root theorem is parametric in this
model; matching a native field's characteristic is a separate domain law. -/
def mixedModel : DomainModel where
  Field identity := Tests.StructuredDomainModels.carrier
    (if identity = "koala-bear" then .small else .large)
  Group _ := ZMod 5
  fieldRing _ := inferInstance
  fieldDecEq _ := inferInstance
  inverse _ := none
  embed _ _ _ := 0
  groupAdd _ := inferInstanceAs (AddCommGroup (ZMod 5))
  groupDecEq _ := inferInstanceAs (DecidableEq (ZMod 5))
  smul _ _ _ point := point

/-- The same certificate accepts genuinely different host carriers. -/
example (left : mixedModel.Field "koala-bear")
    (right : mixedModel.Field "koala-bear.ext8-binomial3") :
    Original.Simulation (Original.CompleteReturns program.payload.entry.signature context 1 artifact)
      (InputFrames connected.inputs.abi program.payload.entry.inputs
        [.data (.field "koala-bear" left), .data (.field "koala-bear.ext8-binomial3" right)])
      (connected.source mixedModel
        [.data (.field "koala-bear" left), .data (.field "koala-bear.ext8-binomial3" right)])
      (Domain.participant mixedModel program context artifact
        [.data (.field "koala-bear" left), .data (.field "koala-bear.ext8-binomial3" right)]) := connected.simulation _ _

example (model : DomainModel) (left right : model.Field "koala-bear") :
    connected.source model [.data (.field "koala-bear" left), .data (.field "koala-bear" right)] =
      .halt .refused := rfl

#print axioms connected
end Tests.MixedDomainRootConnection
