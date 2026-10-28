import Tests.ConnectionCertificate
import Zkc.Source.Structured.UnitViews
import Zkc.Source.Structured.DomainProtocolLinking

/-! Successful guard facts refine an existing cell. Both its original
expression and its normalized true alias remain available to checked outputs,
calculations, redundant guards and sends. No successful-input premise is used. -/
set_option autoImplicit false
set_option maxRecDepth 12000
noncomputable section
namespace Tests.ConnectionGuardRefinement
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate

def initial : Layout [.value .boolean] := [.data (.present (.var .here))]
def aliases : Form [] [] [.value .boolean] [.boolean, .boolean] :=
  .guard .boolean (.var .here) (.bool true)
    (.done (.cons (.present (.var .here)) (.cons (.present (.bool true)) .nil)))
def guardView : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.guard 0 []) Domain.View.empty

/-- The same physical Boolean discharges both expressions, on every model. -/
def aliasesAccepted : Derivation Tests.ConnectionCertificate.arithmeticRouting {} [] []
    [.boolean, .boolean] 0 [[0,1], [0,1]] [.data 0, .data 0] none [] initial aliases guardView := by
  derive_connection_alignment

def guardRefinementSignature : ProtocolSignature :=
  ⟨"guardRefinement", ["P", "V"], [.boolean], [.boolean, .boolean], [[0,1]], [[0,1], [0,1]]⟩
def guardRefinementBody : Region protocolDialect guardRefinementSignature.inputs guardRefinementSignature.outputs :=
  .letOp (.mark "check") .nil .nil <|
  .letOp (.guard 1 "check") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanAnd rfl) (.cons .here (.cons .here .nil)) .nil <|
  .letOp (.mark "outgoing") .nil .nil <|
  .letOp (.exchange .boolean 1 0 "outgoing") (.cons .here .nil) .nil <|
  .ret (.cons .here (.cons (.there (.there .here)) .nil))
def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "guardRefinement"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"guardRefinement", .protocol, .publicDef, [.boolean], [.boolean, .boolean],
    some ⟨["P", "V"], [["P", "V"]], [["P", "V"], ["P", "V"]]⟩,
    [], some (.protocol ⟨"guardRefinement", []⟩), .block [
      .instruction (.guard "V") [0] [] [] "check",
      .instruction .booleanAnd [0,0] [.boolean] [] "",
      .instruction (.exchange "V" "P") [0] [.boolean] [] "outgoing"] (.ret [0,2])⟩]
  contracts := [⟨"guardRefinement", []⟩]
  catalogue := blsCatalogue
structured_views snapshot helpers [] protocols [guardRefinement]
theorem admitted : check snapshot = .ok program := kernel_admission

def outgoing : Template :=
  ⟨"guardRefinement", [], ["message", "guardRefinement", "outgoing", "outgoing", "V", "P"]⟩
def context : Context := .plain "guardRefinement" ["P", "V"] 0 1
def routing : Original.Routing := ⟨snapshot, context, .validator, 0, [outgoing], [], [], []⟩
def pattern : InputPattern guardRefinementSignature.inputs := .cons .present .nil
def view : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.guard 0 []) <|
  Domain.View.sequence (Domain.View.guard 0 []) <|
  Domain.View.sequence (Domain.View.calculation model .booleanAnd [0,0] [.data .boolean]) <|
  Domain.View.sequence (Domain.View.send "outgoing" "outgoing" "P" 1 []) Domain.View.empty

def accepted : Certificate routing {} [] 1 2 guardRefinementDefinition pattern
    [.data 1, .data 0] none [] initial view := by derive_connection_alignment

def simulation (model : DomainModel) (condition : Bool) (history : Domain.History model.toCarriers) :=
  accepted.simulation (RosterDistinct.root 1 2) model (Occurrence.helpers model program.payload)
    (fun entry => entry.elim0) (Occurrence.table model program.payload) ⟨[],history⟩
    (.cons condition .nil) rfl ⟨[.data .boolean], [.data 0]⟩ [.data (.boolean condition)] rfl
    (by intro reference member; simp at member; subst reference; simp)
    ⟨⟨condition,rfl,rfl⟩,trivial⟩ [.data (.boolean condition)]
    (.cons ⟨condition,rfl,rfl⟩ .nil) (by simp [ArtifactBinding.Captures])

example : aliasesAccepted.size = 2 := rfl
example : accepted.alignment.size = 5 := rfl

-- Guarding one cell cannot establish a true alias for an unrelated cell.
/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation Tests.ConnectionCertificate.arithmeticRouting {} [] []
    [.boolean, .boolean] 0 [[0,1], [0,1]] [.data 0, .data 1] none []
    (initial ++ [.data (.present (.bool false))]) aliases guardView := by
  derive_connection_alignment

-- Success never supplies the opposite Boolean or an invented output value.
/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation Tests.ConnectionCertificate.arithmeticRouting {} [] []
    [.boolean] 0 [[0,1]] [.data 0] none [] initial
    (.guard .boolean (.var .here) (.bool true) (.done (.cons (.present (.bool false)) .nil))) guardView := by
  derive_connection_alignment

-- A missing guard cannot justify source normalization to true.
/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Derivation Tests.ConnectionCertificate.arithmeticRouting {} [] []
    [.boolean] 0 [[0,1]] [.data 0] none [] initial
    (.done (.cons (.present (.bool true)) .nil)) (fun _ => Domain.View.empty) := by
  derive_connection_alignment

end Tests.ConnectionGuardRefinement
