module

public import TestsSecurity.RootConnectionFixture
public import ZkcSecurity.Bindings.Transcript.RootConnectionExecution

@[expose] public section

/-! Refutation controls for the complete consumer contract, independent of
acceptance. These finite metadata fixtures test the fixed output interface;
the actual admitted source/root is exercised in RootConnectionFixture.
-/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.RootConnectionControls
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir
open ConnectionInstallation

def signature : ProtocolSignature :=
  ⟨"Residual", ["P", "V"], [], [.boolean, .field "f"], [], [[1], [1]]⟩
def context : Context := .fiatShamir "Residual" ["P", "V"] 0 1 0
  "random.f/0" (some (.draw "f")) "suite" []
def artifact : Participant where
  source := "output-contract-fixture"
  candidate := "output-contract-fixture"
  symbol := "validator"
  policy := ⟨"Residual", "P", "V", 0, "", [], [], [], "suite", "fixture"⟩
  inputs := []
  outputs := [.data .boolean, .data (.field "f"), .transcript "suite"]
  instructions := []
  returned := [0, 1, 2]
def layout : ReturnLayout signature context 1 artifact :=
  (ReturnLayout.build signature context 1 artifact).toOption.get (by decide +kernel)

def result (model : DomainModel) (accepted : Bool) (residual : model.Field "f")
    (history : Domain.History model.toCarriers) : Domain.Result model.toCarriers :=
  let row := [.data (.boolean accepted), .data (.field "f" residual), .transcript "suite" history]
  ⟨row, row⟩

def source (model : DomainModel) (accepted : Bool) (residual : model.Field "f")
    (history : Domain.History model.toCarriers) :
    Values (Component model.Value) signature.outputs × Original.State model.toCarriers :=
  ⟨.cons (some accepted) (.cons (some residual) .nil), ⟨[], history⟩⟩

theorem complete (model : DomainModel) (accepted : Bool) (residual : model.Field "f")
    (history : Domain.History model.toCarriers) :
    Original.CompleteReturns signature context 1 artifact (source model accepted residual history)
      (result model accepted residual history) where
  schema := ⟨[.data .boolean, .data (.field "f")], rfl, rfl⟩
  values := ⟨[.data (.boolean accepted), .data (.field "f" residual)], rfl, rfl⟩
  readback := rfl
  sorts := by kernel_rfl
  frames := rfl

/-- Equal acceptance cannot conceal a changed non-Boolean source residual. -/
theorem wrong_residual (model : DomainModel) (accepted : Bool) (left right : model.Field "f")
    (changed : left ≠ right) (history : Domain.History model.toCarriers) :
    ¬ Original.CompleteReturns signature context 1 artifact (source model accepted left history)
      (result model accepted right history) := by
  intro related
  have rows := (complete model accepted left history).values_unique related
  have atResidual := congrArg (fun row => row[1]?) rows
  have packaged : (Domain.Payload.field "f" left : Domain.Payload model.toCarriers) =
      Domain.Payload.field "f" right := by simpa [result] using atResidual
  have same : left = right := Domain.Payload.mk_inj.mp packaged
  exact changed same

/-- A stale final transcript fails even if every data output agrees. -/
theorem wrong_history (model : DomainModel) (accepted : Bool) (residual : model.Field "f")
    (before reached : Domain.History model.toCarriers) (changed : before ≠ reached) :
    ¬ Original.CompleteReturns signature context 1 artifact (source model accepted residual before)
      (result model accepted residual reached) := by
  intro related
  have rows := (complete model accepted residual before).values_unique related
  have atHistory := congrArg (fun row => row[2]?) rows
  have same : before = reached := by simpa [result] using atHistory
  exact changed same

/-- A different nominal field is rejected despite identical host carriers. -/
example : (ReturnLayout.build signature context 1
    { artifact with outputs := [.data .boolean, .data (.field "other"), .transcript "suite"] }).toOption = none := by decide +kernel

example : (ReturnLayout.build signature context 1
    { artifact with outputs := [.data .boolean, .transcript "suite"], returned := [0, 2] }).toOption = none := by decide +kernel

/-- Source-selected positions skip hidden values and include earlier visible
residuals. Selection is derived from source scopes, not a chosen agreement. -/
theorem selected_after_hidden (model : DomainModel) (accepted : Bool) (residual : model.Field "f") :
    ∃ value : Bool,
      (Values.cons (none : Component model.Value .index)
        (.cons (some residual) (.cons (some accepted) .nil)) :
          Values (Component model.Value) [.index, .field "f", .boolean]).get (.there (.there .here)) = some value ∧
      ([.data (.field "f" residual), .data (.boolean accepted)] : Domain.Environment model.toCarriers)[
        scopePosition 1 [[], [1], [1]] (.there (.there .here) : Var [.index, .field "f", .boolean] .boolean)]? =
          some (.data (.boolean value)) := by
  exact ConnectionOutputSelection.roleOutputValues_boolean 1 [[], [1], [1]] _ (.there (.there .here)) rfl rfl

#print axioms RootConnection.readingFromABI
#print axioms RootConnection.publicBridge
#print axioms RootConnection.publicCoherent
#print axioms RootConnection.publicReadValues
#print axioms RootConnection.publicReadAcceptance
#print axioms RootConnection.compiledAcceptance_agree
#print axioms RootConnection.compiledReadAcceptance
#print axioms RootConnection.compiledVerifier
#print axioms RootConnection.runtime
#print axioms RootConnection.honestReadback
#print axioms wrong_residual
#print axioms wrong_history

end TestsSecurity.RootConnectionControls
