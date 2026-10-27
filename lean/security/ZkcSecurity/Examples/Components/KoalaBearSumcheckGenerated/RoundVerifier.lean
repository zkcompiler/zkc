module

public import ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Inputs
public import Zkc.Source.Structured.Bindings.Template

@[expose] public section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.RoundVerifier
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
abbrev program : Program := ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Inputs.program
abbrev definition : CheckedProtocol := program.payload.protocols.get ⟨0, by decide +kernel⟩
theorem definition_member : definition ∈ program.payload.protocols := List.get_mem _ _
def signature : Signature := ⟨[(⟨(⟨"s14h6d697865645f73756d636865636b5h656d626564", .local, [(.field "koala-bear")], [(.field "koala-bear.ext8-binomial3")]⟩ : Helper), (.returns []), []⟩ : LawKey)], false, true, [(⟨"zkf_e175305e9d926d39d1325e6c28c342f04dd993207dd3d89f317b2afc9c2a1471", .math, [(.field "koala-bear"), (.field "koala-bear"), (.field "koala-bear")], [.boolean]⟩ : Helper), (⟨"s14h6d697865645f73756d636865636b7h70656e64696e67", .local, [(.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")]⟩ : Helper), (⟨"s14h6d697865645f73756d636865636b10h6f70656e5f636c61696d", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")]⟩ : Helper), (⟨"zkl_daa4cc1b0228f87a89c04d62b4b161ffd93cfdc07ffcd4c34bb70b214836fc85", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")]⟩ : Helper), (⟨"s14h6d697865645f73756d636865636b8h61745f706f696e74", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")]⟩ : Helper), (⟨"s14h6d697865645f73756d636865636b14h7465726d696e616c5f76616c7565", .math, [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean]⟩ : Helper), (⟨"_mathematical_admission_0", .local, [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean]⟩ : Helper), (⟨"s14h6d697865645f73756d636865636b5h636865636b", .local, [(.field "koala-bear"), (.field "koala-bear"), (.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean]⟩ : Helper)], []⟩
def role : Nat := 1
def roster : Nat := 2
def template : Template definition signature role roster where
  form := (.owned 1 (⟨"s14h6d697865645f73756d636865636b10h6f70656e5f636c61696d", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")]⟩ : Helper) (.cons (.input (.there (.there .here))) (.cons (.input (.there (.there (.there .here)))) .nil)) (.receive (.field "koala-bear.ext8-binomial3") "label_6c6f77_0" 0 (.receive (.field "koala-bear.ext8-binomial3") "label_68696768_0" 0 (.split (.read (.there (.there .here)) (.there .here)) (.halt .incomplete) (.guard (.field "koala-bear.ext8-binomial3") (.calc (.fieldAdd "koala-bear.ext8-binomial3") rfl (.cons (.var (.there (.there .here))) (.cons (.var (.there .here)) .nil)) .here) (.var .here) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.halt .incomplete) (.query "label_6368616c6c656e6765" "koala-bear.ext8-binomial3" (.cons (.var .here) .nil) (.send (.field "koala-bear.ext8-binomial3") "label_64656c6976657279_0" 0 (.var .here) (.owned 1 (⟨"zkl_daa4cc1b0228f87a89c04d62b4b161ffd93cfdc07ffcd4c34bb70b214836fc85", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")]⟩ : Helper) (.cons (.read (.there (.there (.there (.there (.there .here))))) .here) (.cons (.present (.var .here)) .nil)) (.owned 1 (⟨"s14h6d697865645f73756d636865636b8h61745f706f696e74", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")]⟩ : Helper) (.cons (.read .here .here) (.cons (.present (.calc (.fieldAdd "koala-bear.ext8-binomial3") rfl (.cons (.var (.there (.there (.there (.there (.there .here)))))) (.cons (.calc (.fieldMultiply "koala-bear.ext8-binomial3") rfl (.cons (.calc (.fieldSubtract "koala-bear.ext8-binomial3") rfl (.cons (.var (.there (.there (.there (.there .here))))) (.cons (.var (.there (.there (.there (.there (.there .here)))))) .nil)) .here) (.cons (.var (.there .here)) .nil)) .here) .nil)) .here)) .nil)) (.done (.cons (.read .here .here) (.cons (.read .here (.there .here)) .nil)))))))))))))
  normalized := by kernel_rfl
  matched := by decide +kernel
def helperTables (model : DomainModel) : Tables model :=
  program.payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩
def capture (model : DomainModel) : ProtocolTable model.Value (Interface model) :=
  (program.payload.protocols.take 0).foldl (extendProtocolTableOn model (.silent _) (participantActionsOn model.toCarriers) (helperTables model)) []
theorem capture_exact (model : DomainModel) : capture model =
  (program.payload.protocols.take 0).foldl (extendProtocolTableOn model (.silent _) (participantActionsOn model.toCarriers) (helperTables model)) [] := rfl
theorem source_capture (model : DomainModel) :
  invokeProtocol (program.payload.plainProtocolTableOn model) definition.signature =
    definition.denoteWithOn model (.silent _) (participantActionsOn model.toCarriers) (helperTables model) (capture model) .silent := by kernel_rfl
end
end ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.RoundVerifier
