module

public import ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Inputs
public import Zkc.Source.Structured.Bindings.Template

@[expose] public section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.RootProducer
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
abbrev program : Program := ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Inputs.program
abbrev definition : CheckedProtocol := program.payload.protocols.get ⟨1, by decide +kernel⟩
theorem definition_member : definition ∈ program.payload.protocols := List.get_mem _ _
def signature : Signature := ⟨[(⟨(⟨"s14h6d697865645f73756d636865636b5h656d626564", .local, [(.field "koala-bear")], [(.field "koala-bear.ext8-binomial3")]⟩ : Helper), (.returns []), []⟩ : LawKey)], false, true, [(⟨"zkf_e175305e9d926d39d1325e6c28c342f04dd993207dd3d89f317b2afc9c2a1471", .math, [(.field "koala-bear"), (.field "koala-bear"), (.field "koala-bear")], [.boolean]⟩ : Helper), (⟨"s14h6d697865645f73756d636865636b7h70656e64696e67", .local, [(.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")]⟩ : Helper), (⟨"s14h6d697865645f73756d636865636b10h6f70656e5f636c61696d", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")]⟩ : Helper), (⟨"zkl_daa4cc1b0228f87a89c04d62b4b161ffd93cfdc07ffcd4c34bb70b214836fc85", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")]⟩ : Helper), (⟨"s14h6d697865645f73756d636865636b8h61745f706f696e74", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")]⟩ : Helper), (⟨"s14h6d697865645f73756d636865636b14h7465726d696e616c5f76616c7565", .math, [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean]⟩ : Helper), (⟨"_mathematical_admission_0", .local, [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean]⟩ : Helper), (⟨"s14h6d697865645f73756d636865636b5h636865636b", .local, [(.field "koala-bear"), (.field "koala-bear"), (.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean]⟩ : Helper)], [(⟨(⟨"s14h6d697865645f73756d636865636b5h526f756e64", ["role00000000", "role00000001"], [(.field "koala-bear"), (.field "koala-bear"), (.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.service "random.koala-bear.ext8-binomial3/0")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [[0], [0], [1], [1], [1]], [[1], [1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil))))), []⟩ : CalleeKey)]⟩
def role : Nat := 0
def roster : Nat := 2
def template : Template definition signature role roster where
  form := (.apply ⟨0, by decide⟩ (⟨"s14h6d697865645f73756d636865636b5h526f756e64", ["role00000000", "role00000001"], [(.field "koala-bear"), (.field "koala-bear"), (.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.service "random.koala-bear.ext8-binomial3/0")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [[0], [0], [1], [1], [1]], [[1], [1]]⟩ : ProtocolSignature) [0, 1] "label_726f756e64" (by change (Values (Argument [(⟨(⟨"s14h6d697865645f73756d636865636b5h656d626564", .local, [(.field "koala-bear")], [(.field "koala-bear.ext8-binomial3")]⟩ : Helper), (.returns []), []⟩ : LawKey)] [(.component (.field "koala-bear")), (.component (.field "koala-bear")), (.component (.field "koala-bear")), (.component (.service "random.koala-bear.ext8-binomial3/0"))]) [(.component (.field "koala-bear")), (.component (.field "koala-bear")), (.component (.vector "koala-bear.ext8-binomial3")), (.component (.field "koala-bear.ext8-binomial3")), (.component (.service "random.koala-bear.ext8-binomial3/0"))]); exact (.cons (.input .here) (.cons (.input (.there .here)) (.cons .absent (.cons .absent (.cons (.input (.there (.there (.there .here)))) .nil)))))) (.done (.cons .absent .nil)))
  normalized := by kernel_rfl
  matched := by decide +kernel
def helperTables (model : DomainModel) : Tables model :=
  program.payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩
def capture (model : DomainModel) : ProtocolTable model.Value (Interface model) :=
  (program.payload.protocols.take 1).foldl (extendProtocolTableOn model (.silent _) (participantActionsOn model.toCarriers) (helperTables model)) []
theorem capture_exact (model : DomainModel) : capture model =
  (program.payload.protocols.take 1).foldl (extendProtocolTableOn model (.silent _) (participantActionsOn model.toCarriers) (helperTables model)) [] := rfl
theorem source_capture (model : DomainModel) :
  invokeProtocol (program.payload.plainProtocolTableOn model) definition.signature =
    definition.denoteWithOn model (.silent _) (participantActionsOn model.toCarriers) (helperTables model) (capture model) .silent := by kernel_rfl
end
end ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.RootProducer
