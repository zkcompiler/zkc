import Zkc.Source.Structured.Formation

/-! Typed raw errors, stable string adapters and exact successful formation.
These controls exercise the shared elaborator without parsing or lowering. -/

set_option autoImplicit false
namespace Tests.StructuredFormation
open Zkc.Source Zkc.Source.Structured

private def definition : Definition :=
  .function ⟨"helper", .local, .privateDef, [.boolean], [.boolean], none, [], none,
    .block [] (.ret [0])⟩

private def signature : ProtocolSignature :=
  ⟨"protocol", ["P", "V"], [.boolean], [.boolean], [[1, 0]], [[0]]⟩

private def failure {α : Type} : Except FormationDiagnostic α → Option FormationDiagnostic
  | .error diagnostic => some diagnostic
  | .ok _ => none

-- Different failures retain both the original typed cause and declaration.
example : failure (formDefinitionDiagnostic definition .local (.ret [1])) =
    some ⟨"helper", .operand (.invalidOperand 1 .boolean)⟩ := rfl

example : failure (formDefinitionDiagnostic definition .local (.ret [])) =
    some ⟨"helper", .operand (.operandCount 1 0)⟩ := rfl

example : failure (formDefinitionDiagnostic definition .local
    (.letOp (.booleanConstant true) [] [.index] .nil (.ret [0]))) =
    some ⟨"helper", .resultTypes [.boolean] [.index]⟩ := rfl

example : failure (formDefinitionDiagnostic definition .local
    (.letOp (.branch [] [.boolean]) [0] [.boolean] .nil (.ret [0]))) =
    some ⟨"helper", .regionCount 2 0⟩ := rfl

-- A protocol repeat requires one closed callback with its exact ports.
private def repeatOp : ProtocolOp := .repeat ⟨[], [], [0], [], 1⟩ "repeat"
private def repeatSignature : ProtocolSignature :=
  ⟨"repeatProtocol", ["P"], [.index], [], [[0]], []⟩

example : failure (formProtocolDiagnostic repeatSignature
    (.letOp repeatOp [0] [] .nil (.ret []))) =
    some ⟨"repeatProtocol", .regionCount 1 0⟩ := rfl

example : failure (formProtocolDiagnostic repeatSignature
    (.letOp repeatOp [0] [] (.cons [] [] (.ret []) .nil) (.ret []))) =
    some ⟨"repeatProtocol", .regionInputs [.index] []⟩ := rfl

example : failure (formProtocolDiagnostic repeatSignature
    (.letOp repeatOp [0] [] (.cons [.index] [.boolean] (.ret [0]) .nil) (.ret []))) =
    some ⟨"repeatProtocol", .regionOutputs [] [.boolean]⟩ := rfl

example : failure (formProtocolDiagnostic repeatSignature
    (.letOp repeatOp [0] [] (.cons [.index] [] (.ret [0]) .nil) (.ret []))) =
    some ⟨"repeatProtocol", .operand (.operandCount 0 1)⟩ := rfl

-- Preserve the old adapters for every tree, including their success values.
theorem definition_adapter_exact (declaration : Definition) (kind : HelperKind)
    (raw : RawRegion Ty Op) :
    formDefinition declaration kind raw =
      match formed : raw.elaborate (dialect := dialect) declaration.inputs declaration.outputs with
      | .error _ => .error "structured-formation"
      | .ok body => .ok ⟨declaration.name, kind, declaration.inputs, declaration.outputs,
          raw, body, formed⟩ := by
  unfold formDefinition formDefinitionDiagnostic
  split <;> split <;> simp_all [Except.mapError, FormationDiagnostic.code]
  rename_i bodyOne first bodyTwo second
  exact Except.ok.inj (first.symm.trans second)

theorem protocol_adapter_exact (header : ProtocolSignature) (raw : RawRegion Ty ProtocolOp) :
    formProtocol header raw =
      match formed : raw.elaborate (dialect := protocolDialect) header.inputs header.outputs with
      | .error _ => .error "structured-formation"
      | .ok body => .ok ⟨header, raw, body, formed⟩ := by
  unfold formProtocol formProtocolDiagnostic
  split <;> split <;> simp_all [Except.mapError, FormationDiagnostic.code]
  rename_i bodyOne first bodyTwo second
  exact Except.ok.inj (first.symm.trans second)

example : formDefinition definition .local (.ret [1]) = .error "structured-formation" := rfl
example : formProtocol signature (.ret [1]) = .error "structured-formation" := rfl

private def helperBody : Region dialect [.boolean] [.boolean] := .ret (.cons .here .nil)
private def protocolBody : Region protocolDialect [.boolean] [.boolean] := .ret (.cons .here .nil)

example : formDefinitionDiagnostic definition .local helperBody.erase =
    .ok ⟨"helper", .local, [.boolean], [.boolean], helperBody.erase, helperBody,
      helperBody.elaborate_erase⟩ := rfl

example : formProtocolDiagnostic signature protocolBody.erase =
    .ok ⟨signature, protocolBody.erase, protocolBody, protocolBody.elaborate_erase⟩ := rfl

example : FormationDiagnostic.code ⟨"helper", .regionCount 2 0⟩ = "structured-formation" := rfl

-- Display bounds do not truncate the typed diagnostic stored by formation.
private def longName : String := String.ofList (List.replicate 600 'x')
private def longDiagnostic : FormationDiagnostic :=
  ⟨longName, .resultTypes (List.replicate 200 .boolean) []⟩

example (diagnostic : FormationDiagnostic) (maxChars : Nat) :
    (diagnostic.details maxChars).length ≤ maxChars := by
  unfold FormationDiagnostic.details
  rw [String.length_ofList]
  exact List.length_take_le _ _

-- Repr's text renderer is executable tooling, not a kernel reduction rule.
#eval show IO Unit from do
  unless longDiagnostic.declaration.length == 600 do
    throw (IO.userError "diagnostic context was truncated")
  unless longDiagnostic.details.length ≤ 512 && (longDiagnostic.details 32).length == 32 do
    throw (IO.userError "diagnostic display exceeded its bound")
  unless longDiagnostic.details 0 == "" do
    throw (IO.userError "zero diagnostic display bound was ignored")
  unless (FormationDiagnostic.details ⟨"helper", .regionCount 2 0⟩).startsWith "helper: " do
    throw (IO.userError "diagnostic display lost declaration context")

end Tests.StructuredFormation
