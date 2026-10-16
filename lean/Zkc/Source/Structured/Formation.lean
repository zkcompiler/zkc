module

public import Zkc.Source.Structured.CheckedData

@[expose] public section

/-! Raw formation preserves its typed cause independently of source lowering.
The string adapters retain the existing stable refusal code. -/

namespace Zkc.Source.Structured

/-- The exact raw formation error, with the declaration being formed. This is
an in-process diagnostic, not an extension of the source wire format. -/
structure FormationDiagnostic where
  declaration : String
  cause : RegionFormationError Ty
  deriving DecidableEq, Repr

def FormationDiagnostic.code (_diagnostic : FormationDiagnostic) : String :=
  "structured-formation"

/-- Bounded display text in Unicode characters; the stored context and cause
remain exact. Limit the displayed name separately so the cause stays visible. -/
def FormationDiagnostic.details (diagnostic : FormationDiagnostic) (maxChars : Nat := 512) : String :=
  let declaration := String.ofList (diagnostic.declaration.toList.take 128)
  String.ofList ((declaration ++ ": " ++ reprStr diagnostic.cause).toList.take maxChars)

/-- Form the supplied tree once, preserving its typed error and full signature. -/
def formDefinitionDiagnostic (definition : Definition) (kind : HelperKind)
    (raw : RawRegion Ty Op) : Except FormationDiagnostic CheckedDefinition :=
  match formed : raw.elaborate (dialect := dialect) definition.inputs definition.outputs with
  | .error cause => .error ⟨definition.name, cause⟩
  | .ok body => .ok ⟨definition.name, kind, definition.inputs, definition.outputs, raw, body, formed⟩

/-- Form exactly the supplied raw tree without changing retained signatures. -/
def formDefinition (definition : Definition) (kind : HelperKind) (raw : RawRegion Ty Op) :
    Except String CheckedDefinition :=
  (formDefinitionDiagnostic definition kind raw).mapError FormationDiagnostic.code

theorem formDefinition_raw {definition : Definition} {kind : HelperKind} {raw : RawRegion Ty Op}
    {checked : CheckedDefinition} (accepted : formDefinition definition kind raw = .ok checked) :
    checked.raw = raw := by
  unfold formDefinition formDefinitionDiagnostic at accepted
  split at accepted
  · contradiction
  · cases Except.ok.inj accepted
    rfl

/-- Protocol formation uses the same diagnostic cause and preserves all resolved
roles and scopes from the supplied signature. No lowering is repeated. -/
def formProtocolDiagnostic (signature : ProtocolSignature) (raw : RawRegion Ty ProtocolOp) :
    Except FormationDiagnostic CheckedProtocol :=
  match formed : raw.elaborate (dialect := protocolDialect) signature.inputs signature.outputs with
  | .error cause => .error ⟨signature.name, cause⟩
  | .ok body => .ok ⟨signature, raw, body, formed⟩

def formProtocol (signature : ProtocolSignature) (raw : RawRegion Ty ProtocolOp) :
    Except String CheckedProtocol :=
  (formProtocolDiagnostic signature raw).mapError FormationDiagnostic.code

/-- Successful formation preserves both the complete signature and the exact tree. -/
theorem formProtocol_exact {signature : ProtocolSignature} {raw : RawRegion Ty ProtocolOp}
    {checked : CheckedProtocol} (accepted : formProtocol signature raw = .ok checked) :
    checked.signature = signature ∧ checked.raw = raw := by
  unfold formProtocol formProtocolDiagnostic at accepted
  split at accepted
  · contradiction
  · cases Except.ok.inj accepted
    exact ⟨rfl, rfl⟩

end Zkc.Source.Structured
