module

public import Zkc.IR.Source.Structured.Import
public import Zkc.IR.Source.Structured.UnitViews
public meta import Zkc.IR.Source.Structured.UnitViews
public meta import Lean.Elab.Deriving.ToExpr
public meta import Lean.Elab.Command
public meta import Lean.PrettyPrinter.Delaborator
public meta import Zkc.IR.Source.Structured.Limits
public meta import Zkc.IR.Source.Structured.Format

/-! Data quotation of the original source checkpoint. Rendering bytes into Lean data
is a named trust boundary; applicability still requires ordinary kernel admission.
There is no protocol-specific renderer, alternative source body, or native proof axiom. -/

public meta section
open Lean Zkc.Source.Structured

namespace Zkc.Tools.StructuredSource

deriving instance ToExpr for PIR.Stop
deriving instance ToExpr for Zkc.Source.Structured.DomainSort
deriving instance ToExpr for Zkc.Source.Structured.Nominal
deriving instance ToExpr for Zkc.Source.Structured.Service
deriving instance ToExpr for Zkc.Source.Structured.Catalogue
deriving instance ToExpr for Zkc.Source.Structured.OriginNominalKind
deriving instance ToExpr for Zkc.Source.Structured.OriginTerm
deriving instance ToExpr for Zkc.Source.Structured.ProtocolOrigin
deriving instance ToExpr for Zkc.Source.Structured.FunctionOrigin
deriving instance ToExpr for Zkc.Source.Structured.SourcePlacement
deriving instance ToExpr for Zkc.Source.Structured.SourceField
deriving instance ToExpr for Zkc.Source.Structured.SourceMembers
deriving instance ToExpr for Zkc.Source.Structured.SourceRecord
deriving instance ToExpr for Zkc.Source.Structured.SourcePort
deriving instance ToExpr for Zkc.Source.Structured.SourceProtocol
deriving instance ToExpr for Zkc.Source.Structured.SourceDeclarations
deriving instance ToExpr for Zkc.Source.Structured.Ty, Zkc.Source.Structured.OracleKind,
  Zkc.Source.Structured.ProductFields
deriving instance ToExpr for Zkc.Source.Structured.Kind
deriving instance ToExpr for Zkc.Source.Structured.Visibility
deriving instance ToExpr for Zkc.Source.Structured.Bound
deriving instance ToExpr for Zkc.Source.Structured.DomainConstructor
deriving instance ToExpr for Zkc.Source.Structured.Domain
deriving instance ToExpr for Zkc.Source.Structured.BindingArgument
deriving instance ToExpr for Zkc.Source.Structured.BindingSchema
deriving instance ToExpr for Zkc.Source.Structured.Binding
deriving instance ToExpr for Zkc.Source.Structured.OracleDescriptor
deriving instance ToExpr for Zkc.Source.Structured.PrimitiveParameter
deriving instance ToExpr for Zkc.Source.Structured.Descriptor
deriving instance ToExpr for Zkc.Source.Structured.Terminator
deriving instance ToExpr for Zkc.Source.Structured.Block, Zkc.Source.Structured.Instruction,
  Zkc.Source.Structured.WireRegion
deriving instance ToExpr for Zkc.Source.Structured.ProtocolInterface
deriving instance ToExpr for Zkc.Source.Structured.Function
deriving instance ToExpr for Zkc.Source.Structured.FiniteDeclaration
deriving instance ToExpr for Zkc.Source.Structured.CollectDeclaration
deriving instance ToExpr for Zkc.Source.Structured.RealizationDeclaration
deriving instance ToExpr for Zkc.Source.Structured.MapDeclaration
deriving instance ToExpr for Zkc.Source.Structured.OracleDeclaration
deriving instance ToExpr for Zkc.Source.Structured.Definition
deriving instance ToExpr for Zkc.Source.Structured.Relation
deriving instance ToExpr for Zkc.Source.Structured.ContractDirection
deriving instance ToExpr for Zkc.Source.Structured.ContractSelector
deriving instance ToExpr for Zkc.Source.Structured.RelationApplication
deriving instance ToExpr for Zkc.Source.Structured.ContractKind
deriving instance ToExpr for Zkc.Source.Structured.ContractClause
deriving instance ToExpr for Zkc.Source.Structured.ProtocolContract
deriving instance ToExpr for Zkc.Source.Structured.Snapshot

open Lean.Elab Command

/-- Materialize checked constructor data while retaining all kernel proof fields. -/
elab "source_value% " value:term : term => UnitViews.normalizeTerm value

/-- Quote a literal source checkpoint and check the complete admitted subject.
The literal is part of the module dependency, so changing it invalidates admission.
Generated declaration names are implementation locators, never semantic evidence. -/
elab "import_source " name:ident " from " source:str : command => UnitViews.synchronously do
  let .ok json := Format.parse source.getString
    | throwError "invalid structured-source encoding"
  let .ok snapshot := Format.snapshot json
    | throwError "unsupported structured-source vocabulary"
  let quoted ← liftTermElabM <| Lean.PrettyPrinter.delab (toExpr snapshot)
  let sourceName := mkIdent (name.getId ++ `source)
  let acceptedName := mkIdent (name.getId ++ `accepted)
  UnitViews.emit { command := "source admission" } (← `(def $sourceName : Snapshot := $quoted))
  UnitViews.emit { command := "source admission" } (← `(theorem $acceptedName :
    (check $sourceName).isOk = true := by decide +kernel))
  let checkedName := mkIdent (name.getId ++ `checked)
  let programName := mkIdent (name.getId ++ `program)
  let programExact := mkIdent (name.getId ++ `programExact)
  UnitViews.emit { command := "source admission" } (← `(def $checkedName : Imported $sourceName :=
    Zkc.Verification.Imported.ofIsOk check $sourceName $acceptedName))
  UnitViews.emit { command := "source admission" } (← `(def $programName : Program :=
    source_value% ($checkedName).program))
  UnitViews.emit { command := "source admission" } (← `(theorem $programExact :
    ($checkedName).program = $programName := by kernel_rfl))
  UnitViews.emit { command := "source admission" } (← `(def $name : Imported $sourceName :=
    ⟨$programName, ($checkedName).admitted.trans (congrArg Except.ok $programExact)⟩))

end Zkc.Tools.StructuredSource
