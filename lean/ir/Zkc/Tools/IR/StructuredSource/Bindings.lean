module

public import Zkc.IR.Source.Structured.UnitViews
public import Zkc.Tools.IR.StructuredSource.Quotation
public meta import Lean.PrettyPrinter.Delaborator
public meta import Zkc.IR.Source.Structured.UnitViews

/-! Checked presentations of actual admitted declarations. The caller supplies only a lookup
name. Full signatures, typed bodies and membership equations come from the admitted source;
mathematical laws cannot replace them with a similarly named implementation. -/

public meta section
open Lean Meta Elab Command Term
open Zkc.Source Zkc.Source.Structured

namespace Zkc.Tools.StructuredSource

elab "source_helper " name:ident " from " imported:term " named " symbol:str : command =>
    UnitViews.synchronously do
  let lookup ← `((($imported).program.payload.definitions).find?
    (fun definition => definition.name == $symbol))
  let selected ← liftTermElabM do
    let value ← UnitViews.normalizeTerm lookup
    let_expr Option.some _ definition := value
      | throwError "no admitted helper named {symbol.getString}"
    return definition
  let helper ← liftTermElabM do
    let signature ← mkAppM ``CheckedDefinition.helper #[selected]
    Lean.PrettyPrinter.delab (← UnitViews.normalize signature)
  let body ← `(source_value% (Option.get $lookup (by decide +kernel)).body)
  let signatureName := mkIdent (name.getId ++ `signature)
  let bodyName := mkIdent (name.getId ++ `body)
  let selectedName := mkIdent (name.getId ++ `selected)
  let memberName := mkIdent (name.getId ++ `member)
  let associationName := mkIdent (name.getId ++ `association)
  UnitViews.emit { command := "source binding" } (← `(abbrev $signatureName : Helper := $helper))
  UnitViews.emit { command := "source binding" } (← `(def $bodyName :
    Region dialect ($signatureName).inputs ($signatureName).outputs := $body))
  UnitViews.emit { command := "source binding" } (← `(def $name : CheckedDefinition :=
    CheckedDefinition.ofBody $signatureName $bodyName))
  UnitViews.emit { command := "source binding" } (← `(theorem $selectedName :
    $lookup = some $name := by kernel_rfl))
  UnitViews.emit { command := "source binding" } (← `(theorem $memberName :
    $name ∈ ($imported).program.payload.definitions :=
    List.mem_of_find?_eq_some $selectedName))
  UnitViews.emit { command := "source binding" } (← `(theorem $associationName :
    BodyIn ($imported).program.payload.definitions $signatureName $bodyName :=
      BodyIn.of_mem $memberName rfl rfl))

elab "source_protocol " name:ident " from " imported:term " named " symbol:str : command =>
    UnitViews.synchronously do
  let lookup ← `((($imported).program.payload.protocols).find?
    (fun definition => definition.name == $symbol))
  let selected ← liftTermElabM do
    let value ← UnitViews.normalizeTerm lookup
    let_expr Option.some _ definition := value
      | throwError "no admitted protocol named {symbol.getString}"
    return definition
  let signature ← liftTermElabM do
    Lean.PrettyPrinter.delab (← UnitViews.normalize
      (← mkAppM ``CheckedProtocol.signature #[selected]))
  let body ← `(source_value% (Option.get $lookup (by decide +kernel)).body)
  let signatureName := mkIdent (name.getId ++ `signature)
  let bodyName := mkIdent (name.getId ++ `body)
  let selectedName := mkIdent (name.getId ++ `selected)
  let memberName := mkIdent (name.getId ++ `member)
  UnitViews.emit { command := "source binding" } (← `(abbrev $signatureName :
    ProtocolSignature := $signature))
  UnitViews.emit { command := "source binding" } (← `(def $bodyName :
    Region protocolDialect ($signatureName).inputs ($signatureName).outputs := $body))
  UnitViews.emit { command := "source binding" } (← `(def $name : CheckedProtocol :=
    CheckedProtocol.ofBody $signatureName $bodyName))
  UnitViews.emit { command := "source binding" } (← `(theorem $selectedName :
    $lookup = some $name := by kernel_rfl))
  UnitViews.emit { command := "source binding" } (← `(theorem $memberName :
    $name ∈ ($imported).program.payload.protocols :=
    List.mem_of_find?_eq_some $selectedName))

end Zkc.Tools.StructuredSource
