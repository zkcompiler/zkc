module

public import ZkcTools.StructuredSource.Bindings.Generate
public import ZkcTools.StructuredSource.Bindings.Inputs

@[expose] public section

/-! Deterministic attribution data for generated bindings. These records name
proposed proof declarations and exact admitted occurrences. They are not proof
receipts: kernel status is supplied independently by the checking driver. -/

namespace ZkcTools.StructuredSource.Bindings
open Lean Zkc.Source Zkc.Source.Structured
open ZkcTools.StructuredSource.Presentation

def ledgerRow (fields : List (String × Json)) : Json := Json.mkObj fields
def ledgerStrings (values : List String) : Json := toJson values

mutual
  def ledgerRegionOccurrences {inputs outputs : List Ty} (path : String) :
      Region protocolDialect inputs outputs → List Json
    | .ret values => [ledgerRow [("path", toJson path), ("kind", "return"),
        ("operands", toJson (operandsText values))]]
    | .stop reason => [ledgerRow [("path", toJson path), ("kind", "stop"),
        ("reason", toJson (stopText reason))]]
    | .bind body next => ledgerRegionOccurrences (path ++ "/bind") body ++
        ledgerRegionOccurrences (path ++ "/next") next
    | .letOp op args bodies next =>
        ledgerRow [("path", toJson path), ("kind", "operation"),
          ("operation", toJson (protocolOpText op)), ("operands", toJson (operandsText args))] ::
        (ledgerRegionsOccurrences (path ++ "/regions") 0 bodies ++ ledgerRegionOccurrences (path ++ "/next") next)
  def ledgerRegionsOccurrences {signatures : List (List Ty × List Ty)} (path : String) (index : Nat) :
      Regions protocolDialect signatures → List Json
    | .nil => []
    | .cons body rest => ledgerRegionOccurrences (path ++ "/" ++ toString index) body ++
        ledgerRegionsOccurrences path (index + 1) rest
end

/-- Attribution is descriptive and cannot assert a kernel result. Helpers kept
opaque by normalization retain open mathematical obligations, even when their
whole structural invocation equation has been checked. -/
def obligationLedger (program : Program) (output : Output) : Json := Id.run do
  let mut structural : List Json := []
  for (definition, index) in program.payload.protocols.zipIdx do
    if !output.protocols.isEmpty && !output.protocols.contains index then continue
    for role in List.range definition.roles.length do
      if !output.roles.isEmpty && !output.roles.contains role then continue
      let name := output.moduleName ++ "." ++ roleName index role
      structural := structural ++ [ledgerRow [
        ("id", toJson name), ("expected_layer", "I"), ("route", "general-rule"),
        ("proof_status", "external-kernel-receipt-required"),
        ("declarations", ledgerStrings [name ++ "_invocation", name ++ "_certificate"]),
        ("protocol_index", toJson index), ("protocol", toJson definition.name),
        ("signature", toJson (signatureText definition.signature)), ("role", toJson role),
        ("occurrences", toJson (ledgerRegionOccurrences "body" definition.body))]]
  let mathematical := program.payload.definitions.zipIdx.map fun (definition, index) =>
    let projection := match definition.body with | .ret _ => true | _ => false
    ledgerRow [("id", toJson (output.moduleName ++ ".helper" ++ toString index)),
      ("helper_index", toJson index), ("helper", toJson (helperText definition.helper)),
      ("body", toJson (helperRegionText definition.body)),
      ("expected_layer", "I"),
      ("route", if projection then "general-rule" else "unattributed"),
      ("obligation", if projection then "exact-return-projection" else "mathematical-helper-realization"),
      ("proof_status", if projection then "external-kernel-receipt-required" else "open"),
      ("declarations", ledgerStrings [])]
  return ledgerRow [("format", "zkc.component-bindings.obligations/0"),
    ("source", toJson program.snapshot.source), ("entry", toJson program.snapshot.entry),
    ("module", toJson output.moduleName),
    ("attribution_is_proof_status", false),
    ("structural", toJson structural), ("mathematical_helpers", toJson mathematical)]

end ZkcTools.StructuredSource.Bindings
