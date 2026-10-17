module

public import ZkcExamples.Structured.RepeatServiceData
public import ZkcExamples.Structured.RepeatServiceBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.RepeatServiceViews
open Zkc.Source Zkc.Source.Structured RepeatServiceBodies

set_option smartUnfolding false

def drawDefinition : CheckedProtocol where
  toProtocolSignature := drawSignature
  raw := drawBody.erase
  body := drawBody
  formed := drawBody.elaborate_erase

theorem draw_signature : drawDefinition.signature = drawSignature := rfl
theorem draw_raw : drawDefinition.raw = drawBody.erase := rfl
theorem draw_body : drawDefinition.body = drawBody := rfl

def runDefinition : CheckedProtocol where
  toProtocolSignature := runSignature
  raw := runBody.erase
  body := runBody
  formed := runBody.elaborate_erase

theorem run_signature : runDefinition.signature = runSignature := rfl
theorem run_raw : runDefinition.raw = runBody.erase := rfl
theorem run_body : runDefinition.body = runBody := rfl

def definitions : List CheckedDefinition :=
  []

def ordered : List OrderedDefinition :=
  []

def headers : List ProtocolSignature := [runSignature, drawSignature]

def domains : List DomainSpec := []

def summaries : IdentitySummaries := []

def unit : UnitPayload where
  definitions := definitions
  protocols := [drawDefinition, runDefinition]
  entryIndex := ⟨1, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨RepeatServiceData.snapshot, unit⟩

theorem headers_checked : checkUnitHeaders RepeatServiceData.snapshot =
    .ok (domains, headers, summaries) := rfl

theorem helpers_checked : checkUnitHelpers RepeatServiceData.snapshot domains summaries = .ok ordered := rfl

theorem protocols_checked :
    checkUnitProtocols RepeatServiceData.snapshot domains summaries headers ordered = .ok unit.protocols := rfl

theorem native_metadata_checked :
    (checkNativeApplicationBudgets RepeatServiceData.snapshot).isOk = true := by decide +kernel

theorem effective_sites_checked :
    checkEffectiveProtocolSites RepeatServiceData.snapshot = .ok () := rfl

theorem metadata_checked : checkApplicationMetadata RepeatServiceData.snapshot = .ok () :=
  checkApplicationMetadata_of_checks native_metadata_checked effective_sites_checked

theorem payload_linked : linkUnitPayload RepeatServiceData.snapshot ordered unit.protocols = .ok unit := rfl

/-- All declarations, callback trees and metadata phases of the original unit. -/
theorem kernel_admission : check RepeatServiceData.snapshot = .ok program :=
  check_parts _ unit (check_payload_of_phases headers_checked helpers_checked
    protocols_checked metadata_checked payload_linked)

def imported : Imported RepeatServiceData.snapshot := ⟨program, kernel_admission⟩

theorem exact_subject : program.snapshot = RepeatServiceData.snapshot := imported.exactSubject

theorem draw_member : drawDefinition ∈ unit.protocols := List.mem_cons_self

theorem run_member : runDefinition ∈ unit.protocols := List.mem_cons_of_mem _ (List.mem_cons_self)

theorem entry_selection : unit.entry = runDefinition := rfl
theorem entry_signature : program.payload.entry.signature = runSignature := rfl
theorem entry_raw : program.payload.entry.raw = runBody.erase := rfl

/-- Complete original-to-checked association includes every nested callback. -/
theorem complete_protocol_source (definition : CheckedProtocol)
    (member : definition ∈ unit.protocols) :
    ∃ function domains signatures summaries,
      .function function ∈ RepeatServiceData.snapshot.definitions ∧
      function.kind = .protocol ∧
      checkUnitHeaders RepeatServiceData.snapshot = .ok (domains, signatures, summaries) ∧
      checkProtocol RepeatServiceData.snapshot domains summaries function signatures = .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol RepeatServiceData.snapshot domains summaries signatures function
        definition.signature = .ok definition.raw :=
  imported.protocolSource member

/-- Every original protocol is admitted to one exact checked tree. -/
theorem complete_original_protocol (function : Zkc.Source.Structured.Function)
    (member : .function function ∈ RepeatServiceData.snapshot.definitions)
    (kind : function.kind = .protocol) :
    ∃ domains headers summaries,
      checkUnitHeaders RepeatServiceData.snapshot = .ok (domains, headers, summaries) ∧
      ∃ definition, definition ∈ unit.protocols ∧
        checkProtocol RepeatServiceData.snapshot domains summaries function headers = .ok definition ∧
        ∀ other, other ∈ unit.protocols →
          checkProtocol RepeatServiceData.snapshot domains summaries function headers = .ok other →
            other = definition :=
  imported.protocolChecked member kind

/-- The complete checked Run tree contains this application inside its repeat callback. -/
theorem callback_application_occurs :
    .protocolApply drawSignature [0, 1] "s7" ∈ runDefinition.raw.operations := by
  rw [run_raw]
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))

/-- The actual retained repeat operands and prefix result origins transfer the
first and second service inputs to callback positions three and four. -/
theorem callback_origin_transfer :
    (let original : Zkc.Source.Structured.Function :=
       RepeatServiceData.snapshot.protocolFunctions[0]
     let instructions : List Instruction := original.body.topLevelInstructions
     let origins : List (Option Nat) := (instructions.take 3).foldl
       (fun origins (.instruction _ _ results _ _) =>
         List.replicate results.length none ++ origins)
       ((List.range original.inputs.length).map some)
     match (instructions[3]? : Option Instruction) with
     | Option.some (Instruction.instruction (.protocolRepeat ..) operands _ _ _) =>
         repeatOrigins repeatSpec operands origins
     | _ => []) = [none, none, none, some 1, some 2] := rfl

/-- Recursive inversion supplies an inherited lexical environment in which each
service operand names a bounded original input with its contract and mapped owner.
The existential statement does not distinguish the two same-contract inputs;
callback_origin_transfer and the process equations establish their actual routing. -/
theorem callback_service_origins :
    ∃ function domains headers summaries interface context,
    ∃ origins : List (Option Nat), ∃ name roles operands,
      .function function ∈ RepeatServiceData.snapshot.definitions ∧ function.kind = .protocol ∧
      checkUnitHeaders RepeatServiceData.snapshot = .ok (domains, headers, summaries) ∧
      checkProtocol RepeatServiceData.snapshot domains summaries function headers = .ok runDefinition ∧
      function.interface = some interface ∧ runDefinition.roles = interface.roles ∧
      validProtocolIdentifier "s7" = true ∧
      resolveProtocolApplication RepeatServiceData.snapshot headers interface name roles =
        .ok (drawSignature, [0, 1]) ∧
      typesAt context operands = .ok drawSignature.inputs ∧
      (∀ type scope operand, ((type, scope), operand) ∈
          (drawSignature.inputs.zip drawSignature.inputScopes).zip operands → type.isService = true →
        ∃ input, origins[operand]? = some (some input) ∧ input < function.inputs.length ∧
          function.inputs[input]? = some type ∧
          (scope.map (fun role => [0, 1][role]?.getD 0)).length = 1 ∧
          runDefinition.inputScopes[input]? = some (scope.map (fun role => [0, 1][role]?.getD 0))) :=
  by
    obtain ⟨function, domains, headers, summaries, interface, context, origins, name, roles,
      operands, _, _, retained, kind, headerEq, checked, interfaceEq, roster, validSite, resolved,
      types, services⟩ := imported.protocolApplication_source run_member callback_application_occurs
    exact ⟨function, domains, headers, summaries, interface, context, origins, name, roles,
      operands, retained, kind, headerEq, checked, interfaceEq, roster, validSite, resolved,
      types, services⟩

/-- Source membership is in the full recursive instruction inventory, at the exact site. -/
theorem callback_original_instruction :
    ∃ function domains headers summaries interface context,
    ∃ origins : List (Option Nat), ∃ name roles operands regions,
      .instruction (.protocolApply name roles) operands drawSignature.outputs regions "s7" ∈
        function.body.storedInstructions ∧
      .function function ∈ RepeatServiceData.snapshot.definitions ∧ function.kind = .protocol ∧
      checkUnitHeaders RepeatServiceData.snapshot = .ok (domains, headers, summaries) ∧
      checkProtocol RepeatServiceData.snapshot domains summaries function headers = .ok runDefinition ∧
      function.interface = some interface ∧ runDefinition.roles = interface.roles ∧
      validProtocolIdentifier "s7" = true ∧
      resolveProtocolApplication RepeatServiceData.snapshot headers interface name roles =
        .ok (drawSignature, [0, 1]) ∧
      typesAt context operands = .ok drawSignature.inputs ∧
      (∀ type scope operand, ((type, scope), operand) ∈
          (drawSignature.inputs.zip drawSignature.inputScopes).zip operands → type.isService = true →
        ∃ input, origins[operand]? = some (some input) ∧ input < function.inputs.length ∧
          function.inputs[input]? = some type ∧
          (scope.map (fun role => [0, 1][role]?.getD 0)).length = 1 ∧
          runDefinition.inputScopes[input]? = some (scope.map (fun role => [0, 1][role]?.getD 0))) :=
  imported.protocolApplication_source run_member callback_application_occurs

theorem callback_roles :
    [0, 1].length = drawSignature.roles.length ∧
      (∀ role ∈ [0, 1], role < runDefinition.roles.length) ∧ [0, 1].Nodup :=
  imported.protocolApplication_roles run_member callback_application_occurs

theorem callback_callee :
    ∃ name function instructions terminal,
      lookupDefinition RepeatServiceData.snapshot name = .ok (.function function) ∧
      (Definition.function function).acceptsEdge .protocolApply = true ∧
      resolveProtocolSignature function = .ok drawSignature ∧
      function.body = .block instructions terminal ∧
      instructions.any (fun (.instruction descriptor _ _ _ _) =>
        match descriptor with | .statement .. => true | _ => false) = false :=
  imported.protocolApplication_callee run_member callback_application_occurs

/-- Every stored level of the admitted source callee is statement free. -/
theorem callback_callee_statement_free :
    ∃ name function,
      lookupDefinition RepeatServiceData.snapshot name = .ok (.function function) ∧
      (Definition.function function).acceptsEdge .protocolApply = true ∧
      resolveProtocolSignature function = .ok drawSignature ∧
      function.body.storedInstructions.any Instruction.isStatement = false :=
  imported.protocolApplication_callee_statementFree run_member callback_application_occurs

end ZkcExamples.Structured.RepeatServiceViews
