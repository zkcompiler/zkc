module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.RepeatServiceData
public import ZkcExamples.Structured.RepeatServiceBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.RepeatServiceViews
open Zkc.Source Zkc.Source.Structured RepeatServiceBodies

set_option smartUnfolding false

structured_views RepeatServiceData.snapshot
  helpers []
  protocols [draw, run]

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
