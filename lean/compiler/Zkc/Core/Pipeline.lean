module

public import Zkc.Core.Entry
public import Zkc.Core.RoleSyntax

public section

/-! The steps of the tool after elaboration, as functions from a typed package to raw
syntax: the expansion of the entry, the role programs of the expanded entry, and the
role programs of every protocol with applications kept as calls.

The entry of a package is its last protocol. The compiled tool prints the results of
these functions, and the kernel evaluates the same functions in the per-package checks.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

inductive PipelineRefusal where
  /-- The package has no protocol. -/
  | noEntry
  /-- The entry is specification-only. -/
  | specificationOnlyEntry
  | expansion (refusal : ExpandRefusal)
  | projection (refusal : ProjectionRefusal)
  /-- The expanded entry violates a residual condition. -/
  | residual (violation : Violation)
  deriving Repr

section Entry

variable {typeTable : TypeTable} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- The expansion of the last protocol of a program, with the callees' expansions as
nested blocks. -/
def expandLast :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      Except PipelineRefusal ((header : ProtocolHeader) × Expanded operations functions header)
  | _, .nil => .error .noEntry
  | _, .snoc (header := header) earlier definition wellFormed =>
      match expandProtocols Identities.written (.snoc earlier definition wellFormed) with
      | .error refusal => .error (.expansion refusal)
      | .ok table =>
          match table.get .here with
          | some expanded => .ok ⟨header, expanded⟩
          | none => .error .specificationOnlyEntry

/-- The header of an expanded entry: the entry's, deployed. -/
@[reducible] def ProtocolHeader.deployed (header : ProtocolHeader) : ProtocolHeader :=
  ⟨header.roles, header.inputs, header.outputs, header.agreements, false⟩

/-- An expanded entry as a definition that applies no protocol. -/
def Expanded.definition {header : ProtocolHeader} (expanded : Expanded operations functions header) :
    ProtocolDefinition operations functions [] header.deployed :=
  ⟨expanded.body⟩

/-- The raw syntax of an expanded entry. -/
def Expanded.raw (functionCount : Nat) {header : ProtocolHeader}
    (expanded : Expanded operations functions header) : Raw.Protocol :=
  unelaborateProtocol functionCount 0 expanded.definition

/-- The programs of the roles below `count` of an expanded entry, before `later`. -/
def projectRoles (functionCount : Nat) {header : ProtocolHeader}
    (expanded : Expanded operations functions header) :
    (count : Nat) → List Raw.RoleProgram → Except PipelineRefusal (List Raw.RoleProgram)
  | 0, later => .ok later
  | role + 1, later =>
      match projectExpanded role expanded with
      | .error refusal => .error (.projection refusal)
      | .ok program =>
          projectRoles functionCount expanded role
            (unelaborateRoleProgram functionCount 0 0 role program :: later)

end Entry

/-- The expansion of the entry of a package, with the callees' expansions as nested
blocks. -/
def Typed.expandEntryNested (typed : Typed) :
    Except PipelineRefusal
      ((header : ProtocolHeader) × Expanded (typed.table.map (·.signature)) typed.functions header) :=
  expandLast typed.program.protocols

/-- The expansion of the entry of a package: one region without nested blocks. -/
def Typed.expandEntry (typed : Typed) :
    Except PipelineRefusal
      ((header : ProtocolHeader) × Expanded (typed.table.map (·.signature)) typed.functions header) :=
  match typed.expandEntryNested with
  | .error refusal => .error refusal
  | .ok ⟨header, expanded⟩ => .ok ⟨header, expanded.flatten⟩

/-- The expanded entry of a package, as raw syntax, when it has no residual violation. -/
def Typed.expandedProtocol (typed : Typed) : Except PipelineRefusal Raw.Protocol :=
  match typed.expandEntry with
  | .error refusal => .error refusal
  | .ok ⟨_, expanded⟩ =>
      match expanded.definition.violation typed.typeTable with
      | none => .ok (expanded.raw typed.functions.length)
      | some violation => .error (.residual violation)

/-- The role programs of the expanded entry of a package, in role order. -/
def Typed.entryRoles (typed : Typed) : Except PipelineRefusal (List Raw.RoleProgram) :=
  match typed.expandEntry with
  | .error refusal => .error refusal
  | .ok ⟨header, expanded⟩ => projectRoles typed.functions.length expanded header.roles []

/-- The role programs of every protocol of a package, with applications kept as calls. -/
def Typed.calledRoles (typed : Typed) : Except PipelineRefusal (List Raw.RoleProgram) :=
  match projectProtocols typed.program.protocols with
  | .error refusal => .error (.projection refusal)
  | .ok projected =>
      .ok (unelaborateRolePrograms typed.functions.length projected.headers.length
        projected.programs [])

end Zkc.Core
