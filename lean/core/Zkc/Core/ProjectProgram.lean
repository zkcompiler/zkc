module

public import Zkc.Core.Project

public section

/-! Projection of a whole program, keeping applications as calls.

Every protocol has one role program per formal role. The programs are listed in program
order, a protocol's programs after those of the protocols it may apply, so a role
program is typed over the headers of the role programs before it and a `call` names its
callee by position. Nothing is expanded: an `apply` of the protocol becomes, for the role
that the role map assigns to a formal role, one `call` of the callee's program of that
formal role. A role outside the role map gets no operation: a protocol does nothing for a
side without any of its roles (`Zkc.Core.program_idle`).
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The role programs of a program in order, each typed over the headers of the earlier
ones. Each records the number of its protocol and its role. -/
inductive RolePrograms (operations : List OperationSignature) (functions : List FunctionHeader) :
    List RoleHeader → Type where
  | nil : RolePrograms operations functions []
  | snoc {programs : List RoleHeader} {header : RoleHeader}
      (earlier : RolePrograms operations functions programs) (definition role : Nat)
      (program : RoleProgram operations functions programs header) :
      RolePrograms operations functions (header :: programs)

/-- The most recent entry is at the level of the old depth. -/
theorem atLevel?_recent {β : Type} (Δ : List β) (head : β) :
    atLevel? (head :: Δ) (Δ.length + 1) Δ.length = some head := by
  have position : Δ.length + 1 - 1 - Δ.length = 0 := by omega
  simp only [atLevel?, Nat.lt_succ_self, ↓reduceIte, position]
  rfl

section Program

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- The programs so far, among them those of the formal roles `next`, `next + 1`, … of
one protocol, whose levels are listed in that order. -/
structure Formals (operations : List OperationSignature) (functions : List FunctionHeader)
    (protocols : List ProtocolHeader) (header : ProtocolHeader) (next : Nat) where
  headers : List RoleHeader
  programs : RolePrograms operations functions headers
  callees : ProjectedCallees protocols headers
  levels : List Nat
  valid : ∀ (index level : Nat), levels[index]? = some level →
    atLevel? headers callees.depth level = some (roleHeader (next + index) header)

/-- The programs of the formal roles below `remaining`, from the highest down. Each is
projected over the callees' programs and is not a callee of the others. -/
@[expose] def projectFormals {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) :
    (remaining : Nat) → Formals operations functions protocols header remaining →
      Except ProjectionRefusal (Formals operations functions protocols header 0)
  | 0, state => .ok state
  | formal + 1, ⟨headers, programs, callees, levels, valid⟩ =>
      match projectProtocol formal callees definition with
      | .error refusal => .error refusal
      | .ok program =>
          projectFormals definition formal
            ⟨roleHeader formal header :: headers, .snoc programs protocols.length formal program,
              callees.weaken _, callees.depth :: levels, fun index level found => by
                cases index with
                | zero =>
                    have same : callees.depth = level := Option.some.inj found
                    subst same
                    show atLevel? (_ :: headers) (callees.depth + 1) callees.depth = _
                    rw [callees.counted]
                    exact atLevel?_recent headers _
                | succ index =>
                    have earlier := valid index level found
                    rw [Nat.add_assoc, Nat.add_comm 1 index] at earlier
                    exact atLevel?_cons headers _ earlier⟩

/-- The role programs of the protocols of a program, with the table that names them. -/
structure Projected (operations : List OperationSignature) (functions : List FunctionHeader)
    (protocols : List ProtocolHeader) where
  headers : List RoleHeader
  programs : RolePrograms operations functions headers
  callees : ProjectedCallees protocols headers

/-- The projection of every protocol of a program to every one of its roles. -/
@[expose] def projectProtocols {typeTable : TypeTable} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      Except ProjectionRefusal (Projected operations functions protocols)
  | _, .nil => .ok ⟨[], .nil, .empty⟩
  | _, .snoc (header := header) earlier definition _ =>
      match projectProtocols earlier with
      | .error refusal => .error refusal
      | .ok ⟨headers, programs, callees⟩ =>
          match projectFormals definition header.roles
              ⟨headers, programs, callees, [], fun _ _ found => nomatch found⟩ with
          | .error refusal => .error refusal
          | .ok ⟨headers, programs, callees, levels, valid⟩ =>
              .ok ⟨headers, programs,
                callees.extend header levels fun formal level found => by
                    have at_ := valid formal level found
                    rwa [Nat.zero_add] at at_⟩

end Program

end Zkc.Core
