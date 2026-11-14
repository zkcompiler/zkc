module

public import Zkc.Core.ExpandMeaning
public import Zkc.Core.Flatten
public import Zkc.Core.ProjectMeaning

public section

/-! The statements for a whole definition and for an entry.

**A definition.** `projectProtocol_meaning`: the program of a role of a protocol, run on
the role's inputs, is the protocol's meaning for a side whose only member, among the
protocol's roles, is the role, with the results restricted to the role's values. The
translation of the inputs is `Translation.initial`, and `Agrees.initial` relates the two
initial environments.

**An entry, by expansion.** `expandEntry_meaning`: the expansion of an entry has the
entry's meaning for every side (`Expanded.Sound`). `Expanded.flatten_sound`: so has the
expansion without nested blocks. `projectExpanded_meaning`: the program of a role of a
sound expansion is the entry's meaning for the side with that role alone. In all three, a
site of the expanded definition is read at the site it comes from (`Expanded.label`): the
model reports an effect of a callee at the callee's own site, whatever the application it
was reached through, and the expanded definition has one site number for every path.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

section Definition

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {programs : List RoleHeader}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {called : RoleTable model programs} {callees : ProjectedCallees protocols programs} {role : Nat}

/-- The program of a role of a protocol has the meaning of the protocol for a side with
that role alone. -/
theorem projectProtocol_meaning (sound : CalleesSound model table called callees)
    {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (program : RoleProgram operations functions programs (roleHeader role header))
    (projects : projectProtocol role callees definition = .ok program)
    (identity : Nat) (path : List Nat) (side : Side) (only : side.Only role header.roles)
    (inside : side role = true) (arguments : Values (SideValue model side) header.inputs) :
    program.body.denote (roleMeaning model functionTable called (ownSites identity path))
        (Environment.ofValues (ownValues model side role inside header.inputs arguments)) =
      (definition.meaning model functionTable table identity path side arguments).bind fun values =>
        .done (ownValues model side role inside header.outputs values) := by
  unfold projectProtocol at projects
  split at projects
  · rename_i body projectsBody
    simp only [Except.ok.injEq] at projects
    subst projects
    exact projectRegion_meaning (functionTable := functionTable)
      (label := ownSites identity path) sound only inside definition.body _ body projectsBody _ _
      (Agrees.initial header.inputs arguments)
  · cases projects

/-- The same for the side whose only member is the role. -/
theorem projectProtocol_single (sound : CalleesSound model table called callees)
    {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (program : RoleProgram operations functions programs (roleHeader role header))
    (projects : projectProtocol role callees definition = .ok program)
    (identity : Nat) (path : List Nat)
    (arguments : Values (SideValue model (single role)) header.inputs) :
    program.body.denote (roleMeaning model functionTable called (ownSites identity path))
        (Environment.ofValues
          (ownValues model (single role) role (Side.single_inside role) header.inputs arguments)) =
      (definition.meaning model functionTable table identity path (single role) arguments).bind
        fun values =>
          .done (ownValues model (single role) role (Side.single_inside role) header.outputs values) :=
  projectProtocol_meaning sound definition program projects identity path (single role)
    (Side.only_single role header.roles) (Side.single_inside role) arguments

end Definition

/-! ## An entry, by expansion -/

section Entry

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader}
  (functionTable : FunctionTable model functions)

/-- The site of an effect of an expanded definition, under the applications that reached
the definition: the site its operation has before expansion. -/
def Expanded.label {header : ProtocolHeader} (expanded : Expanded operations functions header)
    (path : List Nat) : Nat → Site :=
  fun site =>
    match expanded.origins[site]? with
    | some origin => origin.siteUnder path
    | none => ⟨path, 0, site⟩

theorem Expanded.labels {header : ProtocolHeader} (expanded : Expanded operations functions header)
    (path : List Nat) : Labels (expanded.label path) path 0 expanded.origins := by
  intro index origin found
  simp only [Expanded.label, Nat.zero_add, found]

/-- The meaning of an expanded definition: its body, which applies nothing, with the
effect of every operation at the site the operation has before expansion. -/
def Expanded.meaning (model : Model) (functionTable : FunctionTable model functions)
    {header : ProtocolHeader} (expanded : Expanded operations functions header) :
    header.Meaning model :=
  fun path side arguments =>
    expanded.body.denote (labelledMeaning model (expanded.label path) functionTable .nil side)
      (Environment.ofValues arguments)

/-- An expansion has the meaning of a protocol: the two are one process for every path
of applications, every side and all inputs. -/
def Expanded.Sound (model : Model) (functionTable : FunctionTable model functions)
    {header : ProtocolHeader} (meaning : header.Meaning model)
    (expanded : Expanded operations functions header) : Prop :=
  ∀ (path : List Nat) (side : Side) (arguments : Values (SideValue model side) header.inputs),
    expanded.meaning model functionTable path side arguments = meaning path side arguments

/-- Expansion keeps the meaning of an entry for every side: the expanded definition,
which applies nothing, is the entry in the model, whose applications run their callees. -/
theorem expandEntry_meaning (identities : Identities)
    (program : Protocols typeTable operations functions protocols)
    (expansions : ExpandedTable operations functions protocols)
    (expands : expandProtocols identities program = .ok expansions) {header : ProtocolHeader}
    (entry : Var protocols header) (expanded : Expanded operations functions header)
    (found : expansions.get entry = some expanded) :
    expanded.Sound model functionTable ((program.table model functionTable identities).get entry) :=
  fun path side arguments =>
    (expandProtocols_sound functionTable identities program expansions expands).body entry
      expanded found path _ (expanded.labels path) side arguments

/-- Expansion as an equality of processes: the meaning of the expanded entry is the
meaning of the entry. An effect of the expansion has the site that the effect has in the
program with applications: the sites of the applications that reached the operation,
then the identity of the operation's definition and the operation's site. -/
theorem expandEntry_equal (identities : Identities)
    (program : Protocols typeTable operations functions protocols)
    (expansions : ExpandedTable operations functions protocols)
    (expands : expandProtocols identities program = .ok expansions) {header : ProtocolHeader}
    (entry : Var protocols header) (expanded : Expanded operations functions header)
    (found : expansions.get entry = some expanded) :
    expanded.meaning model functionTable =
      (program.table model functionTable identities).get entry :=
  funext fun path => funext fun side => funext fun arguments =>
    expandEntry_meaning functionTable identities program expansions expands entry expanded found
      path side arguments

/-- An expansion without nested blocks: the callee's operations stand in the caller's
region. The sites and their origins are unchanged. -/
def Expanded.flatten {header : ProtocolHeader} (expanded : Expanded operations functions header) :
    Expanded operations functions header :=
  ⟨expanded.body.flatten, expanded.origins, expanded.count, expanded.counted, expanded.depth⟩

/-- Removing the nested blocks of an expansion keeps its meaning. -/
theorem Expanded.flatten_sound {header : ProtocolHeader} {meaning : header.Meaning model}
    {expanded : Expanded operations functions header}
    (sound : expanded.Sound model functionTable meaning) :
    expanded.flatten.Sound model functionTable meaning :=
  fun path side arguments =>
    (Region.flatten_denote (labelledMeaning model (expanded.label path) functionTable .nil side)
      expanded.body arguments).trans (sound path side arguments)

/-- The program of a role of an expanded entry. It calls no other role program. -/
def projectExpanded (role : Nat) {header : ProtocolHeader}
    (expanded : Expanded operations functions header) :
    Except ProjectionRefusal (RoleProgram operations functions [] (roleHeader role header)) :=
  match projectRegion role header.roles ProjectedCallees.empty expanded.body
      (Translation.initial role header.inputs) with
  | .ok body => .ok ⟨true, body⟩
  | .error refusal => .error refusal

/-- An expanded definition applies nothing, so its table of callees is sound. -/
theorem CalleesSound.empty :
    CalleesSound model (.nil : ProtocolTable model []) (.nil : RoleTable model [])
      ProjectedCallees.empty :=
  ⟨fun callee => callee.elimNil, fun callee => callee.elimNil⟩

/-- The entry-level statement: for an entry and a role, the role's program of the
expanded entry, run on the role's inputs, is the entry's meaning for the side with that
role alone, restricted to the role's outputs. `meaning` is the entry's meaning in the
model; `expandEntry_meaning` and `Expanded.flatten_sound` give the premise for the
expansion and for the expansion without nested blocks. -/
theorem projectExpanded_meaning {header : ProtocolHeader} {meaning : header.Meaning model}
    {expanded : Expanded operations functions header}
    (sound : expanded.Sound model functionTable meaning) (role : Nat)
    (roleProgram : RoleProgram operations functions [] (roleHeader role header))
    (projects : projectExpanded role expanded = .ok roleProgram) (path : List Nat)
    (arguments : Values (SideValue model (single role)) header.inputs) :
    roleProgram.body.denote (roleMeaning model functionTable .nil (expanded.label path))
        (Environment.ofValues
          (ownValues model (single role) role (Side.single_inside role) header.inputs arguments)) =
      (meaning path (single role) arguments).bind fun values =>
        .done (ownValues model (single role) role (Side.single_inside role) header.outputs values) := by
  unfold projectExpanded at projects
  split at projects
  · rename_i body projectsBody
    simp only [Except.ok.injEq] at projects
    subst projects
    have projected := projectRegion_meaning (functionTable := functionTable)
      (label := expanded.label path) CalleesSound.empty (Side.only_single role header.roles)
      (Side.single_inside role) expanded.body _ body projectsBody _ _
      (Agrees.initial header.inputs arguments)
    have same := sound path (single role) arguments
    unfold Expanded.meaning at same
    rw [same] at projected
    exact projected
  · cases projects

/-- The pipeline of the tool for one entry and one role: expand, remove nested blocks,
project. The role's program is the entry's meaning for the side with that role alone. -/
theorem projectEntry_meaning (identities : Identities)
    (program : Protocols typeTable operations functions protocols)
    (expansions : ExpandedTable operations functions protocols)
    (expands : expandProtocols identities program = .ok expansions) {header : ProtocolHeader}
    (entry : Var protocols header) (expanded : Expanded operations functions header)
    (found : expansions.get entry = some expanded) (role : Nat)
    (roleProgram : RoleProgram operations functions [] (roleHeader role header))
    (projects : projectExpanded role expanded.flatten = .ok roleProgram) (path : List Nat)
    (arguments : Values (SideValue model (single role)) header.inputs) :
    roleProgram.body.denote (roleMeaning model functionTable .nil (expanded.label path))
        (Environment.ofValues
          (ownValues model (single role) role (Side.single_inside role) header.inputs arguments)) =
      (((program.table model functionTable identities).get entry) path (single role)
        arguments).bind fun values =>
        .done (ownValues model (single role) role (Side.single_inside role) header.outputs values) :=
  projectExpanded_meaning functionTable
    (Expanded.flatten_sound functionTable
      (expandEntry_meaning functionTable identities program expansions expands entry expanded found))
    role roleProgram projects path arguments

end Entry

end Zkc.Core
