module

public import Zkc.Core.Entry
public import Zkc.Core.ProjectProgram
public import Zkc.Core.Idle

public section

/-! The program-level statement for projection that keeps applications as calls.

`projectProtocols_sound`: for every protocol of a program and every formal role, the role
program that the table names has the meaning of the protocol for a side with that role
alone, restricted to the role's values; and every protocol returns without an effect for a
side without any of its roles. The proof is an induction over the protocols of the
program. For one protocol the programs of its formal roles are added one at a time; the
invariant `FormalsSound` says that the table of the callees stays sound when the list of
role programs grows and that the programs added so far have the protocol's meaning. That
a protocol does nothing for a side without its roles follows from its shape
(`program_idle`).

The meaning of a role program reports an effect at a site of its own protocol: no site is
renumbered; a called program reports the path of the calls that reached it.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

section Table

variable {protocols : List ProtocolHeader} {programs : List RoleHeader}

namespace ProjectedCallees

theorem level_lt (table : ProjectedCallees protocols programs) {header : ProtocolHeader}
    (callee : Var protocols header) {formal level : Nat}
    (found : table.level? callee.index formal = some level) : level < table.depth := by
  have image := table.level?_valid callee found
  unfold atLevel? at image
  split at image
  · assumption
  · cases image

/-- The table names a program exactly when it records a level for it. -/
theorem find_eq_some_iff (table : ProjectedCallees protocols programs) {header : ProtocolHeader}
    (callee : Var protocols header) (formal : Nat)
    (program : Var programs (roleHeader formal header)) :
    table.find callee formal = some program ↔
      ∃ level, table.level? callee.index formal = some level ∧
        program.index = table.depth - 1 - level := by
  unfold find
  split
  · rename_i missing
    constructor
    · intro found; cases found
    · rintro ⟨level, found, _⟩
      rw [missing] at found
      cases found
  · rename_i level found
    constructor
    · intro same
      exact ⟨level, found, by rw [← Option.some.inj same]⟩
    · rintro ⟨other, at_, index⟩
      have same : level = other := Option.some.inj (found.symm.trans at_)
      subst same
      exact congrArg some (Var.ext index.symm)

theorem level?_weaken (table : ProjectedCallees protocols programs) (added : RoleHeader)
    (index formal : Nat) : (table.weaken added).level? index formal = table.level? index formal :=
  rfl

theorem level?_extend_zero (table : ProjectedCallees protocols programs) (header : ProtocolHeader)
    (levels : List Nat)
    (valid : ∀ (formal level : Nat), levels[formal]? = some level →
      atLevel? programs table.depth level = some (roleHeader formal header)) (formal : Nat) :
    (table.extend header levels valid).level? 0 formal = levels[formal]? := by
  unfold level? extend
  simp only [Sequence.get?_eq, Sequence.toList_push, List.getElem?_cons_zero]

theorem level?_extend_succ (table : ProjectedCallees protocols programs) (header : ProtocolHeader)
    (levels : List Nat)
    (valid : ∀ (formal level : Nat), levels[formal]? = some level →
      atLevel? programs table.depth level = some (roleHeader formal header)) (index formal : Nat) :
    (table.extend header levels valid).level? (index + 1) formal =
      table.level? index formal := by
  unfold level? extend
  simp only [Sequence.get?_eq, Sequence.toList_push, List.getElem?_cons_succ]

end ProjectedCallees

end Table

section Meaning

variable (model : Model) {operations : List OperationSignature} {functions : List FunctionHeader}
  (functionTable : FunctionTable model functions)

/-- The meanings of the role programs, most recent first. A program reports its effects
at the sites of its own protocol, by the protocol's identity. -/
@[expose] def RolePrograms.table (identities : Identities) :
    {programs : List RoleHeader} → RolePrograms operations functions programs →
      RoleTable model programs
  | _, .nil => .nil
  | _, .snoc earlier definition _ program =>
      .cons
        (fun path arguments =>
          program.body.denote
            (roleMeaning model functionTable (earlier.table identities)
              (ownSites (identities definition) path))
            (Environment.ofValues arguments))
        (earlier.table identities)

variable {model} {functionTable} {protocols : List ProtocolHeader}
  {table : ProtocolTable model protocols}

/-- The table of callees stays sound when one more role program is added. -/
theorem CalleesSound.weaken {programs : List RoleHeader} {called : RoleTable model programs}
    {callees : ProjectedCallees protocols programs}
    (sound : CalleesSound model table called callees) (added : RoleHeader)
    (meaning : RoleHeader.Meaning model added) :
    CalleesSound model table (.cons meaning called) (callees.weaken added) := by
  refine ⟨fun {header} callee formal program found path side only inside arguments => ?_,
    fun {header} callee => sound.silent callee⟩
  obtain ⟨level, at_, index⟩ := ((callees.weaken added).find_eq_some_iff callee formal program).mp found
  have below := callees.level_lt callee at_
  have valid := callees.level?_valid callee at_
  have earlierValid : programs[callees.depth - 1 - level]? = some (roleHeader formal header) := by
    unfold atLevel? at valid
    simpa only [below, ↓reduceIte] using valid
  have same : program = (Var.mk (callees.depth - 1 - level) earlierValid).there := by
    apply Var.ext
    show program.index = callees.depth - 1 - level + 1
    rw [index]
    show callees.depth + 1 - 1 - level = _
    omega
  subst same
  exact sound.program callee formal ⟨callees.depth - 1 - level, earlierValid⟩
    ((callees.find_eq_some_iff callee formal _).mpr ⟨level, at_, rfl⟩) path side only inside
    arguments

/-- The programs so far are sound: the table of the callees is, and each program of the
protocol added so far has the protocol's meaning for a side with its formal role alone. -/
structure FormalsSound (model : Model) (functionTable : FunctionTable model functions)
    (table : ProtocolTable model protocols) (identities : Identities) {header : ProtocolHeader}
    (meaning : header.Meaning model) {next : Nat}
    (state : Formals operations functions protocols header next) : Prop where
  callees : CalleesSound model table (state.programs.table model functionTable identities)
    state.callees
  formals : ∀ (index level : Nat), state.levels[index]? = some level →
    ∀ (role : Nat), role = next + index →
    ∀ (program : Var state.headers (roleHeader role header)),
      program.index = state.callees.depth - 1 - level →
      ∀ (path : List Nat) (side : Side), side.Only role header.roles →
      ∀ (inside : side role = true) (arguments : Values (SideValue model side) header.inputs),
        (state.programs.table model functionTable identities).get program path
            (ownValues model side role inside header.inputs arguments) =
          (meaning path side arguments).bind fun values =>
            .done (ownValues model side role inside header.outputs values)

/-- Adding the programs of the remaining formal roles keeps the programs sound. -/
theorem projectFormals_sound (identities : Identities) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) :
    ∀ (remaining : Nat) (state : Formals operations functions protocols header remaining)
      (result : Formals operations functions protocols header 0),
      projectFormals definition remaining state = .ok result →
      FormalsSound model functionTable table identities
          (definition.meaning model functionTable table (identities protocols.length)) state →
        FormalsSound model functionTable table identities
          (definition.meaning model functionTable table (identities protocols.length)) result
  | 0, state, result, projects, sound => by
      simp only [projectFormals, Except.ok.injEq] at projects
      exact projects ▸ sound
  | formal + 1, ⟨headers, programs, callees, levels, valid⟩, result, projects, sound => by
      unfold projectFormals at projects
      split at projects
      · cases projects
      · rename_i program projectsRole
        refine projectFormals_sound identities definition formal _ result projects ⟨?_, ?_⟩
        · exact sound.callees.weaken _ _
        · intro index level found role known candidate at_ path side only inside arguments
          cases index with
          | zero =>
              have sameLevel : callees.depth = level := Option.some.inj found
              subst sameLevel
              subst known
              have here : candidate = Var.here := by
                apply Var.ext
                rw [at_]
                show callees.depth + 1 - 1 - callees.depth = 0
                omega
              subst here
              exact projectProtocol_meaning sound.callees definition program projectsRole _ path side
                only inside arguments
          | succ index =>
              have earlierFound : levels[index]? = some level := found
              have earlierValid := valid index level earlierFound
              have below : level < callees.depth := by
                unfold atLevel? at earlierValid
                split at earlierValid
                · assumption
                · cases earlierValid
              have sameRole : role = formal + 1 + index := by omega
              subst sameRole
              have position : headers[callees.depth - 1 - level]? =
                  some (roleHeader (formal + 1 + index) header) := by
                unfold atLevel? at earlierValid
                simpa only [below, ↓reduceIte] using earlierValid
              have there : candidate = (Var.mk (callees.depth - 1 - level) position).there := by
                apply Var.ext
                rw [at_]
                show callees.depth + 1 - 1 - level = callees.depth - 1 - level + 1
                omega
              subst there
              exact sound.formals index level earlierFound _ rfl ⟨_, position⟩ rfl path side only
                inside arguments

end Meaning

/-! ## Every program -/

section Program

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {functionTable : FunctionTable model functions} {protocols : List ProtocolHeader}

/-- The program-level statement: every role program that projection produces for a
program has the meaning of its protocol for a side with its role alone, and every protocol
returns without an effect for a side without any of its roles. -/
theorem projectProtocols_sound {typeTable : TypeTable} (identities : Identities) :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols)
      (projected : Projected operations functions protocols),
      projectProtocols program = .ok projected →
        CalleesSound model (program.table model functionTable identities)
          (projected.programs.table model functionTable identities) projected.callees
  | _, .nil, projected, projects => by
      simp only [projectProtocols, Except.ok.injEq] at projects
      subst projects
      exact ⟨fun callee => callee.elimNil, fun callee => callee.elimNil⟩
  | _, .snoc (header := header) earlier definition wellFormed, projected, projects => by
      unfold projectProtocols at projects
      split at projects
      · cases projects
      · rename_i headers programs callees projectsEarlier
        have earlierSound := projectProtocols_sound identities earlier ⟨headers, programs, callees⟩
          projectsEarlier
        split at projects
        · cases projects
        · rename_i finalHeaders finalPrograms finalCallees levels valid projectsFormals
          simp only [Except.ok.injEq] at projects
          subst projects
          have sound := projectFormals_sound (model := model) (functionTable := functionTable)
            (table := earlier.table model functionTable identities) identities definition
            header.roles _ _ projectsFormals
            ⟨earlierSound, fun _ _ found => nomatch found⟩
          refine ⟨fun {other} callee => ?_, fun {other} callee path side absent arguments =>
            program_idle functionTable identities (.snoc earlier definition wellFormed) callee path
              side (fun role below => absent role (Nat.blt_eq.mpr below)) arguments⟩
          cases callee with
          | here =>
              intro formal candidate found path side only inside arguments
              obtain ⟨level, at_, index⟩ := (ProjectedCallees.find_eq_some_iff _ _ formal candidate).mp found
              rw [Var.index_here, ProjectedCallees.level?_extend_zero] at at_
              exact sound.formals formal level at_ formal (Nat.zero_add formal).symm candidate index
                path side only inside arguments
          | there callee =>
              intro formal candidate found path side only inside arguments
              obtain ⟨level, at_, index⟩ := (ProjectedCallees.find_eq_some_iff _ _ formal candidate).mp found
              rw [Var.index_there, ProjectedCallees.level?_extend_succ] at at_
              exact sound.callees.program callee formal candidate
                ((finalCallees.find_eq_some_iff callee formal candidate).mpr ⟨level, at_, index⟩)
                path side only inside arguments

/-- The two routes agree. For an entry and a role, the program obtained by expanding the
entry, removing nested blocks and projecting, with its sites read at the sites they come
from, has the process of the program obtained by projecting with applications kept as
calls: both are the entry's meaning for the side with that role alone. -/
theorem expansion_agrees_with_calls {typeTable : TypeTable}
    (program : Protocols typeTable operations functions protocols)
    (identities : Identities) (expansions : ExpandedTable operations functions protocols)
    (expands : expandProtocols identities program = .ok expansions)
    (projected : Projected operations functions protocols)
    (projects : projectProtocols program = .ok projected) {header : ProtocolHeader}
    (entry : Var protocols header) (expanded : Expanded operations functions header)
    (found : expansions.get entry = some expanded) (role : Nat)
    (flat : RoleProgram operations functions [] (roleHeader role header))
    (projectsFlat : projectExpanded role expanded.flatten = .ok flat)
    (calling : Var projected.headers (roleHeader role header))
    (named : projected.callees.find entry role = some calling) (path : List Nat)
    (arguments : Values (SideValue model (single role)) header.inputs) :
    flat.body.denote (roleMeaning model functionTable .nil (expanded.label path))
        (Environment.ofValues
          (ownValues model (single role) role (Side.single_inside role) header.inputs arguments)) =
      (projected.programs.table model functionTable identities).get calling path
        (ownValues model (single role) role (Side.single_inside role) header.inputs arguments) :=
  (projectEntry_meaning functionTable identities program expansions expands entry expanded found
    role flat projectsFlat path arguments).trans
    ((projectProtocols_sound (functionTable := functionTable) identities program projected
      projects).program entry role calling named path (single role)
      (Side.only_single role header.roles) (Side.single_inside role) arguments).symm

end Program


end Zkc.Core
