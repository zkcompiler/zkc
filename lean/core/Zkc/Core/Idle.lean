module

public import Zkc.Core.EndpointsMeaning

public section

/-! A protocol does nothing for a side without any of its roles.

A protocol definition without a residual violation encloses the regions of its loops and
choices and names its own roles only (`definition_shape`). The protocols of a program are
each without a violation, so every program has that shape (`protocols_enclosed`). A
definition that names its own roles only returns without an effect for a side without any
of them when the protocols it applies do (`definition_idle`), so every protocol of every
program does (`program_idle`). The shape is also what the restriction law needs
(`Zkc.Core.EndpointsProgram`).

The conditions used are: the roles an operation names are below the role count and, inside
a `repeat` or `choose`, participants; the values that enter or leave a `repeat` are held by
participants; a role map has one entry per formal role of the callee; a protocol region
has no `stop`.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The roles that may act at a place: the participants of the enclosing `repeat` or
`choose`, or every role of the protocol. -/
def allowedRoles (roles : Nat) : Option (List Nat) → List Nat
  | none => List.range roles
  | some participants => participants

section Operations

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool} {typeTable : TypeTable} {roles : Nat}
  {enclosing : Option (List Nat)}

/-- The conditions on the roles that an operation names hold. -/
theorem acting_clean :
    ∀ (op : ProtocolOp operations functions protocols deployed),
      ProtocolOp.violation typeTable roles enclosing op = none →
      ∀ entry ∈ actingRoles roles enclosing (ProtocolOp.roles op), entry.1 = true
  | .at _ _ _, clean, entry, member =>
      firstViolation_holds _ (earlierViolation_both clean).1 entry member
  | .exchange .., clean, entry, member =>
      firstViolation_holds _ clean entry (List.mem_append_left _ member)
  | .draw .., clean, entry, member =>
      firstViolation_holds _ clean entry (List.mem_append_left _ member)
  | .sample .., clean, entry, member => firstViolation_holds _ clean entry member
  | .repeat .., clean, entry, member =>
      firstViolation_holds _ clean entry (List.mem_append_left _ member)
  | .choose .., clean, entry, member =>
      firstViolation_holds _ clean entry (List.mem_append_left _ member)
  | .apply .., clean, entry, member =>
      firstViolation_holds _ clean entry (List.mem_append_left _ member)

/-- The roles that an operation names may act where it stands. -/
theorem roles_allowed (op : ProtocolOp operations functions protocols deployed)
    (clean : ProtocolOp.violation typeTable roles enclosing op = none) :
    ∀ role ∈ ProtocolOp.roles op, role ∈ allowedRoles roles enclosing := by
  intro role member
  have below := acting_clean op clean
    ((ProtocolOp.roles op).all fun role => Nat.blt role roles, .roleOutOfRange)
    (List.mem_cons_self ..)
  have inside := acting_clean op clean
    ((ProtocolOp.roles op).all (participates enclosing), .roleOutsideParticipants)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  cases enclosing with
  | none => exact List.mem_range.mpr (Nat.blt_eq.mp (List.all_eq_true.mp below role member))
  | some participants =>
      exact (occursIn_iff participants role).mp (List.all_eq_true.mp inside role member)

/-- The role map of an application covers the roles of the callee. -/
theorem covers_clean :
    ∀ (op : ProtocolOp operations functions protocols deployed),
      ProtocolOp.violation typeTable roles enclosing op = none → opCovers op
  | .apply (header := header) _ roleMap _ _, clean => by
      have sameLength := firstViolation_holds _ clean
        (Nat.beq roleMap.length header.roles, .roleMapLength)
        (List.mem_append_right _ (List.mem_cons_self ..))
      exact Nat.le_of_eq (Nat.eq_of_beq_eq_true sameLength).symm
  | .at .., _ => trivial
  | .exchange .., _ => trivial
  | .draw .., _ => trivial
  | .sample .., _ => trivial
  | .repeat .., _ => trivial
  | .choose .., _ => trivial

/-- A `repeat` or `choose` whose regions name its participants only encloses them. -/
theorem encloses_clean :
    ∀ (op : ProtocolOp operations functions protocols deployed)
      (bodies : Regions (ProtocolDialect operations functions protocols deployed)
        (ProtocolOp.regions op)),
      ProtocolOp.violation typeTable roles enclosing op = none →
      regionsWithin (allowedRoles roles (ProtocolOp.enclosing enclosing op)) bodies →
        opEncloses op bodies
  | .repeat participants _ carried _ captures _, _, clean, nested => by
      have held := firstViolation_holds _ clean
        (Located.heldBy participants (carried ++ captures), .valueOutsideParticipants)
        (List.mem_append_right _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      refine ⟨?_, nested⟩
      unfold Located.heldBy at held ⊢
      rw [List.all_append, Bool.and_eq_true] at held
      exact held.1
  | .choose .., _, _, nested => nested
  | .at .., _, _, _ => trivial
  | .exchange .., _, _, _ => trivial
  | .draw .., _, _, _ => trivial
  | .sample .., _, _, _ => trivial
  | .apply .., _, _, _ => trivial

mutual
  /-- A region that the checker's pass accepts has the shape. -/
  theorem regionSites_shape (typeTable : TypeTable) (roles : Nat) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
        (enclosing : Option (List Nat)) (sites result : List Nat),
        protocolRegionSites typeTable roles enclosing region sites = .ok result →
          regionEnclosed region ∧ regionWithin (allowedRoles roles enclosing) region
    | .ret _, _, _, _, _ => ⟨trivial, trivial⟩
    | .stop _, _, _, _, checked => by
        unfold protocolRegionSites at checked
        cases checked
    | .bind (mid := mid) body rest, enclosing, sites, result, checked => by
        unfold protocolRegionSites at checked
        cases named : Located.allNamed typeTable mid with
        | false =>
            rw [named] at checked
            cases checked
        | true =>
            rw [named] at checked
            simp only [Bool.cond_true] at checked
            split at checked
            · cases checked
            · rename_i bodySites bodyChecked
              have first := regionSites_shape typeTable roles body enclosing sites bodySites
                bodyChecked
              have second := regionSites_shape typeTable roles rest enclosing bodySites result
                checked
              exact ⟨⟨first.1, second.1⟩, ⟨first.2, second.2⟩⟩
    | .letOp op _ bodies rest, enclosing, sites, result, checked => by
        unfold protocolRegionSites at checked
        split at checked
        · cases checked
        · rename_i clean
          cases named : Located.allNamed typeTable (ProtocolOp.results op) with
          | false =>
              rw [named] at checked
              cases checked
          | true =>
              rw [named] at checked
              simp only [Bool.cond_true] at checked
              split at checked
              · cases checked
              · rename_i nestedSites nestedChecked
                have nested := regionsSites_shape typeTable roles bodies
                  (ProtocolOp.enclosing enclosing op) _ nestedSites nestedChecked
                have later := regionSites_shape typeTable roles rest enclosing nestedSites result
                  checked
                exact ⟨⟨encloses_clean op bodies clean nested.2, nested.1, later.1⟩,
                  ⟨roles_allowed op clean, covers_clean op clean, later.2⟩⟩

  theorem regionsSites_shape (typeTable : TypeTable) (roles : Nat)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures)
        (enclosing : Option (List Nat)) (sites result : List Nat),
        protocolRegionsSites typeTable roles enclosing regions sites = .ok result →
          regionsEnclosed regions ∧ regionsWithin (allowedRoles roles enclosing) regions
    | .nil, _, _, _, _ => ⟨trivial, trivial⟩
    | .cons body tail, enclosing, sites, result, checked => by
        unfold protocolRegionsSites at checked
        split at checked
        · cases checked
        · rename_i bodySites bodyChecked
          have first := regionSites_shape typeTable roles body enclosing sites bodySites
            bodyChecked
          have later := regionsSites_shape typeTable roles tail enclosing bodySites result checked
          exact ⟨⟨first.1, later.1⟩, ⟨first.2, later.2⟩⟩
end

end Operations

section Programs

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader}

/-- Every definition of the program encloses the regions of its loops and choices, names
its own roles only and applies protocols whose roles the role map covers. -/
@[expose] def protocolsEnclosed :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols → Prop
  | _, .nil => True
  | _, .snoc (header := header) earlier definition _ =>
      protocolsEnclosed earlier ∧ regionEnclosed definition.body ∧
        regionWithin (List.range header.roles) definition.body

/-- A definition without a residual violation has the shape that the restriction law
needs: its loops and choices enclose their regions, and its operations name its own roles
and apply protocols whose roles the role map covers. -/
theorem definition_shape {protocols : List ProtocolHeader} {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (wellFormed : definition.violation typeTable = none) :
    regionEnclosed definition.body ∧ regionWithin (List.range header.roles) definition.body := by
  unfold ProtocolDefinition.violation at wellFormed
  have sites := (earlierViolation_both wellFormed).2
  cases checked : definition.sites typeTable with
  | error violation =>
      rw [checked] at sites
      cases sites
  | ok found => exact regionSites_shape typeTable header.roles definition.body none [] found checked

/-- The protocols of every program have the shape. -/
theorem protocols_enclosed :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols), protocolsEnclosed program
  | _, .nil => trivial
  | _, .snoc earlier definition wellFormed =>
      ⟨protocols_enclosed earlier, (definition_shape definition wellFormed).1,
        (definition_shape definition wellFormed).2⟩

end Programs

/-! ## Idleness -/

section Idle

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} (functionTable : FunctionTable model functions)
  {protocols : List ProtocolHeader} {table : ProtocolTable model protocols}

/-- A definition does nothing for a side without any of its roles. -/
theorem definition_idle (calleesIdle : CalleesIdle table) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (within : regionWithin (List.range header.roles) definition.body) (identity : Nat)
    (path : List Nat) (side : Side) (absent : ∀ role, role < header.roles → side role = false)
    (arguments : Values (SideValue model side) header.inputs) :
    ∃ values, definition.meaning model functionTable table identity path side arguments =
      .done values :=
  region_idle calleesIdle side (List.range header.roles)
    (fun role member => absent role (List.mem_range.mp member)) definition.body within _

/-- Every protocol of a program does nothing for a side without any of its roles. -/
theorem protocols_idle (identities : Identities) :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols), protocolsEnclosed program →
        CalleesIdle (program.table model functionTable identities)
  | _, .nil, _ => fun callee => callee.elimNil
  | _, .snoc earlier definition _, enclosed => by
      intro callee
      cases callee with
      | here =>
          intro path side absent arguments
          exact definition_idle functionTable
            (fun callee => protocols_idle identities earlier enclosed.1 callee) definition
            enclosed.2.2 _ path side absent arguments
      | there callee => exact protocols_idle identities earlier enclosed.1 callee

/-- Every protocol of every program does nothing for a side without any of its roles: no
hypothesis about shape. -/
theorem program_idle (identities : Identities)
    (program : Protocols typeTable operations functions protocols) :
    CalleesIdle (program.table model functionTable identities) :=
  fun callee => protocols_idle functionTable identities program (protocols_enclosed program) callee

end Idle

end Zkc.Core
