module

public import Zkc.Core.WellFormed

public section

/-! What a definition without a residual violation is known to satisfy.

`ProtocolDefinition.violation` decides the residual conditions in one pass and returns the
first one violated. The functions that run after the check (projection, expansion, the
threading steps) use some of those conditions and must not refuse a program for a
condition that the check has decided. This file turns "the pass found no violation" back
into the facts, operation by operation:

- `Region.Legal`, `Regions.Legal`: the pass over a region succeeds. A region of a
  well-formed definition is legal, and so is every region nested in a legal region
  (`Region.Legal.letOp`, `Region.Legal.bind`, `Regions.Legal.cons`).
- `ProtocolOp.violation_*`: what the absence of a violation says of each operation form.
- `HeadersLegal`: the ports of every protocol of a program are held by roles below its
  role count.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## Lists of conditions -/

theorem firstViolation_none :
    ∀ {conditions : List (Bool × Violation)}, firstViolation conditions = none →
      ∀ pair ∈ conditions, pair.1 = true
  | [], _, _, member => nomatch member
  | (holds, violation) :: rest, none_, pair, member => by
      cases holds with
      | false => cases none_
      | true =>
          rcases List.mem_cons.mp member with rfl | later
          · rfl
          · exact firstViolation_none (conditions := rest) none_ pair later

theorem earlierViolation_none {first second : Option Violation}
    (none_ : earlierViolation first second = none) : first = none ∧ second = none := by
  cases first with
  | none => exact ⟨rfl, none_⟩
  | some violation => cases none_

theorem all_blt {bound : Nat} {roles : List Nat}
    (all : (roles.all fun role => Nat.blt role bound) = true) :
    ∀ role ∈ roles, Nat.blt role bound = true := by
  simpa only [List.all_eq_true] using all

/-- A formal role within a role map runs as one of the map's entries. -/
theorem RoleMap.apply_mem : ∀ (map : RoleMap) (index : Nat), index < map.length →
    map.apply index ∈ map
  | [], _, below => absurd below (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: rest, index + 1, below =>
      List.mem_cons_of_mem _ (RoleMap.apply_mem rest index (Nat.lt_of_succ_lt_succ below))

/-! ## Operations -/

section Operations

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool} {typeTable : TypeTable} {roles : Nat}
  {enclosing : Option (List Nat)}

/-- The roles that an operation without a violation names are below the role count. -/
theorem ProtocolOp.roles_below {op : ProtocolOp operations functions protocols deployed}
    (legal : ProtocolOp.violation typeTable roles enclosing op = none) :
    ∀ role ∈ ProtocolOp.roles op, Nat.blt role roles = true := by
  have acting : firstViolation (actingRoles roles enclosing (ProtocolOp.roles op)) = none →
      ∀ role ∈ ProtocolOp.roles op, Nat.blt role roles = true := fun none_ =>
    all_blt (firstViolation_none none_ (_, .roleOutOfRange) List.mem_cons_self)
  have prefix_ : ∀ {more : List (Bool × Violation)},
      firstViolation (actingRoles roles enclosing (ProtocolOp.roles op) ++ more) = none →
        ∀ role ∈ ProtocolOp.roles op, Nat.blt role roles = true := fun none_ =>
    all_blt (firstViolation_none none_ (_, .roleOutOfRange)
      (List.mem_append_left _ List.mem_cons_self))
  cases op with
  | «at» role op bodies => exact acting (earlierViolation_none legal).1
  | exchange sender receiver site type => exact prefix_ legal
  | draw owner receivers site law => exact prefix_ legal
  | sample owner site law => exact acting legal
  | «repeat» participants count carried collected captures covered => exact prefix_ legal
  | choose participants tag captures outputs covered => exact prefix_ legal
  | apply callee roleMap site permitted => exact prefix_ legal

/-- Inside a `repeat` or `choose`, the roles that an operation without a violation names
are participants. -/
theorem ProtocolOp.roles_participate {participants : List Nat}
    {op : ProtocolOp operations functions protocols deployed}
    (legal : ProtocolOp.violation typeTable roles (some participants) op = none) :
    ∀ role ∈ ProtocolOp.roles op, occursIn participants role = true := by
  have all : ((ProtocolOp.roles op).all (participates (some participants))) = true →
      ∀ role ∈ ProtocolOp.roles op, occursIn participants role = true := fun holds =>
    List.all_eq_true.mp holds
  have acting : firstViolation (actingRoles roles (some participants) (ProtocolOp.roles op)) = none →
      ∀ role ∈ ProtocolOp.roles op, occursIn participants role = true := fun none_ =>
    all (firstViolation_none none_ (_, .roleOutsideParticipants)
      (List.mem_cons_of_mem _ List.mem_cons_self))
  have prefix_ : ∀ {more : List (Bool × Violation)},
      firstViolation (actingRoles roles (some participants) (ProtocolOp.roles op) ++ more) = none →
        ∀ role ∈ ProtocolOp.roles op, occursIn participants role = true := fun none_ =>
    all (firstViolation_none none_ (_, .roleOutsideParticipants)
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  cases op with
  | «at» role op bodies => exact acting (earlierViolation_none legal).1
  | exchange sender receiver site type => exact prefix_ legal
  | draw owner receivers site law => exact prefix_ legal
  | sample owner site law => exact acting legal
  | «repeat» participants count carried collected captures covered => exact prefix_ legal
  | choose participants tag captures outputs covered => exact prefix_ legal
  | apply callee roleMap site permitted => exact prefix_ legal

/-- The participants that enclose the regions of an operation are those that enclose the
operation, or the roles the operation names (the participants of a `repeat` or `choose`). -/
theorem ProtocolOp.enclosing_cases (enclosing : Option (List Nat))
    (op : ProtocolOp operations functions protocols deployed) :
    ProtocolOp.enclosing enclosing op = enclosing ∨
      ProtocolOp.enclosing enclosing op = some (ProtocolOp.roles op) := by
  cases op <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem ProtocolOp.violation_at {role : Nat} {op : LocalOp operations functions deployed}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions}
    (legal : ProtocolOp.violation (protocols := protocols) typeTable roles enclosing
      (.at role op bodies) = none) : Nat.blt role roles = true :=
  ProtocolOp.roles_below legal role List.mem_cons_self

theorem ProtocolOp.violation_exchange {sender receiver site : Nat} {type : Ty}
    (legal : ProtocolOp.violation (operations := operations) (functions := functions)
      (protocols := protocols) (deployed := deployed) typeTable roles enclosing
      (.exchange sender receiver site type) = none) :
    Nat.blt sender roles = true ∧ Nat.blt receiver roles = true :=
  ⟨ProtocolOp.roles_below legal sender List.mem_cons_self,
    ProtocolOp.roles_below legal receiver (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem ProtocolOp.violation_draw {owner site : Nat} {receivers : List Nat} {inputs : List Ty}
    {output : Ty} {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true}
    (legal : ProtocolOp.violation (functions := functions) (protocols := protocols)
      (deployed := deployed) typeTable roles enclosing (.draw owner receivers site law populated) = none) :
    Nat.blt owner roles = true ∧ ∀ receiver ∈ receivers, Nat.blt receiver roles = true :=
  ⟨ProtocolOp.roles_below legal owner List.mem_cons_self,
    fun receiver member => ProtocolOp.roles_below legal receiver (List.mem_cons_of_mem _ member)⟩

theorem ProtocolOp.violation_sample {owner site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {populated : output.populated = true}
    (legal : ProtocolOp.violation (functions := functions) (protocols := protocols)
      (deployed := deployed) typeTable roles enclosing (.sample owner site law populated) = none) :
    Nat.blt owner roles = true :=
  ProtocolOp.roles_below legal owner List.mem_cons_self

/-- The participants of a `repeat` or `choose` without a violation: below the role count,
each once, and holding the given values. -/
theorem participants_legal {participants : List Nat} {values : List Located}
    {more : List (Bool × Violation)}
    (legal : firstViolation (actingRoles roles enclosing participants ++
      (participantConditions participants values ++ more)) = none) :
    (∀ role ∈ participants, Nat.blt role roles = true) ∧ distinctNumbers participants = true ∧
      Located.heldBy participants values = true := by
  have holds := firstViolation_none legal
  refine ⟨all_blt (holds (_, .roleOutOfRange) (List.mem_append_left _ List.mem_cons_self)), ?_, ?_⟩
  · exact holds (_, .repeatedParticipant)
      (List.mem_append_right _ (List.mem_append_left _
        (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact holds (_, .valueOutsideParticipants)
      (List.mem_append_right _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem ProtocolOp.violation_repeat {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    (legal : ProtocolOp.violation (operations := operations) (functions := functions)
      (protocols := protocols) (deployed := deployed) typeTable roles enclosing
      (.repeat participants count carried collected captures covered) = none) :
    (∀ role ∈ participants, Nat.blt role roles = true) ∧ distinctNumbers participants = true ∧
      Located.heldBy participants (carried ++ captures) = true := by
  have shaped : firstViolation (actingRoles roles enclosing participants ++
      (participantConditions participants (carried ++ captures) ++ [])) = none := by
    rw [List.append_nil]
    exact legal
  exact participants_legal shaped

theorem ProtocolOp.violation_choose {participants : List Nat} {tag : ChoiceTag}
    {captures outputs : List Located} {covered : Located.heldBy participants outputs = true}
    (legal : ProtocolOp.violation (operations := operations) (functions := functions)
      (protocols := protocols) (deployed := deployed) typeTable roles enclosing
      (.choose participants tag captures outputs covered) = none) :
    (∀ role ∈ participants, Nat.blt role roles = true) ∧ distinctNumbers participants = true ∧
      Located.heldBy participants (captures ++ outputs) = true :=
  participants_legal legal

/-- The role map of an application without a violation: its entries are below the
caller's role count, it has one entry per formal role of the callee, and its entries are
distinct. -/
theorem ProtocolOp.violation_apply {header : ProtocolHeader} {callee : Var protocols header}
    {roleMap : RoleMap} {site : Nat} {permitted : (deployed && header.specificationOnly) = false}
    (legal : ProtocolOp.violation (operations := operations) (functions := functions) typeTable
      roles enclosing (.apply callee roleMap site permitted) = none) :
    (∀ role ∈ roleMap, Nat.blt role roles = true) ∧ roleMap.length = header.roles ∧
      distinctNumbers roleMap = true := by
  have holds := firstViolation_none legal
  refine ⟨ProtocolOp.roles_below legal, ?_, ?_⟩
  · exact Nat.eq_of_beq_eq_true
      (holds (_, .roleMapLength) (List.mem_append_right _ List.mem_cons_self))
  · exact holds (_, .roleMapNotInjective)
      (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

end Operations

/-! ## Regions -/

section Regions

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- The pass over a region finds no violation. The sites met before the region do not
matter. -/
@[expose] def Region.Legal (typeTable : TypeTable) (roles : Nat) (enclosing : Option (List Nat)) {Γ out : List Located}
    (region : Region (ProtocolDialect operations functions protocols deployed) Γ out) : Prop :=
  ∃ sites result, protocolRegionSites typeTable roles enclosing region sites = .ok result

/-- The pass over closed regions finds no violation. -/
@[expose] def Regions.Legal (typeTable : TypeTable) (roles : Nat) (enclosing : Option (List Nat))
    {signatures : List (List Located × List Located)}
    (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures) :
    Prop :=
  ∃ sites result, protocolRegionsSites typeTable roles enclosing regions sites = .ok result

variable {typeTable : TypeTable} {roles : Nat} {enclosing : Option (List Nat)}

/-- A legal region that starts with an operation: the operation has no violation, its
nested regions are legal inside it, and the rest is legal. -/
theorem Region.Legal.letOp {Γ out : List Located}
    {op : ProtocolOp operations functions protocols deployed}
    {arguments : Operands Γ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed)
      (ProtocolOp.regions op)}
    {next : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll Γ (ProtocolOp.results op)) out}
    (legal : Region.Legal typeTable roles enclosing
      (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies next)) :
    ProtocolOp.violation typeTable roles enclosing op = none ∧
      Regions.Legal typeTable roles (ProtocolOp.enclosing enclosing op) bodies ∧
      Region.Legal typeTable roles enclosing next := by
  obtain ⟨sites, result, passes⟩ := legal
  unfold protocolRegionSites at passes
  split at passes
  · cases passes
  · rename_i clean
    cases named : Located.allNamed typeTable (ProtocolOp.results op) with
    | false =>
        rw [named] at passes
        cases passes
    | true =>
        rw [named] at passes
        simp only [Bool.cond_true] at passes
        split at passes
        · cases passes
        · rename_i middle nested
          exact ⟨clean, ⟨_, middle, nested⟩, ⟨middle, result, passes⟩⟩

/-- A legal region that starts with a nested block: the block and the rest are legal. -/
theorem Region.Legal.bind {Γ mid out : List Located}
    {body : Region (ProtocolDialect operations functions protocols deployed) Γ mid}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ mid) out}
    (legal : Region.Legal typeTable roles enclosing (Region.bind body next)) :
    Region.Legal typeTable roles enclosing body ∧ Region.Legal typeTable roles enclosing next := by
  obtain ⟨sites, result, passes⟩ := legal
  unfold protocolRegionSites at passes
  cases named : Located.allNamed typeTable mid with
  | false =>
      rw [named] at passes
      cases passes
  | true =>
      rw [named] at passes
      simp only [Bool.cond_true] at passes
      split at passes
      · cases passes
      · rename_i middle first
        exact ⟨⟨sites, middle, first⟩, ⟨middle, result, passes⟩⟩

/-- A legal protocol region contains no `stop`. -/
theorem Region.Legal.not_stop {Γ out : List Located} {reason : PIR.Stop}
    (legal : Region.Legal typeTable roles enclosing
      (Region.stop (dialect := ProtocolDialect operations functions protocols deployed)
        (Γ := Γ) (out := out) reason)) : False := by
  obtain ⟨sites, result, passes⟩ := legal
  simp only [protocolRegionSites] at passes
  cases passes

theorem Regions.Legal.cons {inputs outputs : List Located}
    {rest : List (List Located × List Located)}
    {body : Region (ProtocolDialect operations functions protocols deployed) (bindAll [] inputs)
      outputs}
    {tail : Regions (ProtocolDialect operations functions protocols deployed) rest}
    (legal : Regions.Legal typeTable roles enclosing (Regions.cons body tail)) :
    Region.Legal typeTable roles enclosing body ∧ Regions.Legal typeTable roles enclosing tail := by
  obtain ⟨sites, result, passes⟩ := legal
  unfold protocolRegionsSites at passes
  split at passes
  · cases passes
  · rename_i middle first
    exact ⟨⟨sites, middle, first⟩, ⟨middle, result, passes⟩⟩

end Regions

/-! ## Definitions and programs -/

section Definitions

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- The ports of a protocol are held by roles below its role count. -/
@[expose] def ProtocolHeader.PortsLegal (header : ProtocolHeader) : Prop :=
  ∀ port ∈ header.inputs ++ header.outputs, Nat.blt port.holder header.roles = true

/-- The body of a definition without a violation is legal. -/
theorem ProtocolDefinition.body_legal {typeTable : TypeTable} {header : ProtocolHeader}
    {definition : ProtocolDefinition operations functions protocols header}
    (wellFormed : definition.violation typeTable = none) :
    Region.Legal typeTable header.roles none definition.body := by
  have body := (earlierViolation_none wellFormed).2
  unfold ProtocolDefinition.sites at body
  split at body
  · cases body
  · rename_i sites passes
    exact ⟨[], sites, passes⟩

/-- The ports of a definition without a violation are held by its roles. -/
theorem ProtocolDefinition.ports_legal {typeTable : TypeTable} {header : ProtocolHeader}
    {definition : ProtocolDefinition operations functions protocols header}
    (wellFormed : definition.violation typeTable = none) : header.PortsLegal := by
  have signature := firstViolation_none (earlierViolation_none wellFormed).1
  have held := signature (_, .roleOutOfRange)
    (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simpa only [ProtocolHeader.PortsLegal, List.all_eq_true] using held

/-- The ports of every protocol of the list are held by roles below its role count. -/
@[expose] def HeadersLegal (protocols : List ProtocolHeader) : Prop :=
  ∀ {header : ProtocolHeader}, Var protocols header → header.PortsLegal

theorem HeadersLegal.nil : HeadersLegal [] := fun callee => callee.elimNil

theorem HeadersLegal.cons {header : ProtocolHeader} (legal : header.PortsLegal)
    (earlier : HeadersLegal protocols) : HeadersLegal (header :: protocols) := by
  intro other callee
  cases callee with
  | here => exact legal
  | there callee => exact earlier callee

/-- The headers of a program are legal: each of its definitions has no violation. -/
theorem Protocols.headersLegal {typeTable : TypeTable} :
    ∀ {protocols : List ProtocolHeader},
      Protocols typeTable operations functions protocols → HeadersLegal protocols
  | _, .nil => HeadersLegal.nil
  | _, .snoc earlier _ wellFormed =>
      HeadersLegal.cons (ProtocolDefinition.ports_legal wellFormed) earlier.headersLegal

end Definitions

end Zkc.Core
