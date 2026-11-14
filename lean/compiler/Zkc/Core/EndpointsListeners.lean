module

public import Zkc.Core.EndpointsMeaning
public import Zkc.Core.ThreadSites
public import Zkc.Core.ProjectMeaning

public section

/-! The listeners of a program: which of two sides hears at each site.

The restriction law is stated for listeners that are those of the region it is about
(`regionListens`, in `Zkc.Core.EndpointsMeaning`): at the site of every `draw` a side hears
exactly when the other side has the owner and it has a receiver. This file shows that every
protocol of every program has such listeners, for every path under which it is reached and
every two sides that each hold at most one of its roles (`Protocols.listened`,
`Protocols.entry_listened`).

That one function of sites answers for every `draw` is the uniqueness of the sites of a
well-formed definition: a site is one operation of one definition under one path of
applications, with one owner and fixed receivers.

- `opHearers`, `regionHearers`: the sides that hear at a site relative to a definition, the
  path of applications below the definition and the site number of the operation. A `draw`
  answers at its own site, with an empty path; an application answers below its site with
  what the protocol it applies answers for the preimages of the two sides; no other
  operation answers. `regionHearers` returns the first answer of the operations of a region.
- A region answers only at relative sites that start at one of its sites
  (`regionHearers_outside`), so, the sites of a region being pairwise different, the answer
  of a region at a site that starts in one of its parts is the answer of that part
  (`bind_hearers`, `letOp_hearers`, `cons_hearers`).
- `region_listens`: listeners that read the answers of a region below a path
  (`Listeners.ReadBelow`) are those of the region. The receivers of a `draw` are pairwise
  different, so a side with at most one role of the protocol holds at most one of them; a role map is injective, so the preimage of such a side holds at most
  one role of the protocol applied.
- `Listeners.below`: the listeners that read given answers below a path.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## Sides with at most one role -/

/-- The side holds at most one of the roles below a count. -/
@[expose] def Side.AtMostOne (side : Side) (roles : Nat) : Prop :=
  ∀ one other, one < roles → other < roles → side one = true → side other = true → one = other

/-- A side whose only member among the roles below a count is one role holds at most one. -/
theorem Side.Only.atMostOne {side : Side} {role roles : Nat} (only : side.Only role roles) :
    side.AtMostOne roles := by
  intro one other oneBelow otherBelow oneInside otherInside
  rw [only one (Nat.blt_eq.mpr oneBelow)] at oneInside
  rw [only other (Nat.blt_eq.mpr otherBelow)] at otherInside
  exact (Nat.eq_of_beq_eq_true oneInside).trans (Nat.eq_of_beq_eq_true otherInside).symm

/-- A role map with distinct entries is injective on the roles it has an entry for. -/
theorem RoleMap.apply_injective : ∀ (map : RoleMap), distinctNumbers map = true →
    ∀ one other, one < map.length → other < map.length → map.apply one = map.apply other →
      one = other
  | [], _, _, _, below, _, _ => absurd below (Nat.not_lt_zero _)
  | head :: rest, distinct, one, other, oneBelow, otherBelow, same => by
    have parts : occursIn rest head = false ∧ distinctNumbers rest = true := by
      simpa only [distinctNumbers, Bool.and_eq_true, Bool.not_eq_true'] using distinct
    have outside : head ∉ rest := fun inside =>
      Bool.noConfusion (parts.1.symm.trans ((occursIn_iff rest head).mpr inside))
    match one, other, oneBelow, otherBelow, same with
    | 0, 0, _, _, _ => rfl
    | 0, later + 1, _, laterBelow, same =>
      have member := RoleMap.apply_mem rest later (Nat.lt_of_succ_lt_succ laterBelow)
      have equal : head = RoleMap.apply rest later := same
      exact absurd (equal ▸ member) outside
    | earlier + 1, 0, earlierBelow, _, same =>
      have member := RoleMap.apply_mem rest earlier (Nat.lt_of_succ_lt_succ earlierBelow)
      have equal : RoleMap.apply rest earlier = head := same
      exact absurd (equal ▸ member) outside
    | earlier + 1, later + 1, earlierBelow, laterBelow, same =>
      exact congrArg (· + 1) (RoleMap.apply_injective rest parts.2 earlier later
        (Nat.lt_of_succ_lt_succ earlierBelow) (Nat.lt_of_succ_lt_succ laterBelow) same)

/-- The preimage, under an injective role map into the roles below a count, of a side that
holds at most one of those roles holds at most one of the roles that the map has an entry
for. -/
theorem Side.AtMostOne.preimage {side : Side} {roles : Nat} (atMostOne : side.AtMostOne roles)
    {roleMap : RoleMap} (below : ∀ role ∈ roleMap, Nat.blt role roles = true)
    (distinct : distinctNumbers roleMap = true) :
    (Side.preimage roleMap side).AtMostOne roleMap.length := by
  intro one other oneBelow otherBelow oneInside otherInside
  exact RoleMap.apply_injective roleMap distinct one other oneBelow otherBelow
    (atMostOne _ _ (Nat.blt_eq.mp (below _ (RoleMap.apply_mem roleMap one oneBelow)))
      (Nat.blt_eq.mp (below _ (RoleMap.apply_mem roleMap other otherBelow))) oneInside
      otherInside)

/-- A side with at most one of the roles below a count holds at most one of distinct
receivers below the count. -/
theorem hearsOnce_of_atMostOne {side : Side} {roles : Nat} (atMostOne : side.AtMostOne roles) :
    ∀ (receivers : List Nat), distinctNumbers receivers = true →
      (∀ receiver ∈ receivers, Nat.blt receiver roles = true) → hearsOnce side receivers
  | [], _, _ => trivial
  | role :: rest, distinct, below => by
    have parts : occursIn rest role = false ∧ distinctNumbers rest = true := by
      simpa only [distinctNumbers, Bool.and_eq_true, Bool.not_eq_true'] using distinct
    have outside : role ∉ rest := fun inside =>
      Bool.noConfusion (parts.1.symm.trans ((occursIn_iff rest role).mpr inside))
    refine ⟨fun inside => ?_, hearsOnce_of_atMostOne atMostOne rest parts.2 fun receiver member =>
      below receiver (List.mem_cons_of_mem _ member)⟩
    rcases Bool.eq_false_or_eq_true (rest.any side) with some | none
    · obtain ⟨other, member, otherInside⟩ := List.any_eq_true.mp some
      have same := atMostOne role other (Nat.blt_eq.mp (below role List.mem_cons_self))
        (Nat.blt_eq.mp (below other (List.mem_cons_of_mem _ member))) inside otherInside
      exact absurd (same ▸ member) outside
    · exact none

/-- The receivers of a `draw` without a violation are listed once each. -/
theorem ProtocolOp.violation_draw_receivers {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
    {typeTable : TypeTable} {roles : Nat} {enclosing : Option (List Nat)} {owner site : Nat}
    {receivers : List Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {populated : output.populated = true}
    (legal : ProtocolOp.violation (functions := functions) (protocols := protocols)
      (deployed := deployed) typeTable roles enclosing
      (.draw owner receivers site law populated) = none) :
    distinctNumbers receivers = true :=
  firstViolation_none legal (_, .repeatedReceiver)
    (List.mem_append_right _ List.mem_cons_self)

/-! ## The sides that hear at a site -/

/-- The sides that hear at the sites relative to a definition: at a path of applications
below the definition and a site number, whether the first side hears there and whether the
second does, when an operation answers. -/
abbrev Hearers : Type := List Nat → Nat → Option (Bool × Bool)

/-- For every protocol of a program, the most recent first: for two sides, the sides that
hear at the sites relative to the protocol. -/
abbrev HearerTable (protocols : List ProtocolHeader) : Type :=
  Values (fun _ : ProtocolHeader => Side → Side → Hearers) protocols

/-- Where a site relative to a definition starts: at the site of the application through
which it is reached, or, for a site of the definition's own operation, at its number. -/
@[expose] def siteStart : List Nat → Nat → Nat
  | [], number => number
  | first :: _, _ => first

section Hearers

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}
variable (callees : HearerTable protocols) (first second : Side)

/-- The sides that hear at a site relative to the definition of one operation. A side hears
at the site of a `draw` when the other side has the owner and it has a receiver. -/
@[expose] def opHearers :
    ProtocolOp operations functions protocols deployed → List Nat → Nat → Option (Bool × Bool)
  | .draw owner receivers site _ _, path, number =>
      if path = [] ∧ number = site then
        some (second owner && receivers.any first, first owner && receivers.any second)
      else none
  | .apply callee roleMap site _, path, number =>
      match path with
      | start :: rest =>
          if start = site then
            (callees.get callee) (Side.preimage roleMap first) (Side.preimage roleMap second) rest
              number
          else none
      | [] => none
  | _, _, _ => none

mutual
  /-- The sides that hear at a site relative to the definition of a region: the first answer
  of its operations, nested regions included. -/
  @[expose] def regionHearers {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out → List Nat → Nat →
        Option (Bool × Bool)
    | .ret _, _, _ => none
    | .stop _, _, _ => none
    | .bind body rest, path, number =>
        (regionHearers body path number).or (regionHearers rest path number)
    | .letOp op _ bodies rest, path, number =>
        (opHearers callees first second op path number).or
          ((regionsHearers bodies path number).or (regionHearers rest path number))

  @[expose] def regionsHearers {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures → List Nat →
        Nat → Option (Bool × Bool)
    | .nil, _, _ => none
    | .cons body tail, path, number =>
        (regionHearers body path number).or (regionsHearers tail path number)
end

/-- An operation answers only at relative sites that start at its site. -/
theorem opHearers_outside (op : ProtocolOp operations functions protocols deployed)
    (path : List Nat) (number : Nat) (outside : siteStart path number ∉ ProtocolOp.sites op) :
    opHearers callees first second op path number = none := by
  cases op with
  | «at» role op bodies => rfl
  | exchange sender receiver site type => rfl
  | sample owner site law populated => rfl
  | «repeat» participants count carried collected captures covered => rfl
  | choose participants tag captures outputs covered => rfl
  | draw owner receivers site law populated =>
      unfold opHearers
      refine ite_eq_right fun answers => outside ?_
      obtain ⟨emptyPath, sameNumber⟩ := answers
      subst emptyPath
      rw [ProtocolOp.sites_draw]
      exact List.mem_singleton.mpr sameNumber
  | apply callee roleMap site permitted =>
      cases path with
      | nil => rfl
      | cons start rest =>
          unfold opHearers
          dsimp only
          refine ite_eq_right fun same => outside ?_
          rw [ProtocolOp.sites_apply]
          exact List.mem_singleton.mpr same

mutual
  /-- A region answers only at relative sites that start at one of its sites. -/
  theorem regionHearers_outside {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
        (path : List Nat) (number : Nat), siteStart path number ∉ regionSites region →
          regionHearers callees first second region path number = none
    | .ret _, _, _, _ => rfl
    | .stop _, _, _, _ => rfl
    | .bind body rest, path, number, outside => by
        show (regionHearers callees first second body path number).or
          (regionHearers callees first second rest path number) = none
        rw [regionHearers_outside body path number fun member =>
            outside (List.mem_append_right _ member),
          regionHearers_outside rest path number fun member =>
            outside (List.mem_append_left _ member)]
        rfl
    | .letOp op _ bodies rest, path, number, outside => by
        show (opHearers callees first second op path number).or
          ((regionsHearers callees first second bodies path number).or
            (regionHearers callees first second rest path number)) = none
        rw [opHearers_outside callees first second op path number fun member =>
            outside (List.mem_append_right _ (List.mem_append_right _ member)),
          regionsHearers_outside bodies path number fun member =>
            outside (List.mem_append_right _ (List.mem_append_left _ member)),
          regionHearers_outside rest path number fun member =>
            outside (List.mem_append_left _ member)]
        rfl

  theorem regionsHearers_outside {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures)
        (path : List Nat) (number : Nat), siteStart path number ∉ regionsSites regions →
          regionsHearers callees first second regions path number = none
    | .nil, _, _, _ => rfl
    | .cons body tail, path, number, outside => by
        show (regionHearers callees first second body path number).or
          (regionsHearers callees first second tail path number) = none
        rw [regionHearers_outside body path number fun member =>
            outside (List.mem_append_right _ member),
          regionsHearers_outside tail path number fun member =>
            outside (List.mem_append_left _ member)]
        rfl
end

/-! ## The answers of the parts of a region -/

variable (whole : Hearers)

/-- The answers of a sequence of two regions whose sites are pairwise different are, at the
relative sites that start in either, the answers of that one. -/
theorem bind_hearers {Γ mid out : List Located}
    (body : Region (ProtocolDialect operations functions protocols deployed) Γ mid)
    (rest : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ mid) out)
    (unique : (regionSites (Region.bind body rest)).Nodup)
    (agrees : ∀ path number, siteStart path number ∈ regionSites (Region.bind body rest) →
      whole path number = regionHearers callees first second (Region.bind body rest) path number) :
    ((regionSites body).Nodup ∧ ∀ path number, siteStart path number ∈ regionSites body →
        whole path number = regionHearers callees first second body path number) ∧
      ((regionSites rest).Nodup ∧ ∀ path number, siteStart path number ∈ regionSites rest →
        whole path number = regionHearers callees first second rest path number) := by
  have split : (regionSites rest ++ regionSites body).Nodup := unique
  obtain ⟨restUnique, bodyUnique, apart⟩ := List.nodup_append.mp split
  refine ⟨⟨bodyUnique, fun path number inside => ?_⟩, ⟨restUnique, fun path number inside => ?_⟩⟩
  · rw [agrees path number (List.mem_append_right _ inside)]
    show (regionHearers callees first second body path number).or
      (regionHearers callees first second rest path number) = _
    rw [regionHearers_outside callees first second rest path number fun other =>
      apart _ other _ inside rfl, Option.or_none]
  · rw [agrees path number (List.mem_append_left _ inside)]
    show (regionHearers callees first second body path number).or
      (regionHearers callees first second rest path number) = _
    rw [regionHearers_outside callees first second body path number fun other =>
      apart _ inside _ other rfl, Option.none_or]

/-- The answers of an operation, its regions and the region after it, when their sites are
pairwise different: at the relative sites that start in one of the three, the answers of
that one. -/
theorem letOp_hearers {Γ out : List Located}
    (op : ProtocolOp operations functions protocols deployed)
    (arguments : Operands Γ (ProtocolOp.arguments op))
    (bodies : Regions (ProtocolDialect operations functions protocols deployed)
      (ProtocolOp.regions op))
    (rest : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll Γ (ProtocolOp.results op)) out)
    (unique : (regionSites (Region.letOp (dialect := ProtocolDialect operations functions
      protocols deployed) op arguments bodies rest)).Nodup)
    (agrees : ∀ path number,
      siteStart path number ∈ regionSites (Region.letOp (dialect := ProtocolDialect operations
        functions protocols deployed) op arguments bodies rest) →
      whole path number = regionHearers callees first second (Region.letOp
        (dialect := ProtocolDialect operations functions protocols deployed) op arguments bodies
        rest) path number) :
    (∀ path number, siteStart path number ∈ ProtocolOp.sites op →
        whole path number = opHearers callees first second op path number) ∧
      ((regionsSites bodies).Nodup ∧ ∀ path number, siteStart path number ∈ regionsSites bodies →
        whole path number = regionsHearers callees first second bodies path number) ∧
      ((regionSites rest).Nodup ∧ ∀ path number, siteStart path number ∈ regionSites rest →
        whole path number = regionHearers callees first second rest path number) := by
  have split : (regionSites rest ++ (regionsSites bodies ++ ProtocolOp.sites op)).Nodup := unique
  obtain ⟨restUnique, nestedUnique, apart⟩ := List.nodup_append.mp split
  obtain ⟨bodiesUnique, _, nestedApart⟩ := List.nodup_append.mp nestedUnique
  have answers : ∀ path number,
      regionHearers callees first second (Region.letOp (dialect := ProtocolDialect operations
        functions protocols deployed) op arguments bodies rest) path number =
        (opHearers callees first second op path number).or
          ((regionsHearers callees first second bodies path number).or
            (regionHearers callees first second rest path number)) := fun _ _ => rfl
  refine ⟨fun path number inside => ?_, ⟨bodiesUnique, fun path number inside => ?_⟩,
    ⟨restUnique, fun path number inside => ?_⟩⟩
  · rw [agrees path number (List.mem_append_right _ (List.mem_append_right _ inside)), answers,
      regionsHearers_outside callees first second bodies path number fun other =>
        nestedApart _ other _ inside rfl,
      regionHearers_outside callees first second rest path number fun other =>
        apart _ other _ (List.mem_append_right _ inside) rfl,
      Option.or_none, Option.or_none]
  · rw [agrees path number (List.mem_append_right _ (List.mem_append_left _ inside)), answers,
      opHearers_outside callees first second op path number fun other =>
        nestedApart _ inside _ other rfl,
      regionHearers_outside callees first second rest path number fun other =>
        apart _ other _ (List.mem_append_left _ inside) rfl,
      Option.or_none, Option.none_or]
  · rw [agrees path number (List.mem_append_left _ inside), answers,
      opHearers_outside callees first second op path number fun other =>
        apart _ inside _ (List.mem_append_right _ other) rfl,
      regionsHearers_outside callees first second bodies path number fun other =>
        apart _ inside _ (List.mem_append_left _ other) rfl,
      Option.none_or, Option.none_or]

/-- The answers of the first of several closed regions and of the later ones, when their
sites are pairwise different. -/
theorem cons_hearers {inputs outputs : List Located}
    {signatures : List (List Located × List Located)}
    (body : Region (ProtocolDialect operations functions protocols deployed) (bindAll [] inputs)
      outputs)
    (tail : Regions (ProtocolDialect operations functions protocols deployed) signatures)
    (unique : (regionsSites (Regions.cons body tail)).Nodup)
    (agrees : ∀ path number, siteStart path number ∈ regionsSites (Regions.cons body tail) →
      whole path number =
        regionsHearers callees first second (Regions.cons body tail) path number) :
    ((regionSites body).Nodup ∧ ∀ path number, siteStart path number ∈ regionSites body →
        whole path number = regionHearers callees first second body path number) ∧
      ((regionsSites tail).Nodup ∧ ∀ path number, siteStart path number ∈ regionsSites tail →
        whole path number = regionsHearers callees first second tail path number) := by
  have split : (regionsSites tail ++ regionSites body).Nodup := unique
  obtain ⟨tailUnique, bodyUnique, apart⟩ := List.nodup_append.mp split
  refine ⟨⟨bodyUnique, fun path number inside => ?_⟩, ⟨tailUnique, fun path number inside => ?_⟩⟩
  · rw [agrees path number (List.mem_append_right _ inside)]
    show (regionHearers callees first second body path number).or
      (regionsHearers callees first second tail path number) = _
    rw [regionsHearers_outside callees first second tail path number fun other =>
      apart _ other _ inside rfl, Option.or_none]
  · rw [agrees path number (List.mem_append_left _ inside)]
    show (regionHearers callees first second body path number).or
      (regionsHearers callees first second tail path number) = _
    rw [regionHearers_outside callees first second body path number fun other =>
      apart _ inside _ other rfl, Option.none_or]

end Hearers

/-! ## Listeners that read the answers of a region -/

/-- The listeners read given answers below a path: at every site below the path where the
answers say which sides hear, the listeners say the same. -/
@[expose] def Listeners.ReadBelow (listeners : Listeners) (path : List Nat) (whole : Hearers) :
    Prop :=
  ∀ (rest : List Nat) (identity number : Nat) (hearers : Bool × Bool),
    whole rest number = some hearers →
      listeners.first ⟨path ++ rest, identity, number⟩ = hearers.1 ∧
        listeners.second ⟨path ++ rest, identity, number⟩ = hearers.2

/-- The listeners that read given answers below a path. Where no operation answers, and at
a site that is not below the path, neither side hears. -/
@[expose] def Listeners.below (path : List Nat) (whole : Hearers) : Listeners where
  first site :=
    if path <+: site.path then
      ((whole (site.path.drop path.length) site.number).getD (false, false)).1
    else false
  second site :=
    if path <+: site.path then
      ((whole (site.path.drop path.length) site.number).getD (false, false)).2
    else false

theorem Listeners.below_reads (path : List Nat) (whole : Hearers) :
    (Listeners.below path whole).ReadBelow path whole := by
  intro rest identity number hearers answers
  simp only [Listeners.below, List.prefix_append, ↓reduceIte, List.drop_left, answers,
    Option.getD_some, and_self]

section Listens

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool} {typeTable : TypeTable} {roles : Nat}
  {listeners : Listeners} {listens : ListenTable protocols} {callees : HearerTable protocols}
  {first second : Side} {identity : Nat} {path : List Nat} {whole : Hearers}

/-- Listeners that read the answer of one operation below a path are those of the operation,
for two sides that each hold at most one of the roles of the definition. -/
theorem op_listens
    (calleesListen : ∀ {header : ProtocolHeader} (callee : Var protocols header) (path : List Nat)
      (first second : Side), first.AtMostOne header.roles → second.AtMostOne header.roles →
        listeners.ReadBelow path ((callees.get callee) first second) →
          (listens.get callee) path first second)
    (oneFirst : first.AtMostOne roles) (oneSecond : second.AtMostOne roles)
    (reads : listeners.ReadBelow path whole) {enclosing : Option (List Nat)}
    (op : ProtocolOp operations functions protocols deployed)
    (clean : ProtocolOp.violation typeTable roles enclosing op = none)
    (agrees : ∀ rest number, siteStart rest number ∈ ProtocolOp.sites op →
      whole rest number = opHearers callees first second op rest number) :
    opListens listeners (ownSites identity path) listens first second op := by
  cases op with
  | «at» role op bodies => trivial
  | exchange sender receiver site type => trivial
  | sample owner site law populated => trivial
  | «repeat» participants count carried collected captures covered => trivial
  | choose participants tag captures outputs covered => trivial
  | draw owner receivers site law populated =>
      have own : whole [] site =
          some (second owner && receivers.any first, first owner && receivers.any second) :=
        (agrees [] site (by rw [ProtocolOp.sites_draw]; exact List.mem_singleton_self site)).trans
          (ite_eq_left ⟨rfl, rfl⟩)
      have read := reads [] identity site _ own
      rw [List.append_nil] at read
      have below := (ProtocolOp.violation_draw clean).2
      have distinct := ProtocolOp.violation_draw_receivers clean
      exact ⟨read.1, read.2, hearsOnce_of_atMostOne oneFirst receivers distinct below,
        hearsOnce_of_atMostOne oneSecond receivers distinct below⟩
  | apply callee roleMap site permitted =>
      obtain ⟨below, sameLength, distinct⟩ := ProtocolOp.violation_apply clean
      refine calleesListen callee (path ++ [site]) _ _
        (sameLength ▸ oneFirst.preimage below distinct)
        (sameLength ▸ oneSecond.preimage below distinct) ?_
      intro rest calleeIdentity number hearers answers
      have own : whole (site :: rest) number = some hearers :=
        (agrees (site :: rest) number
          (by rw [ProtocolOp.sites_apply]; exact List.mem_singleton_self site)).trans
          ((ite_eq_left rfl).trans answers)
      have read := reads (site :: rest) calleeIdentity number hearers own
      rw [List.append_assoc]
      exact read

mutual
  /-- Listeners that read, below a path, the answers of a region whose sites are pairwise
  different are those of the region, for two sides that each hold at most one of the roles
  of the definition. -/
  theorem region_listens_part
      (calleesListen : ∀ {header : ProtocolHeader} (callee : Var protocols header)
        (path : List Nat) (first second : Side), first.AtMostOne header.roles →
          second.AtMostOne header.roles →
          listeners.ReadBelow path ((callees.get callee) first second) →
            (listens.get callee) path first second)
      (oneFirst : first.AtMostOne roles) (oneSecond : second.AtMostOne roles)
      (reads : listeners.ReadBelow path whole) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
        (enclosing : Option (List Nat)), Region.Legal typeTable roles enclosing region →
        (regionSites region).Nodup →
        (∀ rest number, siteStart rest number ∈ regionSites region →
          whole rest number = regionHearers callees first second region rest number) →
        regionListens listeners (ownSites identity path) listens first second region
    | .ret _, _, _, _, _ => trivial
    | .stop _, _, _, _, _ => trivial
    | .bind body rest, enclosing, legal, unique, agrees => by
        have parts := bind_hearers callees first second whole body rest unique agrees
        exact ⟨region_listens_part calleesListen oneFirst oneSecond reads body enclosing
            legal.bind.1 parts.1.1 parts.1.2,
          region_listens_part calleesListen oneFirst oneSecond reads rest enclosing legal.bind.2
            parts.2.1 parts.2.2⟩
    | .letOp op arguments bodies rest, enclosing, legal, unique, agrees => by
        obtain ⟨clean, nestedLegal, restLegal⟩ := legal.letOp
        have parts := letOp_hearers callees first second whole op arguments bodies rest unique
          agrees
        exact ⟨op_listens calleesListen oneFirst oneSecond reads op clean parts.1,
          regions_listen_part calleesListen oneFirst oneSecond reads bodies _ nestedLegal
            parts.2.1.1 parts.2.1.2,
          region_listens_part calleesListen oneFirst oneSecond reads rest enclosing restLegal
            parts.2.2.1 parts.2.2.2⟩

  theorem regions_listen_part
      (calleesListen : ∀ {header : ProtocolHeader} (callee : Var protocols header)
        (path : List Nat) (first second : Side), first.AtMostOne header.roles →
          second.AtMostOne header.roles →
          listeners.ReadBelow path ((callees.get callee) first second) →
            (listens.get callee) path first second)
      (oneFirst : first.AtMostOne roles) (oneSecond : second.AtMostOne roles)
      (reads : listeners.ReadBelow path whole)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures)
        (enclosing : Option (List Nat)), Regions.Legal typeTable roles enclosing regions →
        (regionsSites regions).Nodup →
        (∀ rest number, siteStart rest number ∈ regionsSites regions →
          whole rest number = regionsHearers callees first second regions rest number) →
        regionsListens listeners (ownSites identity path) listens first second regions
    | .nil, _, _, _, _ => trivial
    | .cons body tail, enclosing, legal, unique, agrees => by
        have parts := cons_hearers callees first second whole body tail unique agrees
        exact ⟨region_listens_part calleesListen oneFirst oneSecond reads body enclosing
            legal.cons.1 parts.1.1 parts.1.2,
          regions_listen_part calleesListen oneFirst oneSecond reads tail enclosing legal.cons.2
            parts.2.1 parts.2.2⟩
end

end Listens

/-! ## The protocols of a program -/

section Programs

variable {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader}

/-- For every protocol of a program and two sides: the sides that hear at the sites relative
to the protocol. -/
@[expose] def Protocols.hearers :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      HearerTable protocols
  | _, .nil => .nil
  | _, .snoc earlier definition _ =>
      .cons (fun first second => regionHearers earlier.hearers first second definition.body)
        earlier.hearers

/-- For every protocol of a program: that given listeners are those of the protocol reached
under a path, for two sides. -/
@[expose] def Protocols.listens (listeners : Listeners) (identities : Identities) :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      ListenTable protocols
  | _, .nil => .nil
  | _, .snoc (protocols := earlierHeaders) earlier definition _ =>
      .cons (fun path first second =>
          regionListens listeners (ownSites (identities earlierHeaders.length) path)
            (earlier.listens listeners identities) first second definition.body)
        (earlier.listens listeners identities)

/-- Listeners that read, below a path, what a protocol of a program answers for two sides
that each hold at most one of its roles are those of the protocol reached under the path. -/
theorem Protocols.listened (listeners : Listeners) (identities : Identities) :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols) {header : ProtocolHeader}
      (callee : Var protocols header) (path : List Nat) (first second : Side),
      first.AtMostOne header.roles → second.AtMostOne header.roles →
      listeners.ReadBelow path ((program.hearers.get callee) first second) →
        ((program.listens listeners identities).get callee) path first second
  | _, .nil, _, callee, _, _, _, _, _, _ => callee.elimNil
  | _, .snoc earlier definition wellFormed, _, callee, path, first, second, oneFirst, oneSecond,
      reads => by
      cases callee with
      | here =>
          exact region_listens_part (Protocols.listened listeners identities earlier) oneFirst
            oneSecond reads definition.body none (ProtocolDefinition.body_legal wellFormed)
            (ProtocolDefinition.regionSites_nodup wellFormed) fun _ _ _ => rfl
      | there callee =>
          exact Protocols.listened listeners identities earlier callee path first second
            oneFirst oneSecond reads

/-- The listeners of a protocol of a program reached under a path, for two sides: at every
site below the path, which of the two sides hears there. -/
@[expose] def Protocols.listeners {protocols : List ProtocolHeader}
    (program : Protocols typeTable operations functions protocols) {header : ProtocolHeader}
    (entry : Var protocols header) (path : List Nat) (first second : Side) : Listeners :=
  Listeners.below path ((program.hearers.get entry) first second)

/-- The listeners of a protocol of a program are those of the protocol, for two sides that
each hold at most one of its roles. -/
theorem Protocols.entry_listened (identities : Identities) {protocols : List ProtocolHeader}
    (program : Protocols typeTable operations functions protocols) {header : ProtocolHeader}
    (entry : Var protocols header) (path : List Nat) (first second : Side)
    (oneFirst : first.AtMostOne header.roles) (oneSecond : second.AtMostOne header.roles) :
    ((program.listens (program.listeners entry path first second) identities).get entry) path
      first second :=
  Protocols.listened _ identities program entry path first second oneFirst oneSecond
    (Listeners.below_reads path _)

end Programs

end Zkc.Core
