module

public import Zkc.Core.Specialize
public import Zkc.Core.ThreadSites
public import Zkc.Core.Laws
public import Zkc.Core.RoundTrip

public section

/-! The image of a legal region under a threading step passes the check of a definition.

The check of a definition (`ProtocolDefinition.violation`) decides the signature, then
passes over the body (`protocolRegionSites`) and collects its sites, then tests the sites.
This file says what the pass finds on what a threading step makes of a legal region.

- `Region.Passes`, `Regions.Passes`: the pass over a region succeeds from every list of
  sites and returns the given sites before them. A region is built from parts that pass
  (`Region.Passes.ret`, `.bind`, `.letOp`, `Regions.Passes.cons`).
- `Emitted.Passes`: a sequence of operations that a rule emits has no violation, results
  of types of the package and the given sites; it is built from operations
  (`Emitted.Passes.operation`, `.local`) and sequences (`.andThen`), and what it stands
  before passes with its sites added (`Emitted.Passes.wrap`).
- `Rule.Legal`: the obligation of a rule. What it emits at an exchange without a violation
  and at a draw between two roles that may act there passes, with no site but the site of
  the exchange or the draw; its entry passes when its threaded body does, with the sites of
  the body; the signature of its entry has no violation; and where it emits anything, the
  types of the two threaded values are types of the package.
- `plainRegion_passes`: the copy of a legal region passes, with the sites of the region.
- `threadRegion_passes`: the image that threads of a legal region passes, with sites
  among those of the region, when the types of the two threaded values are types of the
  package; and they are when the region contains a rewritten operation
  (`ImagePasses`). The two threaded values of a threaded `repeat` or `choose` are held by
  its participants because a region with a rewritten operation names both transcript roles
  (`touches_participants`).
- `Threads.header_legal`: the signature of the image that threads has no violation when
  the definition's has none and its two transcript roles are roles of the definition, which
  they are when the body contains a rewritten operation (`touches_below`).
- `ProtocolDefinition.violation_of_passes`: a definition whose signature has no violation
  and whose body passes with sites among those of a well-formed definition has no
  violation.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

/-! ## Lists of conditions -/

/-- Conditions that all hold have no violation. -/
theorem firstViolation_of_all :
    ∀ {conditions : List (Bool × Violation)}, (∀ pair ∈ conditions, pair.1 = true) →
      firstViolation conditions = none
  | [], _ => rfl
  | (holds, violation) :: rest, all => by
      have head : holds = true := all (holds, violation) List.mem_cons_self
      subst head
      exact firstViolation_of_all (conditions := rest) fun pair member =>
        all pair (List.mem_cons_of_mem _ member)

/-- Two lists of conditions have no violation exactly when neither has one. -/
theorem firstViolation_append (first second : List (Bool × Violation)) :
    firstViolation (first ++ second) = none ↔
      firstViolation first = none ∧ firstViolation second = none :=
  ⟨fun clean =>
    ⟨firstViolation_of_all fun pair member =>
        firstViolation_none clean pair (List.mem_append_left _ member),
      firstViolation_of_all fun pair member =>
        firstViolation_none clean pair (List.mem_append_right _ member)⟩,
    fun clean => firstViolation_of_all fun pair member =>
      (List.mem_append.mp member).elim (firstViolation_none clean.1 pair)
        (firstViolation_none clean.2 pair)⟩

/-! ## Sites -/

/-- The uniqueness test accepts sites that are pairwise different, below the limit and not
seen before. -/
theorem unusedSites_complete :
    ∀ (sites : List Nat) (seen : Nat), sites.Nodup →
      (∀ site ∈ sites, seen.testBit site = false ∧ site < siteLimit) →
      unusedSites seen sites = none
  | [], _, _, _ => rfl
  | site :: rest, seen, nodup, fresh => by
      obtain ⟨absent, nodupRest⟩ := List.nodup_cons.mp nodup
      obtain ⟨unseen, below⟩ := fresh site List.mem_cons_self
      unfold unusedSites
      rw [Nat.blt_eq.mpr below, unseen]
      refine unusedSites_complete rest _ nodupRest fun other member => ?_
      refine ⟨?_, (fresh other (List.mem_cons_of_mem _ member)).2⟩
      rw [testBit_mark, (fresh other (List.mem_cons_of_mem _ member)).1]
      have different : site ≠ other := fun same => absent (same ▸ member)
      simp [different]

/-- Sites among sites that pass the uniqueness test pass it. -/
theorem sitesViolation_sublist {kept sites : List Nat} (among : kept.Sublist sites)
    (clean : sitesViolation sites = none) : sitesViolation kept = none := by
  obtain ⟨nodup, fresh⟩ := unusedSites_spec sites 0 clean
  exact unusedSites_complete kept 0 (nodup.sublist among) fun site member =>
    fresh site (among.subset member)

/-! ## The types of the threaded values -/

/-- The types of the two threaded values are types of the package. -/
@[expose] def Threads.Named (typeTable : TypeTable) (t : Threads) : Prop :=
  Ty.named typeTable t.prover = true ∧ Ty.named typeTable t.verifier = true

/-- The two threaded values before values of types of the package have types of the
package. -/
theorem Threads.Named.states {typeTable : TypeTable} {t : Threads} (named : t.Named typeTable)
    (roles : TranscriptRoles) {rest : List Located}
    (others : Located.allNamed typeTable rest = true) :
    Located.allNamed typeTable (t.states roles ++ rest) = true := by
  show (Ty.named typeTable t.prover &&
    (Ty.named typeTable t.verifier && Located.allNamed typeTable rest)) = true
  rw [named.1, named.2, others]
  rfl

/-- Values after the two threaded values have types of the package when all do. -/
theorem Threads.named_of_states {typeTable : TypeTable} {t : Threads} {roles : TranscriptRoles}
    {rest : List Located} (named : Located.allNamed typeTable (t.states roles ++ rest) = true) :
    t.Named typeTable := by
  have parts : (Ty.named typeTable t.prover &&
      (Ty.named typeTable t.verifier && Located.allNamed typeTable rest)) = true := named
  simp only [Bool.and_eq_true] at parts
  exact ⟨parts.1, parts.2.1⟩

/-! ## A region that passes the check -/

section Passes

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool} {typeTable : TypeTable} {roles : Nat}
  {enclosing : Option (List Nat)}

/-- The pass of the check over a region succeeds from every list of sites, and returns the
given sites before them. -/
@[expose] def Region.Passes (typeTable : TypeTable) (roles : Nat) (enclosing : Option (List Nat))
    {Γ out : List Located}
    (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
    (kept : List Nat) : Prop :=
  ∀ sites, protocolRegionSites typeTable roles enclosing region sites = .ok (kept ++ sites)

/-- The pass over closed regions succeeds from every list of sites, and returns the given
sites before them. -/
@[expose] def Regions.Passes (typeTable : TypeTable) (roles : Nat) (enclosing : Option (List Nat))
    {signatures : List (List Located × List Located)}
    (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures)
    (kept : List Nat) : Prop :=
  ∀ sites, protocolRegionsSites typeTable roles enclosing regions sites = .ok (kept ++ sites)

/-- A region that passes is legal. -/
theorem Region.Passes.legal {Γ out : List Located}
    {region : Region (ProtocolDialect operations functions protocols deployed) Γ out}
    {kept : List Nat} (passes : Region.Passes typeTable roles enclosing region kept) :
    Region.Legal typeTable roles enclosing region :=
  ⟨[], _, passes []⟩

theorem Region.Passes.ret {Γ out : List Located} (values : Operands Γ out) :
    Region.Passes typeTable roles enclosing
      (Region.ret (dialect := ProtocolDialect operations functions protocols deployed) values)
      [] := by
  intro sites
  unfold protocolRegionSites
  rfl

/-- The pass over a region that starts with a nested block, when the values of the block
have types of the package. -/
theorem protocolRegionSites_after_block {Γ mid out : List Located}
    {body : Region (ProtocolDialect operations functions protocols deployed) Γ mid}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ mid) out}
    {first : List Nat} (named : Located.allNamed typeTable mid = true)
    (bodyPasses : Region.Passes typeTable roles enclosing body first) (sites : List Nat) :
    protocolRegionSites typeTable roles enclosing (Region.bind body next) sites =
      protocolRegionSites typeTable roles enclosing next (first ++ sites) := by
  rw [protocolRegionSites, named, bodyPasses sites]
  rfl

theorem Region.Passes.bind {Γ mid out : List Located}
    {body : Region (ProtocolDialect operations functions protocols deployed) Γ mid}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ mid) out}
    {first second : List Nat} (named : Located.allNamed typeTable mid = true)
    (bodyPasses : Region.Passes typeTable roles enclosing body first)
    (nextPasses : Region.Passes typeTable roles enclosing next second) :
    Region.Passes typeTable roles enclosing (Region.bind body next) (second ++ first) := by
  intro sites
  rw [protocolRegionSites_after_block named bodyPasses, nextPasses, List.append_assoc]

/-- The pass over a region that starts with an operation without a violation, whose results
have types of the package and whose nested regions pass. -/
theorem protocolRegionSites_after_operation {Γ out : List Located}
    {op : ProtocolOp operations functions protocols deployed}
    {arguments : Operands Γ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed)
      (ProtocolOp.regions op)}
    {next : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll Γ (ProtocolOp.results op)) out}
    {nested : List Nat}
    (clean : ProtocolOp.violation typeTable roles enclosing op = none)
    (named : Located.allNamed typeTable (ProtocolOp.results op) = true)
    (bodiesPass : Regions.Passes typeTable roles (ProtocolOp.enclosing enclosing op) bodies nested)
    (sites : List Nat) :
    protocolRegionSites typeTable roles enclosing
        (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
          arguments bodies next) sites =
      protocolRegionSites typeTable roles enclosing next
        (nested ++ (ProtocolOp.sites op ++ sites)) := by
  rw [protocolRegionSites, clean]
  dsimp only
  rw [named, bodiesPass]
  rfl

theorem Region.Passes.letOp {Γ out : List Located}
    {op : ProtocolOp operations functions protocols deployed}
    {arguments : Operands Γ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed)
      (ProtocolOp.regions op)}
    {next : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll Γ (ProtocolOp.results op)) out}
    {nested after : List Nat}
    (clean : ProtocolOp.violation typeTable roles enclosing op = none)
    (named : Located.allNamed typeTable (ProtocolOp.results op) = true)
    (bodiesPass : Regions.Passes typeTable roles (ProtocolOp.enclosing enclosing op) bodies nested)
    (nextPasses : Region.Passes typeTable roles enclosing next after) :
    Region.Passes typeTable roles enclosing
      (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies next)
      (after ++ (nested ++ ProtocolOp.sites op)) := by
  intro sites
  rw [protocolRegionSites_after_operation clean named bodiesPass, nextPasses]
  simp only [List.append_assoc]

theorem Regions.Passes.nil :
    Regions.Passes typeTable roles enclosing
      (Regions.nil (dialect := ProtocolDialect operations functions protocols deployed)) [] := by
  intro sites
  unfold protocolRegionsSites
  rfl

theorem Regions.Passes.cons {inputs outputs : List Located}
    {rest : List (List Located × List Located)}
    {body : Region (ProtocolDialect operations functions protocols deployed) (bindAll [] inputs)
      outputs}
    {tail : Regions (ProtocolDialect operations functions protocols deployed) rest}
    {first later : List Nat}
    (bodyPasses : Region.Passes typeTable roles enclosing body first)
    (tailPasses : Regions.Passes typeTable roles enclosing tail later) :
    Regions.Passes typeTable roles enclosing (Regions.cons body tail) (later ++ first) := by
  intro sites
  rw [protocolRegionsSites, bodyPasses sites]
  dsimp only
  rw [tailPasses, List.append_assoc]

/-- The results of the first operation of a legal region have types of the package. -/
theorem Region.Legal.results_named {Γ out : List Located}
    {op : ProtocolOp operations functions protocols deployed}
    {arguments : Operands Γ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed)
      (ProtocolOp.regions op)}
    {next : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll Γ (ProtocolOp.results op)) out}
    (legal : Region.Legal typeTable roles enclosing
      (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies next)) :
    Located.allNamed typeTable (ProtocolOp.results op) = true := by
  obtain ⟨sites, result, passes⟩ := legal
  exact (protocolRegionSites_letOp passes).2.1

/-- The values of the nested block that a legal region starts with have types of the
package. -/
theorem Region.Legal.mid_named {Γ mid out : List Located}
    {body : Region (ProtocolDialect operations functions protocols deployed) Γ mid}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ mid) out}
    (legal : Region.Legal typeTable roles enclosing (Region.bind body next)) :
    Located.allNamed typeTable mid = true := by
  obtain ⟨sites, result, passes⟩ := legal
  exact (protocolRegionSites_bind passes).1

/-! ## Roles that may act -/

/-- A role may act at a place: it is below the role count and, inside a `repeat` or
`choose`, a participant. -/
@[expose] def Acts (roles : Nat) (enclosing : Option (List Nat)) (role : Nat) : Prop :=
  Nat.blt role roles = true ∧ participates enclosing role = true

/-- The roles that an operation without a violation names may act where it stands. -/
theorem ProtocolOp.roles_act {op : ProtocolOp operations functions protocols deployed}
    (legal : ProtocolOp.violation typeTable roles enclosing op = none) :
    ∀ role ∈ ProtocolOp.roles op, Acts roles enclosing role := by
  have acting : firstViolation (actingRoles roles enclosing (ProtocolOp.roles op)) = none →
      ((ProtocolOp.roles op).all (participates enclosing)) = true := fun none_ =>
    firstViolation_none none_ (_, .roleOutsideParticipants)
      (List.mem_cons_of_mem _ List.mem_cons_self)
  have prefix_ : ∀ {more : List (Bool × Violation)},
      firstViolation (actingRoles roles enclosing (ProtocolOp.roles op) ++ more) = none →
        ((ProtocolOp.roles op).all (participates enclosing)) = true := fun none_ =>
    firstViolation_none none_ (_, .roleOutsideParticipants)
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have all : ((ProtocolOp.roles op).all (participates enclosing)) = true := by
    cases op with
    | «at» role op bodies => exact acting (earlierViolation_none legal).1
    | exchange sender receiver site type => exact prefix_ legal
    | draw owner receivers site law => exact prefix_ legal
    | sample owner site law => exact acting legal
    | «repeat» participants count carried collected captures covered => exact prefix_ legal
    | choose participants tag captures outputs covered => exact prefix_ legal
    | apply callee roleMap site permitted => exact prefix_ legal
  intro role member
  exact ⟨ProtocolOp.roles_below legal role member, List.all_eq_true.mp all role member⟩

/-- A local operation of a role that may act, whose regions have no violation, has no
violation. -/
theorem ProtocolOp.violation_at_none {role : Nat} {op : LocalOp operations functions deployed}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions}
    (acts : Acts roles enclosing role) (clean : localRegionsViolation typeTable bodies = none) :
    ProtocolOp.violation (protocols := protocols) typeTable roles enclosing (.at role op bodies) =
      none := by
  have acting : firstViolation (actingRoles roles enclosing [role]) = none :=
    firstViolation_of_all fun pair member => by
      simp only [actingRoles, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp [acts.1]
      · simp [acts.2]
  show earlierViolation (firstViolation (actingRoles roles enclosing [role]))
    (localRegionsViolation typeTable bodies) = none
  rw [acting, clean]
  rfl

/-! ## Emitted operations that pass the check -/

/-- A sequence of emitted operations has no violation, results of types of the package and
the given sites: the pass over the sequence before a region is the pass over the region
from those sites and the sites met before. -/
@[expose] def Emitted.Passes (typeTable : TypeTable) (roles : Nat) (enclosing : Option (List Nat))
    {Δ results : List Located}
    (emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ results)
    (added : List Nat) : Prop :=
  ∀ (out : List Located)
    (next : Region (ProtocolDialect operations functions protocols deployed) emitted.context out)
    (sites : List Nat),
    protocolRegionSites typeTable roles enclosing (emitted.wrap next) sites =
      protocolRegionSites typeTable roles enclosing next (added ++ sites)

/-- A region after emitted operations passes with their sites after its own. -/
theorem Emitted.Passes.wrap {Δ results out : List Located}
    {emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ results}
    {next : Region (ProtocolDialect operations functions protocols deployed) emitted.context out}
    {added kept : List Nat} (passes : Emitted.Passes typeTable roles enclosing emitted added)
    (nextPasses : Region.Passes typeTable roles enclosing next kept) :
    Region.Passes typeTable roles enclosing (emitted.wrap next) (kept ++ added) := by
  intro sites
  rw [passes _ next sites, nextPasses, List.append_assoc]

/-- A region after emitted operations without a site passes with its own sites. -/
theorem Emitted.Passes.wrap_nil {Δ results out : List Located}
    {emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ results}
    {next : Region (ProtocolDialect operations functions protocols deployed) emitted.context out}
    {kept : List Nat} (passes : Emitted.Passes typeTable roles enclosing emitted [])
    (nextPasses : Region.Passes typeTable roles enclosing next kept) :
    Region.Passes typeTable roles enclosing (emitted.wrap next) kept :=
  fun sites => (passes _ next sites).trans (nextPasses sites)

/-- One operation without a violation, whose results have types of the package and whose
nested regions pass without a site. -/
theorem Emitted.Passes.operation {Δ : List Located}
    {op : ProtocolOp operations functions protocols deployed}
    {arguments : Operands Δ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed)
      (ProtocolOp.regions op)}
    (clean : ProtocolOp.violation typeTable roles enclosing op = none)
    (named : Located.allNamed typeTable (ProtocolOp.results op) = true)
    (bodiesPass : Regions.Passes typeTable roles (ProtocolOp.enclosing enclosing op) bodies []) :
    Emitted.Passes typeTable roles enclosing
      (Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies)
      (ProtocolOp.sites op) :=
  fun _ next sites => protocolRegionSites_after_operation clean named bodiesPass sites

/-- One local operation of a role that may act, whose regions have no violation and whose
results have types of the package. It has no site. -/
theorem Emitted.Passes.local {Δ : List Located} {role : Nat}
    (op : LocalOp operations functions deployed)
    {bodies : Regions (LocalDialect operations functions deployed) op.regions}
    {arguments : Operands Δ
      (ProtocolOp.arguments (ProtocolOp.at (protocols := protocols) role op bodies))}
    (acts : Acts roles enclosing role) (named : Ty.allNamed typeTable op.results = true)
    (clean : localRegionsViolation typeTable bodies = none := by rfl) :
    Emitted.Passes typeTable roles enclosing
      (Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
        (.at role op bodies) arguments .nil) [] :=
  Emitted.Passes.operation (ProtocolOp.violation_at_none acts clean)
    ((Located.allNamed_atRole typeTable role op.results).trans named) Regions.Passes.nil

/-- A sequence, then a second one: the sites of the second before those of the first. -/
theorem Emitted.Passes.andThen {Δ first second results : List Located}
    {before : Emitted (ProtocolDialect operations functions protocols deployed) Δ first}
    {after : Emitted (ProtocolDialect operations functions protocols deployed) before.context
      second}
    {values : Operands after.context results} {earlier later : List Nat}
    (beforePasses : Emitted.Passes typeTable roles enclosing before earlier)
    (afterPasses : Emitted.Passes typeTable roles enclosing after later) :
    Emitted.Passes typeTable roles enclosing (before.andThen after values) (later ++ earlier) := by
  intro out next sites
  exact (beforePasses _ (after.wrap next) sites).trans
    ((afterPasses _ next (earlier ++ sites)).trans (by rw [List.append_assoc]; exact rfl))

end Passes

/-! ## Signatures -/

/-- The signature of a protocol has no violation. -/
@[expose] def ProtocolHeader.SignatureLegal (typeTable : TypeTable) (header : ProtocolHeader) :
    Prop :=
  firstViolation
    (portConditions typeTable header.roles (header.inputs ++ header.outputs) ++
      (agreementConditions header.agreements.inputs ++
        agreementConditions header.agreements.outputs)) = none

/-- The ports of a protocol have no violation exactly when the protocol has a role, the
holders of the ports are roles of it and their types are types of the package. -/
theorem portConditions_none {typeTable : TypeTable} {roles : Nat} {ports : List Located} :
    firstViolation (portConditions typeTable roles ports) = none ↔
      Nat.beq roles 0 = false ∧ (∀ port ∈ ports, Nat.blt port.holder roles = true) ∧
        Located.allNamed typeTable ports = true := by
  constructor
  · intro clean
    have holds := firstViolation_none clean
    refine ⟨?_, ?_, ?_⟩
    · have some := holds (_, .noRole) List.mem_cons_self
      simpa using some
    · have held := holds (_, .roleOutOfRange) (List.mem_cons_of_mem _ List.mem_cons_self)
      simpa only [List.all_eq_true] using held
    · exact holds (_, .nominalRow)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rintro ⟨some, held, named⟩
    refine firstViolation_of_all fun pair member => ?_
    simp only [portConditions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [some]
    · simpa only [List.all_eq_true] using held
    · exact named

/-- What a signature without a violation is. -/
theorem ProtocolHeader.signatureLegal_iff {typeTable : TypeTable} {header : ProtocolHeader} :
    header.SignatureLegal typeTable ↔
      (Nat.beq header.roles 0 = false ∧
        (∀ port ∈ header.inputs ++ header.outputs, Nat.blt port.holder header.roles = true) ∧
          Located.allNamed typeTable (header.inputs ++ header.outputs) = true) ∧
        firstViolation (agreementConditions header.agreements.inputs ++
          agreementConditions header.agreements.outputs) = none := by
  unfold ProtocolHeader.SignatureLegal
  rw [firstViolation_append, portConditions_none]

theorem occursIn_succ (number : Nat) :
    ∀ (numbers : List Nat),
      occursIn (numbers.map (· + 1)) (number + 1) = occursIn numbers number
  | [] => rfl
  | head :: rest => by
      show (Nat.beq (number + 1) (head + 1) || occursIn (rest.map (· + 1)) (number + 1)) =
        (Nat.beq number head || occursIn rest number)
      rw [occursIn_succ number rest]
      rfl

/-- Numbers that are each one more are as distinct as they were. -/
theorem distinctNumbers_succ :
    ∀ (numbers : List Nat), distinctNumbers (numbers.map (· + 1)) = distinctNumbers numbers
  | [] => rfl
  | number :: rest => by
      show (!(occursIn (rest.map (· + 1)) (number + 1)) && distinctNumbers (rest.map (· + 1))) =
        (!(occursIn rest number) && distinctNumbers rest)
      rw [occursIn_succ, distinctNumbers_succ rest]

/-- Agreements over ports that follow one more port have the conditions they had: the
holders are the same and every port is one position later. -/
theorem agreementConditions_under {ports : List Located} (head : Located)
    (agreements : List (Agreement ports)) :
    agreementConditions (agreements.map fun agreement => agreement.under head) =
      agreementConditions agreements := by
  have positions : ((agreements.map fun agreement => agreement.under head).flatMap
      fun agreement => agreement.copies.map (·.port.index)) =
        (agreements.flatMap fun agreement => agreement.copies.map (·.port.index)).map (· + 1) := by
    induction agreements with
    | nil => rfl
    | cons agreement rest ih =>
        simp only [List.map_cons, List.flatMap_cons, List.map_append, ih]
        congr 1
        simp only [Agreement.under, Agreement.copies, List.map_cons, List.map_map]
        rfl
  have holders : ((agreements.map fun agreement => agreement.under head).map fun agreement =>
      agreement.copies.map (·.holder)) =
        agreements.map fun agreement => agreement.copies.map (·.holder) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro agreement _
    simp only [Function.comp, Agreement.under, Agreement.copies, List.map_cons, List.map_map]
    rfl
  unfold agreementConditions copyConditions
  rw [holders, positions, distinctNumbers_succ]

/-- Agreements over ports that follow two more ports have the conditions they had. -/
theorem agreementConditions_under_two {ports : List Located} (first second : Located)
    (agreements : List (Agreement ports)) :
    agreementConditions
        (agreements.map fun agreement => (agreement.under second).under first) =
      agreementConditions agreements := by
  have twice : (agreements.map fun agreement => (agreement.under second).under first) =
      (agreements.map fun agreement => agreement.under second).map fun agreement =>
        agreement.under first := by
    rw [List.map_map]
    rfl
  rw [twice, agreementConditions_under, agreementConditions_under]

/-- The signature of the image that threads has no violation, when the definition's has
none, the two transcript roles are roles of the definition and the types of the threaded
values are types of the package. -/
theorem Threads.header_legal {typeTable : TypeTable} {t : Threads} (named : t.Named typeTable)
    {roles : TranscriptRoles} {header : ProtocolHeader}
    (prover : Nat.blt roles.prover header.roles = true)
    (verifier : Nat.blt roles.verifier header.roles = true)
    (legal : header.SignatureLegal typeTable) :
    (t.header (some roles) header).SignatureLegal typeTable := by
  rw [ProtocolHeader.signatureLegal_iff] at legal ⊢
  obtain ⟨⟨some, held, typed⟩, agreed⟩ := legal
  rw [Located.allNamed_append] at typed
  simp only [Bool.and_eq_true] at typed
  refine ⟨⟨some, ?_, ?_⟩, ?_⟩
  · intro port member
    change port ∈ (t.states roles ++ header.inputs) ++ (t.states roles ++ header.outputs) at member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with ((rfl | rfl) | input) | ((rfl | rfl) | output)
    · exact prover
    · exact verifier
    · exact held port (List.mem_append_left _ input)
    · exact prover
    · exact verifier
    · exact held port (List.mem_append_right _ output)
  · change Located.allNamed typeTable
      ((t.states roles ++ header.inputs) ++ (t.states roles ++ header.outputs)) = true
    rw [Located.allNamed_append, named.states roles typed.1, named.states roles typed.2]
    rfl
  · change firstViolation
      (agreementConditions (header.agreements.inputs.map fun agreement =>
          (agreement.under (t.second roles)).under (t.first roles)) ++
        agreementConditions (header.agreements.outputs.map fun agreement =>
          (agreement.under (t.second roles)).under (t.first roles))) = none
    rw [agreementConditions_under_two, agreementConditions_under_two]
    exact agreed

/-- The ports of every protocol of the list have types of the package. -/
@[expose] def HeadersNamed (typeTable : TypeTable) (protocols : List ProtocolHeader) : Prop :=
  ∀ {header : ProtocolHeader}, Var protocols header →
    Located.allNamed typeTable (header.inputs ++ header.outputs) = true

section Definitions

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {typeTable : TypeTable}

/-- What a definition without a violation is: its signature has none, and the sites of its
body pass the uniqueness test. Its body is legal (`ProtocolDefinition.body_legal`). -/
theorem ProtocolDefinition.violation_parts {header : ProtocolHeader}
    {definition : ProtocolDefinition operations functions protocols header}
    (wellFormed : definition.violation typeTable = none) :
    header.SignatureLegal typeTable ∧ sitesViolation (regionSites definition.body) = none := by
  have parts := earlierViolation_none wellFormed
  refine ⟨parts.1, ?_⟩
  have body := parts.2
  unfold ProtocolDefinition.sites at body
  split at body
  · cases body
  · rename_i sites collected
    have same := protocolRegionSites_collects typeTable header.roles definition.body none [] sites
      collected
    rw [same, List.append_nil] at body
    exact body

/-- A definition whose signature has no violation and whose body passes with sites that
pass the uniqueness test has no violation. -/
theorem ProtocolDefinition.violation_of_passes {header : ProtocolHeader}
    {definition : ProtocolDefinition operations functions protocols header} {kept : List Nat}
    (signature : header.SignatureLegal typeTable)
    (passes : Region.Passes typeTable header.roles none definition.body kept)
    (clean : sitesViolation kept = none) : definition.violation typeTable = none := by
  unfold ProtocolDefinition.violation ProtocolDefinition.sites
  unfold ProtocolHeader.SignatureLegal at signature
  rw [signature, passes []]
  show sitesViolation (kept ++ []) = none
  rw [List.append_nil]
  exact clean

/-- The ports of the protocols of a program have types of the package. -/
theorem Protocols.headersNamed :
    ∀ {protocols : List ProtocolHeader},
      Protocols typeTable operations functions protocols → HeadersNamed typeTable protocols
  | _, .nil => fun callee => callee.elimNil
  | _, .snoc earlier _ wellFormed => fun callee => by
      cases callee with
      | here =>
          exact (ProtocolHeader.signatureLegal_iff.mp
            (ProtocolDefinition.violation_parts wellFormed).1).1.2.2
      | there callee => exact earlier.headersNamed callee

end Definitions

/-! ## The obligation of a rule -/

/-- A rule emits what the check of a definition accepts.

- At an exchange from the prover to the verifier that has no violation and carries a type
  of the package, what the rule emits passes the check where the exchange stood, with no
  site but the exchange's.
- At a draw between the two transcript roles, which may both act where the draw stood, of
  a type of the package, what the rule emits passes the check, with no site but the draw's.
- The signature of the entry that the rule makes has no violation when the entry's has
  none and the two transcript roles are roles of the entry.
- The entry that the rule makes threads its body once, and passes the check with the sites
  of its threaded body when that passes.
- Where the rule emits anything, the types of the two threaded values are types of the
  package. -/
structure Rule.Legal (typeTable : TypeTable) {t : Threads} {operations : List OperationSignature}
    {functions : List FunctionHeader} (rule : Rule t operations functions) : Prop where
  exchange : ∀ {protocols : List ProtocolHeader} {deployed : Bool} (place : Place) (site : Nat)
    (type : Ty) {Δ : List Located} (value : Var Δ ⟨type, place.roles.prover⟩)
    (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles))
    (emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
      [⟨type, place.roles.verifier⟩, t.first place.roles, t.second place.roles]),
    rule.exchange place site type value first second = .ok emitted →
      t.Named typeTable ∧
        ∀ (roles : Nat) (enclosing : Option (List Nat)),
          ProtocolOp.violation typeTable roles enclosing
            (ProtocolOp.exchange (operations := operations) (functions := functions)
              (protocols := protocols) (deployed := deployed) place.roles.prover
              place.roles.verifier site type) = none →
          Ty.named typeTable type = true →
          ∃ added, added.Sublist [site] ∧ Emitted.Passes typeTable roles enclosing emitted added
  draw : ∀ {protocols : List ProtocolHeader} {deployed : Bool} (place : Place) (site : Nat)
    {inputs : List Ty} {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    {Δ : List Located} (first : Var Δ (t.first place.roles))
    (second : Var Δ (t.second place.roles))
    (emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
      [⟨output, place.roles.prover⟩, ⟨output, place.roles.verifier⟩, t.first place.roles,
        t.second place.roles]),
    rule.draw place site law first second = .ok emitted →
      t.Named typeTable ∧
        ∀ (roles : Nat) (enclosing : Option (List Nat)),
          Acts roles enclosing place.roles.prover → Acts roles enclosing place.roles.verifier →
          Ty.named typeTable output = true →
          ∃ added, added.Sublist [site] ∧ Emitted.Passes typeTable roles enclosing emitted added
  entryPorts : ∀ (roles : TranscriptRoles) (header : ProtocolHeader),
    Nat.blt roles.prover header.roles = true → Nat.blt roles.verifier header.roles = true →
    header.SignatureLegal typeTable →
      ((rule.entryPorts roles header).header header).SignatureLegal typeTable
  entry : ∀ {protocols : List ProtocolHeader} {deployed : Bool} (place : Place)
    (header : ProtocolHeader)
    (body : {Δ : List Located} → Renaming (bindAll [] header.inputs) Δ →
      Var Δ (t.first place.roles) → Var Δ (t.second place.roles) →
        Except StepRefusal (Region (ProtocolDialect operations functions protocols deployed) Δ
          (t.states place.roles ++ header.outputs)))
    (region : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll [] (rule.entryPorts place.roles header).inputs)
      (rule.entryPorts place.roles header).outputs),
    rule.entry place header body = .ok region →
      t.Named typeTable ∧
        (Nat.blt place.roles.prover header.roles = true →
          Nat.blt place.roles.verifier header.roles = true →
          Located.allNamed typeTable header.outputs = true →
          ∃ (Δ : List Located) (rename : Renaming (bindAll [] header.inputs) Δ)
            (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles))
            (threaded : Region (ProtocolDialect operations functions protocols deployed) Δ
              (t.states place.roles ++ header.outputs)),
            body rename first second = .ok threaded ∧
              ∀ kept, Region.Passes typeTable header.roles none threaded kept →
                Region.Passes typeTable header.roles none region kept)

/-! ## Rewritten operations name both transcript roles -/

theorem bothTouch_true {first second : Except StepRefusal Bool}
    (touched : bothTouch first second = .ok true) : first = .ok true ∨ second = .ok true := by
  match first, second, touched with
  | .ok true, .ok _, _ => exact Or.inl rfl
  | .ok false, .ok true, _ => exact Or.inr rfl
  | .ok false, .ok false, touched => cases touched

theorem preimageBelow_lt (roleMap : RoleMap) (role : Nat) :
    ∀ (bound : Nat) (found : { index : Nat // roleMap.apply index = role }),
      preimageBelow roleMap role bound = some found → found.val < bound
  | 0, _, none_ => nomatch none_
  | bound + 1, found, at_ => by
      unfold preimageBelow at at_
      split at at_
      · cases at_
        exact Nat.lt_succ_self bound
      · exact Nat.lt_succ_of_lt (preimageBelow_lt roleMap role bound found at_)

/-- A role that has a preimage under a role map is one of the map's entries. -/
theorem preimageOf_mem {roleMap : RoleMap} {role inner : Nat}
    (found : preimageOf roleMap (some role) = some inner) : role ∈ roleMap := by
  change (preimage roleMap role).map (·.val) = some inner at found
  cases at_ : preimage roleMap role with
  | none =>
      rw [at_] at found
      cases found
  | some index =>
      have below := preimageBelow_lt roleMap role roleMap.length index at_
      have member := RoleMap.apply_mem roleMap index.val below
      rw [index.property] at member
      exact member

section Touches

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} (t : Threads)
  {derives : Bool} {table : CalleeTable t.header old new} {definition prover verifier : Nat}

/-- An operation that is rewritten for a pair of roles names both. -/
theorem touchesOp_roles {op : ProtocolOp operations functions old deployed}
    (touched : touchesOp t derives table definition (some prover) (some verifier) op = .ok true) :
    prover ∈ ProtocolOp.roles op ∧ verifier ∈ ProtocolOp.roles op := by
  cases op with
  | «at» role op bodies => simp only [touchesOp] at touched; cases touched
  | sample owner site law => simp only [touchesOp] at touched; cases touched
  | «repeat» participants count carried collected captures covered =>
      simp only [touchesOp] at touched; cases touched
  | choose participants tag captures outputs covered => simp only [touchesOp] at touched; cases touched
  | exchange sender receiver site type =>
      simp only [touchesOp] at touched
      by_cases between : (isRole (some prover) sender && isRole (some verifier) receiver) = true
      · simp only [Bool.and_eq_true] at between
        rw [← Nat.eq_of_beq_eq_true between.1, ← Nat.eq_of_beq_eq_true between.2]
        exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      · rw [ite_eq_right between] at touched
        by_cases toward : (isRole (some verifier) sender && isRole (some prover) receiver) = true
        · rw [ite_eq_left toward] at touched
          cases touched
        · rw [ite_eq_right toward] at touched
          cases touched
  | draw owner receivers site law =>
      simp only [touchesOp] at touched
      by_cases owns : (isRole (some prover) owner || isRole (some verifier) owner) = true
      · rw [ite_eq_left owns] at touched
        by_cases deriving_ : derives = true
        · rw [ite_eq_left deriving_] at touched
          by_cases byProver : isRole (some prover) owner = true
          · rw [ite_eq_left byProver] at touched
            match receivers, touched with
            | [receiver], touched =>
                dsimp only at touched
                by_cases same : Nat.beq receiver verifier = true
                · rw [← Nat.eq_of_beq_eq_true byProver, ← Nat.eq_of_beq_eq_true same]
                  exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
                · rw [ite_eq_right same] at touched
                  cases touched
            | [], touched => cases touched
            | _ :: _ :: _, touched => cases touched
          · rw [ite_eq_right byProver] at touched
            have byVerifier : Nat.beq verifier owner = true := by
              cases isProver : isRole (some prover) owner with
              | true => exact absurd isProver byProver
              | false =>
                  rw [isProver] at owns
                  exact owns
            match receivers, touched with
            | [receiver], touched =>
                dsimp only at touched
                by_cases same : Nat.beq receiver prover = true
                · rw [← Nat.eq_of_beq_eq_true byVerifier, ← Nat.eq_of_beq_eq_true same]
                  exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self⟩
                · rw [ite_eq_right same] at touched
                  cases touched
            | [], touched => cases touched
            | _ :: _ :: _, touched => cases touched
        · rw [ite_eq_right deriving_] at touched
          by_cases byProver : isRole (some prover) owner = true
          · rw [ite_eq_left byProver] at touched
            dsimp only at touched
            by_cases received : occursIn receivers verifier = true
            · rw [ite_eq_left received] at touched
              cases touched
            · rw [ite_eq_right received] at touched
              cases touched
          · rw [ite_eq_right byProver] at touched
            dsimp only at touched
            by_cases received : occursIn receivers prover = true
            · rw [ite_eq_left received] at touched
              cases touched
            · rw [ite_eq_right received] at touched
              cases touched
      · rw [ite_eq_right owns] at touched
        cases touched
  | apply callee roleMap site permitted =>
      simp only [touchesOp] at touched
      cases atProver : preimageOf roleMap (some prover) with
      | none =>
          rw [atProver] at touched
          cases touched
      | some inner =>
          cases atVerifier : preimageOf roleMap (some verifier) with
          | none =>
              rw [atProver, atVerifier] at touched
              cases touched
          | some outer => exact ⟨preimageOf_mem atProver, preimageOf_mem atVerifier⟩

variable {typeTable : TypeTable} {roles : Nat}

mutual
  /-- Inside a `repeat` or `choose` of a legal definition, a region with a rewritten
  operation has both transcript roles among the participants. -/
  theorem touches_participants {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        (enclosing : Option (List Nat)), Region.Legal typeTable roles enclosing region →
        touches t derives table definition (some prover) (some verifier) region = .ok true →
        ∀ (participants : List Nat), enclosing = some participants →
          occursIn participants prover = true ∧ occursIn participants verifier = true
    | .ret values, _, _, touched, _, _ => by
        simp only [touches] at touched
        cases touched
    | .stop reason, _, _, touched, _, _ => by
        simp only [touches] at touched
        cases touched
    | .bind body rest, enclosing, legal, touched, participants, inside => by
        unfold touches at touched
        rcases bothTouch_true touched with first | second
        · exact touches_participants body enclosing legal.bind.1 first participants inside
        · exact touches_participants rest enclosing legal.bind.2 second participants inside
    | .letOp op arguments bodies rest, enclosing, legal, touched, participants, inside => by
        subst inside
        unfold touches at touched
        have named := ProtocolOp.roles_participate legal.letOp.1
        rcases bothTouch_true touched with own | later
        · have both := touchesOp_roles t own
          exact ⟨named _ both.1, named _ both.2⟩
        · rcases bothTouch_true later with nested | after
          · rcases ProtocolOp.enclosing_cases (some participants) op with same | fresh
            · exact touchesRegions_participants bodies _ legal.letOp.2.1 nested participants same
            · have both := touchesRegions_participants bodies _ legal.letOp.2.1 nested _ fresh
              exact ⟨named _ ((occursIn_iff _ _).mp both.1), named _ ((occursIn_iff _ _).mp both.2)⟩
          · exact touches_participants rest _ legal.letOp.2.2 after participants rfl

  theorem touchesRegions_participants {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (enclosing : Option (List Nat)), Regions.Legal typeTable roles enclosing regions →
        touchesRegions t derives table definition (some prover) (some verifier) regions = .ok true →
        ∀ (participants : List Nat), enclosing = some participants →
          occursIn participants prover = true ∧ occursIn participants verifier = true
    | .nil, _, _, touched, _, _ => by
        simp only [touchesRegions] at touched
        cases touched
    | .cons body tail, enclosing, legal, touched, participants, inside => by
        unfold touchesRegions at touched
        rcases bothTouch_true touched with first | later
        · exact touches_participants body enclosing legal.cons.1 first participants inside
        · exact touchesRegions_participants tail enclosing legal.cons.2 later participants inside
end

/-- The two threaded values of a `choose` whose arms contain a rewritten operation are
held by its participants: the refusal `image` of that case of `threadRegion` cannot occur
for a legal definition. -/
theorem choose_states_held {participants : List Nat} {tag : ChoiceTag}
    {captures outputs : List Located} {covered : Located.heldBy participants outputs = true}
    {bodies : Regions (ProtocolDialect operations functions old deployed)
      (tag.regions participants captures outputs)}
    (legal : Regions.Legal typeTable roles (some participants) bodies)
    (place : Place)
    (touched : touchesRegions t derives table place.definition (some place.roles.prover)
      (some place.roles.verifier) bodies = .ok true) :
    Located.heldBy participants (t.states place.roles ++ outputs) = true := by
  have both := touchesRegions_participants t bodies _ legal touched participants rfl
  simp only [Located.heldBy, List.all_eq_true] at covered ⊢
  intro located member
  rcases List.mem_append.mp member with state | output
  · rcases List.mem_cons.mp state with rfl | second
    · exact both.1
    · rcases List.mem_cons.mp second with rfl | none_
      · exact both.2
      · cases none_
  · exact covered located output

/-- A region that starts with an operation contains a rewritten operation in the operation,
in its nested regions or in what follows. -/
theorem touches_letOp {Γ out : List Located}
    {op : ProtocolOp operations functions old deployed}
    {arguments : Operands Γ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions old deployed) (ProtocolOp.regions op)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (ProtocolOp.results op)) out}
    (touched : touches t derives table definition (some prover) (some verifier)
      (Region.letOp (dialect := ProtocolDialect operations functions old deployed) op arguments
        bodies rest) = .ok true) :
    touchesOp t derives table definition (some prover) (some verifier) op = .ok true ∨
      touchesRegions t derives table definition (some prover) (some verifier) bodies = .ok true ∨
      touches t derives table definition (some prover) (some verifier) rest = .ok true := by
  unfold touches at touched
  rcases bothTouch_true touched with own | later
  · exact .inl own
  · exact .inr (bothTouch_true later)

/-- An exchange that is rewritten is from the prover to the verifier. -/
theorem touchesOp_exchange {sender receiver site : Nat} {type : Ty}
    (touched : touchesOp (operations := operations) (functions := functions)
      (deployed := deployed) t derives table definition (some prover) (some verifier)
      (.exchange sender receiver site type) = .ok true) :
    sender = prover ∧ receiver = verifier := by
  simp only [touchesOp] at touched
  by_cases between : (isRole (some prover) sender && isRole (some verifier) receiver) = true
  · simp only [Bool.and_eq_true] at between
    exact ⟨(Nat.eq_of_beq_eq_true between.1).symm, (Nat.eq_of_beq_eq_true between.2).symm⟩
  · rw [if_neg between] at touched
    split at touched <;> cases touched

/-- A draw that is rewritten is by one transcript role with the other as its only
receiver. -/
theorem touchesOp_draw {owner site : Nat} {receivers : List Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {populated : output.populated = true}
    (touched : touchesOp (functions := functions) (deployed := deployed) t derives table
      definition (some prover) (some verifier) (.draw owner receivers site law populated) =
        .ok true) :
    (owner = verifier ∧ receivers = [prover]) ∨ (owner = prover ∧ receivers = [verifier]) := by
  simp only [touchesOp] at touched
  by_cases owns : (isRole (some prover) owner || isRole (some verifier) owner) = true
  · rw [if_pos owns] at touched
    by_cases deriving_ : derives = true
    · rw [if_pos deriving_] at touched
      by_cases byProver : isRole (some prover) owner = true
      · rw [if_pos byProver] at touched
        match receivers, touched with
        | [receiver], touched =>
            dsimp only at touched
            by_cases same : Nat.beq receiver verifier = true
            · exact .inr ⟨(Nat.eq_of_beq_eq_true byProver).symm,
                by rw [Nat.eq_of_beq_eq_true same]⟩
            · rw [if_neg same] at touched
              cases touched
        | [], touched => cases touched
        | _ :: _ :: _, touched => cases touched
      · rw [if_neg byProver] at touched
        have byVerifier : Nat.beq verifier owner = true := by
          cases isProver : isRole (some prover) owner with
          | true => exact absurd isProver byProver
          | false =>
              rw [isProver] at owns
              exact owns
        match receivers, touched with
        | [receiver], touched =>
            dsimp only at touched
            by_cases same : Nat.beq receiver prover = true
            · exact .inl ⟨(Nat.eq_of_beq_eq_true byVerifier).symm,
                by rw [Nat.eq_of_beq_eq_true same]⟩
            · rw [if_neg same] at touched
              cases touched
        | [], touched => cases touched
        | _ :: _ :: _, touched => cases touched
    · rw [if_neg deriving_] at touched
      by_cases byProver : isRole (some prover) owner = true
      · rw [if_pos byProver] at touched
        dsimp only at touched
        split at touched <;> cases touched
      · rw [if_neg byProver] at touched
        dsimp only at touched
        split at touched <;> cases touched
  · rw [if_neg owns] at touched
    cases touched

mutual
  /-- A legal region with a rewritten operation names both transcript roles in an operation,
  so both are below the role count. -/
  theorem touches_below {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        (enclosing : Option (List Nat)), Region.Legal typeTable roles enclosing region →
        touches t derives table definition (some prover) (some verifier) region = .ok true →
        Nat.blt prover roles = true ∧ Nat.blt verifier roles = true
    | .ret values, _, _, touched => by
        simp only [touches] at touched
        cases touched
    | .stop reason, _, _, touched => by
        simp only [touches] at touched
        cases touched
    | .bind body rest, enclosing, legal, touched => by
        unfold touches at touched
        rcases bothTouch_true touched with first | second
        · exact touches_below body enclosing legal.bind.1 first
        · exact touches_below rest enclosing legal.bind.2 second
    | .letOp op arguments bodies rest, enclosing, legal, touched => by
        rcases touches_letOp t touched with own | nested | after
        · have both := touchesOp_roles t own
          have below := ProtocolOp.roles_below legal.letOp.1
          exact ⟨below _ both.1, below _ both.2⟩
        · exact touchesRegions_below bodies _ legal.letOp.2.1 nested
        · exact touches_below rest _ legal.letOp.2.2 after

  theorem touchesRegions_below {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (enclosing : Option (List Nat)), Regions.Legal typeTable roles enclosing regions →
        touchesRegions t derives table definition (some prover) (some verifier) regions =
          .ok true →
        Nat.blt prover roles = true ∧ Nat.blt verifier roles = true
    | .nil, _, _, touched => by
        simp only [touchesRegions] at touched
        cases touched
    | .cons body tail, enclosing, legal, touched => by
        unfold touchesRegions at touched
        rcases bothTouch_true touched with first | later
        · exact touches_below body enclosing legal.cons.1 first
        · exact touchesRegions_below tail enclosing legal.cons.2 later
end

end Touches


/-! ## A copied region passes the check -/

section Copies

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} {t : Threads}
  {table : CalleeTable t.header old new} {typeTable : TypeTable} {roles : Nat}

/-- The sites of a region that starts with an operation. -/
theorem regionSites_letOp {Γ out : List Located}
    (op : ProtocolOp operations functions old deployed)
    (arguments : Operands Γ (ProtocolOp.arguments op))
    (bodies : Regions (ProtocolDialect operations functions old deployed) (ProtocolOp.regions op))
    (rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (ProtocolOp.results op)) out) :
    regionSites (Region.letOp (dialect := ProtocolDialect operations functions old deployed) op
        arguments bodies rest) =
      regionSites rest ++ (regionsSites bodies ++ ProtocolOp.sites op) := by
  rw [regionSites]

mutual
  /-- The copy of a legal region passes the check, with the sites of the region. -/
  theorem plainRegion_passes {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        (enclosing : Option (List Nat)), Region.Legal typeTable roles enclosing region →
        ∀ {Δ : List Located} (rename : Renaming Γ Δ)
          (copy : Region (ProtocolDialect operations functions new deployed) Δ out),
          plainRegion t table region rename = .ok copy →
          Region.Passes typeTable roles enclosing copy (regionSites region)
    | .ret values, _, _, _, rename, copy, copies => by
        unfold plainRegion at copies
        cases copies
        exact Region.Passes.ret _
    | .stop reason, _, legal, _, _, _, _ => (Region.Legal.not_stop legal).elim
    | .bind (mid := mid) body rest, enclosing, legal, _, rename, copy, copies => by
        unfold plainRegion at copies
        split at copies
        · rename_i first second copiesBody copiesRest
          cases copies
          exact Region.Passes.bind legal.mid_named
            (plainRegion_passes body enclosing legal.bind.1 rename first copiesBody)
            (plainRegion_passes rest enclosing legal.bind.2 _ second copiesRest)
        · cases copies
        · cases copies
    | .letOp (.at role op bodies) arguments nested rest, enclosing, legal, _, rename, copy,
        copies => by
        cases nested
        unfold plainRegion at copies
        split at copies
        · rename_i next copiesRest
          cases copies
          rw [regionSites_letOp]
          exact Region.Passes.letOp (op := .at role op bodies) legal.letOp.1 legal.results_named
            Regions.Passes.nil (plainRegion_passes rest enclosing legal.letOp.2.2 _ next copiesRest)
        · cases copies
    | .letOp (.exchange sender receiver site type) arguments nested rest, enclosing, legal, _,
        rename, copy, copies => by
        cases nested
        unfold plainRegion at copies
        split at copies
        · rename_i next copiesRest
          cases copies
          rw [regionSites_letOp]
          exact Region.Passes.letOp (op := .exchange sender receiver site type) legal.letOp.1
            legal.results_named Regions.Passes.nil
            (plainRegion_passes rest enclosing legal.letOp.2.2 _ next copiesRest)
        · cases copies
    | .letOp (.draw owner receivers site law populated) arguments nested rest, enclosing, legal, _,
        rename, copy, copies => by
        cases nested
        unfold plainRegion at copies
        split at copies
        · rename_i next copiesRest
          cases copies
          rw [regionSites_letOp]
          exact Region.Passes.letOp (op := .draw owner receivers site law populated)
            legal.letOp.1 legal.results_named Regions.Passes.nil
            (plainRegion_passes rest enclosing legal.letOp.2.2 _ next copiesRest)
        · cases copies
    | .letOp (.sample owner site law populated) arguments nested rest, enclosing, legal, _,
        rename, copy, copies => by
        cases nested
        unfold plainRegion at copies
        split at copies
        · rename_i next copiesRest
          cases copies
          rw [regionSites_letOp]
          exact Region.Passes.letOp (op := .sample owner site law populated) legal.letOp.1
            legal.results_named Regions.Passes.nil
            (plainRegion_passes rest enclosing legal.letOp.2.2 _ next copiesRest)
        · cases copies
    | .letOp (.repeat participants count carried collected captures covered) arguments bodies
        rest, enclosing, legal, _, rename, copy, copies => by
        unfold plainRegion at copies
        split at copies
        · rename_i nested next copiesBodies copiesRest
          cases copies
          rw [regionSites_letOp]
          exact Region.Passes.letOp
            (op := .repeat participants count carried collected captures covered) legal.letOp.1
            legal.results_named
            (plainRegions_passes bodies (some participants) legal.letOp.2.1 nested copiesBodies)
            (plainRegion_passes rest enclosing legal.letOp.2.2 _ next copiesRest)
        · cases copies
        · cases copies
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, enclosing,
        legal, _, rename, copy, copies => by
        unfold plainRegion at copies
        split at copies
        · rename_i nested next copiesBodies copiesRest
          cases copies
          rw [regionSites_letOp]
          exact Region.Passes.letOp (op := .choose participants tag captures outputs covered)
            legal.letOp.1 legal.results_named
            (plainRegions_passes bodies (some participants) legal.letOp.2.1 nested copiesBodies)
            (plainRegion_passes rest enclosing legal.letOp.2.2 _ next copiesRest)
        · cases copies
        · cases copies
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest,
        enclosing, legal, _, rename, copy, copies => by
        cases nested
        unfold plainRegion at copies
        split at copies
        · rename_i image next found copiesRest
          cases copies
          rw [regionSites_letOp]
          exact Region.Passes.letOp (op := .apply (header := header) image roleMap site permitted)
            legal.letOp.1 legal.results_named Regions.Passes.nil
            (plainRegion_passes rest enclosing legal.letOp.2.2 _ next copiesRest)
        · cases copies
        · cases copies

  theorem plainRegions_passes {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (enclosing : Option (List Nat)), Regions.Legal typeTable roles enclosing regions →
        ∀ (copies : Regions (ProtocolDialect operations functions new deployed) signatures),
          plainRegions t table regions = .ok copies →
          Regions.Passes typeTable roles enclosing copies (regionsSites regions)
    | .nil, _, _, copies, copied => by
        unfold plainRegions at copied
        cases copied
        exact Regions.Passes.nil
    | .cons (inputs := inputs) body tail, enclosing, legal, copies, copied => by
        unfold plainRegions at copied
        split at copied
        · rename_i first later copiesBody copiesTail
          cases copied
          exact Regions.Passes.cons
            (plainRegion_passes body enclosing legal.cons.1 _ first copiesBody)
            (plainRegions_passes tail enclosing legal.cons.2 later copiesTail)
        · cases copied
        · cases copied
end

end Copies

/-! ## An image that threads passes the check -/

theorem Located.allNamed_head {typeTable : TypeTable} {located : Located} {rest : List Located}
    (named : Located.allNamed typeTable (located :: rest) = true) :
    Ty.named typeTable located.type = true := by
  simp only [Located.allNamed, Bool.and_eq_true] at named
  exact named.1

/-- Values held by other roles have the types they had. -/
theorem Located.allNamed_rename (typeTable : TypeTable) (roleMap : RoleMap) :
    ∀ (ports : List Located),
      Located.allNamed typeTable (ports.map (Located.rename roleMap)) =
        Located.allNamed typeTable ports
  | [] => rfl
  | located :: rest => by
      show (Ty.named typeTable located.type &&
          Located.allNamed typeTable (rest.map (Located.rename roleMap))) =
        (Ty.named typeTable located.type && Located.allNamed typeTable rest)
      rw [Located.allNamed_rename typeTable roleMap rest]

/-- The two threaded values are held by participants that include both transcript roles. -/
theorem states_held {t : Threads} {participants : List Nat} {roles : TranscriptRoles}
    (prover : occursIn participants roles.prover = true)
    (verifier : occursIn participants roles.verifier = true) :
    Located.heldBy participants (t.states roles) = true := by
  show (occursIn participants roles.prover && (occursIn participants roles.verifier && true)) =
    true
  rw [prover, verifier]
  rfl

/-- The finding that an operation is not rewritten is not the finding that it is. -/
theorem untouched_ne_touched : (Except.ok false : Except StepRefusal Bool) ≠ .ok true :=
  fun same => by cases same

section Threaded

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} {t : Threads}
  {rule : Rule t operations functions} {table : CalleeTable t.header old new} {place : Place}
  {typeTable : TypeTable} {roles : Nat} {enclosing : Option (List Nat)}

/-- What holds of the image that threads of a region. When the region contains a rewritten
operation, the types of the two threaded values are types of the package; and when they
are, the image passes the check with sites among those of the region. -/
@[expose] def ImagePasses (typeTable : TypeTable) (roles : Nat) (rule : Rule t operations functions)
    (table : CalleeTable t.header old new) (place : Place) (enclosing : Option (List Nat))
    {Γ out : List Located}
    (region : Region (ProtocolDialect operations functions old deployed) Γ out) : Prop :=
  ∀ (Δ : List Located) (rename : Renaming Γ Δ) (first : Var Δ (t.first place.roles))
    (second : Var Δ (t.second place.roles))
    (image : Region (ProtocolDialect operations functions new deployed) Δ
      (t.states place.roles ++ out)),
    threadRegion t rule table place region rename first second = .ok image →
      (touches t rule.derives table place.definition (some place.roles.prover)
          (some place.roles.verifier) region = .ok true → t.Named typeTable) ∧
        (t.Named typeTable →
          ∃ kept, kept.Sublist (regionSites region) ∧
            Region.Passes typeTable roles enclosing image kept)

/-- The same of the images of the regions of a threaded `choose`. -/
@[expose] def ImagesPass (typeTable : TypeTable) (roles : Nat) (rule : Rule t operations functions)
    (table : CalleeTable t.header old new) (place : Place) (enclosing : Option (List Nat))
    {signatures targets : List (List Located × List Located)}
    (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
    (threaded : ThreadedRegions t place.roles signatures targets) : Prop :=
  ∀ (images : Regions (ProtocolDialect operations functions new deployed) targets),
    threadRegions t rule table place regions threaded = .ok images →
      (touchesRegions t rule.derives table place.definition (some place.roles.prover)
          (some place.roles.verifier) regions = .ok true → t.Named typeTable) ∧
        (t.Named typeTable →
          ∃ kept, kept.Sublist (regionsSites regions) ∧
            Regions.Passes typeTable roles enclosing images kept)

/-- In a region that starts with an operation that is not rewritten and whose nested
regions contain no rewritten operation, a rewritten operation is in what follows. -/
theorem touches_rest {derives : Bool} {definition prover verifier : Nat} {Γ out : List Located}
    {op : ProtocolOp operations functions old deployed}
    {arguments : Operands Γ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions old deployed) (ProtocolOp.regions op)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (ProtocolOp.results op)) out}
    (ownUntouched : touchesOp t derives table definition (some prover) (some verifier) op ≠
      .ok true)
    (nestedUntouched : touchesRegions t derives table definition (some prover) (some verifier)
      bodies = .ok false)
    (touched : touches t derives table definition (some prover) (some verifier)
      (Region.letOp (dialect := ProtocolDialect operations functions old deployed) op arguments
        bodies rest) = .ok true) :
    touches t derives table definition (some prover) (some verifier) rest = .ok true := by
  rcases touches_letOp t touched with own | nested | after
  · exact absurd own ownUntouched
  · rw [nestedUntouched] at nested
    cases nested
  · exact after

/-- A region of the image that starts with an operation passes with sites among those of
the old region, when the operation has no violation, its results have types of the package,
its sites are among the old operation's, and its nested regions and what follows pass with
sites among those of the old ones. -/
theorem passes_operation {Γ out Δ target : List Located}
    {op : ProtocolOp operations functions old deployed}
    {arguments : Operands Γ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions old deployed) (ProtocolOp.regions op)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (ProtocolOp.results op)) out}
    {image : ProtocolOp operations functions new deployed}
    {imageArguments : Operands Δ (ProtocolOp.arguments image)}
    {imageBodies : Regions (ProtocolDialect operations functions new deployed)
      (ProtocolOp.regions image)}
    {imageRest : Region (ProtocolDialect operations functions new deployed)
      (bindAll Δ (ProtocolOp.results image)) target}
    (clean : ProtocolOp.violation typeTable roles enclosing image = none)
    (named : Located.allNamed typeTable (ProtocolOp.results image) = true)
    (sites : (ProtocolOp.sites image).Sublist (ProtocolOp.sites op))
    (nested : ∃ kept, kept.Sublist (regionsSites bodies) ∧
      Regions.Passes typeTable roles (ProtocolOp.enclosing enclosing image) imageBodies kept)
    (after : ∃ kept, kept.Sublist (regionSites rest) ∧
      Region.Passes typeTable roles enclosing imageRest kept) :
    ∃ kept,
      kept.Sublist (regionSites
        (Region.letOp (dialect := ProtocolDialect operations functions old deployed) op arguments
          bodies rest)) ∧
        Region.Passes typeTable roles enclosing
          (Region.letOp (dialect := ProtocolDialect operations functions new deployed) image
            imageArguments imageBodies imageRest) kept := by
  obtain ⟨inner, innerAmong, innerPasses⟩ := nested
  obtain ⟨later, laterAmong, laterPasses⟩ := after
  refine ⟨later ++ (inner ++ ProtocolOp.sites image), ?_,
    Region.Passes.letOp clean named innerPasses laterPasses⟩
  rw [regionSites_letOp]
  exact List.Sublist.append laterAmong (List.Sublist.append innerAmong sites)

/-- What a rule emits in place of an operation, before the image of what follows, passes
with sites among those of the old region, when it passes with sites among the operation's
and what follows passes with sites among those of the old rest. -/
theorem passes_emitted {Γ out Δ results target : List Located}
    {op : ProtocolOp operations functions old deployed}
    {arguments : Operands Γ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions old deployed) (ProtocolOp.regions op)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (ProtocolOp.results op)) out}
    {emitted : Emitted (ProtocolDialect operations functions new deployed) Δ results}
    {imageRest : Region (ProtocolDialect operations functions new deployed) emitted.context
      target}
    {added : List Nat} (sites : added.Sublist (ProtocolOp.sites op))
    (passes : Emitted.Passes typeTable roles enclosing emitted added)
    (after : ∃ kept, kept.Sublist (regionSites rest) ∧
      Region.Passes typeTable roles enclosing imageRest kept) :
    ∃ kept,
      kept.Sublist (regionSites
        (Region.letOp (dialect := ProtocolDialect operations functions old deployed) op arguments
          bodies rest)) ∧
        Region.Passes typeTable roles enclosing (emitted.wrap imageRest) kept := by
  obtain ⟨later, laterAmong, laterPasses⟩ := after
  refine ⟨later ++ added, ?_, passes.wrap laterPasses⟩
  rw [regionSites_letOp]
  exact List.Sublist.append laterAmong (sites.trans (List.sublist_append_right _ _))

/-- A region that returns the two threaded values after the first of its other values
passes as the region does, when its values have types of the package. -/
theorem Region.returnAfter_passes {protocols : List ProtocolHeader} {Δ states : List Located} :
    ∀ (leading : List Located) {trailing : List Located}
      {region : Region (ProtocolDialect operations functions protocols deployed) Δ
        (states ++ (leading ++ trailing))} {kept : List Nat},
      Located.allNamed typeTable (states ++ (leading ++ trailing)) = true →
      Region.Passes typeTable roles enclosing region kept →
      Region.Passes typeTable roles enclosing
        (Region.returnAfter (dialect := ProtocolDialect operations functions protocols deployed)
          states leading region) kept
  | [], _, _, _, _, passes => passes
  | head :: rest, _, _, _, named, passes => Region.Passes.bind named passes (Region.Passes.ret _)

/-- A `repeat` that carries values held by its participants before its own has no
violation when the `repeat` has none. -/
theorem repeat_threaded_clean {participants : List Nat} {count : RepeatCount}
    {carried collected captures states : List Located}
    {covered : Located.heldBy participants collected = true}
    (legal : ProtocolOp.violation (operations := operations) (functions := functions)
      (protocols := old) (deployed := deployed) typeTable roles enclosing
      (.repeat participants count carried collected captures covered) = none)
    (held : Located.heldBy participants states = true) :
    ProtocolOp.violation (operations := operations) (functions := functions) (protocols := new)
      (deployed := deployed) typeTable roles enclosing
      (.repeat participants count (states ++ carried) collected captures covered) = none := by
  have same : Located.heldBy participants ((states ++ carried) ++ captures) =
      Located.heldBy participants (carried ++ captures) := by
    simp only [Located.heldBy, List.all_append] at held ⊢
    rw [held, Bool.true_and]
  show firstViolation (actingRoles roles enclosing participants ++
    participantConditions participants ((states ++ carried) ++ captures)) = none
  rw [participantConditions, same]
  exact legal

/-- A `choose` that captures and returns values held by its participants before its own
has no violation when the `choose` has none. -/
theorem choose_threaded_clean {participants : List Nat} {tag : ChoiceTag}
    {captures outputs states : List Located}
    {covered : Located.heldBy participants outputs = true}
    {held : Located.heldBy participants (states ++ outputs) = true}
    (legal : ProtocolOp.violation (operations := operations) (functions := functions)
      (protocols := old) (deployed := deployed) typeTable roles enclosing
      (.choose participants tag captures outputs covered) = none)
    (statesHeld : Located.heldBy participants states = true) :
    ProtocolOp.violation (operations := operations) (functions := functions) (protocols := new)
      (deployed := deployed) typeTable roles enclosing
      (.choose participants tag (states ++ captures) (states ++ outputs) held) = none := by
  have same : Located.heldBy participants ((states ++ captures) ++ (states ++ outputs)) =
      Located.heldBy participants (captures ++ outputs) := by
    simp only [Located.heldBy, List.all_append] at statesHeld ⊢
    rw [statesHeld, Bool.true_and, Bool.true_and]
  show firstViolation (actingRoles roles enclosing participants ++
    (participantConditions participants ((states ++ captures) ++ (states ++ outputs)) ++
      [(tag.inhabited, .noArm)])) = none
  rw [participantConditions, same]
  exact legal

/-- What an exchange becomes passes the check where the exchange stood, with no site but
the exchange's, and the types of the threaded values are types of the package. -/
theorem rewrittenExchange_passes (legalRule : rule.Legal typeTable) {sender receiver site : Nat}
    {type : Ty} {Δ : List Located} {value : Var Δ ⟨type, sender⟩}
    {first : Var Δ (t.first place.roles)} {second : Var Δ (t.second place.roles)}
    {emitted : Emitted (ProtocolDialect operations functions new deployed) Δ
      [⟨type, receiver⟩, t.first place.roles, t.second place.roles]}
    (rewritten : rewrittenExchange t rule place sender receiver site type value first second =
      some (.ok emitted)) :
    t.Named typeTable ∧
      ∀ (roles : Nat) (enclosing : Option (List Nat)),
        ProtocolOp.violation typeTable roles enclosing
          (ProtocolOp.exchange (operations := operations) (functions := functions)
            (protocols := new) (deployed := deployed) sender receiver site type) = none →
        Ty.named typeTable type = true →
        ∃ added, added.Sublist [site] ∧ Emitted.Passes typeTable roles enclosing emitted added := by
  unfold rewrittenExchange at rewritten
  split at rewritten
  · rename_i between
    obtain ⟨rfl, rfl⟩ := between
    split at rewritten
    · rename_i raw emits
      simp only [Option.some.injEq, Except.ok.injEq] at rewritten
      subst rewritten
      obtain ⟨named, passes⟩ := legalRule.exchange _ _ _ _ _ _ _ emits
      exact ⟨named, fun roles enclosing clean typeNamed => passes roles enclosing clean typeNamed⟩
    · simp only [Option.some.injEq] at rewritten
      cases rewritten
  · cases rewritten

/-- An exchange that the step leaves as it is is not from the prover to the verifier. -/
theorem rewrittenExchange_missing {sender receiver site : Nat} {type : Ty} {Δ : List Located}
    {value : Var Δ ⟨type, sender⟩} {first : Var Δ (t.first place.roles)}
    {second : Var Δ (t.second place.roles)}
    (missing : rewrittenExchange (new := new) (deployed := deployed) t rule place sender receiver
      site type value first second = none) :
    ¬(sender = place.roles.prover ∧ receiver = place.roles.verifier) := by
  intro between
  unfold rewrittenExchange at missing
  rw [dif_pos between] at missing
  split at missing <;> cases missing

/-- What a draw becomes passes the check where the draw stood, with no site but the
draw's, and the types of the threaded values are types of the package. -/
theorem rewrittenDraw_passes (legalRule : rule.Legal typeTable) {owner receiver site : Nat}
    {inputs : List Ty} {output : Ty} {law : Var operations ⟨inputs, [output], .sampling⟩}
    {Δ : List Located} {first : Var Δ (t.first place.roles)}
    {second : Var Δ (t.second place.roles)}
    {emitted : Emitted (ProtocolDialect operations functions new deployed) Δ
      [⟨output, owner⟩, ⟨output, receiver⟩, t.first place.roles, t.second place.roles]}
    (rewritten : rewrittenDraw t rule place owner receiver site law first second =
      some (.ok emitted)) :
    t.Named typeTable ∧
      ∀ (roles : Nat) (enclosing : Option (List Nat)),
        Acts roles enclosing owner → Acts roles enclosing receiver →
        Ty.named typeTable output = true →
        ∃ added, added.Sublist [site] ∧ Emitted.Passes typeTable roles enclosing emitted added := by
  unfold rewrittenDraw at rewritten
  split at rewritten
  · rename_i byVerifier
    obtain ⟨rfl, rfl⟩ := byVerifier
    split at rewritten
    · rename_i raw emits
      simp only [Option.some.injEq, Except.ok.injEq] at rewritten
      subst rewritten
      obtain ⟨named, passes⟩ := legalRule.draw _ _ _ _ _ _ emits
      exact ⟨named, fun roles enclosing ownerActs receiverActs outputNamed =>
        passes roles enclosing receiverActs ownerActs outputNamed⟩
    · simp only [Option.some.injEq] at rewritten
      cases rewritten
  · split at rewritten
    · rename_i byProver
      obtain ⟨rfl, rfl⟩ := byProver
      split at rewritten
      · rename_i raw emits
        simp only [Option.some.injEq, Except.ok.injEq] at rewritten
        subst rewritten
        obtain ⟨named, passes⟩ := legalRule.draw _ _ _ _ _ _ emits
        exact ⟨named, fun roles enclosing ownerActs receiverActs outputNamed =>
          passes roles enclosing ownerActs receiverActs outputNamed⟩
      · simp only [Option.some.injEq] at rewritten
        cases rewritten
    · cases rewritten

/-- A draw with one receiver that the step leaves as it is is not between the two
transcript roles. -/
theorem rewrittenDraw_missing {owner receiver site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {Δ : List Located}
    {first : Var Δ (t.first place.roles)} {second : Var Δ (t.second place.roles)}
    (missing : rewrittenDraw (new := new) (deployed := deployed) t rule place owner receiver site
      law first second = none) :
    ¬((owner = place.roles.verifier ∧ [receiver] = [place.roles.prover]) ∨
      (owner = place.roles.prover ∧ [receiver] = [place.roles.verifier])) := by
  unfold rewrittenDraw at missing
  rintro (⟨isVerifier, isProver⟩ | ⟨isProver, isVerifier⟩)
  · rw [dif_pos ⟨isVerifier, List.head_eq_of_cons_eq isProver⟩] at missing
    split at missing <;> cases missing
  · split at missing
    · split at missing <;> cases missing
    · rw [dif_pos ⟨isProver, List.head_eq_of_cons_eq isVerifier⟩] at missing
      split at missing <;> cases missing

/-- An application for which the callee has no image that threads is not rewritten. -/
theorem threadedCallee_missing {derives : Bool} {definition : Nat} {roles : TranscriptRoles}
    {header : ProtocolHeader} {callee : Var old header} {roleMap : RoleMap} {site : Nat}
    {permitted : (deployed && header.specificationOnly) = false}
    (missing : threadedCallee t table roles roleMap callee = none) :
    touchesOp (operations := operations) (functions := functions) t derives table definition
      (some roles.prover) (some roles.verifier) (.apply callee roleMap site permitted) ≠
        .ok true := by
  intro touched
  unfold threadedCallee at missing
  simp only [touchesOp] at touched
  change (match (preimage roleMap roles.prover).map (·.val),
      (preimage roleMap roles.verifier).map (·.val) with
    | some inner, some outer =>
        (Except.ok (table.find callee (some ⟨inner, outer⟩)).isSome : Except StepRefusal Bool)
    | _, _ => .ok false) = .ok true at touched
  cases atProver : preimage roleMap roles.prover with
  | none =>
      rw [atProver] at touched
      cases touched
  | some inner =>
      cases atVerifier : preimage roleMap roles.verifier with
      | none =>
          rw [atProver, atVerifier] at touched
          cases touched
      | some outer =>
          rw [atProver, atVerifier] at touched missing
          obtain ⟨inner, isProver⟩ := inner
          obtain ⟨outer, isVerifier⟩ := outer
          dsimp only [Option.map] at touched
          dsimp only at missing
          split at missing
          · cases missing
          · rename_i absent
            rw [absent] at touched
            cases touched

/-- The sites of the one region of a `repeat`. -/
theorem regionsSites_single {inputs outputs : List Located}
    (body : Region (ProtocolDialect operations functions old deployed) (bindAll [] inputs)
      outputs) :
    regionsSites (Regions.cons body Regions.nil) = regionSites body := by
  simp only [regionsSites, List.nil_append]

mutual
  /-- The image that threads of a legal region passes the check with sites among those of
  the region, when the types of the two threaded values are types of the package; they are
  when the region contains a rewritten operation. The rule emits what the check accepts,
  and the ports of the images made so far have types of the package. -/
  theorem threadRegion_passes (legalRule : rule.Legal typeTable)
      (headers : HeadersNamed typeTable new) (place : Place) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        (enclosing : Option (List Nat)), Region.Legal typeTable roles enclosing region →
        ImagePasses typeTable roles rule table place enclosing region
    | .ret values, _, _ => by
        intro Δ rename first second image threads
        unfold threadRegion at threads
        cases threads
        refine ⟨fun touched => ?_, fun _ => ⟨[], List.nil_sublist _, Region.Passes.ret _⟩⟩
        simp only [touches] at touched
        cases touched
    | .stop reason, _, legal => (Region.Legal.not_stop legal).elim
    | .bind (mid := mid) body rest, enclosing, legal => by
        intro Δ rename first second image threads
        unfold threadRegion at threads
        dsimp only at threads
        split at threads
        · rename_i early late threadsBody threadsRest
          cases threads
          obtain ⟨bodyNamed, bodyPasses⟩ := threadRegion_passes legalRule headers place body
            enclosing legal.bind.1 _ _ _ _ early threadsBody
          obtain ⟨restNamed, restPasses⟩ := threadRegion_passes legalRule headers place rest
            enclosing legal.bind.2 _ _ _ _ late threadsRest
          refine ⟨fun touched => ?_, fun named => ?_⟩
          · unfold touches at touched
            rcases bothTouch_true touched with inBody | inRest
            · exact bodyNamed inBody
            · exact restNamed inRest
          · obtain ⟨before, beforeAmong, beforePasses⟩ := bodyPasses named
            obtain ⟨after, afterAmong, afterPasses⟩ := restPasses named
            refine ⟨after ++ before, ?_,
              Region.Passes.bind (named.states place.roles legal.mid_named) beforePasses
                afterPasses⟩
            rw [regionSites]
            exact List.Sublist.append afterAmong beforeAmong
        · cases threads
        · cases threads
    | .letOp (.at role op bodies) arguments nested rest, enclosing, legal => by
        cases nested
        intro Δ rename first second image threads
        unfold threadRegion at threads
        split at threads
        · rename_i next threadsRest
          cases threads
          obtain ⟨restNamed, restPasses⟩ := threadRegion_passes legalRule headers place rest
            enclosing legal.letOp.2.2 _ _ _ _ next threadsRest
          exact ⟨fun touched => restNamed (touches_rest (by exact untouched_ne_touched) rfl touched),
            fun named => passes_operation (image := .at role op bodies) legal.letOp.1
              legal.results_named (List.Sublist.refl _)
              ⟨[], List.nil_sublist _, Regions.Passes.nil⟩ (restPasses named)⟩
        · cases threads
    | .letOp (.sample owner site law populated) arguments nested rest, enclosing, legal => by
        cases nested
        intro Δ rename first second image threads
        unfold threadRegion at threads
        split at threads
        · rename_i next threadsRest
          cases threads
          obtain ⟨restNamed, restPasses⟩ := threadRegion_passes legalRule headers place rest
            enclosing legal.letOp.2.2 _ _ _ _ next threadsRest
          exact ⟨fun touched => restNamed (touches_rest (by exact untouched_ne_touched) rfl touched),
            fun named => passes_operation (image := .sample owner site law populated)
              legal.letOp.1 legal.results_named (List.Sublist.refl _)
              ⟨[], List.nil_sublist _, Regions.Passes.nil⟩ (restPasses named)⟩
        · cases threads
    | .letOp (.exchange sender receiver site type) arguments nested rest, enclosing, legal => by
        cases nested
        intro Δ rename first second image threads
        have ihRest := threadRegion_passes legalRule headers place rest enclosing legal.letOp.2.2
        unfold threadRegion at threads
        split at threads
        · rename_i emitted rewritten
          split at threads
          · rename_i next threadsRest
            cases threads
            obtain ⟨restNamed, restPasses⟩ := ihRest _ _ _ _ next threadsRest
            obtain ⟨named, emits⟩ := rewrittenExchange_passes legalRule rewritten
            refine ⟨fun _ => named, fun named => ?_⟩
            obtain ⟨added, among, passes⟩ := emits roles enclosing legal.letOp.1
              (Located.allNamed_head legal.results_named)
            exact passes_emitted among passes (restPasses named)
          · cases threads
        · cases threads
        · rename_i unrewritten
          split at threads
          · rename_i next threadsRest
            cases threads
            obtain ⟨restNamed, restPasses⟩ := ihRest _ _ _ _ next threadsRest
            exact ⟨fun touched => restNamed (touches_rest
                (fun own => rewrittenExchange_missing unrewritten (touchesOp_exchange t own)) rfl
                touched),
              fun named => passes_operation (image := .exchange sender receiver site type)
                legal.letOp.1 legal.results_named (List.Sublist.refl _)
                ⟨[], List.nil_sublist _, Regions.Passes.nil⟩ (restPasses named)⟩
          · cases threads
    | .letOp (.draw owner receivers site law populated) arguments nested rest, enclosing,
        legal => by
        cases nested
        intro Δ rename first second image threads
        have ihRest := threadRegion_passes legalRule headers place rest enclosing legal.letOp.2.2
        cases receivers with
        | nil =>
            unfold threadRegion at threads
            split at threads
            · rename_i next threadsRest
              cases threads
              obtain ⟨restNamed, restPasses⟩ := ihRest _ _ _ _ next threadsRest
              exact ⟨fun touched => restNamed (touches_rest
                  (fun own => by
                    rcases touchesOp_draw t own with ⟨_, one⟩ | ⟨_, one⟩ <;> cases one) rfl
                  touched),
                fun named => passes_operation (image := .draw owner [] site law populated)
                  legal.letOp.1 legal.results_named (List.Sublist.refl _)
                  ⟨[], List.nil_sublist _, Regions.Passes.nil⟩ (restPasses named)⟩
            · cases threads
        | cons receiver others =>
            cases others with
            | cons another more =>
                unfold threadRegion at threads
                split at threads
                · rename_i next threadsRest
                  cases threads
                  obtain ⟨restNamed, restPasses⟩ := ihRest _ _ _ _ next threadsRest
                  exact ⟨fun touched => restNamed (touches_rest
                      (fun own => by
                        rcases touchesOp_draw t own with ⟨_, one⟩ | ⟨_, one⟩ <;> cases one) rfl
                      touched),
                    fun named => passes_operation
                      (image := .draw owner (receiver :: another :: more) site law populated)
                      legal.letOp.1 legal.results_named (List.Sublist.refl _)
                      ⟨[], List.nil_sublist _, Regions.Passes.nil⟩ (restPasses named)⟩
                · cases threads
            | nil =>
                unfold threadRegion at threads
                split at threads
                · rename_i emitted rewritten
                  split at threads
                  · rename_i next threadsRest
                    cases threads
                    obtain ⟨restNamed, restPasses⟩ := ihRest _ _ _ _ next threadsRest
                    obtain ⟨named, emits⟩ := rewrittenDraw_passes legalRule rewritten
                    refine ⟨fun _ => named, fun named => ?_⟩
                    have acts := ProtocolOp.roles_act legal.letOp.1
                    obtain ⟨added, among, passes⟩ := emits roles enclosing
                      (acts owner List.mem_cons_self)
                      (acts receiver (List.mem_cons_of_mem _ List.mem_cons_self))
                      (Located.allNamed_head legal.results_named)
                    exact passes_emitted among passes (restPasses named)
                  · cases threads
                · cases threads
                · rename_i unrewritten
                  split at threads
                  · rename_i next threadsRest
                    cases threads
                    obtain ⟨restNamed, restPasses⟩ := ihRest _ _ _ _ next threadsRest
                    exact ⟨fun touched => restNamed (touches_rest
                        (fun own => rewrittenDraw_missing unrewritten (touchesOp_draw t own)) rfl
                        touched),
                      fun named => passes_operation
                        (image := .draw owner [receiver] site law populated) legal.letOp.1
                        legal.results_named (List.Sublist.refl _)
                        ⟨[], List.nil_sublist _, Regions.Passes.nil⟩ (restPasses named)⟩
                  · cases threads
    | .letOp (.repeat participants count carried collected captures covered) arguments
        (.cons body .nil) rest, enclosing, legal => by
        intro Δ rename first second image threads
        have ihRest := threadRegion_passes legalRule headers place rest enclosing legal.letOp.2.2
        have ihBody := threadRegion_passes legalRule headers place body (some participants)
          (Regions.Legal.cons legal.letOp.2.1).1
        unfold threadRegion at threads
        dsimp only at threads
        split at threads
        · rename_i touched
          split at threads
          rename_i inner same
          obtain ⟨rfl⟩ : body = inner := by injection same
          split at threads
          · rename_i threaded next threadsBody threadsRest
            cases threads
            obtain ⟨bodyNamed, bodyPasses⟩ := ihBody _ _ _ _ threaded threadsBody
            obtain ⟨_, restPasses⟩ := ihRest _ _ _ _ next threadsRest
            have named : t.Named typeTable := bodyNamed (by
              unfold touchesRegions at touched
              rcases bothTouch_true touched with own | none_
              · exact own
              · simp only [touchesRegions] at none_
                cases none_)
            have both := touchesRegions_participants t (Regions.cons body Regions.nil) _
              legal.letOp.2.1 touched participants rfl
            refine ⟨fun _ => named, fun named => ?_⟩
            obtain ⟨inside, insideAmong, insidePasses⟩ := bodyPasses named
            have original : Located.allNamed typeTable
                (collectedSequencesAt count.size collected ++ carried) = true :=
              legal.results_named
            have collectedNamed := Located.allNamed_collected original
            rw [Located.allNamed_append] at original
            simp only [Bool.and_eq_true] at original
            have resultsNamed : Located.allNamed typeTable
                (collectedSequencesAt count.size collected ++ (t.states place.roles ++ carried)) =
                  true := by
              rw [Located.allNamed_append, original.1, named.states place.roles original.2]
              rfl
            have valuesNamed : Located.allNamed typeTable
                (t.states place.roles ++ (collected ++ carried)) = true :=
              named.states place.roles (by
                rw [Located.allNamed_append, collectedNamed, original.2]
                rfl)
            exact passes_operation
              (image := .repeat participants count (t.states place.roles ++ carried) collected
                captures covered)
              (repeat_threaded_clean legal.letOp.1 (states_held both.1 both.2)) resultsNamed
              (List.Sublist.refl _)
              ⟨[] ++ inside, by rw [regionsSites_single]; exact insideAmong,
                Regions.Passes.cons
                  (Region.returnAfter_passes collected valuesNamed insidePasses)
                  Regions.Passes.nil⟩
              (restPasses named)
          · cases threads
          · cases threads
        · rename_i untouched
          split at threads
          · rename_i copies next copied threadsRest
            cases threads
            obtain ⟨restNamed, restPasses⟩ := ihRest _ _ _ _ next threadsRest
            exact ⟨fun touched => restNamed (touches_rest (by exact untouched_ne_touched) untouched touched),
              fun named => passes_operation
                (image := .repeat participants count carried collected captures covered)
                legal.letOp.1 legal.results_named (List.Sublist.refl _)
                ⟨_, List.Sublist.refl _,
                  plainRegions_passes _ (some participants) legal.letOp.2.1 copies copied⟩
                (restPasses named)⟩
          · cases threads
          · cases threads
        · cases threads
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, enclosing,
        legal => by
        intro Δ rename first second image threads
        have ihRest := threadRegion_passes legalRule headers place rest enclosing legal.letOp.2.2
        unfold threadRegion at threads
        split at threads
        · rename_i touched
          split at threads
          · rename_i held
            dsimp only at threads
            split at threads
            · rename_i threaded next threadsBodies threadsRest
              cases threads
              obtain ⟨bodiesNamed, bodiesPass⟩ := threadRegions_passes legalRule headers place
                bodies (t.choice place.roles participants captures outputs tag) (some participants)
                legal.letOp.2.1 threaded threadsBodies
              obtain ⟨_, restPasses⟩ := ihRest _ _ _ _ next threadsRest
              have both := touchesRegions_participants t bodies _ legal.letOp.2.1 touched
                participants rfl
              refine ⟨fun _ => bodiesNamed touched, fun named => ?_⟩
              exact passes_operation
                (image := .choose participants tag (t.states place.roles ++ captures)
                  (t.states place.roles ++ outputs) held)
                (choose_threaded_clean legal.letOp.1 (states_held both.1 both.2))
                (named.states place.roles legal.results_named) (List.Sublist.refl _)
                (bodiesPass named) (restPasses named)
            · cases threads
            · cases threads
          · cases threads
        · rename_i untouched
          split at threads
          · rename_i copies next copied threadsRest
            cases threads
            obtain ⟨restNamed, restPasses⟩ := ihRest _ _ _ _ next threadsRest
            exact ⟨fun touched => restNamed (touches_rest (by exact untouched_ne_touched) untouched touched),
              fun named => passes_operation
                (image := .choose participants tag captures outputs covered) legal.letOp.1
                legal.results_named (List.Sublist.refl _)
                ⟨_, List.Sublist.refl _,
                  plainRegions_passes _ (some participants) legal.letOp.2.1 copies copied⟩
                (restPasses named)⟩
          · cases threads
          · cases threads
        · cases threads
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest,
        enclosing, legal => by
        cases nested
        intro Δ rename first second image threads
        have ihRest := threadRegion_passes legalRule headers place rest enclosing legal.letOp.2.2
        unfold threadRegion at threads
        split at threads
        · rename_i threaded found
          dsimp only at threads
          split at threads
          · rename_i next threadsRest
            cases threads
            obtain ⟨_, restPasses⟩ := ihRest _ _ _ _ next threadsRest
            have ports : Located.allNamed typeTable
                ((t.states threaded.inner ++ header.inputs) ++
                  (t.states threaded.inner ++ header.outputs)) = true :=
              headers threaded.image
            rw [Located.allNamed_append] at ports
            simp only [Bool.and_eq_true] at ports
            have named : t.Named typeTable := Threads.named_of_states ports.1
            refine ⟨fun _ => named, fun named => ?_⟩
            have original : Located.allNamed typeTable
                (header.outputs.map (Located.rename roleMap)) = true := legal.results_named
            rw [Located.allNamed_rename] at original
            have resultsNamed : Located.allNamed typeTable
                ((t.states threaded.inner ++ header.outputs).map (Located.rename roleMap)) =
                  true := by
              rw [Located.allNamed_rename]
              exact named.states threaded.inner original
            exact passes_operation (image := .apply threaded.image roleMap site permitted)
              legal.letOp.1 resultsNamed (List.Sublist.refl _)
              ⟨[], List.nil_sublist _, Regions.Passes.nil⟩ (restPasses named)
          · cases threads
        · rename_i missing
          split at threads
          · rename_i plain next found threadsRest
            cases threads
            obtain ⟨restNamed, restPasses⟩ := ihRest _ _ _ _ next threadsRest
            exact ⟨fun touched => restNamed (touches_rest (threadedCallee_missing missing) rfl
                touched),
              fun named => passes_operation
                (image := .apply (header := header) plain roleMap site permitted) legal.letOp.1
                legal.results_named (List.Sublist.refl _)
                ⟨[], List.nil_sublist _, Regions.Passes.nil⟩ (restPasses named)⟩
          · cases threads
          · cases threads

  /-- The same of the regions of a threaded `choose`. -/
  theorem threadRegions_passes (legalRule : rule.Legal typeTable)
      (headers : HeadersNamed typeTable new) (place : Place)
      {signatures targets : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (threaded : ThreadedRegions t place.roles signatures targets)
        (enclosing : Option (List Nat)), Regions.Legal typeTable roles enclosing regions →
        ImagesPass typeTable roles rule table place enclosing regions threaded
    | regions, threaded, enclosing, legal =>
        match threaded, regions, legal with
        | .nil, .nil, _ => by
            intro images threads
            simp only [threadRegions] at threads
            cases threads
            refine ⟨fun touched => ?_, fun _ => ⟨[], List.nil_sublist _, Regions.Passes.nil⟩⟩
            simp only [touchesRegions] at touched
            cases touched
        | .cons leading added threaded, .cons body tail, legal => by
            intro images threads
            simp only [threadRegions] at threads
            split at threads
            · rename_i early late threadsBody threadsTail
              cases threads
              obtain ⟨bodyNamed, bodyPasses⟩ := threadRegion_passes legalRule headers place body
                enclosing legal.cons.1 _ _ _ _ early threadsBody
              obtain ⟨tailNamed, tailPass⟩ := threadRegions_passes legalRule headers place tail
                threaded enclosing legal.cons.2 late threadsTail
              refine ⟨fun touched => ?_, fun named => ?_⟩
              · unfold touchesRegions at touched
                rcases bothTouch_true touched with inBody | inTail
                · exact bodyNamed inBody
                · exact tailNamed inTail
              · obtain ⟨before, beforeAmong, beforePasses⟩ := bodyPasses named
                obtain ⟨after, afterAmong, afterPass⟩ := tailPass named
                refine ⟨after ++ before, ?_, Regions.Passes.cons beforePasses afterPass⟩
                rw [regionsSites]
                exact List.Sublist.append afterAmong beforeAmong
            · cases threads
            · cases threads
end


end Threaded

end Zkc.Core
