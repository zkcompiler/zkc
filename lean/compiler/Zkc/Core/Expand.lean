module

public import Zkc.Core.Elaborate

public section

/-! Expansion of applications on typed terms.

The expansion of a deployed protocol is one region without `apply`, typed over the empty
list of protocol headers, so that it contains no application by typing. Protocols are
expanded in program order; the expansion of an application is the callee's expansion,
already free of applications, instantiated at the call:

- the callee's roles go through the role map (`instantiateRegion`);
- the callee's inputs are the application's operands, and its returned values are the
  application's results: the instantiated body is a nested block (`Region.bind`) in the
  caller's context, so the caller's own operations keep their context and their operands;
- sites are renumbered in the order of the expanded body, from zero. The expansion
  records, for every new site number, where the site comes from: the sites of the
  applications it was reached through, outermost first, and its own site
  (`SiteOrigin`). A site of the expanded definition is below the site limit.

Instantiation renames a region that has no application under one role map, so no role
map is ever composed with another one.

A specification-only protocol has no expansion; a deployed protocol applies none.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- Where a site of an expanded definition comes from: the applications it was reached
through, outermost first, each as the applying definition's identity and the
application's site, and the operation's own definition and site. -/
structure SiteOrigin where
  applications : List Point
  site : Point
  deriving Repr, DecidableEq

/-- The origin of a site of a callee, reached through one more application. -/
def SiteOrigin.under (application : Point) (origin : SiteOrigin) : SiteOrigin :=
  ⟨application :: origin.applications, origin.site⟩

/-- The site of the effects of an expanded operation, under the applications that reached
the expanded definition: the sites of the applications, then the operation's own
definition and site. It is the site that the operation's effect has in the definition
before expansion. -/
@[expose] def SiteOrigin.siteUnder (path : List Nat) (origin : SiteOrigin) : Site :=
  ⟨path ++ origin.applications.map (·.number), origin.site.definition, origin.site.number⟩

theorem SiteOrigin.siteUnder_under (path : List Nat) (application : Point) (origin : SiteOrigin) :
    (origin.under application).siteUnder path = origin.siteUnder (path ++ [application.number]) := by
  simp only [siteUnder, under, List.map_cons, List.append_assoc, List.singleton_append]

/-! ## Renaming the roles of a region -/

/-- A located type of a callee as the caller sees it: held by the role that runs its
holder. -/
@[expose] def Renamed (roleMap : RoleMap) (source target : Located) : Prop :=
  target = source.rename roleMap

/-- A map from the values of a callee's context to values of the caller's context, at
the renamed types. -/
abbrev RoleRenaming (roleMap : RoleMap) (Γ Δ : List Located) : Type :=
  Mapping (Renamed roleMap) Γ Δ

/-- Outputs held by participants are, renamed, held by the renamed participants. -/
theorem heldBy_rename (roleMap : RoleMap) {participants : List Nat} {outputs : List Located}
    (covered : Located.heldBy participants outputs = true) :
    Located.heldBy (participants.map roleMap.apply) (outputs.map (Located.rename roleMap)) = true := by
  simp only [Located.heldBy, occursIn, List.all_eq_true, List.any_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at covered ⊢
  intro located member
  obtain ⟨role, inside, same⟩ := covered located member
  refine ⟨roleMap.apply role, ⟨role, inside, rfl⟩, ?_⟩
  show Nat.beq (roleMap.apply located.holder) (roleMap.apply role) = true
  rw [Nat.eq_of_beq_eq_true same]
  exact Nat.beq_refl _

namespace RoleRenaming

variable {roleMap : RoleMap} {Γ Δ : List Located}

/-- The caller's value for a value of the callee. -/
@[expose] def image (map : RoleRenaming roleMap Γ Δ) {located : Located} (reference : Var Γ located) :
    Var Δ (located.rename roleMap) :=
  map.apply reference rfl

/-- One more value on both sides. -/
@[expose] def keepOne (map : RoleRenaming roleMap Γ Δ) (source : Located) :
    RoleRenaming roleMap (source :: Γ) (source.rename roleMap :: Δ) :=
  map.keep source (source.rename roleMap) fun _ same => same

/-- New values on both sides. -/
@[expose] def keepAll : {Γ Δ : List Located} → RoleRenaming roleMap Γ Δ → (added : List Located) →
    RoleRenaming roleMap (bindAll Γ added) (bindAll Δ (added.map (Located.rename roleMap)))
  | _, _, map, [] => map
  | _, _, map, located :: rest => keepAll (map.keepOne located) rest

/-- New values of one holder. -/
@[expose] def keepAt (role : Nat) : {Γ Δ : List Located} → RoleRenaming roleMap Γ Δ → (types : List Ty) →
    RoleRenaming roleMap (bindAll Γ (Located.atRole role types))
      (bindAll Δ (Located.atRole (roleMap.apply role) types))
  | _, _, map, [] => map
  | _, _, map, type :: rest => keepAt role (map.keepOne ⟨type, role⟩) rest

/-- New values of one type, one per role of a list. -/
@[expose] def keepRoles (type : Ty) : {Γ Δ : List Located} → RoleRenaming roleMap Γ Δ → (roles : List Nat) →
    RoleRenaming roleMap (bindAll Γ (Located.ofRoles type roles))
      (bindAll Δ (Located.ofRoles type (roles.map roleMap.apply)))
  | _, _, map, [] => map
  | _, _, map, role :: rest => keepRoles type (map.keepOne ⟨type, role⟩) rest

/-- New values of two lists. -/
@[expose] def keepAppend : {Γ Δ : List Located} → RoleRenaming roleMap Γ Δ → (first second : List Located) →
    RoleRenaming roleMap (bindAll Γ (first ++ second))
      (bindAll Δ (first.map (Located.rename roleMap) ++ second.map (Located.rename roleMap)))
  | _, _, map, [], second => map.keepAll second
  | _, _, map, located :: first, second => keepAppend (map.keepOne located) first second

/-- The results of a `repeat`: the sequences of its collected values, then its carried
values. -/
@[expose] def keepCollected (size : Option Nat) :
    {Γ Δ : List Located} → RoleRenaming roleMap Γ Δ → (collected carried : List Located) →
      RoleRenaming roleMap (bindAll Γ (collectedSequencesAt size collected ++ carried))
        (bindAll Δ (collectedSequencesAt size (collected.map (Located.rename roleMap)) ++
          carried.map (Located.rename roleMap)))
  | _, _, map, [], carried => map.keepAll carried
  | _, _, map, located :: rest, carried =>
      keepCollected size (map.keepOne ⟨.seq located.type size, located.holder⟩) rest carried

/-- The inputs of a closed region. -/
@[expose] def initial (roleMap : RoleMap) (inputs : List Located) :
    RoleRenaming roleMap (bindAll [] inputs) (bindAll [] (inputs.map (Located.rename roleMap))) :=
  keepAll (Mapping.start (Δ := ([] : List Located)) 0 rfl) inputs

/-- New values of one type, one per role of a list, then new values of two lists. -/
@[expose] def keepRolesAppend (type : Ty) :
    {Γ Δ : List Located} → RoleRenaming roleMap Γ Δ → (roles : List Nat) →
      (first second : List Located) →
        RoleRenaming roleMap (bindAll Γ (Located.ofRoles type roles ++ (first ++ second)))
          (bindAll Δ (Located.ofRoles type (roles.map roleMap.apply) ++
            (first.map (Located.rename roleMap) ++ second.map (Located.rename roleMap))))
  | _, _, map, [], first, second => map.keepAppend first second
  | _, _, map, role :: rest, first, second =>
      keepRolesAppend type (map.keepOne ⟨type, role⟩) rest first second

/-- The inputs of a loop's region: the iteration number of each participant, the carried
values, then the captures. -/
@[expose] def initialLoop (roleMap : RoleMap) (participants : List Nat)
    (first second : List Located) :
    RoleRenaming roleMap (bindAll [] (Located.ofRoles .nat participants ++ (first ++ second)))
      (bindAll [] (Located.ofRoles .nat (participants.map roleMap.apply) ++
        (first.map (Located.rename roleMap) ++ second.map (Located.rename roleMap)))) :=
  keepRolesAppend .nat (Mapping.start (Δ := ([] : List Located)) 0 rfl) participants first second

/-- The inputs of the region of an alternative of a variant: the payload of each
participant, then the captures. -/
@[expose] def initialAlternative (roleMap : RoleMap) (payload : Ty) (participants : List Nat)
    (captures : List Located) :
    RoleRenaming roleMap (bindAll [] (Located.ofRoles payload participants ++ captures))
      (bindAll [] (Located.ofRoles payload (participants.map roleMap.apply) ++
        captures.map (Located.rename roleMap))) :=
  keepRolesAppend payload (Mapping.start (Δ := ([] : List Located)) 0 rfl) participants []
    captures

/-- The callee's inputs are the operands of the application. -/
@[expose] def bindOperands : {Γ : List Located} → RoleRenaming roleMap Γ Δ → (inputs : List Located) →
    Operands Δ (inputs.map (Located.rename roleMap)) → RoleRenaming roleMap (bindAll Γ inputs) Δ
  | _, map, [], _ => map
  | _, map, located :: rest, .cons reference operands =>
      bindOperands (map.bind located reference fun _ same => same) rest operands

/-- The operands of an operation, renamed. -/
@[expose] def operands (map : RoleRenaming roleMap Γ Δ) : {types : List Located} → Operands Γ types →
    Operands Δ (types.map (Located.rename roleMap))
  | _, .nil => .nil
  | _, .cons reference rest => .cons (map.image reference) (operands map rest)

/-- The operands of an operation of one role. -/
@[expose] def operandsAt (map : RoleRenaming roleMap Γ Δ) (role : Nat) :
    (types : List Ty) → Operands Γ (Located.atRole role types) →
      Operands Δ (Located.atRole (roleMap.apply role) types)
  | [], _ => .nil
  | type :: types, .cons reference rest =>
      .cons (map.image (located := ⟨type, role⟩) reference) (operandsAt map role types rest)

/-- Operands of one type, one per role of a list. -/
@[expose] def operandsOf (map : RoleRenaming roleMap Γ Δ) (type : Ty) :
    (roles : List Nat) → Operands Γ (Located.ofRoles type roles) →
      Operands Δ (Located.ofRoles type (roles.map roleMap.apply))
  | [], _ => .nil
  | role :: roles, .cons reference rest =>
      .cons (map.image (located := ⟨type, role⟩) reference) (operandsOf map type roles rest)

/-- The count operands of a `repeat`: none for a count of the operation. -/
@[expose] def countOperands (map : RoleRenaming roleMap Γ Δ) (participants : List Nat) :
    (count : RepeatCount) → Operands Γ (count.operands participants) →
      Operands Δ (count.operands (participants.map roleMap.apply))
  | .static _, _ => .nil
  | .runtime _, operands => map.operandsOf .nat participants operands

end RoleRenaming

section Instantiate

variable {operations : List OperationSignature} {functions : List FunctionHeader} {deployed : Bool}

/-- For each region of a list, the map of its inputs to the inputs of its image under a
role map, whose signature it fixes: the image's inputs, and the renamed outputs. -/
inductive RegionRenamings (roleMap : RoleMap) :
    List (List Located × List Located) → List (List Located × List Located) → Type where
  | nil : RegionRenamings roleMap [] []
  | cons {inputs outputs : List Located} {rest : List (List Located × List Located)}
      {renamed : List Located} {targets : List (List Located × List Located)}
      (map : RoleRenaming roleMap (bindAll [] inputs) (bindAll [] renamed))
      (tail : RegionRenamings roleMap rest targets) :
      RegionRenamings roleMap ((inputs, outputs) :: rest)
        ((renamed, outputs.map (Located.rename roleMap)) :: targets)

/-- The regions of a choice on a condition or an arm number under a role map: the inputs
of each are the renamed captures. -/
@[expose] def armRenamings (roleMap : RoleMap) (captures outputs : List Located) :
    (count : Nat) →
      RegionRenamings roleMap (List.replicate count (captures, outputs))
        (List.replicate count
          (captures.map (Located.rename roleMap), outputs.map (Located.rename roleMap)))
  | 0 => .nil
  | count + 1 =>
      .cons (RoleRenaming.initial roleMap captures) (armRenamings roleMap captures outputs count)

/-- The regions of a choice on a variant under a role map: the inputs of the region of an
alternative are the payloads of the renamed participants and the renamed captures. -/
@[expose] def alternativeRenamings (roleMap : RoleMap) (participants : List Nat)
    (captures outputs : List Located) :
    (alternatives : List Ty) →
      RegionRenamings roleMap
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs))
        (alternatives.map fun payload =>
          (Located.ofRoles payload (participants.map roleMap.apply) ++
            captures.map (Located.rename roleMap), outputs.map (Located.rename roleMap)))
  | [] => .nil
  | payload :: rest =>
      .cons (RoleRenaming.initialAlternative roleMap payload participants captures)
        (alternativeRenamings roleMap participants captures outputs rest)

/-- The regions of a choice under a role map as the regions of the renamed choice. -/
@[expose] def choiceRenamings (roleMap : RoleMap) (participants : List Nat)
    (captures outputs : List Located) :
    (tag : ChoiceTag) →
      RegionRenamings roleMap (tag.regions participants captures outputs)
        (tag.regions (participants.map roleMap.apply) (captures.map (Located.rename roleMap))
          (outputs.map (Located.rename roleMap)))
  | .condition => armRenamings roleMap captures outputs 2
  | .arm count => armRenamings roleMap captures outputs count
  | .alternative _ alternatives =>
      alternativeRenamings roleMap participants captures outputs alternatives

mutual
  /-- A region without applications, with its roles run by the caller's roles, its sites
  moved by `base`, and its values taken from the caller's context. -/
  @[expose] def instantiateRegion (roleMap : RoleMap) (base : Nat) {Γ out : List Located} :
      Region (ProtocolDialect operations functions [] deployed) Γ out → {Δ : List Located} →
        RoleRenaming roleMap Γ Δ →
          Region (ProtocolDialect operations functions [] deployed) Δ
            (out.map (Located.rename roleMap))
    | .ret values, _, map => .ret (map.operands values)
    | .stop reason, _, _ => .stop reason
    | .bind (mid := mid) body rest, _, map =>
        .bind (instantiateRegion roleMap base body map)
          (instantiateRegion roleMap base rest (map.keepAll mid))
    | .letOp (.at role op bodies) arguments _ rest, _, map =>
        .letOp (.at (roleMap.apply role) op bodies) (map.operandsAt role op.arguments arguments) .nil
          (instantiateRegion roleMap base rest (map.keepAt role op.results))
    | .letOp (.exchange sender receiver site type) arguments _ rest, _, map =>
        .letOp (.exchange (roleMap.apply sender) (roleMap.apply receiver) (base + site) type)
          (map.operands arguments) .nil
          (instantiateRegion roleMap base rest (map.keepOne ⟨type, receiver⟩))
    | .letOp (.draw owner receivers site (inputs := inputs) (output := output) law populated) arguments _ rest,
        _, map =>
        .letOp (.draw (roleMap.apply owner) (receivers.map roleMap.apply) (base + site) law populated)
          (map.operandsAt owner inputs arguments) .nil
          (instantiateRegion roleMap base rest
            ((map.keepOne ⟨output, owner⟩).keepRoles output receivers))
    | .letOp (.sample owner site (inputs := inputs) (output := output) law populated) arguments _ rest, _,
        map =>
        .letOp (.sample (roleMap.apply owner) (base + site) law populated)
          (map.operandsAt owner inputs arguments) .nil
          (instantiateRegion roleMap base rest (map.keepOne ⟨output, owner⟩))
    | .letOp (.repeat participants count carried collected captures covered) arguments bodies rest,
        _, map =>
        match bodies with
        | .cons body .nil =>
            .letOp
              (.repeat (participants.map roleMap.apply) count
                (carried.map (Located.rename roleMap)) (collected.map (Located.rename roleMap))
                (captures.map (Located.rename roleMap)) (heldBy_rename roleMap covered))
              ((map.countOperands participants count
                  (Values.split (count.operands participants) arguments).1).append
                ((map.operands (Values.split carried
                    (Values.split (count.operands participants) arguments).2).1).append
                  (map.operands (Values.split carried
                    (Values.split (count.operands participants) arguments).2).2)))
              -- The region yields the renamed collected values, then the renamed carried
              -- ones: the renaming of the two lists, appended.
              (.cons ((instantiateRegion roleMap base body
                (RoleRenaming.initialLoop roleMap participants carried captures)).retype
                  List.map_append) .nil)
              (instantiateRegion roleMap base rest (map.keepCollected count.size collected carried))
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, _, map =>
        .letOp
          (.choose (participants.map roleMap.apply) tag (captures.map (Located.rename roleMap))
            (outputs.map (Located.rename roleMap)) (heldBy_rename roleMap covered))
          ((map.operandsOf tag.type participants
              (Values.split (Located.ofRoles tag.type participants) arguments).1).append
            (map.operands (Values.split (Located.ofRoles tag.type participants) arguments).2))
          (instantiateRegions roleMap base bodies
            (choiceRenamings roleMap participants captures outputs tag))
          (instantiateRegion roleMap base rest (map.keepAll outputs))
    | .letOp (.apply callee ..) .., _, _ => callee.elimNil

  /-- Closed regions under a role map, each from the inputs that a map of the region's
  inputs fixes. -/
  def instantiateRegions (roleMap : RoleMap) (base : Nat)
      {signatures targets : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions [] deployed) signatures →
        RegionRenamings roleMap signatures targets →
          Regions (ProtocolDialect operations functions [] deployed) targets
    | .nil, .nil => .nil
    | .cons body tail, .cons map renamings =>
        .cons (instantiateRegion roleMap base body map) (instantiateRegions roleMap base tail renamings)
end

end Instantiate

/-! ## Expansion -/

inductive ExpandRefusal where
  /-- An applied protocol is specification-only and has no expansion. -/
  | specificationOnly
  /-- The expanded definition would have a site that is not below the site limit. -/
  | siteLimit
  /-- Applications are nested deeper than the limit. -/
  | applicationDepth
  deriving Repr

/-- The depth of a context. -/
structure Depth {α : Type} (Γ : List α) where
  depth : Nat
  counted : depth = Γ.length

namespace Depth

variable {α : Type} {Γ : List α}

def empty : Depth ([] : List α) := ⟨0, rfl⟩

def bindAll (known : Depth Γ) (added : List α) : Depth (Zkc.Source.bindAll Γ added) :=
  ⟨known.depth + added.length, by rw [length_bindAll, known.counted]⟩

end Depth

/-- Applications are nested at most this deep. The expansion of a protocol contains a
copy of the expansion of every protocol it applies, so the work to expand a chain of
applications grows with the square of its length. -/
def applicationLimit : Nat := 64

/-- The expansion of a deployed protocol: its body without applications, the origin of
every site, by site number, and the depth of the applications it replaced. -/
structure Expanded (operations : List OperationSignature) (functions : List FunctionHeader)
    (header : ProtocolHeader) where
  body : Region (ProtocolDialect operations functions [] true) (bindAll [] header.inputs)
    header.outputs
  origins : List SiteOrigin
  count : Nat
  counted : count = origins.length
  depth : Nat

/-- The expansions of the protocols, most recent first; none for a specification-only
protocol. -/
abbrev ExpandedTable (operations : List OperationSignature) (functions : List FunctionHeader)
    (protocols : List ProtocolHeader) : Type :=
  Values (fun header => Option (Expanded operations functions header)) protocols

/-- The expansion of a region: the region, the origins of its sites, which are numbered
from the start of the region in order, and the depth of the applications it replaced. -/
structure Expansion (operations : List OperationSignature) (functions : List FunctionHeader)
    (Γ out : List Located) where
  region : Region (ProtocolDialect operations functions [] true) Γ out
  origins : List SiteOrigin
  depth : Nat

/-- The expansion of closed regions. -/
structure Expansions (operations : List OperationSignature) (functions : List FunctionHeader)
    (signatures : List (List Located × List Located)) where
  regions : Regions (ProtocolDialect operations functions [] true) signatures
  origins : List SiteOrigin
  depth : Nat

section Expand

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- The values of a callee's inputs: the operands of the application. -/
@[expose] def RoleRenaming.ofOperands (roleMap : RoleMap) {Δ : List Located} (depth : Depth Δ)
    (inputs : List Located) (operands : Operands Δ (inputs.map (Located.rename roleMap))) :
    RoleRenaming roleMap (bindAll [] inputs) Δ :=
  RoleRenaming.bindOperands (Mapping.start depth.depth depth.counted) inputs operands

-- The equation that the match on the table names is a hypothesis of the meaning theorem.
set_option linter.unusedVariables false in
mutual
  /-- The expansion of a region of a deployed protocol, with its sites numbered from
  `start`. An application becomes a nested block: the callee's expansion at the call. -/
  @[expose] def expandRegion (table : ExpandedTable operations functions protocols) (identity : Nat)
      {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols true) Γ out → Depth Γ → Nat →
        Except ExpandRefusal (Expansion operations functions Γ out)
    | .ret values, _, _ => .ok ⟨.ret values, [], 0⟩
    | .stop reason, _, _ => .ok ⟨.stop reason, [], 0⟩
    | .bind (mid := mid) body rest, depth, start =>
        match expandRegion table identity body depth start with
        | .error refusal => .error refusal
        | .ok first =>
            match expandRegion table identity rest (depth.bindAll mid) (start + first.origins.length) with
            | .error refusal => .error refusal
            | .ok second =>
                .ok ⟨.bind first.region second.region, first.origins ++ second.origins,
                  Nat.max first.depth second.depth⟩
    | .letOp (.at role op bodies) arguments _ rest, depth, start =>
        match expandRegion table identity rest (depth.bindAll _) start with
        | .error refusal => .error refusal
        | .ok rest =>
            .ok ⟨.letOp (.at role op bodies) arguments .nil rest.region, rest.origins, rest.depth⟩
    | .letOp (.exchange sender receiver site type) arguments _ rest, depth, start =>
        match expandRegion table identity rest (depth.bindAll _) (start + 1) with
        | .error refusal => .error refusal
        | .ok rest =>
            .ok ⟨.letOp (.exchange sender receiver start type) arguments .nil rest.region,
              ⟨[], ⟨identity, site⟩⟩ :: rest.origins, rest.depth⟩
    | .letOp (.draw owner receivers site law populated) arguments _ rest, depth, start =>
        match expandRegion table identity rest (depth.bindAll _) (start + 1) with
        | .error refusal => .error refusal
        | .ok rest =>
            .ok ⟨.letOp (.draw owner receivers start law populated) arguments .nil rest.region,
              ⟨[], ⟨identity, site⟩⟩ :: rest.origins, rest.depth⟩
    | .letOp (.sample owner site law populated) arguments _ rest, depth, start =>
        match expandRegion table identity rest (depth.bindAll _) (start + 1) with
        | .error refusal => .error refusal
        | .ok rest =>
            .ok ⟨.letOp (.sample owner start law populated) arguments .nil rest.region,
              ⟨[], ⟨identity, site⟩⟩ :: rest.origins, rest.depth⟩
    | .letOp (.repeat participants count carried collected captures covered) arguments
        bodies rest, depth, start =>
        match expandRegions table identity bodies start with
        | .error refusal => .error refusal
        | .ok nested =>
            match expandRegion table identity rest (depth.bindAll _) (start + nested.origins.length) with
            | .error refusal => .error refusal
            | .ok rest =>
                .ok ⟨.letOp (.repeat participants count carried collected captures covered) arguments
                  nested.regions rest.region, nested.origins ++ rest.origins, Nat.max nested.depth rest.depth⟩
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, depth,
        start =>
        match expandRegions table identity bodies start with
        | .error refusal => .error refusal
        | .ok nested =>
            match expandRegion table identity rest (depth.bindAll _) (start + nested.origins.length) with
            | .error refusal => .error refusal
            | .ok rest =>
                .ok ⟨.letOp (.choose participants tag captures outputs covered) arguments
                  nested.regions rest.region, nested.origins ++ rest.origins,
                  Nat.max nested.depth rest.depth⟩
    | .letOp (.apply (header := header) callee roleMap site _) arguments _ rest, depth, start =>
        match found : table.get callee with
        | none => .error .specificationOnly
        | some expanded =>
            match Nat.ble (start + expanded.count) siteLimit with
            | false => .error .siteLimit
            | true =>
                match Nat.blt expanded.depth applicationLimit with
                | false => .error .applicationDepth
                | true =>
                    match expandRegion table identity rest (depth.bindAll _) (start + expanded.count) with
                    | .error refusal => .error refusal
                    | .ok rest =>
                        .ok ⟨.bind
                          (instantiateRegion roleMap start expanded.body
                            (RoleRenaming.ofOperands roleMap depth header.inputs arguments))
                          rest.region,
                          expanded.origins.map (SiteOrigin.under ⟨identity, site⟩) ++
                            rest.origins,
                          Nat.max (expanded.depth + 1) rest.depth⟩

  @[expose] def expandRegions (table : ExpandedTable operations functions protocols) (identity : Nat)
      {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols true) signatures → Nat →
        Except ExpandRefusal (Expansions operations functions signatures)
    | .nil, _ => .ok ⟨.nil, [], 0⟩
    | .cons (inputs := inputs) body tail, start =>
        match expandRegion table identity body (Depth.empty.bindAll inputs) start with
        | .error refusal => .error refusal
        | .ok first =>
            match expandRegions table identity tail (start + first.origins.length) with
            | .error refusal => .error refusal
            | .ok later =>
                .ok ⟨.cons first.region later.regions, first.origins ++ later.origins,
                  Nat.max first.depth later.depth⟩
end

/-- The expansion of one protocol over the expansions of the earlier ones; none for a
specification-only protocol. -/
@[expose] def expandProtocol (table : ExpandedTable operations functions protocols) (identity : Nat) :
    (header : ProtocolHeader) → ProtocolDefinition operations functions protocols header →
      Except ExpandRefusal (Option (Expanded operations functions header))
  | ⟨_, _, _, _, true⟩, _ => .ok none
  | ⟨_, inputs, _, _, false⟩, definition =>
      match expandRegion table identity definition.body (Depth.empty.bindAll inputs) 0 with
      | .error refusal => .error refusal
      | .ok expansion =>
          .ok (some ⟨expansion.region, expansion.origins, expansion.origins.length, rfl,
            expansion.depth⟩)

/-- The expansions of the protocols of a program with the given identities. -/
@[expose] def expandProtocols {typeTable : TypeTable} (identities : Identities) :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      Except ExpandRefusal (ExpandedTable operations functions protocols)
  | _, .nil => .ok .nil
  | _, .snoc (protocols := earlierHeaders) (header := header) earlier definition _ =>
      match expandProtocols identities earlier with
      | .error refusal => .error refusal
      | .ok table =>
          match expandProtocol table (identities earlierHeaders.length) header definition with
          | .error refusal => .error refusal
          | .ok entry => .ok (.cons entry table)

end Expand

end Zkc.Core
