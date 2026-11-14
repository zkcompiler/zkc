module

public import Zkc.Core.Legal
public import Zkc.Core.ProjectProgramMeaning

public section

/-! Projection never refuses a legal program.

`projectRegion` decides again, by evaluation, facts that the residual check has decided:

| refusal | condition decided again | from the residual check by |
|---|---|---|
| `roleOutOfRange` | the roles an operation names are below the role count | `ProtocolOp.violation_at`, `_exchange`, `_draw`, `_sample`, `_repeat`, `_choose` |
| `repeatedParticipant` | the participants of a `repeat` or `choose` are distinct | `ProtocolOp.violation_repeat`, `_choose` |
| `outputOutsideParticipants` | a role outside a `choose` holds none of its outputs, and one outside a `repeat` none of its collected values | typing (`covered`), `ownCopy_none` and `ownCountOperands_none` |
| `roleMap` | the role map sends exactly the formal role to the role, and every formal role to a role below the role count | `ProtocolOp.violation_apply` and `calleeSide_legal` |
| `missingProgram` | the callee has a program for the formal role | the table of callees is complete (`CalleesComplete`) |
| `calleePorts` | the callee's ports are held by its roles | `HeadersLegal` (the callee has no violation) |

`projectRegion_accepted` proves, by induction on the region, that a legal region is
projected for every role over a complete table of callees. `projectProtocols_complete` is the
program-level statement: every program has role programs, and the table names one for
every protocol and every role below its role count.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## Role maps -/

/-- With distinct entries, a formal role within the map runs as the role exactly when it
is the formal role that `formalRole` finds. -/
theorem formalRole_decides (role : Nat) : ∀ (map : RoleMap), distinctNumbers map = true →
    ∀ (index : Nat), index < map.length →
      Nat.beq (map.apply index) role = Nat.beq index (formalRole role map)
  | [], _, _, below => absurd below (Nat.not_lt_zero _)
  | entry :: rest, distinct, index, below => by
      simp only [distinctNumbers, Bool.and_eq_true, Bool.not_eq_true'] at distinct
      cases same : Nat.beq entry role with
      | true =>
          cases index with
          | zero =>
              show Nat.beq entry role =
                Nat.beq 0 (cond (Nat.beq entry role) 0 (formalRole role rest + 1))
              rw [same]
              rfl
          | succ index =>
              show Nat.beq (RoleMap.apply rest index) role =
                Nat.beq (index + 1) (cond (Nat.beq entry role) 0 (formalRole role rest + 1))
              rw [same]
              have member := RoleMap.apply_mem rest index (Nat.lt_of_succ_lt_succ below)
              cases other : Nat.beq (RoleMap.apply rest index) role with
              | false => rfl
              | true =>
                  have equal : RoleMap.apply rest index = entry :=
                    (Nat.eq_of_beq_eq_true other).trans (Nat.eq_of_beq_eq_true same).symm
                  rw [equal] at member
                  have occurs := (occursIn_iff rest entry).mpr member
                  rw [distinct.1] at occurs
                  cases occurs
      | false =>
          cases index with
          | zero =>
              show Nat.beq entry role =
                Nat.beq 0 (cond (Nat.beq entry role) 0 (formalRole role rest + 1))
              rw [same]
              rfl
          | succ index =>
              show Nat.beq (RoleMap.apply rest index) role =
                Nat.beq (index + 1) (cond (Nat.beq entry role) 0 (formalRole role rest + 1))
              rw [same]
              exact formalRole_decides role rest distinct.2 index (Nat.lt_of_succ_lt_succ below)

/-- The check of the callee's side that projection evaluates at an `apply` holds for a
role map without a violation. -/
theorem calleeSide_legal {bound role count : Nat} {roleMap : RoleMap}
    (below : ∀ entry ∈ roleMap, Nat.blt entry bound = true) (length : roleMap.length = count)
    (distinct : distinctNumbers roleMap = true) :
    calleeSide bound role (formalRole role roleMap) count roleMap = true := by
  simp only [calleeSide, List.all_eq_true, Bool.and_eq_true, List.mem_range]
  intro callee inside
  have within : callee < roleMap.length := length ▸ inside
  exact ⟨below _ (RoleMap.apply_mem roleMap callee within),
    (agreeBool_decides _ _).mpr (formalRole_decides role roleMap distinct callee within)⟩

/-! ## Translations and operands -/

section Translations

variable {role : Nat} {Γ : List Located} {Δ : List Ty}

/-- Values none of which the role holds are skipped. -/
theorem unheld_some : ∀ {Γ : List Located} (translate : Translation role Γ Δ)
    (added : List Located), (∀ located ∈ added, Nat.beq located.holder role = false) →
      ∃ later, translate.unheld added = some later
  | _, translate, [], _ => ⟨translate, rfl⟩
  | _, translate, located :: rest, absent => by
      unfold Translation.unheld
      split
      · exact unheld_some _ rest fun other member => absent other (List.mem_cons_of_mem _ member)
      · rename_i present
        exact absurd ((absent located List.mem_cons_self).symm.trans present) (by decide)

/-- A role that holds none of the collected values of a loop has the results of the loop
that it is outside of. -/
theorem passedCollected_some {Γ₀ : List Located} (base : Translation role Γ₀ Δ)
    (size : Option Nat) (carried : List Located) (operands : Operands Γ₀ carried) :
    ∀ {Γ : List Located} (translate : Translation role Γ Δ) (collected : List Located),
      (∀ located ∈ collected, Nat.beq located.holder role = false) →
        ∃ later, Translation.passedCollected base size translate collected carried operands =
          some later
  | _, translate, [], _ => ⟨_, rfl⟩
  | _, translate, located :: rest, absent => by
      unfold Translation.passedCollected
      split
      · exact passedCollected_some base size carried operands _ rest fun other member =>
          absent other (List.mem_cons_of_mem _ member)
      · rename_i present
        exact absurd ((absent located List.mem_cons_self).symm.trans present) (by decide)

/-- Values held by the participants of a `repeat` or `choose` are not held by a role
that is no participant. -/
theorem heldBy_absent {participants : List Nat} {values : List Located}
    (covered : Located.heldBy participants values = true)
    (absent : ∀ participant ∈ participants, Nat.beq participant role = false) :
    ∀ located ∈ values, Nat.beq located.holder role = false := by
  intro located member
  simp only [Located.heldBy, List.all_eq_true] at covered
  have holder := (occursIn_iff participants located.holder).mp (covered located member)
  exact absent _ holder

theorem consCalled_held (translate : Translation role Γ Δ) (located : Located)
    (reference : Var Γ located) {rest : List Ty} (tail : Operands Δ rest) :
    ∀ (returned held : Bool) (same : Nat.beq located.holder role = held), held = returned →
      ∃ result, consCalled (F := Var Δ) (type := located.type) returned
        (heldArgument translate located reference held same) (some tail) = some result
  | true, true, _, _ => ⟨_, rfl⟩
  | false, false, _, _ => ⟨_, rfl⟩

/-- The role holds the operands of a call of its formal role's program: the callee's
inputs that the formal role holds. -/
theorem calledArguments_some (translate : Translation role Γ Δ) (roleMap : RoleMap)
    (formal count : Nat)
    (decides : ∀ holder, Nat.blt holder count = true →
      Nat.beq (roleMap.apply holder) role = Nat.beq holder formal) :
    ∀ (inputs : List Located), (∀ located ∈ inputs, Nat.blt located.holder count = true) →
      ∀ (operands : Operands Γ (inputs.map (Located.rename roleMap))),
        ∃ result, calledArguments translate roleMap formal inputs operands = some result
  | [], _, _ => ⟨.nil, rfl⟩
  | located :: rest, held, .cons reference values => by
      obtain ⟨tail, found⟩ := calledArguments_some translate roleMap formal count decides rest
        (fun other member => held other (List.mem_cons_of_mem _ member)) values
      show ∃ result, consCalled (Nat.beq located.holder formal)
        (heldArgument translate (located.rename roleMap) reference
          (Nat.beq (roleMap.apply located.holder) role) rfl)
        (calledArguments translate roleMap formal rest values) = some result
      rw [found]
      exact consCalled_held translate (located.rename roleMap) reference tail _ _ rfl
        (decides located.holder (held located List.mem_cons_self))

theorem calledOne_some {Γ' : List Located} (translate : Translation role Γ Δ) (added : Located)
    (later : List Ty)
    (next : {Δ' : List Ty} → Translation role (added :: Γ) Δ' →
      Option (Translation role Γ' (bindAll Δ' later)))
    (continues : ∀ {Δ' : List Ty} (extended : Translation role (added :: Γ) Δ'),
      ∃ result, next extended = some result) :
    ∀ (returned held : Bool) (same : Nat.beq added.holder role = held), held = returned →
      ∃ result, Translation.calledOne translate added later next returned held same = some result
  | true, true, _, _ => continues _
  | false, false, _, _ => continues _

/-- The results of a call of the formal role's program are the results of the application
that the role holds. -/
theorem called_some (roleMap : RoleMap) (formal count : Nat)
    (decides : ∀ holder, Nat.blt holder count = true →
      Nat.beq (roleMap.apply holder) role = Nat.beq holder formal) :
    ∀ {Γ : List Located} {Δ : List Ty} (translate : Translation role Γ Δ)
      (outputs : List Located), (∀ located ∈ outputs, Nat.blt located.holder count = true) →
        ∃ later, translate.called roleMap formal outputs = some later
  | _, _, translate, [], _ => ⟨translate, rfl⟩
  | _, _, translate, located :: rest, held => by
      show ∃ later, Translation.calledOne translate (located.rename roleMap) (own formal rest)
        (fun later => Translation.called roleMap formal later rest)
        (Nat.beq located.holder formal) (Nat.beq (roleMap.apply located.holder) role) rfl =
          some later
      exact calledOne_some translate (located.rename roleMap) _ _
        (fun extended => called_some roleMap formal count decides extended rest
          fun other member => held other (List.mem_cons_of_mem _ member))
        _ _ rfl (decides located.holder (held located List.mem_cons_self))

end Translations

/-! ## The table of callees -/

section Callees

variable {protocols : List ProtocolHeader} {programs : List RoleHeader}

/-- The table of callees is complete: it has a program for every formal role of every
protocol. -/
structure CalleesComplete (callees : ProjectedCallees protocols programs) : Prop where
  program : ∀ {header : ProtocolHeader} (callee : Var protocols header) (formal : Nat),
    Nat.blt formal header.roles = true → (callees.level? callee.index formal).isSome = true

/-- A complete table names a program for every formal role. -/
theorem CalleesComplete.find {callees : ProjectedCallees protocols programs}
    (complete : CalleesComplete callees) {header : ProtocolHeader} (callee : Var protocols header)
    (formal : Nat) (below : Nat.blt formal header.roles = true) :
    ∃ program, callees.find callee formal = some program := by
  have recorded := complete.program callee formal below
  cases found : callees.level? callee.index formal with
  | none =>
      rw [found] at recorded
      cases recorded
  | some level =>
      have valid := callees.level?_valid callee found
      have position : programs[callees.depth - 1 - level]? = some (roleHeader formal header) := by
        unfold atLevel? at valid
        split at valid
        · exact valid
        · cases valid
      exact ⟨⟨callees.depth - 1 - level, position⟩,
        (callees.find_eq_some_iff callee formal _).mpr ⟨level, found, rfl⟩⟩

theorem CalleesComplete.empty :
    CalleesComplete (ProjectedCallees.empty : ProjectedCallees [] programs) :=
  ⟨fun callee => callee.elimNil⟩

theorem CalleesComplete.weaken {callees : ProjectedCallees protocols programs}
    (complete : CalleesComplete callees) (added : RoleHeader) :
    CalleesComplete (callees.weaken added) :=
  ⟨fun callee formal below => complete.program callee formal below⟩

end Callees

/-! ## Regions -/

/-- A projection is not refused. -/
def Accepted {dialect : Dialect} {Γ out : List dialect.Ty} :
    Except ProjectionRefusal (Region dialect Γ out) → Prop
  | .ok _ => True
  | .error _ => False

theorem Accepted.of_ok {dialect : Dialect} {Γ out : List dialect.Ty}
    {projected : Region dialect Γ out} :
    Accepted (.ok projected : Except ProjectionRefusal _) := trivial

theorem Accepted.ok {dialect : Dialect} {Γ out : List dialect.Ty} :
    ∀ {result : Except ProjectionRefusal (Region dialect Γ out)}, Accepted result →
      ∃ projected, result = .ok projected
  | .ok projected, _ => ⟨projected, rfl⟩
  | .error _, accepted => nomatch accepted

section Regions

variable {typeTable : TypeTable} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {programs : List RoleHeader} {deployed : Bool}
  {callees : ProjectedCallees protocols programs}

/-- The announcements of a coin drawn by another role are projected when the rest is. -/
theorem projectReceives_accepted (role bound site : Nat) (output : Ty) {out : List Ty} :
    ∀ (receivers : List Nat), (∀ receiver ∈ receivers, Nat.blt receiver bound = true) →
    ∀ {Γ : List Located} {Δ : List Ty} (translate : Translation role Γ Δ)
      (rest : {Δ' : List Ty} → Translation role (bindAll Γ (Located.ofRoles output receivers)) Δ' →
        Except ProjectionRefusal (Region (RoleDialect operations functions programs deployed) Δ' out)),
      (∀ {Δ' : List Ty} (later : Translation role (bindAll Γ (Located.ofRoles output receivers)) Δ'),
        Accepted (rest later)) →
        Accepted (projectReceives role site output receivers translate rest)
  | [], _, _, _, translate, rest, continues => continues translate
  | receiver :: receivers, below, _, _, translate, rest, continues => by
      have within := below receiver List.mem_cons_self
      have belowRest : ∀ other ∈ receivers, Nat.blt other bound = true :=
        fun other member => below other (List.mem_cons_of_mem _ member)
      unfold projectReceives
      split
      · obtain ⟨next, projects⟩ := (projectReceives_accepted role bound site output receivers
          belowRest (translate.present ⟨output, receiver⟩) rest continues).ok
        rw [projects]
        exact Accepted.of_ok
      · exact projectReceives_accepted role bound site output receivers belowRest _ rest continues

variable (complete : CalleesComplete callees) (headers : HeadersLegal protocols)
include complete headers

set_option linter.unusedSectionVars false in
mutual
  /-- A legal region is projected for every role. -/
  theorem projectRegion_accepted (role bound : Nat) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
        (enclosing : Option (List Nat)), Region.Legal typeTable bound enclosing region →
        ∀ {Δ : List Ty} (translate : Translation role Γ Δ),
          Accepted (projectRegion (programs := programs) role bound callees region translate)
    | .ret values, _, _, _, translate => by
        unfold projectRegion
        exact Accepted.of_ok
    | .stop reason, _, legal, _, _ => legal.not_stop.elim
    | .bind (mid := mid) body rest, enclosing, legal, Δ, translate => by
        obtain ⟨first, projectsBody⟩ :=
          (projectRegion_accepted role bound body enclosing legal.bind.1 translate).ok
        obtain ⟨second, projectsRest⟩ :=
          (projectRegion_accepted role bound rest enclosing legal.bind.2 (translate.extend mid)).ok
        unfold projectRegion
        rw [projectsBody, projectsRest]
        exact Accepted.of_ok
    | .letOp (.at holder op bodies) arguments nested rest, enclosing, legal, Δ, translate => by
        cases nested
        have within := ProtocolOp.violation_at legal.letOp.1
        unfold projectRegion
        split
        · rename_i beyond
          exact absurd (within.symm.trans beyond) (by decide)
        · rename_i _ present
          obtain ⟨next, projects⟩ :=
            (projectRegion_accepted role bound rest enclosing legal.letOp.2.2
              (Translation.presentAll holder translate op.results)).ok
          rw [projects]
          exact Accepted.of_ok
        · exact projectRegion_accepted role bound rest enclosing legal.letOp.2.2 _
    | .letOp (.exchange sender receiver site type) arguments nested rest, enclosing, legal, Δ,
        translate => by
        cases nested
        have within := ProtocolOp.violation_exchange legal.letOp.1
        have both : (Nat.blt sender bound && Nat.blt receiver bound) = true := by
          rw [within.1, within.2]
          rfl
        unfold projectRegion
        split
        · rename_i beyond
          exact absurd (both.symm.trans beyond) (by decide)
        · exact projectRegion_accepted role bound rest enclosing legal.letOp.2.2 _
        · rename_i _ sends _
          obtain ⟨next, projects⟩ :=
            (projectRegion_accepted role bound rest enclosing legal.letOp.2.2
              (translate.absent ⟨type, receiver⟩ ‹_›)).ok
          rw [projects]
          exact Accepted.of_ok
        · rename_i _ _ receives
          obtain ⟨next, projects⟩ :=
            (projectRegion_accepted role bound rest enclosing legal.letOp.2.2
              (translate.present ⟨type, receiver⟩)).ok
          rw [projects]
          exact Accepted.of_ok
        · exact projectRegion_accepted role bound rest enclosing legal.letOp.2.2 _
    | .letOp (.draw owner receivers site (inputs := inputs) (output := output) law populated) arguments nested
        rest, enclosing, legal, Δ, translate => by
        cases nested
        have within := ProtocolOp.violation_draw legal.letOp.1
        have both : (Nat.blt owner bound && rolesBelow bound receivers) = true := by
          rw [within.1, Bool.true_and]
          simpa only [rolesBelow, List.all_eq_true] using within.2
        unfold projectRegion
        split
        · rename_i beyond
          exact absurd (both.symm.trans beyond) (by decide)
        · rename_i _ owns
          obtain ⟨next, projects⟩ :=
            (projectRegion_accepted role bound rest enclosing legal.letOp.2.2
              (translate.drawn owner output receivers)).ok
          rw [projects]
          exact Accepted.of_ok
        · exact projectReceives_accepted role bound site output receivers within.2 _ _
            fun later => projectRegion_accepted role bound rest enclosing legal.letOp.2.2 later
    | .letOp (.sample owner site (inputs := inputs) (output := output) law populated) arguments nested rest,
        enclosing, legal, Δ, translate => by
        cases nested
        have within := ProtocolOp.violation_sample legal.letOp.1
        unfold projectRegion
        split
        · rename_i beyond
          exact absurd (within.symm.trans beyond) (by decide)
        · rename_i _ owns
          obtain ⟨next, projects⟩ :=
            (projectRegion_accepted role bound rest enclosing legal.letOp.2.2
              (translate.present ⟨output, owner⟩)).ok
          rw [projects]
          exact Accepted.of_ok
        · exact projectRegion_accepted role bound rest enclosing legal.letOp.2.2 _
    | .letOp (.repeat participants count carried collected captures covered) arguments
        (.cons body .nil) rest, enclosing, legal, Δ, translate => by
        have facts := ProtocolOp.violation_repeat legal.letOp.1
        have below : rolesBelow bound participants = true := by
          simpa only [rolesBelow, List.all_eq_true] using facts.1
        unfold projectRegion
        split
        rename_i inner same
        obtain ⟨rfl⟩ : body = inner := by injection same
        split
        · rename_i beyond
          exact absurd (below.symm.trans beyond) (by decide)
        · rename_i _ repeated
          exact absurd (facts.2.1.symm.trans repeated) (by decide)
        · split
          · rename_i copies counted
            obtain ⟨loop, projectsBody⟩ :=
              (projectRegion_accepted role bound body _ legal.letOp.2.1.cons.1
                (Translation.initialLoop role participants carried captures)).ok
            obtain ⟨next, projectsRest⟩ :=
              (projectRegion_accepted role bound rest enclosing legal.letOp.2.2
                (translate.extendCollected count.size collected carried)).ok
            rw [projectsBody, projectsRest]
            exact Accepted.of_ok
          · rename_i missing
            have absent := ownCountOperands_none (translate := translate) participants count _
              missing
            obtain ⟨later, skipped⟩ := passedCollected_some translate count.size carried _
              translate collected (heldBy_absent covered absent)
            split
            · exact projectRegion_accepted role bound rest enclosing legal.letOp.2.2 _
            · rename_i refused
              rw [skipped] at refused
              cases refused
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, enclosing,
        legal, Δ, translate => by
        have facts := ProtocolOp.violation_choose legal.letOp.1
        have below : rolesBelow bound participants = true := by
          simpa only [rolesBelow, List.all_eq_true] using facts.1
        unfold projectRegion
        split
        · rename_i beyond
          exact absurd (below.symm.trans beyond) (by decide)
        · rename_i _ repeated
          exact absurd (facts.2.1.symm.trans repeated) (by decide)
        · split
          · rename_i copy tagged
            obtain ⟨arms, projectsArms⟩ :=
              projectRegions_accepted role bound bodies _ legal.letOp.2.1
                (choiceTranslations role participants captures outputs tag)
            obtain ⟨next, projectsRest⟩ :=
              (projectRegion_accepted role bound rest enclosing legal.letOp.2.2
                (translate.extend outputs)).ok
            rw [projectsArms, projectsRest]
            exact Accepted.of_ok
          · rename_i tagged
            have absent := ownCopy_none (translate := translate) tag.type participants _ tagged
            obtain ⟨later, skipped⟩ := unheld_some translate outputs (heldBy_absent covered absent)
            split
            · exact projectRegion_accepted role bound rest enclosing legal.letOp.2.2 _
            · rename_i missing
              rw [skipped] at missing
              cases missing
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest,
        enclosing, legal, Δ, translate => by
        cases nested
        have facts := ProtocolOp.violation_apply legal.letOp.1
        have side := calleeSide_legal (role := role) facts.1 facts.2.1 facts.2.2
        have decides : ∀ holder, Nat.blt holder header.roles = true →
            Nat.beq (roleMap.apply holder) role = Nat.beq holder (formalRole role roleMap) :=
          fun holder inside => formalRole_decides role roleMap facts.2.2 holder
            (facts.2.1 ▸ Nat.blt_eq.mp inside)
        have ports := headers callee
        unfold projectRegion
        split
        · rename_i beyond
          exact absurd (side.symm.trans beyond) (by decide)
        · rename_i _ inside
          obtain ⟨program, named⟩ := complete.find callee _ inside
          obtain ⟨operands, passes⟩ := calledArguments_some translate roleMap
            (formalRole role roleMap) header.roles decides header.inputs
            (fun located member => ports located (List.mem_append_left _ member)) arguments
          obtain ⟨later, returns⟩ := called_some roleMap (formalRole role roleMap) header.roles
            decides translate header.outputs
            (fun located member => ports located (List.mem_append_right _ member))
          split
          · rename_i missing
            rw [named] at missing
            cases missing
          · split
            · rename_i extended _ _
              obtain ⟨next, projects⟩ :=
                (projectRegion_accepted role bound rest enclosing legal.letOp.2.2 extended).ok
              rw [projects]
              exact Accepted.of_ok
            · rename_i refuses
              exact (refuses operands later passes returns).elim
        · rename_i _ outside
          have absent : ∀ located ∈ header.outputs.map (Located.rename roleMap),
              Nat.beq located.holder role = false := by
            intro located member
            obtain ⟨source, inOutputs, renamed⟩ := List.mem_map.mp member
            subst renamed
            have inside := ports source (List.mem_append_right _ inOutputs)
            show Nat.beq (roleMap.apply source.holder) role = false
            rw [decides source.holder inside]
            cases same : Nat.beq source.holder (formalRole role roleMap) with
            | false => rfl
            | true =>
                rw [Nat.eq_of_beq_eq_true same, outside] at inside
                cases inside
          obtain ⟨later, skipped⟩ := unheld_some translate _ absent
          split
          · exact projectRegion_accepted role bound rest enclosing legal.letOp.2.2 _
          · rename_i missing
            rw [skipped] at missing
            cases missing

  /-- Legal closed regions are projected for every role, whatever the translations of
  their inputs. -/
  theorem projectRegions_accepted (role bound : Nat)
      {signatures : List (List Located × List Located)} {targets : List (List Ty × List Ty)} :
      ∀ (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures)
        (enclosing : Option (List Nat)), Regions.Legal typeTable bound enclosing regions →
        ∀ (translations : RegionTranslations role signatures targets),
          ∃ projected,
            projectRegions (programs := programs) role bound callees regions translations =
              .ok projected
    | .nil, _, _, .nil => ⟨.nil, rfl⟩
    | .cons body tail, enclosing, legal, .cons translate translations => by
        obtain ⟨first, projectsBody⟩ :=
          (projectRegion_accepted role bound body enclosing legal.cons.1 translate).ok
        obtain ⟨later, projectsTail⟩ :=
          projectRegions_accepted role bound tail enclosing legal.cons.2 translations
        simp only [projectRegions]
        rw [projectsBody, projectsTail]
        exact ⟨_, rfl⟩
end

/-- A definition without a violation has a program for every role. -/
theorem projectProtocol_accepted (role : Nat) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (wellFormed : definition.violation typeTable = none) :
    ∃ program, projectProtocol (programs := programs) role callees definition = .ok program := by
  obtain ⟨body, projects⟩ :=
    (projectRegion_accepted (typeTable := typeTable) complete headers role header.roles
      definition.body none (ProtocolDefinition.body_legal wellFormed)
      (Translation.initial role header.inputs)).ok
  unfold projectProtocol
  rw [projects]
  exact ⟨_, rfl⟩

end Regions

/-! ## Programs -/

section Programs

variable {typeTable : TypeTable} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- The programs of the remaining formal roles of a definition without a violation are
added, the table stays complete, and one level is recorded per role. -/
theorem projectFormals_complete (headers : HeadersLegal protocols) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (wellFormed : definition.violation typeTable = none) :
    ∀ (remaining : Nat) (state : Formals operations functions protocols header remaining),
      CalleesComplete state.callees →
        ∃ result, projectFormals definition remaining state = .ok result ∧
          CalleesComplete result.callees ∧
          result.levels.length = state.levels.length + remaining
  | 0, state, complete => ⟨state, rfl, complete, rfl⟩
  | formal + 1, ⟨roleHeaders, programs, callees, levels, valid⟩, complete => by
      obtain ⟨program, projects⟩ := projectProtocol_accepted (programs := roleHeaders) complete
        headers formal definition wellFormed
      unfold projectFormals
      simp only [projects]
      obtain ⟨result, continues, stays, counted⟩ := projectFormals_complete headers definition
        wellFormed formal
        ⟨roleHeader formal header :: roleHeaders, .snoc programs protocols.length formal program,
          callees.weaken _, callees.depth :: levels, _⟩ (complete.weaken _)
      refine ⟨result, continues, stays, ?_⟩
      rw [counted, List.length_cons]
      omega

/-- Projection never refuses a program: every definition of a program has no residual
violation, so every protocol has a program for every one of its roles, and the table of
callees of the result is complete. -/
theorem projectProtocols_complete :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols),
      ∃ projected, projectProtocols program = .ok projected ∧ CalleesComplete projected.callees
  | _, .nil => ⟨_, rfl, CalleesComplete.empty⟩
  | _, .snoc (header := header) earlier definition wellFormed => by
      obtain ⟨⟨roleHeaders, programs, callees⟩, projectsEarlier, complete⟩ :=
        projectProtocols_complete earlier
      obtain ⟨⟨finalHeaders, finalPrograms, finalCallees, levels, valid⟩, projectsFormals, stays,
          counted⟩ :=
        projectFormals_complete earlier.headersLegal definition wellFormed header.roles
          ⟨roleHeaders, programs, callees, [], fun _ _ found => nomatch found⟩ complete
      unfold projectProtocols
      simp only [projectsEarlier, projectsFormals]
      refine ⟨_, rfl, ⟨fun {other} callee formal below => ?_⟩⟩
      cases callee with
        | here =>
            rw [Var.index_here, ProjectedCallees.level?_extend_zero]
            have inside : formal < levels.length := by
              have length : levels.length = header.roles := by simpa using counted
              rw [length]
              exact Nat.blt_eq.mp below
            rw [List.getElem?_eq_getElem inside]
            rfl
        | there callee =>
            rw [Var.index_there, ProjectedCallees.level?_extend_succ]
            exact stays.program callee formal below

/-- Projection with calls returns a program for every protocol of a program and every
role of the protocol. -/
theorem projectProtocols_never_refuses
    (program : Protocols typeTable operations functions protocols) :
    ∃ projected, projectProtocols program = .ok projected ∧
      ∀ {header : ProtocolHeader} (callee : Var protocols header) (role : Nat),
        Nat.blt role header.roles = true →
          ∃ roleProgram, projected.callees.find callee role = some roleProgram := by
  obtain ⟨projected, projects, complete⟩ := projectProtocols_complete program
  exact ⟨projected, projects, fun callee role below => complete.find callee role below⟩

end Programs

end Zkc.Core
