module

public import Zkc.Core.Labelled
public import Zkc.Core.Expand

public section

/-! Expansion keeps the meaning of every side.

Two statements, each a structural induction on the region.

`instantiateRegion_meaning`: the instantiated region, for a side of the caller and a
labelling of its sites, is the original region for the callee's side of the application
(the preimage of the caller's side under the role map) with the labelling moved by the
base, its results seen as the caller's values. Instantiation treats every operation
uniformly, so the proof has no case analysis on the membership of a role: each case
shows that the renamed operation is given the same values and reads the same site.

`expandRegion_meaning`: the expansion of a region, with the labelling that sends each
new site number to the site it came from, has the meaning of the region in the model,
whose `apply` runs the callee's meaning for the callee's side. The case of `apply`
combines the first statement with the same statement for the callee, which the table of
expansions carries (`ExpandedSound`); every other case is a congruence.

`expandProtocols_sound` establishes the invariant of the table by induction over the
protocols of a program.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## Environments under a role map -/

section Values

variable {model : Model} {roleMap : RoleMap} {side : Side}

/-- The caller's environment holds, for every value of the callee, that value. A value
of the callee's side is a value of the caller's side at the renamed type. -/
structure Renames {Γ Δ : List Located} (map : RoleRenaming roleMap Γ Δ)
    (env : Environment (SideValue model (Side.preimage roleMap side)) Γ)
    (image : Environment (SideValue model side) Δ) : Prop where
  value : ∀ {located : Located} (reference : Var Γ located),
    image (map.image reference) = env reference

/-- Copies of one type, one per role of a list, as the caller's values. -/
def renameCopies (model : Model) (roleMap : RoleMap) (side : Side) (type : Ty) :
    (roles : List Nat) →
      Values (SideValue model (Side.preimage roleMap side)) (Located.ofRoles type roles) →
        Values (SideValue model side) (Located.ofRoles type (roles.map roleMap.apply))
  | [], _ => .nil
  | _ :: rest, .cons value values => .cons value (renameCopies model roleMap side type rest values)

/-- Control values, one per participant, indexed by the caller's roles. -/
def renameControls {X : Type} (roleMap : RoleMap) (side : Side) :
    (roles : List Nat) → Values (fun role => Held X (side (roleMap.apply role))) roles →
      Values (fun role => Held X (side role)) (roles.map roleMap.apply)
  | [], _ => .nil
  | _ :: rest, .cons value values => .cons value (renameControls roleMap side rest values)

/-- The sequences of collected values of a `repeat`, as the caller's values. -/
def renameSequences (model : Model) (roleMap : RoleMap) (side : Side) (size : Option Nat) :
    (collected : List Located) →
      Values (SideValue model (Side.preimage roleMap side)) (collectedSequencesAt size collected) →
        Values (SideValue model side)
          (collectedSequencesAt size (collected.map (Located.rename roleMap)))
  | [], _ => .nil
  | _ :: rest, .cons value values =>
      .cons value (renameSequences model roleMap side size rest values)

/-- The results of a `repeat`, as the caller's values. -/
def renameCollected (model : Model) (roleMap : RoleMap) (side : Side) (size : Option Nat)
    (carried : List Located) :
    (collected : List Located) →
      Values (SideValue model (Side.preimage roleMap side))
        (collectedSequencesAt size collected ++ carried) →
        Values (SideValue model side)
          (collectedSequencesAt size (collected.map (Located.rename roleMap)) ++
            carried.map (Located.rename roleMap))
  | [], values => remapValues (F := SideValue model side) (Located.rename roleMap) carried values
  | _ :: rest, .cons value values =>
      .cons value (renameCollected model roleMap side size carried rest values)

variable {Γ Δ : List Located} {map : RoleRenaming roleMap Γ Δ}
  {env : Environment (SideValue model (Side.preimage roleMap side)) Γ}
  {image : Environment (SideValue model side) Δ}

/-- One more value on both sides. -/
theorem Renames.keepOne (renames : Renames map env image) (source : Located)
    (value : SideValue model (Side.preimage roleMap side) source) :
    Renames (map.keepOne source) (env.push value)
      (image.push (ty := source.rename roleMap) value) := by
  refine ⟨fun {located} reference => ?_⟩
  cases reference with
  | here => exact congrArg (image.push (ty := source.rename roleMap) value) (Mapping.apply_keep_here ..)
  | there reference =>
      exact (congrArg (image.push (ty := source.rename roleMap) value)
        (Mapping.apply_keep_there ..)).trans (renames.value reference)

/-- New values on both sides. -/
theorem Renames.keepAll :
    ∀ (added : List Located) {Γ Δ : List Located} {map : RoleRenaming roleMap Γ Δ}
      {env : Environment (SideValue model (Side.preimage roleMap side)) Γ}
      {image : Environment (SideValue model side) Δ}, Renames map env image →
      ∀ (values : Values (SideValue model (Side.preimage roleMap side)) added),
        Renames (map.keepAll added) (Environment.bindAll env values)
          (Environment.bindAll image
            (remapValues (F := SideValue model side) (Located.rename roleMap) added values))
  | [], _, _, _, _, _, renames, .nil => renames
  | located :: rest, _, _, _, _, _, renames, .cons value values =>
      Renames.keepAll rest (renames.keepOne located value) values

/-- New values of one holder. -/
theorem Renames.keepAt (role : Nat) :
    ∀ (types : List Ty) {Γ Δ : List Located} {map : RoleRenaming roleMap Γ Δ}
      {env : Environment (SideValue model (Side.preimage roleMap side)) Γ}
      {image : Environment (SideValue model side) Δ}, Renames map env image →
      ∀ (held : Values (fun type => Held (model.Value type) (side (roleMap.apply role))) types),
        Renames (map.keepAt role types)
          (Environment.bindAll env
            (remapValues (F := SideValue model (Side.preimage roleMap side))
              (fun type => ⟨type, role⟩) types held))
          (Environment.bindAll image
            (remapValues (F := SideValue model side) (fun type => ⟨type, roleMap.apply role⟩)
              types held))
  | [], _, _, _, _, _, renames, .nil => renames
  | type :: rest, _, _, _, _, _, renames, .cons value held =>
      Renames.keepAt role rest (renames.keepOne ⟨type, role⟩ value) held

/-- New values of one type, one per role of a list. -/
theorem Renames.keepRoles (type : Ty) :
    ∀ (roles : List Nat) {Γ Δ : List Located} {map : RoleRenaming roleMap Γ Δ}
      {env : Environment (SideValue model (Side.preimage roleMap side)) Γ}
      {image : Environment (SideValue model side) Δ}, Renames map env image →
      ∀ (copies : Values (SideValue model (Side.preimage roleMap side)) (Located.ofRoles type roles)),
        Renames (map.keepRoles type roles) (Environment.bindAll env copies)
          (Environment.bindAll image (renameCopies model roleMap side type roles copies))
  | [], _, _, _, _, _, renames, .nil => renames
  | role :: rest, _, _, _, _, _, renames, .cons value copies =>
      Renames.keepRoles type rest (renames.keepOne ⟨type, role⟩ value) copies

/-- New values of two lists. -/
theorem Renames.keepAppend (second : List Located)
    (last : Values (SideValue model (Side.preimage roleMap side)) second) :
    ∀ (first : List Located) {Γ Δ : List Located} {map : RoleRenaming roleMap Γ Δ}
      {env : Environment (SideValue model (Side.preimage roleMap side)) Γ}
      {image : Environment (SideValue model side) Δ}, Renames map env image →
      ∀ (values : Values (SideValue model (Side.preimage roleMap side)) first),
        Renames (map.keepAppend first second) (Environment.bindAll env (values.append last))
          (Environment.bindAll image
            ((remapValues (F := SideValue model side) (Located.rename roleMap) first values).append
              (remapValues (F := SideValue model side) (Located.rename roleMap) second last)))
  | [], _, _, _, _, _, renames, .nil => Renames.keepAll second renames last
  | located :: rest, _, _, _, _, _, renames, .cons value values =>
      Renames.keepAppend second last rest (renames.keepOne located value) values

/-- New values of one type, one per role of a list, then new values of two lists. -/
theorem Renames.keepRolesAppend (type : Ty) (first second : List Located)
    (values : Values (SideValue model (Side.preimage roleMap side)) first)
    (last : Values (SideValue model (Side.preimage roleMap side)) second) :
    ∀ (roles : List Nat) {Γ Δ : List Located} {map : RoleRenaming roleMap Γ Δ}
      {env : Environment (SideValue model (Side.preimage roleMap side)) Γ}
      {image : Environment (SideValue model side) Δ}, Renames map env image →
      ∀ (copies : Values (SideValue model (Side.preimage roleMap side)) (Located.ofRoles type roles)),
        Renames (map.keepRolesAppend type roles first second)
          (Environment.bindAll env (copies.append (values.append last)))
          (Environment.bindAll image
            ((renameCopies model roleMap side type roles copies).append
              ((remapValues (F := SideValue model side) (Located.rename roleMap) first values).append
                (remapValues (F := SideValue model side) (Located.rename roleMap) second last))))
  | [], _, _, _, _, _, renames, .nil => Renames.keepAppend second last first renames values
  | role :: rest, _, _, _, _, _, renames, .cons value copies =>
      Renames.keepRolesAppend type first second values last rest
        (renames.keepOne ⟨type, role⟩ value) copies

/-- The results of a `repeat`. -/
theorem Renames.keepCollected (size : Option Nat) (carried : List Located) :
    ∀ (collected : List Located) {Γ Δ : List Located} {map : RoleRenaming roleMap Γ Δ}
      {env : Environment (SideValue model (Side.preimage roleMap side)) Γ}
      {image : Environment (SideValue model side) Δ}, Renames map env image →
      ∀ (values : Values (SideValue model (Side.preimage roleMap side))
          (collectedSequencesAt size collected ++ carried)),
        Renames (map.keepCollected size collected carried) (Environment.bindAll env values)
          (Environment.bindAll image
            (renameCollected model roleMap side size carried collected values))
  | [], _, _, _, _, _, renames, values => Renames.keepAll carried renames values
  | located :: rest, _, _, _, _, _, renames, .cons value values =>
      Renames.keepCollected size carried rest
        (renames.keepOne ⟨.seq located.type size, located.holder⟩ value) values

/-- The empty contexts. -/
theorem Renames.start (depth : Nat) (counted : depth = Δ.length)
    (image : Environment (SideValue model side) Δ) :
    Renames (Mapping.start (R := Renamed roleMap) depth counted) (Environment.empty) image :=
  ⟨fun reference => reference.elimNil⟩

/-- The callee's inputs are the operands of the application. -/
theorem Renames.bindOperands {image : Environment (SideValue model side) Δ} :
    ∀ (inputs : List Located) {Γ : List Located} {map : RoleRenaming roleMap Γ Δ}
      {env : Environment (SideValue model (Side.preimage roleMap side)) Γ}, Renames map env image →
      ∀ (operands : Operands Δ (inputs.map (Located.rename roleMap))),
        Renames (map.bindOperands inputs operands)
          (Environment.bindAll env
            (unmapValues (F := SideValue model side) (Located.rename roleMap) inputs
              (Operands.eval image operands))) image
  | [], _, _, _, renames, .nil => renames
  | located :: rest, _, map, env, renames, .cons reference operands => by
      refine Renames.bindOperands rest (map := map.bind located reference fun _ same => same)
        (env := env.push (image reference)) ⟨fun {other} position => ?_⟩ operands
      cases position with
      | here => exact congrArg image (Mapping.apply_bind_here ..)
      | there position =>
          exact (congrArg image (Mapping.apply_bind_there ..)).trans (renames.value position)

/-- The renamed operands hold the callee's operands, as the caller's values. -/
theorem eval_operands (renames : Renames map env image) :
    ∀ {types : List Located} (values : Operands Γ types),
      Operands.eval image (map.operands values) =
        remapValues (F := SideValue model side) (Located.rename roleMap) types
          (Operands.eval env values)
  | _, .nil => rfl
  | _, .cons reference rest => by
      show Values.cons _ _ = Values.cons _ _
      rw [eval_operands renames rest]
      exact congrArg (fun value => Values.cons value _) (renames.value reference)

/-- The renamed operands of an operation of one role hold the callee's operands. -/
theorem eval_operandsAt (renames : Renames map env image) (role : Nat) :
    ∀ (types : List Ty) (arguments : Operands Γ (Located.atRole role types)),
      unmapValues (F := SideValue model side) (fun type => ⟨type, roleMap.apply role⟩) types
          (Operands.eval image (map.operandsAt role types arguments)) =
        unmapValues (F := SideValue model (Side.preimage roleMap side)) (fun type => ⟨type, role⟩)
          types (Operands.eval env arguments)
  | [], .nil => rfl
  | type :: types, .cons reference rest =>
      cons_congr (renames.value (located := ⟨type, role⟩) reference)
        (eval_operandsAt renames role types rest)

/-- The renamed copies of a control value hold the callee's copies. -/
theorem eval_operandsOf (renames : Renames map env image) (type : Ty) :
    ∀ (roles : List Nat) (operands : Operands Γ (Located.ofRoles type roles)),
      unmapValues (F := SideValue model side) (fun role => ⟨type, role⟩) (roles.map roleMap.apply)
          (Operands.eval image (map.operandsOf type roles operands)) =
        renameControls roleMap side roles
          (unmapValues (F := SideValue model (Side.preimage roleMap side)) (fun role => ⟨type, role⟩)
            roles (Operands.eval env operands))
  | [], .nil => rfl
  | role :: roles, .cons reference rest =>
      cons_congr (renames.value (located := ⟨type, role⟩) reference)
        (eval_operandsOf renames type roles rest)

/-- The copies of a count of the operation under a role map are the callee's copies. -/
theorem staticCopies_rename (number : Nat) :
    ∀ (participants : List Nat),
      repeatCopies model side (participants.map roleMap.apply) (.static number) .nil =
        renameControls roleMap side participants
          (repeatCopies model (Side.preimage roleMap side) participants (.static number) .nil)
  | [] => rfl
  | _ :: rest => cons_congr rfl (staticCopies_rename number rest)

/-- The renamed count operands of a `repeat` hold the callee's copies of the count. -/
theorem eval_countOperands (renames : Renames map env image) (participants : List Nat) :
    ∀ (count : RepeatCount) (operands : Operands Γ (count.operands participants)),
      repeatCopies model side (participants.map roleMap.apply) count
          (Operands.eval image (map.countOperands participants count operands)) =
        renameControls roleMap side participants
          (repeatCopies model (Side.preimage roleMap side) participants count
            (Operands.eval env operands))
  | .static number, _ => staticCopies_rename number participants
  | .runtime _, operands => eval_operandsOf renames .nat participants operands

/-- The values that a region of a `repeat` yields, renamed: the renamed collected values,
then the renamed carried ones. -/
theorem split_retype_remap (carried : List Located) :
    ∀ (collected : List Located)
      (same : (collected ++ carried).map (Located.rename roleMap) =
        collected.map (Located.rename roleMap) ++ carried.map (Located.rename roleMap))
      (produced : Values (SideValue model (Side.preimage roleMap side)) (collected ++ carried)),
      ((remapValues (F := SideValue model side) (Located.rename roleMap) (collected ++ carried)
          produced).retype same).split (collected.map (Located.rename roleMap)) =
        (remapValues (F := SideValue model side) (Located.rename roleMap) collected
            (produced.split collected).1,
          remapValues (F := SideValue model side) (Located.rename roleMap) carried
            (produced.split collected).2)
  | [], _, _ => rfl
  | located :: rest, same, .cons value produced => by
      have tail := split_retype_remap carried rest List.map_append produced
      refine (congrArg (Values.split _)
        (Values.retype_cons same List.map_append value
          (remapValues (F := SideValue model side) (Located.rename roleMap) (rest ++ carried)
            produced))).trans ?_
      exact congr
        (congrArg
          (fun first second =>
            (Values.cons (Value := SideValue model side) (ty := Located.rename roleMap located)
              value first, second))
          (congrArg Prod.fst tail))
        (congrArg Prod.snd tail)

/-- Pushing the renamed collected values onto the renamed sequences. -/
theorem sideCollectedPush_rename {done : Nat} :
    ∀ (collected : List Located)
      (values : Values (SideValue model (Side.preimage roleMap side)) collected)
      (earlier : Values (SideValue model (Side.preimage roleMap side))
        (collectedSequencesAt (some done) collected)),
      sideCollectedPush model side (collected.map (Located.rename roleMap))
          (remapValues (F := SideValue model side) (Located.rename roleMap) collected values)
          (renameSequences model roleMap side (some done) collected earlier) =
        renameSequences model roleMap side (some (done + 1)) collected
          (sideCollectedPush model (Side.preimage roleMap side) collected values earlier)
  | [], _, _ => rfl
  | ⟨_, _⟩ :: rest, .cons _ values, .cons _ earlier =>
      cons_congr rfl (sideCollectedPush_rename rest values earlier)

theorem sideCollectedNone_rename :
    ∀ (collected : List Located),
      sideCollectedNone model side (collected.map (Located.rename roleMap)) =
        renameSequences model roleMap side (some 0) collected
          (sideCollectedNone model (Side.preimage roleMap side) collected)
  | [] => rfl
  | ⟨_, _⟩ :: rest => cons_congr rfl (sideCollectedNone_rename rest)

/-- The results of a finished `repeat` over a count that is a value, renamed. -/
theorem sideCollectedLists_rename {total : Nat} (carried : List Located)
    (state : Values (SideValue model (Side.preimage roleMap side)) carried) :
    ∀ (collected : List Located)
      (values : Values (SideValue model (Side.preimage roleMap side))
        (collectedSequencesAt (some total) collected)),
      (sideCollectedLists model side (collected.map (Located.rename roleMap))
          (renameSequences model roleMap side (some total) collected values)).append
          (remapValues (F := SideValue model side) (Located.rename roleMap) carried state) =
        renameCollected model roleMap side none carried collected
          ((sideCollectedLists model (Side.preimage roleMap side) collected values).append state)
  | [], _ => rfl
  | ⟨_, _⟩ :: rest, .cons _ values =>
      cons_congr rfl (sideCollectedLists_rename carried state rest values)

/-- The results of a finished `repeat` over a count of the operation, renamed. -/
theorem sideCollectedSized_rename {total count : Nat} (same : total = count)
    (carried : List Located)
    (state : Values (SideValue model (Side.preimage roleMap side)) carried) :
    ∀ (collected : List Located)
      (values : Values (SideValue model (Side.preimage roleMap side))
        (collectedSequencesAt (some total) collected)),
      (sideCollectedSized model side same (collected.map (Located.rename roleMap))
          (renameSequences model roleMap side (some total) collected values)).append
          (remapValues (F := SideValue model side) (Located.rename roleMap) carried state) =
        renameCollected model roleMap side (some count) carried collected
          ((sideCollectedSized model (Side.preimage roleMap side) same collected values).append
            state)
  | [], _ => rfl
  | ⟨_, _⟩ :: rest, .cons _ values =>
      cons_congr rfl (sideCollectedSized_rename same carried state rest values)

/-- The results of a `repeat` for a side without a participant, renamed. -/
theorem absentSequences_rename (size : Option Nat) (carried : List Located)
    (state : Values (SideValue model (Side.preimage roleMap side)) carried) :
    ∀ (collected : List Located)
      (renamed : ∀ located ∈ collected.map (Located.rename roleMap), side located.holder = false)
      (original : ∀ located ∈ collected, Side.preimage roleMap side located.holder = false),
      (absentSequences model side size (collected.map (Located.rename roleMap)) renamed).append
          (remapValues (F := SideValue model side) (Located.rename roleMap) carried state) =
        renameCollected model roleMap side size carried collected
          ((absentSequences model (Side.preimage roleMap side) size collected original).append
            state)
  | [], _, _ => rfl
  | _ :: rest, _, _ => cons_congr rfl (absentSequences_rename size carried state rest _ _)

/-- The loop of a `repeat` under a role map: when the renamed region on the renamed state
is the region, renamed, the renamed loop is the loop, renamed. -/
theorem repeatProcess_rename (count : RepeatCount) (carried collected : List Located)
    (step : Nat → Values (SideValue model (Side.preimage roleMap side)) carried →
      PIR.Process (Effects model)
        (Values (SideValue model (Side.preimage roleMap side)) (collected ++ carried)))
    (renamed : Nat → Values (SideValue model side) (carried.map (Located.rename roleMap)) →
      PIR.Process (Effects model)
        (Values (SideValue model side)
          (collected.map (Located.rename roleMap) ++ carried.map (Located.rename roleMap))))
    (related : ∀ iteration state,
      renamed iteration
          (remapValues (F := SideValue model side) (Located.rename roleMap) carried state) =
        (step iteration state).bind fun produced =>
          .done ((remapValues (F := SideValue model side) (Located.rename roleMap)
            (collected ++ carried) produced).retype List.map_append))
    (agreed : Nat) (initial : Values (SideValue model (Side.preimage roleMap side)) carried) :
    repeatProcess model side count (carried.map (Located.rename roleMap))
        (collected.map (Located.rename roleMap)) renamed agreed
        (remapValues (F := SideValue model side) (Located.rename roleMap) carried initial) =
      (repeatProcess model (Side.preimage roleMap side) count carried collected step agreed
          initial).bind fun final =>
        .done (renameCollected model roleMap side count.size carried collected final) := by
  have iterated : ∀ number : Nat,
      repeatIterations model side (carried.map (Located.rename roleMap))
          (collected.map (Located.rename roleMap)) renamed number 0
          (remapValues (F := SideValue model side) (Located.rename roleMap) carried initial)
          (sideCollectedNone model side (collected.map (Located.rename roleMap))) =
        (repeatIterations model (Side.preimage roleMap side) carried collected step number 0
            initial (sideCollectedNone model (Side.preimage roleMap side) collected)).bind
          fun final =>
            .done (remapValues (F := SideValue model side) (Located.rename roleMap) carried final.1,
              renameSequences model roleMap side _ collected final.2) := fun number => by
    rw [sideCollectedNone_rename]
    exact iterations_restrict
      (remapValues (F := SideValue model side) (Located.rename roleMap) carried)
      (fun done => renameSequences model roleMap side (some done) collected)
      (fun produced => (remapValues (F := SideValue model side) (Located.rename roleMap)
        (collected ++ carried) produced).retype List.map_append)
      related
      (fun produced => congrArg Prod.snd (split_retype_remap carried collected _ produced))
      (fun done produced earlier => by
        rw [congrArg Prod.fst (split_retype_remap carried collected _ produced)]
        exact sideCollectedPush_rename collected _ earlier)
      number 0 initial _
  cases count with
  | static number =>
      show PIR.Process.bind _ _ = PIR.Process.bind (PIR.Process.bind _ _) _
      rw [iterated number, PIR.Process.bind_assoc, PIR.Process.bind_assoc]
      refine congrArg (PIR.Process.bind _) (funext fun final => ?_)
      exact congrArg PIR.Process.done
        (sideCollectedSized_rename (iterationsAfter_eq number 0) carried final.1 collected final.2)
  | runtime maximum =>
      show (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined) =
        PIR.Process.bind (if agreed ≤ maximum then PIR.Process.bind _ _ else .halt .undefined) _
      split
      · rw [iterated agreed, PIR.Process.bind_assoc, PIR.Process.bind_assoc]
        refine congrArg (PIR.Process.bind _) (funext fun final => ?_)
        exact congrArg PIR.Process.done
          (sideCollectedLists_rename carried final.1 collected final.2)
      · rfl

end Values

/-! ## Processes under a role map -/

section Processes

variable {X α β : Type} (same : X → X → Bool) (side : Side) (onValue : X → α) (onDisagree : α)

theorem agreeWith_map (transform : α → β) (value : X) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles),
      transform (agreeWith same side onValue onDisagree value roles values) =
        agreeWith same side (fun agreed => transform (onValue agreed)) (transform onDisagree) value
          roles values
  | [], _ => rfl
  | role :: rest, values => by
      cases present : side role with
      | true =>
          rw [agreeWith_present present, agreeWith_present present]
          cases same value (Held.value (side role) present (values.get .here)) with
          | true => exact agreeWith_map transform value rest values.tail
          | false => rfl
      | false =>
          rw [agreeWith_absent present, agreeWith_absent present]
          exact agreeWith_map transform value rest values.tail

/-- A function of the agreed outcome is the agreement on the function's outcomes. -/
theorem agreed_map (transform : α → β) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles)
      (onNone : roles.any side = false → α),
      transform (agreed same side onValue onDisagree roles values onNone) =
        agreed same side (fun agreed => transform (onValue agreed)) (transform onDisagree) roles
          values fun none => transform (onNone none)
  | [], _, _ => rfl
  | role :: rest, values, onNone => by
      cases present : side role with
      | true =>
          rw [agreed_present present, agreed_present present]
          exact agreeWith_map same side onValue onDisagree transform _ rest values.tail
      | false =>
          rw [agreed_absent present, agreed_absent present]
          exact agreed_map transform rest values.tail _

/-- Two agreements with equal outcomes are equal. -/
theorem agreed_congr {onValue other : X → α} {onDisagree otherDisagree : α} {roles : List Nat}
    {values : Values (fun role => Held X (side role)) roles}
    {onNone otherNone : roles.any side = false → α} (sameValue : ∀ value, onValue value = other value)
    (sameDisagree : onDisagree = otherDisagree) (sameNone : ∀ none, onNone none = otherNone none) :
    agreed same side onValue onDisagree roles values onNone =
      agreed same side other otherDisagree roles values otherNone := by
  rw [show onValue = other from funext sameValue, sameDisagree,
    show onNone = otherNone from funext sameNone]

end Processes

/-- A process after an agreement is the agreement on the continued outcomes. -/
theorem agreed_bind {I : PIR.Signature} {X A B : Type} (same : X → X → Bool) (side : Side)
    (onValue : X → PIR.Process I A) (onDisagree : PIR.Process I A) (roles : List Nat)
    (values : Values (fun role => Held X (side role)) roles)
    (onNone : roles.any side = false → PIR.Process I A) (next : A → PIR.Process I B) :
    (agreed same side onValue onDisagree roles values onNone).bind next =
      agreed same side (fun value => (onValue value).bind next) (onDisagree.bind next) roles values
        fun none => (onNone none).bind next :=
  agreed_map same side onValue onDisagree (fun process => process.bind next) roles values onNone

section Renamed

variable {model : Model} (roleMap : RoleMap) (side : Side)

theorem agreeWith_preimage {X α : Type} (same : X → X → Bool) (onValue : X → α) (onDisagree : α)
    (value : X) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side (roleMap.apply role))) roles),
      agreeWith same side onValue onDisagree value (roles.map roleMap.apply)
          (renameControls roleMap side roles values) =
        agreeWith same (Side.preimage roleMap side) onValue onDisagree value roles values
  | [], .nil => rfl
  | role :: rest, .cons head values => by
      cases present : side (roleMap.apply role) with
      | true =>
          have renamed := agreeWith_present (same := same) (side := side) (onValue := onValue)
            (onDisagree := onDisagree) (rest := rest.map roleMap.apply) present (value := value)
            (values := renameControls roleMap side (role :: rest) (.cons head values))
          have original := agreeWith_present (same := same) (side := Side.preimage roleMap side)
            (onValue := onValue) (onDisagree := onDisagree) (role := role) (rest := rest) present
            (value := value) (values := .cons head values)
          refine renamed.trans (Eq.trans ?_ original.symm)
          exact congrArg (fun rest => cond (same value (Held.value _ present head)) rest onDisagree)
            (agreeWith_preimage same onValue onDisagree value rest values)
      | false =>
          have renamed := agreeWith_absent (same := same) (side := side) (onValue := onValue)
            (onDisagree := onDisagree) (rest := rest.map roleMap.apply) present (value := value)
            (values := renameControls roleMap side (role :: rest) (.cons head values))
          have original := agreeWith_absent (same := same) (side := Side.preimage roleMap side)
            (onValue := onValue) (onDisagree := onDisagree) (role := role) (rest := rest) present
            (value := value) (values := .cons head values)
          exact renamed.trans ((agreeWith_preimage same onValue onDisagree value rest values).trans
            original.symm)

/-- The agreement of the caller's roles that run the participants is the agreement of
the participants for the callee's side. -/
theorem agreed_preimage {X α : Type} (same : X → X → Bool) (onValue : X → α) (onDisagree : α) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side (roleMap.apply role))) roles)
      (renamedNone : (roles.map roleMap.apply).any side = false → α)
      (onNone : roles.any (Side.preimage roleMap side) = false → α),
      (∀ renamed original, renamedNone renamed = onNone original) →
      agreed same side onValue onDisagree (roles.map roleMap.apply)
          (renameControls roleMap side roles values) renamedNone =
        agreed same (Side.preimage roleMap side) onValue onDisagree roles values onNone
  | [], .nil, _, _, sameNone => sameNone _ _
  | role :: rest, .cons head values, renamedNone, onNone, sameNone => by
      cases present : side (roleMap.apply role) with
      | true =>
          have renamed := agreed_present (same := same) (side := side) (onValue := onValue)
            (onDisagree := onDisagree) (rest := rest.map roleMap.apply) present
            (values := renameControls roleMap side (role :: rest) (.cons head values))
            (onNone := renamedNone)
          have original := agreed_present (same := same) (side := Side.preimage roleMap side)
            (onValue := onValue) (onDisagree := onDisagree) (role := role) (rest := rest) present
            (values := .cons head values) (onNone := onNone)
          exact renamed.trans ((agreeWith_preimage roleMap side same onValue onDisagree _ rest
            values).trans original.symm)
      | false =>
          have renamed := agreed_absent (same := same) (side := side) (onValue := onValue)
            (onDisagree := onDisagree) (rest := rest.map roleMap.apply) present
            (values := renameControls roleMap side (role :: rest) (.cons head values))
            (onNone := renamedNone)
          have original := agreed_absent (same := same) (side := Side.preimage roleMap side)
            (onValue := onValue) (onDisagree := onDisagree) (role := role) (rest := rest) present
            (values := .cons head values) (onNone := onNone)
          exact renamed.trans ((agreed_preimage same onValue onDisagree rest values _ _
            fun _ _ => sameNone _ _).trans original.symm)

/-- The announcements to the caller's roles that run the receivers are the
announcements to the receivers for the callee's side. -/
theorem receiverReplies_rename (model : Model) (site : Site) (type : Ty) :
    ∀ (roles : List Nat),
      receiverReplies model side site type (roles.map roleMap.apply) =
        (receiverReplies model (Side.preimage roleMap side) site type roles).bind fun replies =>
          .done (renameCopies model roleMap side type roles replies)
  | [] => rfl
  | role :: rest => by
      show (receiveStep model site type (side (roleMap.apply role))).bind _ =
        ((receiveStep model site type (side (roleMap.apply role))).bind _).bind _
      rw [receiverReplies_rename model site type rest, PIR.Process.bind_assoc]
      congr 1
      funext reply
      rw [PIR.Process.bind_assoc, PIR.Process.bind_assoc]
      rfl

theorem heldCopies_rename (model : Model) (type : Ty) (reply : model.Value type) :
    ∀ (roles : List Nat),
      heldCopies model side type reply (roles.map roleMap.apply) =
        renameCopies model roleMap side type roles
          (heldCopies model (Side.preimage roleMap side) type reply roles)
  | [] => rfl
  | _ :: rest => cons_congr rfl (heldCopies_rename model type reply rest)

theorem absentOutputs_rename (model : Model) :
    ∀ (outputs : List Located)
      (renamed : ∀ located ∈ outputs.map (Located.rename roleMap), side located.holder = false)
      (original : ∀ located ∈ outputs, Side.preimage roleMap side located.holder = false),
      absentOutputs model side (outputs.map (Located.rename roleMap)) renamed =
        remapValues (F := SideValue model side) (Located.rename roleMap) outputs
          (absentOutputs model (Side.preimage roleMap side) outputs original)
  | [], _, _ => rfl
  | _ :: rest, _, _ => cons_congr rfl (absentOutputs_rename model rest _ _)

end Renamed

theorem drawStep_bind (model : Model) {α β : Type} (site : Site) (law : SamplingRow)
    (onDraw : model.Value law.output → PIR.Process (Effects model) α)
    (next : α → PIR.Process (Effects model) β) :
    ∀ (owner : Bool) (inputs : Values (fun type => Held (model.Value type) owner) law.inputs)
      (onOutside : owner = false → PIR.Process (Effects model) α),
      (drawStep model site law onDraw owner inputs onOutside).bind next =
        drawStep model site law (fun reply => (onDraw reply).bind next) owner inputs
          fun absent => (onOutside absent).bind next
  | true, _, _ => rfl
  | false, _, _ => rfl

theorem drawStep_congr (model : Model) {α : Type} (site : Site) (law : SamplingRow)
    {onDraw other : model.Value law.output → PIR.Process (Effects model) α} (owner : Bool)
    (inputs : Values (fun type => Held (model.Value type) owner) law.inputs)
    {onOutside otherOutside : owner = false → PIR.Process (Effects model) α}
    (sameDraw : ∀ reply, onDraw reply = other reply)
    (sameOutside : ∀ absent, onOutside absent = otherOutside absent) :
    drawStep model site law onDraw owner inputs onOutside =
      drawStep model site law other owner inputs otherOutside := by
  rw [show onDraw = other from funext sameDraw,
    show onOutside = otherOutside from funext sameOutside]

/-! ## Instantiation -/

/-- The renamed regions and the original regions agree along the maps of their inputs:
each renamed region, on the caller's view of the inputs, is the original with the caller's
view of the results. -/
def RegionsRenamed (model : Model) (roleMap : RoleMap) (side : Side) :
    {signatures targets : List (List Located × List Located)} →
      RegionRenamings roleMap signatures targets →
      Values (RegionFunction (SideValue model (Side.preimage roleMap side)) (Effects model)) signatures →
      Values (RegionFunction (SideValue model side) (Effects model)) targets → Prop
  | _, _, .nil, _, _ => True
  | _, _, .cons (inputs := inputs) (outputs := outputs) (renamed := images) map tail, original,
      renamed =>
      (∀ (values : Values (SideValue model (Side.preimage roleMap side)) inputs)
          (seen : Values (SideValue model side) images),
        Renames (model := model) (side := side) map (Environment.ofValues values)
            (Environment.ofValues seen) →
          (renamed.get .here) seen =
            ((original.get .here) values).bind fun results =>
              .done (remapValues (F := SideValue model side) (Located.rename roleMap) outputs results)) ∧
        RegionsRenamed model roleMap side tail original.tail renamed.tail

section Chosen

variable {model : Model}

/-- The arm that a number selects: the renamed arm is the original arm, seen by the
caller. -/
theorem selectArm_renamed (roleMap : RoleMap) (side : Side) {captures outputs : List Located} :
    ∀ (count : Nat)
      (original : Values (RegionFunction (SideValue model (Side.preimage roleMap side)) (Effects model))
        (List.replicate count (captures, outputs)))
      (renamed : Values (RegionFunction (SideValue model side) (Effects model))
        (List.replicate count
          (captures.map (Located.rename roleMap), outputs.map (Located.rename roleMap)))),
      RegionsRenamed model roleMap side (armRenamings roleMap captures outputs count) original
        renamed →
      ∀ (number : Fin count)
        (values : Values (SideValue model (Side.preimage roleMap side)) captures),
        selectArm (captures.map (Located.rename roleMap), outputs.map (Located.rename roleMap)) count
            renamed number
            (remapValues (F := SideValue model side) (Located.rename roleMap) captures values) =
          (selectArm (captures, outputs) count original number values).bind fun results =>
            .done (remapValues (F := SideValue model side) (Located.rename roleMap) outputs results)
  | 0, _, _, _, number, _ => number.elim0
  | _ + 1, _, _, agree, ⟨0, _⟩, values =>
      agree.1 values _ (Renames.keepAll captures (Renames.start 0 rfl Environment.empty) values)
  | count + 1, original, renamed, agree, ⟨number + 1, below⟩, values =>
      selectArm_renamed roleMap side count original.tail renamed.tail agree.2
        ⟨number, Nat.lt_of_succ_lt_succ below⟩ values

/-- The payloads of the first alternative that the caller's roles hold are those that the
callee's roles hold. -/
theorem firstPayloads_rename (roleMap : RoleMap) (side : Side) (payload : Ty) (rest : List Ty) :
    ∀ (roles : List Nat)
      (copies : Values
        (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side (roleMap.apply role)))
        roles),
      firstPayloads model side payload rest (roles.map roleMap.apply)
          (renameControls roleMap side roles copies) =
        (firstPayloads model (Side.preimage roleMap side) payload rest roles copies).map
          (renameControls roleMap side roles)
  | [], .nil => rfl
  | role :: roles, .cons copy copies => by
      show consFound (firstPayload (side (roleMap.apply role)) copy)
          (firstPayloads model side payload rest (roles.map roleMap.apply)
            (renameControls roleMap side roles copies)) =
        (consFound (firstPayload (side (roleMap.apply role)) copy)
          (firstPayloads model (Side.preimage roleMap side) payload rest roles copies)).map _
      rw [firstPayloads_rename roleMap side payload rest roles copies]
      cases firstPayload (side (roleMap.apply role)) copy <;>
        cases firstPayloads model (Side.preimage roleMap side) payload rest roles copies <;> rfl

/-- The copies of the variant of the later alternatives that the caller's roles hold are
those that the callee's roles hold. -/
theorem laterCopies_rename (roleMap : RoleMap) (side : Side) (payload : Ty) (rest : List Ty) :
    ∀ (roles : List Nat)
      (copies : Values
        (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side (roleMap.apply role)))
        roles),
      laterCopies model side payload rest (roles.map roleMap.apply)
          (renameControls roleMap side roles copies) =
        (laterCopies model (Side.preimage roleMap side) payload rest roles copies).map
          (renameControls roleMap side roles)
  | [], .nil => rfl
  | role :: roles, .cons copy copies => by
      show consFound (laterCopy (side (roleMap.apply role)) copy)
          (laterCopies model side payload rest (roles.map roleMap.apply)
            (renameControls roleMap side roles copies)) =
        (consFound (laterCopy (side (roleMap.apply role)) copy)
          (laterCopies model (Side.preimage roleMap side) payload rest roles copies)).map _
      rw [laterCopies_rename roleMap side payload rest roles copies]
      cases laterCopy (side (roleMap.apply role)) copy <;>
        cases laterCopies model (Side.preimage roleMap side) payload rest roles copies <;> rfl

/-- Values of one type, one per role, indexed by the caller's roles: as located values
they are the caller's copies. -/
theorem remapValues_renameControls (roleMap : RoleMap) (side : Side) (type : Ty) :
    ∀ (roles : List Nat)
      (values : Values (fun role => Held (model.Value type) (side (roleMap.apply role))) roles),
      remapValues (F := SideValue model side) (fun role => ⟨type, role⟩)
          (roles.map roleMap.apply) (renameControls roleMap side roles values) =
        renameCopies model roleMap side type roles
          (remapValues (F := SideValue model (Side.preimage roleMap side))
            (fun role => ⟨type, role⟩) roles values)
  | [], .nil => rfl
  | _ :: rest, .cons _ values =>
      cons_congr rfl (remapValues_renameControls roleMap side type rest values)

/-- The region of an alternative with a number: the renamed region, on the payloads of
the caller's roles, is the original, on the payloads of the callee's roles, seen by the
caller. -/
theorem alternativeProcess_renamed (roleMap : RoleMap) (side : Side) {participants : List Nat}
    {captures outputs : List Located} :
    ∀ (alternatives : List Ty)
      (original : Values (RegionFunction (SideValue model (Side.preimage roleMap side)) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (renamed : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload (participants.map roleMap.apply) ++
            captures.map (Located.rename roleMap), outputs.map (Located.rename roleMap)))),
      RegionsRenamed model roleMap side
        (alternativeRenamings roleMap participants captures outputs alternatives) original
        renamed →
      ∀ (number : Nat)
        (copies : Values
          (fun role => Held (Ty.Variant model.Carrier alternatives) (side (roleMap.apply role)))
          participants)
        (values : Values (SideValue model (Side.preimage roleMap side)) captures),
        alternativeProcess model side (participants.map roleMap.apply)
            (captures.map (Located.rename roleMap)) (outputs.map (Located.rename roleMap))
            alternatives renamed number (renameControls roleMap side participants copies)
            (remapValues (F := SideValue model side) (Located.rename roleMap) captures values) =
          (alternativeProcess model (Side.preimage roleMap side) participants captures outputs
            alternatives original number copies values).bind fun results =>
            .done (remapValues (F := SideValue model side) (Located.rename roleMap) outputs results)
  | [], _, _, _, _, _, _ => rfl
  | payload :: rest, original, renamed, agree, 0, copies, values => by
      have renamedFound := firstPayloads_rename (model := model) roleMap side payload rest
        participants copies
      cases found : firstPayloads model (Side.preimage roleMap side) payload rest participants
          copies with
      | none =>
          rw [found] at renamedFound
          rw [alternativeProcess_first_other renamedFound, alternativeProcess_first_other found]
          rfl
      | some payloads =>
          rw [found] at renamedFound
          rw [alternativeProcess_first renamedFound, alternativeProcess_first found,
            remapValues_renameControls]
          exact agree.1 _ _
            (Renames.keepRolesAppend payload [] captures .nil values participants
              (Renames.start 0 rfl Environment.empty) _)
  | payload :: rest, original, renamed, agree, number + 1, copies, values => by
      have renamedFound := laterCopies_rename (model := model) roleMap side payload rest
        participants copies
      cases found : laterCopies model (Side.preimage roleMap side) payload rest participants
          copies with
      | none =>
          rw [found] at renamedFound
          rw [alternativeProcess_later_other number renamedFound,
            alternativeProcess_later_other number found]
          rfl
      | some later =>
          rw [found] at renamedFound
          rw [alternativeProcess_later number renamedFound, alternativeProcess_later number found]
          exact alternativeProcess_renamed roleMap side rest original.tail renamed.tail agree.2
            number later values

/-- The region that an agreed tag selects: the renamed region is the original region, seen
by the caller. -/
theorem chosenRegion_renamed (roleMap : RoleMap) (side : Side) {participants : List Nat}
    {captures outputs : List Located} :
    ∀ (tag : ChoiceTag)
      (original : Values (RegionFunction (SideValue model (Side.preimage roleMap side)) (Effects model))
        (tag.regions participants captures outputs))
      (renamed : Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions (participants.map roleMap.apply) (captures.map (Located.rename roleMap))
          (outputs.map (Located.rename roleMap)))),
      RegionsRenamed model roleMap side (choiceRenamings roleMap participants captures outputs tag)
        original renamed →
      ∀ (copies : Values
          (fun role => Held (model.Value tag.type) (side (roleMap.apply role))) participants)
        (values : Values (SideValue model (Side.preimage roleMap side)) captures)
        (value : model.Value tag.type),
        chosenRegion model side (participants.map roleMap.apply)
            (captures.map (Located.rename roleMap)) (outputs.map (Located.rename roleMap)) tag
            renamed (renameControls roleMap side participants copies)
            (remapValues (F := SideValue model side) (Located.rename roleMap) captures values)
            value =
          (chosenRegion model (Side.preimage roleMap side) participants captures outputs tag
            original copies values value).bind fun results =>
            .done (remapValues (F := SideValue model side) (Located.rename roleMap) outputs results)
  | .condition, original, renamed, agree, _, values, _ =>
      selectArm_renamed roleMap side 2 original renamed agree _ values
  | .arm count, original, renamed, agree, _, values, _ =>
      selectArm_renamed roleMap side count original renamed agree _ values
  | .alternative _ alternatives, original, renamed, agree, copies, values, _ =>
      alternativeProcess_renamed roleMap side alternatives original renamed agree _ copies values

end Chosen

section Instantiate

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} {functionTable : FunctionTable model functions}

mutual
  /-- The instantiated region is the original region for the callee's side, with the
  labelling moved by the base and the results seen by the caller. -/
  theorem instantiateRegion_meaning (roleMap : RoleMap) (base : Nat) (label : Nat → Site)
      (side : Side) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions [] deployed) Γ out)
        {Δ : List Located} (map : RoleRenaming roleMap Γ Δ)
        (env : Environment (SideValue model (Side.preimage roleMap side)) Γ)
        (image : Environment (SideValue model side) Δ), Renames map env image →
        (instantiateRegion roleMap base region map).denote
            (labelledMeaning model label functionTable .nil side) image =
          (region.denote
              (labelledMeaning model (fun site => label (base + site)) functionTable .nil
                (Side.preimage roleMap side)) env).bind
            fun values =>
              .done (remapValues (F := SideValue model side) (Located.rename roleMap) out values)
    | .ret values, _, map, env, image, renames => by
        show PIR.Process.done (Operands.eval image (map.operands values)) = PIR.Process.done _
        rw [eval_operands renames]
    | .stop reason, _, _, _, _, _ => rfl
    | .bind (mid := mid) body rest, _, map, env, image, renames => by
        show ((instantiateRegion roleMap base body map).denote
              (labelledMeaning model label functionTable .nil side) image).bind _ =
          ((body.denote
              (labelledMeaning model (fun site => label (base + site)) functionTable .nil
                (Side.preimage roleMap side)) env).bind _).bind _
        rw [instantiateRegion_meaning roleMap base label side body map env image renames,
          PIR.Process.bind_assoc, PIR.Process.bind_assoc]
        congr 1
        funext values
        exact instantiateRegion_meaning roleMap base label side rest _ _ _
          (Renames.keepAll mid renames values)
    | .letOp (.at role op bodies) arguments nested rest, _, map, env, image, renames => by
        cases nested
        show ((performStep model _ (side (roleMap.apply role))
              (unmapValues _ _ (Operands.eval image (map.operandsAt role op.arguments arguments)))).bind
            _).bind _ =
          (((performStep model _ (side (roleMap.apply role))
              (unmapValues _ _ (Operands.eval env arguments))).bind _).bind _).bind _
        rw [eval_operandsAt renames role op.arguments arguments]
        simp only [PIR.Process.bind_assoc]
        congr 1
        funext held
        exact instantiateRegion_meaning roleMap base label side rest _ _ _
          (Renames.keepAt role op.results renames held)
    | .letOp (.exchange sender receiver site type) arguments nested rest, _, map, env, image,
        renames => by
        cases nested
        show ((exchangeStep model (label (base + site)) type (side (roleMap.apply sender))
              (side (roleMap.apply receiver))
              ((Operands.eval image (map.operands arguments)).get .here)).bind _).bind _ =
          (((exchangeStep model (label (base + site)) type (side (roleMap.apply sender))
              (side (roleMap.apply receiver)) ((Operands.eval env arguments).get .here)).bind _).bind
            _).bind _
        rw [eval_operands renames arguments]
        simp only [PIR.Process.bind_assoc]
        refine congrArg (PIR.Process.bind _) (funext fun result => ?_)
        exact instantiateRegion_meaning roleMap base label side rest _ _ _
          (renames.keepOne ⟨type, receiver⟩ result)
    | .letOp (.sample owner site (inputs := inputs) (output := output) law populated) arguments nested rest, _,
        map, env, image, renames => by
        cases nested
        show ((sampleStep model (label (base + site)) (.of law populated) (side (roleMap.apply owner))
              (unmapValues _ _ (Operands.eval image (map.operandsAt owner inputs arguments)))).bind
            _).bind _ =
          (((sampleStep model (label (base + site)) (.of law populated) (side (roleMap.apply owner))
              (unmapValues _ _ (Operands.eval env arguments))).bind _).bind _).bind _
        rw [eval_operandsAt renames owner inputs arguments]
        simp only [PIR.Process.bind_assoc]
        refine congrArg (PIR.Process.bind _) (funext fun reply => ?_)
        exact instantiateRegion_meaning roleMap base label side rest _ _ _
          (renames.keepOne ⟨output, owner⟩ reply)
    | .letOp (.draw owner receivers site (inputs := inputs) (output := output) law populated) arguments nested
        rest, _, map, env, image, renames => by
        cases nested
        show (drawStep model (label (base + site)) (.of law populated)
              (fun reply => .done (broadcast model side (roleMap.apply owner)
                (receivers.map roleMap.apply) output reply))
              (side (roleMap.apply owner))
              (unmapValues _ _ (Operands.eval image (map.operandsAt owner inputs arguments)))
              (fun absent =>
                (receiverReplies model side (label (base + site)) output
                  (receivers.map roleMap.apply)).bind fun replies =>
                    .done (.cons (Held.absent _ absent) replies))).bind _ =
          ((drawStep model (label (base + site)) (.of law populated)
              (fun reply => .done (broadcast model (Side.preimage roleMap side) owner receivers
                output reply))
              (side (roleMap.apply owner)) (unmapValues _ _ (Operands.eval env arguments))
              (fun absent =>
                (receiverReplies model (Side.preimage roleMap side) (label (base + site)) output
                  receivers).bind fun replies =>
                    .done (.cons (Held.absent _ absent) replies))).bind _).bind _
        rw [eval_operandsAt renames owner inputs arguments, drawStep_bind, drawStep_bind,
          drawStep_bind]
        refine drawStep_congr model _ _ _ _ (fun reply => ?_) (fun absent => ?_)
        · have later := Renames.keepRoles output receivers
            (renames.keepOne ⟨output, owner⟩ (Held.of _ reply))
            (heldCopies model (Side.preimage roleMap side) output reply receivers)
          rw [← heldCopies_rename] at later
          exact instantiateRegion_meaning roleMap base label side rest _ _ _ later
        · rw [receiverReplies_rename]
          simp only [PIR.Process.bind_assoc]
          refine congrArg (PIR.Process.bind _) (funext fun replies => ?_)
          exact instantiateRegion_meaning roleMap base label side rest _ _ _
            (Renames.keepRoles output receivers
              (renames.keepOne ⟨output, owner⟩ (Held.absent _ absent)) replies)
    | .letOp (.repeat participants count carried collected captures covered) arguments
        (.cons body .nil) rest, _, map, env, image, renames => by
        obtain ⟨countOperands, stateOperands, rfl⟩ :
            ∃ counts state, arguments = Values.append counts state :=
          ⟨_, _, (Values.append_split (count.operands participants) arguments).symm⟩
        obtain ⟨carriedOperands, captureOperands, rfl⟩ :
            ∃ initial captured, stateOperands = Values.append initial captured :=
          ⟨_, _, (Values.append_split carried stateOperands).symm⟩
        show (Region.letOp (dialect := ProtocolDialect operations functions [] deployed)
            (.repeat (participants.map roleMap.apply) count (carried.map (Located.rename roleMap))
              (collected.map (Located.rename roleMap)) (captures.map (Located.rename roleMap))
              (heldBy_rename roleMap covered)) _
            (.cons ((instantiateRegion roleMap base body
              (RoleRenaming.initialLoop roleMap participants carried captures)).retype
                List.map_append) .nil)
            (instantiateRegion roleMap base rest
              (map.keepCollected count.size collected carried))).denote
              (labelledMeaning model label functionTable .nil side) image = _
        rw [labelled_step labelled_repeat_meaning, labelled_step labelled_repeat_meaning]
        simp only [repeatCounts, repeatInitial, repeatCaptured, repeatOutside, eval_append,
          Values.split_append, eval_operands renames]
        rw [eval_countOperands renames participants count countOperands, agreed_bind, agreed_bind,
          agreed_bind]
        refine (agreed_preimage roleMap side Nat.beq _ _ participants _ _
          (fun none => (PIR.Process.done
            (renameCollected model roleMap side count.size carried collected
              ((absentSequences model (Side.preimage roleMap side) count.size collected
                fun _ member => not_held_of_heldBy covered none member).append
                (Operands.eval env carriedOperands)))).bind fun values =>
            (instantiateRegion roleMap base rest
              (map.keepCollected count.size collected carried)).denote
              (labelledMeaning model label functionTable .nil side)
              (Environment.bindAll image values))
          (fun _ _ => by rw [absentSequences_rename])).trans ?_
        refine agreed_congr Nat.beq _ (fun agreed => ?_) rfl (fun _ => ?_)
        · have related : ∀ (iteration : Nat)
              (state : Values (SideValue model (Side.preimage roleMap side)) carried),
              ((instantiateRegion roleMap base body
                  (RoleRenaming.initialLoop roleMap participants carried captures)).retype
                    List.map_append).denote
                (labelledMeaning model label functionTable .nil side)
                (Environment.ofValues
                  ((heldCopies model side .nat iteration (participants.map roleMap.apply)).append
                    ((remapValues (F := SideValue model side) (Located.rename roleMap) carried
                        state).append
                      (remapValues (F := SideValue model side) (Located.rename roleMap) captures
                        (Operands.eval env captureOperands))))) =
              (body.denote
                  (labelledMeaning model (fun site => label (base + site)) functionTable .nil
                    (Side.preimage roleMap side))
                  (Environment.ofValues
                    ((heldCopies model (Side.preimage roleMap side) .nat iteration
                        participants).append
                      (state.append (Operands.eval env captureOperands))))).bind
                fun produced =>
                  .done ((remapValues (F := SideValue model side) (Located.rename roleMap)
                    (collected ++ carried) produced).retype List.map_append) :=
            fun iteration state => by
              refine (Region.denote_retype _ _ _ _).trans ?_
              rw [heldCopies_rename]
              exact (congrArg (fun process => PIR.Process.bind process _)
                (instantiateRegion_meaning roleMap base label side body _ _ _
                  (Renames.keepRolesAppend .nat carried captures state
                    (Operands.eval env captureOperands) participants
                    (Renames.start 0 rfl Environment.empty) _))).trans
                (PIR.Process.bind_assoc _ _ _)
          refine (congrArg (fun process => PIR.Process.bind process _)
            (repeatProcess_rename count carried collected
              (fun iteration state => body.denote
                (labelledMeaning model (fun site => label (base + site)) functionTable .nil
                  (Side.preimage roleMap side))
                (Environment.ofValues
                  ((heldCopies model (Side.preimage roleMap side) .nat iteration
                      participants).append
                    (state.append (Operands.eval env captureOperands)))))
              (fun iteration values => ((instantiateRegion roleMap base body
                  (RoleRenaming.initialLoop roleMap participants carried captures)).retype
                    List.map_append).denote
                (labelledMeaning model label functionTable .nil side)
                (Environment.ofValues
                  ((heldCopies model side .nat iteration (participants.map roleMap.apply)).append
                    (values.append
                      (remapValues (F := SideValue model side) (Located.rename roleMap) captures
                        (Operands.eval env captureOperands))))))
              related agreed (Operands.eval env carriedOperands))).trans ?_
          rw [PIR.Process.bind_assoc, PIR.Process.bind_assoc]
          refine congrArg (PIR.Process.bind _) (funext fun values => ?_)
          exact instantiateRegion_meaning roleMap base label side rest _ _ _
            (Renames.keepCollected count.size carried collected renames values)
        · exact instantiateRegion_meaning roleMap base label side rest _ _ _
            (Renames.keepCollected count.size carried collected renames _)
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, _, map, env,
        image, renames => by
        obtain ⟨tagOperands, captureOperands, rfl⟩ :
            ∃ tags captured, arguments = Values.append tags captured :=
          ⟨_, _, (Values.append_split (Located.ofRoles tag.type participants) arguments).symm⟩
        show (Region.letOp (dialect := ProtocolDialect operations functions [] deployed)
            (.choose (participants.map roleMap.apply) tag (captures.map (Located.rename roleMap))
              (outputs.map (Located.rename roleMap)) (heldBy_rename roleMap covered)) _
            (instantiateRegions roleMap base bodies
              (choiceRenamings roleMap participants captures outputs tag))
            (instantiateRegion roleMap base rest (map.keepAll outputs))).denote
              (labelledMeaning model label functionTable .nil side) image = _
        rw [labelled_step labelled_choose_meaning, labelled_step labelled_choose_meaning]
        simp only [chooseTags, eval_append, Values.split_append, eval_operands renames]
        rw [eval_operandsOf renames tag.type participants tagOperands, agreed_bind, agreed_bind,
          agreed_bind]
        refine (agreed_preimage roleMap side (tag.same model.Carrier) _ _ participants _ _
          (fun none => (PIR.Process.done
            (remapValues (F := SideValue model side) (Located.rename roleMap) outputs
              (absentOutputs model (Side.preimage roleMap side) outputs fun _ member =>
                not_held_of_heldBy covered none member))).bind fun values =>
            (instantiateRegion roleMap base rest (map.keepAll outputs)).denote
              (labelledMeaning model label functionTable .nil side)
              (Environment.bindAll image values))
          (fun _ _ => by rw [absentOutputs_rename])).trans ?_
        refine agreed_congr (tag.same model.Carrier) _ (fun value => ?_) rfl (fun none => ?_)
        · rw [chosenRegion_renamed roleMap side tag _ _
            (instantiateRegions_meaning roleMap base label side bodies _), PIR.Process.bind_assoc,
            PIR.Process.bind_assoc]
          refine congrArg (PIR.Process.bind _) (funext fun values => ?_)
          exact instantiateRegion_meaning roleMap base label side rest _ _ _
            (Renames.keepAll outputs renames values)
        · exact instantiateRegion_meaning roleMap base label side rest _ _ _
            (Renames.keepAll outputs renames _)
    | .letOp (.apply callee ..) .., _, _, _, _, _ => callee.elimNil

  /-- The instantiated closed regions agree with the original ones, along the maps of their
  inputs. -/
  theorem instantiateRegions_meaning (roleMap : RoleMap) (base : Nat) (label : Nat → Site)
      (side : Side) {signatures targets : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions [] deployed) signatures)
        (renamings : RegionRenamings roleMap signatures targets),
        RegionsRenamed model roleMap side renamings
          (regions.denote
            (labelledMeaning model (fun site => label (base + site)) functionTable .nil
              (Side.preimage roleMap side)))
          ((instantiateRegions roleMap base regions renamings).denote
            (labelledMeaning model label functionTable .nil side))
    | .nil, .nil => trivial
    | .cons body tail, .cons _ renamings =>
        ⟨fun _ _ renames =>
            instantiateRegion_meaning roleMap base label side body _ _ _ renames,
          instantiateRegions_meaning roleMap base label side tail renamings⟩
end

end Instantiate

/-! ## Expansion -/

/-- A labelling reads the sites of a region, numbered from `start`, at the sites they
come from. -/
@[expose] def Labels (label : Nat → Site) (path : List Nat) (start : Nat) (origins : List SiteOrigin) :
    Prop :=
  ∀ (index : Nat) (origin : SiteOrigin), origins[index]? = some origin →
    label (start + index) = origin.siteUnder path

namespace Labels

variable {label : Nat → Site} {path : List Nat} {start : Nat}

theorem head {origin : SiteOrigin} {rest : List SiteOrigin}
    (labels : Labels label path start (origin :: rest)) : label start = origin.siteUnder path :=
  labels 0 origin rfl

theorem tail {origin : SiteOrigin} {rest : List SiteOrigin}
    (labels : Labels label path start (origin :: rest)) : Labels label path (start + 1) rest := by
  intro index other found
  have at_ := labels (index + 1) other found
  rwa [Nat.add_assoc, Nat.add_comm 1 index]

theorem left {first second : List SiteOrigin} (labels : Labels label path start (first ++ second)) :
    Labels label path start first := by
  intro index origin found
  have bound : index < first.length := (List.getElem?_eq_some_iff.mp found).1
  exact labels index origin ((List.getElem?_append_left bound).trans found)

theorem right {first second : List SiteOrigin} (labels : Labels label path start (first ++ second)) :
    Labels label path (start + first.length) second := by
  intro index origin found
  have at_ := labels (first.length + index) origin (by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact found)
  rwa [Nat.add_assoc]

/-- The labelling of a callee's expansion at an application: the labelling of the
caller, moved to the start of the callee's sites. -/
theorem under {application : Point} {origins : List SiteOrigin}
    (labels : Labels label path start (origins.map (SiteOrigin.under application))) :
    Labels (fun site => label (start + site)) (path ++ [application.number]) 0 origins := by
  intro index origin found
  have at_ := labels index (origin.under application) (by rw [List.getElem?_map, found]; rfl)
  rw [Nat.zero_add, ← SiteOrigin.siteUnder_under]
  exact at_

/-- The first site of a region is an operation of the definition itself. -/
theorem own {identity site : Nat} {rest : List SiteOrigin}
    (labels : Labels label path start (⟨[], ⟨identity, site⟩⟩ :: rest)) :
    label start = ⟨path, identity, site⟩ := by
  rw [labels.head]
  simp only [SiteOrigin.siteUnder, List.map_nil, List.append_nil]

end Labels

/-- Sequencing two pairs of equal processes. -/
theorem bind_congr {I : PIR.Signature} {A B : Type} {process other : PIR.Process I A}
    {next otherNext : A → PIR.Process I B} (same : process = other)
    (sameNext : ∀ value, next value = otherNext value) :
    process.bind next = other.bind otherNext := by
  rw [same, show next = otherNext from funext sameNext]

section Expand

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {functionTable : FunctionTable model functions}
  {table : ProtocolTable model protocols} {expansions : ExpandedTable operations functions protocols}

/-- The expansions of the table have the meaning of their protocols: with a labelling
that reads each site of an expansion at the site it comes from, the expansion's process
for a side is the protocol's. -/
structure ExpandedSound (model : Model) (functionTable : FunctionTable model functions)
    (table : ProtocolTable model protocols)
    (expansions : ExpandedTable operations functions protocols) : Prop where
  body : ∀ {header : ProtocolHeader} (callee : Var protocols header)
    (expanded : Expanded operations functions header), expansions.get callee = some expanded →
    ∀ (path : List Nat) (label : Nat → Site), Labels label path 0 expanded.origins →
    ∀ (side : Side) (arguments : Values (SideValue model side) header.inputs),
      expanded.body.denote (labelledMeaning model label functionTable .nil side)
          (Environment.ofValues arguments) =
        (table.get callee) path side arguments

variable {label : Nat → Site} {side : Side} {identity : Nat} {path : List Nat}

theorem labelled_at_same {role : Nat} {op : LocalOp operations functions true}
    {bodies : Regions (LocalDialect operations functions true) op.regions}
    {arguments : Values (SideValue model side) (Located.atRole role op.arguments)} :
    labelledOperation model label functionTable (protocols := []) .nil side (.at role op bodies)
        arguments .nil =
      protocolOperation model functionTable table identity path side (.at role op bodies) arguments .nil := rfl

theorem labelled_exchange_site {sender receiver site new : Nat} {type : Ty}
    (same : label new = ⟨path, identity, site⟩)
    {arguments : Values (SideValue model side) [⟨type, sender⟩]} :
    labelledOperation model label functionTable (operations := operations) (protocols := [])
        (deployed := true) .nil side (.exchange sender receiver new type) arguments .nil =
      protocolOperation model functionTable table identity path side (operations := operations) (deployed := true)
        (.exchange sender receiver site type) arguments .nil := by
  show (exchangeStep model (label new) type _ _ _).bind _ = _
  rw [same]
  rfl

theorem labelled_draw_site {owner site new : Nat} {receivers : List Nat} {inputs : List Ty}
    {output : Ty} {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true}
    (same : label new = ⟨path, identity, site⟩)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)} :
    labelledOperation model label functionTable (protocols := []) (deployed := true) .nil side
        (.draw owner receivers new law populated) arguments .nil =
      protocolOperation model functionTable table identity path side (deployed := true)
        (.draw owner receivers site law populated) arguments .nil := by
  show drawStep model (label new) _ _ _ _ _ = _
  rw [same]
  rfl

theorem labelled_sample_site {owner site new : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {populated : output.populated = true}
    (same : label new = ⟨path, identity, site⟩)
    {arguments : Values (SideValue model side) (Located.atRole owner inputs)} :
    labelledOperation model label functionTable (protocols := []) (deployed := true) .nil side
        (.sample owner new law populated) arguments .nil =
      protocolOperation model functionTable table identity path side (deployed := true)
        (.sample owner site law populated) arguments .nil := by
  show (sampleStep model (label new) _ _ _).bind _ = _
  rw [same]
  rfl

theorem labelled_repeat_same {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    {arguments : Values (SideValue model side)
      (count.operands participants ++ (carried ++ captures))}
    {regions : Values (RegionFunction (SideValue model side) (Effects model))
      [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)]} :
    labelledOperation model label functionTable (operations := operations) (protocols := [])
        (deployed := true) .nil side (.repeat participants count carried collected captures covered) arguments
        regions =
      protocolOperation model functionTable table identity path side (operations := operations) (deployed := true)
        (.repeat participants count carried collected captures covered) arguments regions := rfl

theorem labelled_choose_same {participants : List Nat} {tag : ChoiceTag}
    {captures outputs : List Located} {covered : Located.heldBy participants outputs = true}
    {arguments : Values (SideValue model side) (Located.ofRoles tag.type participants ++ captures)}
    {regions : Values (RegionFunction (SideValue model side) (Effects model))
      (tag.regions participants captures outputs)} :
    labelledOperation model label functionTable (operations := operations) (protocols := [])
        (deployed := true) .nil side (.choose participants tag captures outputs covered) arguments
        regions =
      protocolOperation model functionTable table identity path side (operations := operations) (deployed := true)
        (.choose participants tag captures outputs covered) arguments regions := rfl

mutual
  /-- The expansion of a region, with its sites read at the sites they come from, has the
  meaning of the region for every side. -/
  theorem expandRegion_meaning (sound : ExpandedSound model functionTable table expansions)
      (side : Side) (identity : Nat) (path : List Nat) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols true) Γ out)
        (depth : Depth Γ) (start : Nat) (expansion : Expansion operations functions Γ out),
        expandRegion expansions identity region depth start = .ok expansion →
        ∀ (label : Nat → Site), Labels label path start expansion.origins →
        ∀ (env : Environment (SideValue model side) Γ),
          expansion.region.denote (labelledMeaning model label functionTable .nil side) env =
            region.denote (sideMeaning model functionTable table identity path side) env
    | .ret values, _, _, expansion, expands, _, _, _ => by
        simp only [expandRegion, Except.ok.injEq] at expands
        subst expands
        rfl
    | .stop reason, _, _, expansion, expands, _, _, _ => by
        simp only [expandRegion, Except.ok.injEq] at expands
        subst expands
        rfl
    | .bind (mid := mid) body rest, depth, start, expansion, expands, label, labels, env => by
        unfold expandRegion at expands
        split at expands
        · cases expands
        · rename_i first expandsBody
          split at expands
          · cases expands
          · rename_i second expandsRest
            simp only [Except.ok.injEq] at expands
            subst expands
            exact bind_congr
              (expandRegion_meaning sound side identity path body depth start first expandsBody label labels.left env)
              fun values => expandRegion_meaning sound side identity path rest _ _ second expandsRest label
                labels.right _
    | .letOp (.at role op bodies) arguments nested rest, depth, start, expansion, expands, label,
        labels, env => by
        cases nested
        unfold expandRegion at expands
        split at expands
        · cases expands
        · rename_i later expandsRest
          simp only [Except.ok.injEq] at expands
          subst expands
          exact bind_congr (labelled_at_same (label := label) (table := table) (identity := identity) (path := path))
            fun values => expandRegion_meaning sound side identity path rest _ _ later expandsRest label labels _
    | .letOp (.exchange sender receiver site type) arguments nested rest, depth, start, expansion,
        expands, label, labels, env => by
        cases nested
        unfold expandRegion at expands
        split at expands
        · cases expands
        · rename_i later expandsRest
          simp only [Except.ok.injEq] at expands
          subst expands
          exact bind_congr (labelled_exchange_site (functionTable := functionTable) (table := table) labels.own)
            fun values => expandRegion_meaning sound side identity path rest _ _ later expandsRest label
              labels.tail _
    | .letOp (.draw owner receivers site law populated) arguments nested rest, depth, start, expansion,
        expands, label, labels, env => by
        cases nested
        unfold expandRegion at expands
        split at expands
        · cases expands
        · rename_i later expandsRest
          simp only [Except.ok.injEq] at expands
          subst expands
          exact bind_congr (labelled_draw_site (functionTable := functionTable) (table := table) labels.own)
            fun values => expandRegion_meaning sound side identity path rest _ _ later expandsRest label
              labels.tail _
    | .letOp (.sample owner site law populated) arguments nested rest, depth, start, expansion, expands,
        label, labels, env => by
        cases nested
        unfold expandRegion at expands
        split at expands
        · cases expands
        · rename_i later expandsRest
          simp only [Except.ok.injEq] at expands
          subst expands
          exact bind_congr (labelled_sample_site (functionTable := functionTable) (table := table) labels.own)
            fun values => expandRegion_meaning sound side identity path rest _ _ later expandsRest label
              labels.tail _
    | .letOp (.repeat participants count carried collected captures covered) arguments
        bodies rest, depth, start,
        expansion, expands, label, labels, env => by
        unfold expandRegion at expands
        split at expands
        · cases expands
        · rename_i nested expandsBodies
          split at expands
          · cases expands
          · rename_i later expandsRest
            simp only [Except.ok.injEq] at expands
            subst expands
            refine bind_congr ?_
              fun values => expandRegion_meaning sound side identity path rest _ _ later expandsRest label
                labels.right _
            rw [expandRegions_meaning sound side identity path bodies start nested expandsBodies label labels.left]
            exact labelled_repeat_same (label := label) (functionTable := functionTable) (table := table) (identity := identity) (path := path)
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, depth, start,
        expansion, expands, label, labels, env => by
        unfold expandRegion at expands
        split at expands
        · cases expands
        · rename_i nested expandsBodies
          split at expands
          · cases expands
          · rename_i later expandsRest
            simp only [Except.ok.injEq] at expands
            subst expands
            refine bind_congr ?_
              fun values => expandRegion_meaning sound side identity path rest _ _ later expandsRest label
                labels.right _
            rw [expandRegions_meaning sound side identity path bodies start nested expandsBodies label labels.left]
            exact labelled_choose_same (label := label) (functionTable := functionTable) (table := table) (identity := identity) (path := path)
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest, depth,
        start, expansion, expands, label, labels, env => by
        cases nested
        unfold expandRegion at expands
        split at expands
        · cases expands
        · rename_i expanded found
          split at expands
          · cases expands
          · split at expands
            · cases expands
            · split at expands
              · cases expands
              · rename_i later expandsRest
                simp only [Except.ok.injEq] at expands
                subst expands
                have restLabels : Labels label path (start + expanded.count) later.origins := by
                  have moved := labels.right
                  rwa [List.length_map, ← expanded.counted] at moved
                refine bind_congr ?_
                  fun values => expandRegion_meaning sound side identity path rest _ _ later expandsRest label
                    restLabels _
                refine (instantiateRegion_meaning roleMap start label side expanded.body _ _ env
                  (Renames.bindOperands header.inputs (Renames.start depth.depth depth.counted env)
                    arguments)).trans ?_
                exact congrArg (fun process => PIR.Process.bind process _)
                  (sound.body callee expanded found _ _ labels.left.under (Side.preimage roleMap side)
                    (unmapValues (F := SideValue model side) (Located.rename roleMap) header.inputs
                      (Operands.eval env arguments)))

  /-- The expansions of closed regions have the meanings of the regions. -/
  theorem expandRegions_meaning (sound : ExpandedSound model functionTable table expansions)
      (side : Side) (identity : Nat) (path : List Nat) {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions protocols true) signatures)
        (start : Nat) (expanded : Expansions operations functions signatures),
        expandRegions expansions identity regions start = .ok expanded →
        ∀ (label : Nat → Site), Labels label path start expanded.origins →
          expanded.regions.denote (labelledMeaning model label functionTable .nil side) =
            regions.denote (sideMeaning model functionTable table identity path side)
    | .nil, _, expanded, expands, _, _ => by
        simp only [expandRegions, Except.ok.injEq] at expands
        subst expands
        rfl
    | .cons body tail, start, expanded, expands, label, labels => by
        unfold expandRegions at expands
        split at expands
        · cases expands
        · rename_i first expandsBody
          split at expands
          · cases expands
          · rename_i later expandsTail
            simp only [Except.ok.injEq] at expands
            subst expands
            exact cons_congr
              (funext fun values => expandRegion_meaning sound side identity path body _ start first expandsBody
                label labels.left _)
              (expandRegions_meaning sound side identity path tail _ later expandsTail label labels.right)
end

end Expand

/-! ## Programs -/

section Program

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} (functionTable : FunctionTable model functions)

/-- The expansion of one protocol has the protocol's meaning. -/
theorem expandProtocol_meaning {protocols : List ProtocolHeader}
    {table : ProtocolTable model protocols} {expansions : ExpandedTable operations functions protocols}
    (sound : ExpandedSound model functionTable table expansions) (identity : Nat) :
    ∀ (header : ProtocolHeader) (definition : ProtocolDefinition operations functions protocols header)
      (expanded : Expanded operations functions header),
      expandProtocol expansions identity header definition = .ok (some expanded) →
      ∀ (path : List Nat) (label : Nat → Site), Labels label path 0 expanded.origins →
      ∀ (side : Side) (arguments : Values (SideValue model side) header.inputs),
        expanded.body.denote (labelledMeaning model label functionTable .nil side)
            (Environment.ofValues arguments) =
          definition.meaning model functionTable table identity path side arguments
  | ⟨_, _, _, _, true⟩, _, _, expands, _, _, _, _, _ => by
      simp only [expandProtocol, Except.ok.injEq] at expands
      cases expands
  | ⟨_, inputs, _, _, false⟩, definition, expanded, expands, path, label, labels, side, arguments => by
      simp only [expandProtocol] at expands
      split at expands
      · cases expands
      · rename_i expansion expandsBody
        simp only [Except.ok.injEq, Option.some.injEq] at expands
        subst expands
        exact expandRegion_meaning sound side identity path definition.body _ 0 expansion expandsBody label labels _

/-- The expansions of the protocols of a program have the meanings of the protocols. -/
theorem expandProtocols_sound (identities : Identities) :
    ∀ {protocols : List ProtocolHeader} (program : Protocols typeTable operations functions protocols)
      (expansions : ExpandedTable operations functions protocols),
      expandProtocols identities program = .ok expansions →
        ExpandedSound model functionTable (program.table model functionTable identities) expansions
  | _, .nil, _, _ => ⟨fun callee => callee.elimNil⟩
  | _, .snoc (header := header) earlier definition _, expansions, expands => by
      unfold expandProtocols at expands
      split at expands
      · cases expands
      · rename_i table expandsEarlier
        split at expands
        · cases expands
        · rename_i entry expandsEntry
          simp only [Except.ok.injEq] at expands
          subst expands
          have sound := expandProtocols_sound identities earlier table expandsEarlier
          refine ⟨fun {other} callee => ?_⟩
          cases callee with
          | here =>
              intro expanded found path label labels side arguments
              have same : entry = some expanded := found
              subst same
              exact expandProtocol_meaning functionTable sound _ header definition expanded
                expandsEntry path label labels side arguments
          | there callee => exact sound.body callee

end Program

end Zkc.Core
