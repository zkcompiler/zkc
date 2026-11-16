module

public import Zkc.Core.Facts.Growth

@[expose] public section

/-!
What the walk of the analysis does to its state, for the value side: it only adds places that
differ; it keeps the table well formed and grows it, from every skeleton that it follows whose
leaves are below the next identifier (`walk_grows`); and without a skeleton to follow, the
skeleton that it builds has its leaves below the next identifier, apart from the table, and made
in order from the next identifier on (`walk_built`). The lemmas are in the namespace
`Analysis.ValueSide`, apart from those of the facts side (`Facts/Growth.lean`).
-/

namespace Zkc.Core.Analysis.ValueSide

open FactCheck

section
variable {D : Dialect} {Raw : Type}

/-! ## Places that differ -/

/-- The second state has the places that differ of the first, and perhaps more before them. -/
def AddsPlaces {T : Type} (s s' : State T Raw) : Prop :=
  ∃ new, s'.differs = new ++ s.differs

/-- A state adds no place to itself. -/
theorem AddsPlaces.refl {T : Type} (s : State T Raw) : AddsPlaces s s := ⟨[], rfl⟩

/-- Adding places twice adds places. -/
theorem AddsPlaces.trans {T : Type} {s s' s'' : State T Raw} (first : AddsPlaces s s')
    (second : AddsPlaces s' s'') : AddsPlaces s s'' := by
  obtain ⟨new, e⟩ := first
  obtain ⟨new', e'⟩ := second
  exact ⟨new' ++ new, by rw [e', e, List.append_assoc]⟩

/-- A state with the same places that differ adds none. -/
theorem AddsPlaces.of_differs {T : Type} {s s' : State T Raw} (same : s'.differs = s.differs) :
    AddsPlaces s s' := ⟨[], by rw [same]; rfl⟩

/-- A place that is missed is added, at most. -/
theorem miss_adds {T : Type} (place : Place) (following found : Bool) (s : State T Raw) :
    AddsPlaces s (miss place following found s) := by
  unfold miss
  split
  · exact ⟨[place], rfl⟩
  · exact AddsPlaces.refl s

/-- Missing changes only the places that differ. -/
theorem miss_st {T : Type} (place : Place) (following found : Bool) (s : State T Raw) :
    (miss place following found s).st = s.st := by
  unfold miss
  split <;> rfl

/-- Nothing is missed where the entry is found. -/
theorem miss_found {T : Type} (place : Place) (following : Bool) (s : State T Raw) :
    miss place following true s = s := by
  simp [miss]

/-- Nothing is missed where no skeleton is followed. -/
theorem miss_not_following {T : Type} (place : Place) (found : Bool) (s : State T Raw) :
    miss place false found s = s := by
  simp [miss]

/-- Where a skeleton is followed and the entry is not found, the place is added. -/
theorem miss_missed {T : Type} (place : Place) (s : State T Raw) :
    (miss place true false s).differs = place :: s.differs := by
  simp [miss]

/-- The places that a state added to another are none when the second has none: the first has
none either. -/
theorem AddsPlaces.none_before {T : Type} {s s' : State T Raw} (adds : AddsPlaces s s')
    (none : s'.differs = []) : s.differs = [] := by
  obtain ⟨new, e⟩ := adds
  rw [none] at e
  exact (List.append_eq_nil_iff.mp e.symm).2

/-- Where a skeleton is followed and no place differs at the end, the entry was found. -/
theorem hit_of_no_place {α T : Type} {place : Place} {hit : Option α} {s s' : State T Raw}
    (adds : AddsPlaces (miss place true hit.isSome s) s') (noPlace : s'.differs = []) :
    ∃ a, hit = some a := by
  cases hit with
  | none =>
      have nothing := adds.none_before noPlace
      simp [miss] at nothing
  | some a => exact ⟨a, rfl⟩

/-- Where a skeleton is followed and no place differs at the end, the exit was found. -/
theorem found_of_no_place {T : Type} {place : Place} {found : Bool} {s s' : State T Raw}
    (adds : AddsPlaces (miss place true found s) s') (noPlace : s'.differs = []) :
    found = true := by
  cases found with
  | false =>
      have nothing := adds.none_before noPlace
      simp [miss] at nothing
  | true => rfl

/-! ## Leaves -/

/-- The leaves of an entry: as many identifiers as asked for, below the next identifier of the
state after them, which grew well formed; the places that differ are kept. -/
theorem leaves_grows {T : Type} (lo : Option Nat) (count : Nat) (s : State T Raw)
    (wf : Table.WF s.st.next s.st.table) (below : ∀ l, lo = some l → l + count ≤ s.st.next) :
    Table.WF (leaves lo count s).2.st.next (leaves lo count s).2.st.table ∧
      St.Grows s.st (leaves lo count s).2.st ∧
      (∀ i, i ∈ (leaves lo count s).1 → i < (leaves lo count s).2.st.next) ∧
      (leaves lo count s).1.length = count ∧ (leaves lo count s).2.differs = s.differs := by
  cases lo with
  | some l =>
      have := below l rfl
      refine ⟨wf, St.Grows.refl s.st, fun i m => ?_, by simp [leaves], rfl⟩
      have := mem_range'_bounds m
      simp only [leaves] at this ⊢
      omega
  | none =>
      obtain ⟨wf', grows, made⟩ := fresh_grows count s.st wf
      exact ⟨wf', grows, made, by simp [leaves, fresh], rfl⟩

/-- Leaves add no place that differs. -/
theorem leaves_adds {T : Type} (lo : Option Nat) (count : Nat) (s : State T Raw) :
    AddsPlaces s (leaves lo count s).2 := by
  cases lo <;> exact AddsPlaces.refl _

/-- A state with another table adds no place that differs. -/
theorem AddsPlaces.with_st {T : Type} (s : State T Raw) (st : St T Raw) :
    AddsPlaces s { s with st := st } := AddsPlaces.refl _

/-- The leaves of a followed entry are the entry's. -/
theorem leaves_some {T : Type} (lo count : Nat) (s : State T Raw) :
    leaves (some lo) count s = (List.range' lo count, s) := rfl

/-- Without a followed entry, the leaves are new identifiers. -/
theorem leaves_none {T : Type} (count : Nat) (s : State T Raw) :
    leaves none count s = ((fresh count s.st).1, { s with st := (fresh count s.st).2 }) := rfl

/-! ## What a hit says of the followed skeleton -/

section
variable (checks : SkelRules D)

/-- An exit that is found is the followed skeleton's exit. -/
theorem retEntry_hit {outs : List D.Ty} {exit : List Nat} {followed : Option (Skel D outs)}
    (hit : (followed.map (retEntry exit)).getD false = true) : followed = some (.ret exit) := by
  cases followed with
  | none => simp at hit
  | some skel =>
      cases skel <;> simp [retEntry] at hit
      subst hit
      rfl

/-- An operation kept in order that is found is the followed skeleton's next entry, on the same
key and operands, with an operation that the dialect finds the same. -/
theorem effectEntry_hit {outs ins res : List D.Ty} {key : Key} {o : D.Op ins res}
    {operands : List Nat} {followed : Option (Skel D outs)} {results : Nat}
    {rest : Skel D outs} (hit : effectEntry checks key o operands followed = some (results, rest)) :
    ∃ o' : D.Op ins res, checks.sameOp o o' = true ∧
      followed = some (.effect key o' operands results rest) := by
  cases followed with
  | none => simp [effectEntry] at hit
  | some skel =>
      cases skel
      case effect ins' res' key' o' operands' results' rest' =>
        simp only [effectEntry] at hit
        split at hit
        · next sameIns sameRes _ _ =>
            subst sameIns sameRes
            split at hit
            · next decided =>
                obtain ⟨sameOp, rfl, rfl⟩ := decided
                cases hit
                exact ⟨o', sameOp, rfl⟩
            · cases hit
        · cases hit
      all_goals simp [effectEntry] at hit

/-- A guard that is found is the followed skeleton's next entry, on the same key, performers,
condition and reason. -/
theorem guardEntry_hit {outs : List D.Ty} {t : D.Ty} {key : Key} {w : D.Who} {condition : Nat}
    {why : Reason} {followed : Option (Skel D outs)} {rest : Skel D outs}
    (hit : guardEntry checks (t := t) key w condition why followed = some rest) :
    ∃ ok : D.Condition w t, followed = some (.guard key w condition ok why rest) := by
  cases followed with
  | none => simp [guardEntry] at hit
  | some skel =>
      cases skel
      case guard t' key' w' condition' ok' why' rest' =>
        simp only [guardEntry] at hit
        split at hit
        · next sameWho sameTy _ _ =>
            subst sameWho sameTy
            split at hit
            · next decided =>
                obtain ⟨rfl, rfl, rfl⟩ := decided
                cases hit
                exact ⟨ok', rfl⟩
            · cases hit
        · cases hit
      all_goals simp [guardEntry] at hit

/-- A choice that is found is the followed skeleton's next entry, on the same key, performers and
condition, with the entry's regions, leaves and rest. -/
theorem chooseEntry_hit {outs mid : List D.Ty} {t : D.Ty} {key : Key} {w : D.Who}
    {condition : Nat} {followed : Option (Skel D outs)} {onTrue onFalse : Skel D mid}
    {results : Nat} {rest : Skel D outs}
    (hit : chooseEntry checks (mid := mid) (t := t) key w condition followed =
      some (onTrue, onFalse, results, rest)) :
    ∃ ok : D.Condition w t,
      followed = some (.choose key w condition ok onTrue onFalse results rest) := by
  cases followed with
  | none => simp [chooseEntry] at hit
  | some skel =>
      cases skel
      case choose mid' t' key' w' condition' ok' onTrue' onFalse' results' rest' =>
        simp only [chooseEntry] at hit
        split at hit
        · next sameWho sameTy sameMid _ _ _ =>
            subst sameWho sameTy sameMid
            split at hit
            · next decided =>
                obtain ⟨rfl, rfl⟩ := decided
                simp only [cast_eq, Option.some.injEq, Prod.mk.injEq] at hit
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hit
                exact ⟨ok', rfl⟩
            · cases hit
        · cases hit
      all_goals simp [chooseEntry] at hit

/-- A case analysis that is found is the followed skeleton's next entry, on the same key,
performers and subject, with the entry's arms, leaves and rest. -/
theorem casesEntry_hit {outs mid payloads : List D.Ty} {t : D.Ty} {key : Key} {w : D.Who}
    {subject : Nat} {followed : Option (Skel D outs)} {arms : SkelArms D mid payloads}
    {results : Nat} {rest : Skel D outs}
    (hit : casesEntry checks (mid := mid) (t := t) (payloads := payloads) key w subject followed =
      some (arms, results, rest)) :
    ∃ ok : D.Alternatives w t payloads,
      followed = some (.cases key w subject ok arms results rest) := by
  cases followed with
  | none => simp [casesEntry] at hit
  | some skel =>
      cases skel
      case cases mid' t' payloads' key' w' subject' ok' arms' results' rest' =>
        simp only [casesEntry] at hit
        split at hit
        · next sameWho sameTy sameMid samePayloads _ _ _ _ =>
            subst sameWho sameTy sameMid samePayloads
            split at hit
            · next decided =>
                obtain ⟨rfl, rfl⟩ := decided
                simp only [cast_eq, Option.some.injEq, Prod.mk.injEq] at hit
                obtain ⟨rfl, rfl, rfl⟩ := hit
                exact ⟨ok', rfl⟩
            · cases hit
        · cases hit
      all_goals simp [casesEntry] at hit

/-- A loop that is found is the followed skeleton's next entry, on the same key, performers and
initial values, with a count that the loop's count follows, and the entry's leaves, body and
rest. -/
theorem loopEntry_hit {outs carried each : List D.Ty} {key : Key} {w : D.Who}
    {sameTimes : Count D w → Bool} {initial : List Nat} {followed : Option (Skel D outs)}
    {inputs : Nat} {body : Skel D (carried ++ each)} {results : Nat} {rest : Skel D outs}
    (hit : loopEntry checks (carried := carried) (each := each) key w sameTimes initial followed =
      some (inputs, body, results, rest)) :
    ∃ times : Count D w, sameTimes times = true ∧
      followed = some (.loop key w times initial inputs body results rest) := by
  cases followed with
  | none => simp [loopEntry] at hit
  | some skel =>
      cases skel
      case loop carried' each' key' w' times' initial' inputs' body' results' rest' =>
        simp only [loopEntry] at hit
        split at hit
        · next sameWho sameCarried sameEach _ _ _ =>
            subst sameWho sameCarried sameEach
            split at hit
            · next decided =>
                obtain ⟨rfl, sameCount, rfl⟩ := decided
                simp only [cast_eq, Option.some.injEq, Prod.mk.injEq] at hit sameCount
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hit
                exact ⟨times', sameCount, rfl⟩
            · cases hit
        · cases hit
      all_goals simp [loopEntry] at hit

/-- A block that is found is the followed skeleton's next entry, on the same key and number,
with the entry's body, leaves and rest. -/
theorem blockEntry_hit {outs mid : List D.Ty} {key : Key} {number : Nat}
    {followed : Option (Skel D outs)} {body : Skel D mid} {results : Nat} {rest : Skel D outs}
    (hit : blockEntry checks (mid := mid) key number followed = some (body, results, rest)) :
    followed = some (.block key number body results rest) := by
  cases followed with
  | none => simp [blockEntry] at hit
  | some skel =>
      cases skel
      case block mid' key' number' body' results' rest' =>
        simp only [blockEntry] at hit
        split at hit
        · next sameMid _ =>
            subst sameMid
            split at hit
            · next decided =>
                obtain ⟨rfl, rfl⟩ := decided
                simp only [cast_eq, Option.some.injEq, Prod.mk.injEq] at hit
                obtain ⟨rfl, rfl, rfl⟩ := hit
                rfl
            · cases hit
        · cases hit
      all_goals simp [blockEntry] at hit

/-- An attempt that is found is the followed skeleton's next entry, on the same key and
performers, with the entry's leaves, body and rest. -/
theorem attemptEntry_hit {outs mid : List D.Ty} {key : Key} {w : D.Who}
    {followed : Option (Skel D outs)} {input : Nat} {body : Skel D mid} {results : Nat}
    {rest : Skel D outs}
    (hit : attemptEntry checks (mid := mid) key w followed = some (input, body, results, rest)) :
    followed = some (.attempt key w input body results rest) := by
  cases followed with
  | none => simp [attemptEntry] at hit
  | some skel =>
      cases skel
      case attempt mid' key' w' input' body' results' rest' =>
        simp only [attemptEntry] at hit
        split at hit
        · next sameWho sameMid _ _ =>
            subst sameWho sameMid
            split at hit
            · next decided =>
                subst decided
                simp only [cast_eq, Option.some.injEq, Prod.mk.injEq] at hit
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hit
                rfl
            · cases hit
        · cases hit
      all_goals simp [attemptEntry] at hit

end

/-- The first of the arms that are followed is found when arms are followed, and is their first
arm. -/
theorem armEntry_hit {mid payloads : List D.Ty} {payload : D.Ty}
    {followed : Option (SkelArms D mid (payload :: payloads))} {input : Nat} {arm : Skel D mid}
    {rest : SkelArms D mid payloads} (hit : armEntry followed = some (input, arm, rest)) :
    followed = some (.cons input arm rest) := by
  cases followed with
  | none => simp [armEntry] at hit
  | some arms =>
      cases arms with
      | cons input' arm' rest' =>
          simp only [armEntry, Option.some.injEq, Prod.mk.injEq] at hit
          obtain ⟨rfl, rfl, rfl⟩ := hit
          rfl

/-! ## Without a skeleton to follow -/

section
variable (checks : SkelRules D)

/-- No operation is found where no skeleton is followed. -/
theorem effectEntry_none {outs ins res : List D.Ty} (key : Key) (o : D.Op ins res)
    (operands : List Nat) :
    effectEntry checks key o operands (none : Option (Skel D outs)) = none := rfl

/-- No guard is found where no skeleton is followed. -/
theorem guardEntry_none {outs : List D.Ty} {t : D.Ty} (key : Key) (w : D.Who) (condition : Nat)
    (why : Reason) :
    guardEntry checks (t := t) key w condition why (none : Option (Skel D outs)) = none := rfl

/-- No choice is found where no skeleton is followed. -/
theorem chooseEntry_none {outs mid : List D.Ty} {t : D.Ty} (key : Key) (w : D.Who)
    (condition : Nat) :
    chooseEntry checks (mid := mid) (t := t) key w condition (none : Option (Skel D outs)) =
      none := rfl

/-- No case analysis is found where no skeleton is followed. -/
theorem casesEntry_none {outs mid payloads : List D.Ty} {t : D.Ty} (key : Key) (w : D.Who)
    (subject : Nat) :
    casesEntry checks (mid := mid) (t := t) (payloads := payloads) key w subject
      (none : Option (Skel D outs)) = none := rfl

/-- No loop is found where no skeleton is followed. -/
theorem loopEntry_none {outs carried each : List D.Ty} (key : Key) (w : D.Who)
    (sameTimes : Count D w → Bool) (initial : List Nat) :
    loopEntry checks (carried := carried) (each := each) key w sameTimes initial
      (none : Option (Skel D outs)) = none := rfl

/-- No block is found where no skeleton is followed. -/
theorem blockEntry_none {outs mid : List D.Ty} (key : Key) (number : Nat) :
    blockEntry checks (mid := mid) key number (none : Option (Skel D outs)) = none := rfl

/-- No attempt is found where no skeleton is followed. -/
theorem attemptEntry_none {outs mid : List D.Ty} (key : Key) (w : D.Who) :
    attemptEntry checks (mid := mid) key w (none : Option (Skel D outs)) = none := rfl

end

/-- No arm is found where no arms are followed. -/
theorem armEntry_none {mid payloads : List D.Ty} {payload : D.Ty} :
    armEntry (none : Option (SkelArms D mid (payload :: payloads))) = none := rfl

/-- Without a skeleton to follow, the skeleton of a region is the one built. -/
theorem kept_none {outs : List D.Ty} (built : Skel D outs) : kept none built = built := rfl

/-- With a skeleton to follow, the skeleton of a region is the one followed. -/
theorem kept_some {outs : List D.Ty} (followed built : Skel D outs) :
    kept (some followed) built = followed := rfl

/-! ## The walk adds places that differ -/

section
variable [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D) (definition : Key)
  (role : Option Role)

mutual
  /-- The walk only adds places that differ: those of its state are a suffix of its result's. -/
  theorem walk_adds (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (followed : Option (Skel D outs))
        (ids : Ctx Nat) (k : Known) (s : State D.Ty Raw),
        AddsPlaces s (walk rules checks definition role blocks t followed ids k s).state
    | _, _, .ret _, _, _, _, s => by
        simp only [walk]
        exact miss_adds _ _ _ s
    | _, _, .op _ o _ _ rest, _, _, _, s => by
        cases written : rules.written o with
        | some raw =>
            simp only [walk, written]
            exact (AddsPlaces.with_st s _).trans (walk_adds blocks rest _ _ _ _)
        | none =>
            simp only [walk, written]
            refine AddsPlaces.trans ?_ (walk_adds blocks rest _ _ _ _)
            refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
            exact miss_adds _ _ _ s
    | _, _, .guard _ _ _ _ _ rest, _, _, _, s => by
        simp only [walk]
        refine AddsPlaces.trans ?_ (walk_adds blocks rest _ _ _ _)
        exact miss_adds _ _ _ s
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest, _, _, _, s => by
        simp only [walk]
        refine AddsPlaces.trans ?_ (walk_adds blocks rest _ _ _ _)
        refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
        refine AddsPlaces.trans ?_ (walk_adds blocks onFalse _ _ _ _)
        refine AddsPlaces.trans ?_ (walk_adds blocks onTrue _ _ _ _)
        exact miss_adds _ _ _ s
    | _, _, .cases _ _ _ _ _ arms _ rest, _, _, _, s => by
        simp only [walk]
        refine AddsPlaces.trans ?_ (walk_adds blocks rest _ _ _ _)
        refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
        refine AddsPlaces.trans ?_ (walkArms_adds blocks arms _ _ _ _)
        exact miss_adds _ _ _ s
    | _, _, .loop _ _ _ _ _ _ body _ rest, _, _, _, s => by
        simp only [walk]
        refine AddsPlaces.trans ?_ (walk_adds blocks rest _ _ _ _)
        refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
        refine AddsPlaces.trans ?_ (AddsPlaces.with_st _ _)
        refine AddsPlaces.trans ?_ (walk_adds blocks body _ _ _ _)
        refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
        exact miss_adds _ _ _ s
    | _, _, .block key number body _ rest, _, _, _, s => by
        simp only [walk]
        refine AddsPlaces.trans ?_ (walk_adds blocks rest _ _ _ _)
        refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
        refine AddsPlaces.trans ?_ (walk_adds (blocks ++ [(key, number)]) body _ _ _ _)
        exact miss_adds _ _ _ s
    | _, _, .attempt _ _ _ _ body _ rest, _, _, _, s => by
        simp only [walk]
        refine AddsPlaces.trans ?_ (walk_adds blocks rest _ _ _ _)
        refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
        refine AddsPlaces.trans ?_ (walk_adds blocks body _ _ _ _)
        refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
        exact miss_adds _ _ _ s
  /-- The walk of arms only adds places that differ. -/
  theorem walkArms_adds (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads)
        (followed : Option (SkelArms D mid payloads)) (ids : Ctx Nat) (k : Known)
        (s : State D.Ty Raw),
        AddsPlaces s (walkArms rules checks definition role blocks arms followed ids k s).state
    | _, _, _, .nil, _, _, _, s => by
        simp only [walkArms]
        exact AddsPlaces.refl s
    | _, _, _, .cons _ arm rest, _, _, _, s => by
        simp only [walkArms]
        refine AddsPlaces.trans ?_ (walkArms_adds blocks rest _ _ _ _)
        refine AddsPlaces.trans ?_ (walk_adds blocks arm _ _ _ _)
        exact leaves_adds _ _ _
end

end

/-! ## The walk grows the table well formed -/

/-- An option that is some after a map was some before it. -/
theorem map_eq_some {α β : Type} {f : α → β} {x : Option α} {b : β} (mapped : x.map f = some b) :
    ∃ a, x = some a ∧ f a = b := by
  cases x with
  | none => cases mapped
  | some a => exact ⟨a, rfl, Option.some.inj mapped⟩

/-- The leaves of a skeleton that is followed, when one is, are below a number. -/
def FollowedBelow {outs : List D.Ty} (followed : Option (Skel D outs)) (next : Nat) : Prop :=
  ∀ skel, followed = some skel → skel.Below next

/-- The leaves of arms that are followed, when some are, are below a number. -/
def ArmsFollowedBelow {mid payloads : List D.Ty} (followed : Option (SkelArms D mid payloads))
    (next : Nat) : Prop :=
  ∀ arms, followed = some arms → arms.Below next

/-- A skeleton followed below a number is followed below every larger number. -/
theorem FollowedBelow.mono {outs : List D.Ty} {followed : Option (Skel D outs)} {next next' : Nat}
    (fits : FollowedBelow followed next) (le : next ≤ next') : FollowedBelow followed next' :=
  fun skel found => (fits skel found).mono le

/-- Nothing is followed below every number where nothing is followed. -/
theorem FollowedBelow.none {outs : List D.Ty} {next : Nat} :
    FollowedBelow (none : Option (Skel D outs)) next := fun _ found => nomatch found

/-- No arms are followed below every number where none are followed. -/
theorem ArmsFollowedBelow.none {mid payloads : List D.Ty} {next : Nat} :
    ArmsFollowedBelow (none : Option (SkelArms D mid payloads)) next := fun _ found => nomatch found

/-- A skeleton whose leaves are below a number is followed below it. -/
theorem FollowedBelow.of_some {outs : List D.Ty} {skel : Skel D outs} {next : Nat}
    (below : skel.Below next) : FollowedBelow (some skel) next :=
  fun _ found => Option.some.inj found ▸ below

/-- Arms whose leaves are below a number are followed below it. -/
theorem ArmsFollowedBelow.of_some {mid payloads : List D.Ty} {arms : SkelArms D mid payloads}
    {next : Nat} (below : arms.Below next) : ArmsFollowedBelow (some arms) next :=
  fun _ found => Option.some.inj found ▸ below

/-- A part of a hit whose leaves are below a number is followed below every larger number. -/
theorem FollowedBelow.of_hit {α : Type} {outs : List D.Ty} {hit : Option α}
    {part : α → Skel D outs} {next next' : Nat} (below : ∀ a, hit = some a → (part a).Below next)
    (le : next ≤ next') : FollowedBelow (hit.map part) next' := fun _ mapped => by
  obtain ⟨a, found, rfl⟩ := map_eq_some mapped
  exact (below a found).mono le

/-- Arms of a hit whose leaves are below a number are followed below every larger number. -/
theorem ArmsFollowedBelow.of_hit {α : Type} {mid payloads : List D.Ty} {hit : Option α}
    {part : α → SkelArms D mid payloads} {next next' : Nat}
    (below : ∀ a, hit = some a → (part a).Below next) (le : next ≤ next') :
    ArmsFollowedBelow (hit.map part) next' := fun _ mapped => by
  obtain ⟨a, found, rfl⟩ := map_eq_some mapped
  exact (below a found).mono le

/-- The first leaf of a part of a hit, with as many after it as counted, is below every number
above the one that it is below. -/
theorem leaf_below_of_hit {α : Type} {hit : Option α} {part : α → Nat} {count next next' : Nat}
    (below : ∀ a, hit = some a → part a + count ≤ next) (le : next ≤ next') :
    ∀ l, hit.map part = some l → l + count ≤ next' := fun _ mapped => by
  obtain ⟨a, found, rfl⟩ := map_eq_some mapped
  exact Nat.le_trans (below a found) le

section
variable [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D) (definition : Key)
  (role : Option Role)

/-- A value grows the table well formed: its requirements may enter applications, and its
results are shared, as many as its types and below the next identifier. -/
theorem valueStep_grows (place : Place) (written : Raw) (res : List D.Ty) (argIds : List Nat)
    (k : Known) (st : St D.Ty Raw) (wf : Table.WF st.next st.table)
    (below : ∀ a, a ∈ argIds → a < st.next) :
    Table.WF (valueStep rules place written res argIds k st).2.2.next
        (valueStep rules place written res argIds k st).2.2.table ∧
      St.Grows st (valueStep rules place written res argIds k st).2.2 ∧
      (∀ i, i ∈ (valueStep rules place written res argIds k st).1 →
        i < (valueStep rules place written res argIds k st).2.2.next) ∧
      (valueStep rules place written res argIds k st).1.length = res.length := by
  obtain ⟨wf1, grows1⟩ := checkRequirements_grows rules.ops k place written argIds
    (rules.ops.requires written) st wf below
  obtain ⟨wf2, grows2, made⟩ := share_grows written (rules.values.order written argIds)
    res.length _ wf1
    (rules.values.order_lt fun a m => Nat.lt_of_lt_of_le (below a m) grows1.next)
  exact ⟨wf2, grows1.trans grows2, made, share_length _ _ _ _⟩

mutual
  /-- The walk grows the table well formed, from a state whose names in scope have identifiers
  below the next one, and a skeleton to follow, if any, whose leaves are below it. -/
  theorem walk_grows (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (followed : Option (Skel D outs))
        (ids : Ctx Nat) (k : Known) (s : State D.Ty Raw),
        InScope Γ ids s.st.next → Table.WF s.st.next s.st.table →
        FollowedBelow followed s.st.next →
        Table.WF (walk rules checks definition role blocks t followed ids k s).state.st.next
            (walk rules checks definition role blocks t followed ids k s).state.st.table ∧
          St.Grows s.st (walk rules checks definition role blocks t followed ids k s).state.st
    | _, _, .ret _, _, _, _, s, _, wf, _ => by
        simp only [walk, miss_st]
        exact ⟨wf, St.Grows.refl s.st⟩
    | _, _, .op (res := res) key o args results rest, followed, ids, k, s, scope, wf, fits => by
        cases written : rules.written o with
        | some raw =>
            simp only [walk, written]
            obtain ⟨wf1, grows1, made1, length1⟩ := valueStep_grows rules
              ⟨definition, blocks, some key, role⟩ raw res (idsOf ids args) k s.st wf
              (idsOf_lt scope args)
            generalize valueStep rules _ raw res (idsOf ids args) k s.st = step
              at wf1 grows1 made1 length1 ⊢
            obtain ⟨wf2, grows2⟩ := walk_grows blocks rest followed (bindIds ids results step.1)
              step.2.1 { s with st := step.2.2 }
              ((scope.mono grows1.next).bind results step.1 length1 made1) wf1
              (fits.mono grows1.next)
            exact ⟨wf2, grows1.trans grows2⟩
        | none =>
            simp only [walk, written]
            generalize hhit : effectEntry checks key o (idsOf ids args) followed = hit
            have hitBelow : ∀ a, hit = some a →
                a.1 + res.length ≤ s.st.next ∧ a.2.Below s.st.next := fun a found => by
              obtain ⟨_, -, e⟩ := effectEntry_hit checks (hhit.trans found)
              exact fits _ e
            generalize hs1 : miss _ _ _ s = s₁
            have s1st : s₁.st = s.st := by rw [← hs1]; exact miss_st _ _ _ s
            rw [← s1st] at scope wf hitBelow ⊢
            obtain ⟨wf1, grows1, made1, length1, -⟩ := leaves_grows (hit.map (·.1)) res.length s₁
              wf (leaf_below_of_hit (fun a found => (hitBelow a found).1) (Nat.le_refl _))
            generalize leaves _ _ s₁ = made at wf1 grows1 made1 length1 ⊢
            generalize Known.enter rules _ _ = k'
            obtain ⟨wf2, grows2⟩ := walk_grows blocks rest (hit.map (·.2))
              (bindIds ids results made.1) k' made.2
              ((scope.mono grows1.next).bind results made.1 length1 made1) wf1
              (FollowedBelow.of_hit (fun a found => (hitBelow a found).2) grows1.next)
            exact ⟨wf2, grows1.trans grows2⟩
    | _, _, .guard (t := t) key w c _ why rest, followed, ids, k, s, scope, wf, fits => by
        simp only [walk]
        generalize hhit : guardEntry checks (t := t) key w (idOf ids c.name) why followed = hit
        have hitBelow : ∀ a, hit = some a → a.Below s.st.next := fun a found => by
          obtain ⟨_, e⟩ := guardEntry_hit checks (hhit.trans found)
          have below := fits _ e
          exact below
        generalize hs1 : miss _ _ _ s = s₁
        have s1st : s₁.st = s.st := by rw [← hs1]; exact miss_st _ _ _ s
        generalize assume rules.ops _ _ _ _ _ = k'
        rw [← s1st] at scope wf hitBelow ⊢
        exact walk_grows blocks rest hit ids k' s₁ scope wf hitBelow
    | _, _, .choose (mid := mid) (t := t) key w c _ _ onTrue onFalse results rest, followed, ids, k,
        s, scope, wf, fits => by
        simp only [walk]
        generalize hhit : chooseEntry checks (mid := mid) (t := t) key w (idOf ids c.name)
          followed = hit
        have hitBelow : ∀ a, hit = some a → a.1.Below s.st.next ∧ a.2.1.Below s.st.next ∧
            a.2.2.1 + mid.length ≤ s.st.next ∧ a.2.2.2.Below s.st.next := fun a found => by
          obtain ⟨_, e⟩ := chooseEntry_hit checks (hhit.trans found)
          exact fits _ e
        generalize hs1 : miss _ _ _ s = s₁
        have s1st : s₁.st = s.st := by rw [← hs1]; exact miss_st _ _ _ s
        rw [← s1st] at scope wf hitBelow ⊢
        generalize assume rules.ops _ _ k _ true = k1
        obtain ⟨wf1, grows1⟩ := walk_grows blocks onTrue (hit.map (·.1)) ids k1 s₁ scope wf
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).1) (Nat.le_refl _))
        generalize walk rules checks definition role blocks onTrue _ _ _ _ = first at wf1 grows1 ⊢
        generalize assume rules.ops _ _ k _ false = k2
        obtain ⟨wf2, grows2⟩ := walk_grows blocks onFalse (hit.map (·.2.1)) ids k2 first.state
          (scope.mono grows1.next) wf1
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).2.1) grows1.next)
        generalize walk rules checks definition role blocks onFalse _ _ _ _ = second
          at wf2 grows2 ⊢
        obtain ⟨wf3, grows3, made3, length3, -⟩ := leaves_grows (hit.map (·.2.2.1)) mid.length
          second.state wf2
          (leaf_below_of_hit (fun a found => (hitBelow a found).2.2.1) (grows1.trans grows2).next)
        generalize leaves _ _ second.state = made at wf3 grows3 made3 length3 ⊢
        generalize Known.enter rules _ _ = k3
        obtain ⟨wf4, grows4⟩ := walk_grows blocks rest (hit.map (·.2.2.2))
          (bindIds ids results made.1) k3 made.2
          ((scope.mono (grows1.trans (grows2.trans grows3)).next).bind results made.1 length3
            made3) wf3
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).2.2.2)
            (grows1.trans (grows2.trans grows3)).next)
        exact ⟨wf4, grows1.trans (grows2.trans (grows3.trans grows4))⟩
    | _, _, .cases (mid := mid) (t := t) (payloads := payloads) key w x _ _ arms results rest,
        followed, ids, k, s, scope, wf, fits => by
        simp only [walk]
        generalize hhit : casesEntry checks (mid := mid) (t := t) (payloads := payloads) key w
          (idOf ids x.name) followed = hit
        have hitBelow : ∀ a, hit = some a → a.1.Below s.st.next ∧
            a.2.1 + mid.length ≤ s.st.next ∧ a.2.2.Below s.st.next := fun a found => by
          obtain ⟨_, e⟩ := casesEntry_hit checks (hhit.trans found)
          exact fits _ e
        generalize hs1 : miss _ _ _ s = s₁
        have s1st : s₁.st = s.st := by rw [← hs1]; exact miss_st _ _ _ s
        rw [← s1st] at scope wf hitBelow ⊢
        obtain ⟨wf1, grows1⟩ := walkArms_grows blocks arms (hit.map (·.1)) ids k s₁ scope wf
          (ArmsFollowedBelow.of_hit (fun a found => (hitBelow a found).1) (Nat.le_refl _))
        generalize walkArms rules checks definition role blocks arms _ _ _ _ = regions
          at wf1 grows1 ⊢
        obtain ⟨wf3, grows3, made3, length3, -⟩ := leaves_grows (hit.map (·.2.1)) mid.length
          regions.state wf1
          (leaf_below_of_hit (fun a found => (hitBelow a found).2.1) grows1.next)
        generalize leaves _ _ regions.state = made at wf3 grows3 made3 length3 ⊢
        generalize Known.enter rules _ _ = k3
        obtain ⟨wf4, grows4⟩ := walk_grows blocks rest (hit.map (·.2.2))
          (bindIds ids results made.1) k3 made.2
          ((scope.mono (grows1.trans grows3).next).bind results made.1 length3 made3) wf3
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).2.2) (grows1.trans grows3).next)
        exact ⟨wf4, grows1.trans (grows3.trans grows4)⟩
    | _, _, .loop (carried := carried) (each := each) key w times _ init inputs body results rest,
        followed, ids, k, s, scope, wf, fits => by
        simp only [walk]
        generalize hhit : loopEntry checks (carried := carried) (each := each) key w
          (fun count => times.follows checks ids count) (idsOf ids init) followed = hit
        have hitBelow : ∀ a, hit = some a → a.1 + (carried.length + 1) ≤ s.st.next ∧
            a.2.1.Below s.st.next ∧ a.2.2.1 + (carried.length + each.length) ≤ s.st.next ∧
            a.2.2.2.Below s.st.next := fun a found => by
          obtain ⟨_, _, e⟩ := loopEntry_hit checks (hhit.trans found)
          exact fits _ e
        generalize hs1 : miss _ _ _ s = s₁
        have s1st : s₁.st = s.st := by rw [← hs1]; exact miss_st _ _ _ s
        rw [← s1st] at scope wf hitBelow ⊢
        obtain ⟨wf0, grows0, made0, length0, -⟩ := leaves_grows (hit.map (·.1))
          (carried.length + 1) s₁ wf
          (leaf_below_of_hit (fun a found => (hitBelow a found).1) (Nat.le_refl _))
        generalize leaves _ (carried.length + 1) s₁ = inBody at wf0 grows0 made0 length0 ⊢
        generalize bodyKnown rules _ _ _ _ _ _ = k1
        obtain ⟨wf1, grows1⟩ := walk_grows blocks body (hit.map (·.2.1))
          (bindIds ids inputs inBody.1) k1 inBody.2
          ((scope.mono grows0.next).bind inputs inBody.1 (by rw [length0]; rfl) made0) wf0
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).2.1) grows0.next)
        generalize walk rules checks definition role blocks body _ _ _ _ = e at wf1 grows1 ⊢
        obtain ⟨tableSame, nextSame, -, -⟩ :=
          recordBound_state ⟨definition, blocks, some key, role⟩ k ids e.state.st times
        generalize recordBound _ k ids e.state.st times = st₁ at tableSame nextSame ⊢
        have grows2 : St.Grows e.state.st st₁ :=
          ⟨by rw [nextSame]; exact Nat.le_refl _, [], by rw [tableSame]; rfl,
            fun _ m => nomatch m⟩
        have wf2 : Table.WF st₁.next st₁.table := by rw [tableSame, nextSame]; exact wf1
        obtain ⟨wf3, grows3, made3, length3, -⟩ := leaves_grows (hit.map (·.2.2.1))
          (carried.length + each.length) { e.state with st := st₁ } wf2
          (leaf_below_of_hit (fun a found => (hitBelow a found).2.2.1)
            (grows0.trans (grows1.trans grows2)).next)
        generalize leaves _ _ { e.state with st := st₁ } = made at wf3 grows3 made3 length3 ⊢
        generalize Known.enter rules _ _ = k3
        have toRest := grows0.trans (grows1.trans (grows2.trans grows3))
        obtain ⟨wf4, grows4⟩ := walk_grows blocks rest (hit.map (·.2.2.2))
          (bindIds ids results made.1) k3 made.2
          ((scope.mono toRest.next).bind results made.1 (by rw [length3]; simp) made3) wf3
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).2.2.2) toRest.next)
        exact ⟨wf4, toRest.trans grows4⟩
    | _, _, .block (mid := mid) key number body results rest, followed, ids, k, s, scope, wf,
        fits => by
        simp only [walk]
        generalize hhit : blockEntry checks (mid := mid) key number followed = hit
        have hitBelow : ∀ a, hit = some a → a.1.Below s.st.next ∧
            a.2.1 + mid.length ≤ s.st.next ∧ a.2.2.Below s.st.next := fun a found =>
          fits _ (blockEntry_hit checks (hhit.trans found))
        generalize hs1 : miss _ _ _ s = s₁
        have s1st : s₁.st = s.st := by rw [← hs1]; exact miss_st _ _ _ s
        rw [← s1st] at scope wf hitBelow ⊢
        obtain ⟨wf1, grows1⟩ := walk_grows (blocks ++ [(key, number)]) body (hit.map (·.1)) ids k
          s₁ scope wf
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).1) (Nat.le_refl _))
        generalize walk rules checks definition role (blocks ++ [(key, number)]) body _ _ _ _ = e
          at wf1 grows1 ⊢
        obtain ⟨wf3, grows3, made3, length3, -⟩ := leaves_grows (hit.map (·.2.1)) mid.length
          e.state wf1 (leaf_below_of_hit (fun a found => (hitBelow a found).2.1) grows1.next)
        generalize leaves _ _ e.state = made at wf3 grows3 made3 length3 ⊢
        generalize Known.enter rules _ _ = k3
        obtain ⟨wf4, grows4⟩ := walk_grows blocks rest (hit.map (·.2.2))
          (bindIds ids results made.1) k3 made.2
          ((scope.mono (grows1.trans grows3).next).bind results made.1 length3 made3) wf3
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).2.2) (grows1.trans grows3).next)
        exact ⟨wf4, grows1.trans (grows3.trans grows4)⟩
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, followed, ids, k, s, scope, wf,
        fits => by
        simp only [walk]
        generalize hhit : attemptEntry checks (mid := mid) key w followed = hit
        have hitBelow : ∀ a, hit = some a → a.1 + 1 ≤ s.st.next ∧ a.2.1.Below s.st.next ∧
            a.2.2.1 + mid.length ≤ s.st.next ∧ a.2.2.2.Below s.st.next := fun a found =>
          fits _ (attemptEntry_hit checks (hhit.trans found))
        generalize hs1 : miss _ _ _ s = s₁
        have s1st : s₁.st = s.st := by rw [← hs1]; exact miss_st _ _ _ s
        rw [← s1st] at scope wf hitBelow ⊢
        obtain ⟨wf0, grows0, made0, length0, -⟩ := leaves_grows (hit.map (·.1)) 1 s₁ wf
          (leaf_below_of_hit (fun a found => (hitBelow a found).1) (Nat.le_refl _))
        generalize leaves _ 1 s₁ = inBody at wf0 grows0 made0 length0 ⊢
        generalize Known.enter rules (Known.addRanges k inBody.1 _) _ = k1
        obtain ⟨wf1, grows1⟩ := walk_grows blocks body (hit.map (·.2.1))
          (bindIds ids inputs inBody.1) k1 inBody.2
          ((scope.mono grows0.next).bind inputs inBody.1 length0 made0) wf0
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).2.1) grows0.next)
        generalize walk rules checks definition role blocks body _ _ _ _ = e at wf1 grows1 ⊢
        obtain ⟨wf3, grows3, made3, length3, -⟩ := leaves_grows (hit.map (·.2.2.1)) mid.length
          e.state wf1
          (leaf_below_of_hit (fun a found => (hitBelow a found).2.2.1) (grows0.trans grows1).next)
        generalize leaves _ _ e.state = made at wf3 grows3 made3 length3 ⊢
        generalize Known.enter rules _ _ = k3
        have toRest := grows0.trans (grows1.trans grows3)
        obtain ⟨wf4, grows4⟩ := walk_grows blocks rest (hit.map (·.2.2.2))
          (bindIds ids results made.1) k3 made.2
          ((scope.mono toRest.next).bind results made.1 length3 made3) wf3
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).2.2.2) toRest.next)
        exact ⟨wf4, toRest.trans grows4⟩
  /-- The walk of arms grows the table well formed, as the walk of a term. -/
  theorem walkArms_grows (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads)
        (followed : Option (SkelArms D mid payloads)) (ids : Ctx Nat) (k : Known)
        (s : State D.Ty Raw),
        InScope Γ ids s.st.next → Table.WF s.st.next s.st.table →
        ArmsFollowedBelow followed s.st.next →
        Table.WF (walkArms rules checks definition role blocks arms followed ids k s).state.st.next
            (walkArms rules checks definition role blocks arms followed ids k s).state.st.table ∧
          St.Grows s.st
            (walkArms rules checks definition role blocks arms followed ids k s).state.st
    | _, _, _, .nil, _, _, _, s, _, wf, _ => by
        simp only [walkArms]
        exact ⟨wf, St.Grows.refl s.st⟩
    | _, _, _, .cons (payload := payload) inputs arm rest, followed, ids, k, s, scope, wf,
        fits => by
        simp only [walkArms]
        generalize hhit : armEntry followed = hit
        have hitBelow : ∀ a, hit = some a → a.1 + 1 ≤ s.st.next ∧ a.2.1.Below s.st.next ∧
            a.2.2.Below s.st.next := fun a found => fits _ (armEntry_hit (hhit.trans found))
        obtain ⟨wf0, grows0, made0, length0, -⟩ := leaves_grows (hit.map (·.1)) 1 s wf
          (leaf_below_of_hit (fun a found => (hitBelow a found).1) (Nat.le_refl _))
        generalize leaves _ 1 s = made at wf0 grows0 made0 length0 ⊢
        generalize Known.enter rules _ _ = k1
        obtain ⟨wf1, grows1⟩ := walk_grows blocks arm (hit.map (·.2.1))
          (bindIds ids inputs made.1) k1 made.2
          ((scope.mono grows0.next).bind inputs made.1 length0 made0) wf0
          (FollowedBelow.of_hit (fun a found => (hitBelow a found).2.1) grows0.next)
        generalize walk rules checks definition role blocks arm _ _ _ _ = e at wf1 grows1 ⊢
        obtain ⟨wf2, grows2⟩ := walkArms_grows blocks rest (hit.map (·.2.2)) ids k e.state
          (scope.mono (grows0.trans grows1).next) wf1
          (ArmsFollowedBelow.of_hit (fun a found => (hitBelow a found).2.2)
            (grows0.trans grows1).next)
        exact ⟨wf2, grows0.trans (grows1.trans grows2)⟩
end

/-! ## The skeleton that the walk builds -/

mutual
  /-- Without a skeleton to follow, the walk builds a skeleton above its state: its leaves are
  below the next identifier, apart from the table, and made in order from the state's next
  identifier on. -/
  theorem walk_built (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (ids : Ctx Nat) (k : Known)
        (s : State D.Ty Raw),
        InScope Γ ids s.st.next → Table.WF s.st.next s.st.table →
        (walk rules checks definition role blocks t none ids k s).skel.Below
            (walk rules checks definition role blocks t none ids k s).state.st.next ∧
          (walk rules checks definition role blocks t none ids k s).skel.Apart
            (walk rules checks definition role blocks t none ids k s).state.st.table ∧
          (walk rules checks definition role blocks t none ids k s).skel.Fresh s.st.next
    | _, _, .ret _, _, _, _, _, _ => by
        simp only [walk, kept_none]
        exact ⟨trivial, trivial, trivial⟩
    | _, _, .op (res := res) key o args results rest, ids, k, s, scope, wf => by
        cases written : rules.written o with
        | some raw =>
            simp only [walk, written]
            obtain ⟨wf1, grows1, made1, length1⟩ := valueStep_grows rules
              ⟨definition, blocks, some key, role⟩ raw res (idsOf ids args) k s.st wf
              (idsOf_lt scope args)
            generalize valueStep rules _ raw res (idsOf ids args) k s.st = step
              at wf1 grows1 made1 length1 ⊢
            obtain ⟨below, apart, inOrder⟩ := walk_built blocks rest (bindIds ids results step.1)
              step.2.1 { s with st := step.2.2 }
              ((scope.mono grows1.next).bind results step.1 length1 made1) wf1
            exact ⟨below, apart, inOrder.mono grows1.next⟩
        | none =>
            simp only [walk, written, effectEntry_none, Option.isSome_none, miss_not_following,
              Option.map_none, leaves_none, kept_none]
            obtain ⟨wf1, grows1, made1⟩ := fresh_grows res.length s.st wf
            generalize Known.enter rules _ _ = k1
            have scope1 := (scope.mono grows1.next).bind results _ (by simp [fresh]) made1
            obtain ⟨-, grows2⟩ := walk_grows rules checks definition role blocks rest none _ k1
              { s with st := (fresh res.length s.st).2 } scope1 wf1 FollowedBelow.none
            obtain ⟨below, apart, inOrder⟩ := walk_built blocks rest _ k1
              { s with st := (fresh res.length s.st).2 } scope1 wf1
            exact ⟨⟨grows2.next, below⟩, ⟨LeavesApart.of_fresh res.length wf grows2, apart⟩,
              ⟨Nat.le_refl _, inOrder⟩⟩
    | _, _, .guard key w c _ why rest, ids, k, s, scope, wf => by
        simp only [walk, guardEntry_none, Option.isSome_none, miss_not_following, kept_none]
        exact walk_built blocks rest ids _ s scope wf
    | _, _, .choose (mid := mid) key w c _ _ onTrue onFalse results rest, ids, k, s, scope, wf =>
        by
        simp only [walk, chooseEntry_none, Option.isSome_none, miss_not_following,
          Option.map_none, leaves_none, kept_none]
        generalize assume rules.ops _ _ k _ true = k1
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks onTrue none ids k1 s
          scope wf FollowedBelow.none
        obtain ⟨below1, apart1, inOrder1⟩ := walk_built blocks onTrue ids k1 s scope wf
        generalize walk rules checks definition role blocks onTrue none ids k1 s = first
          at wf1 grows1 below1 apart1 inOrder1 ⊢
        generalize assume rules.ops _ _ k _ false = k2
        obtain ⟨wf2, grows2⟩ := walk_grows rules checks definition role blocks onFalse none ids k2
          first.state (scope.mono grows1.next) wf1 FollowedBelow.none
        obtain ⟨below2, apart2, inOrder2⟩ := walk_built blocks onFalse ids k2 first.state
          (scope.mono grows1.next) wf1
        generalize walk rules checks definition role blocks onFalse none ids k2 first.state = second
          at wf2 grows2 below2 apart2 inOrder2 ⊢
        obtain ⟨wf3, grows3, made3⟩ := fresh_grows mid.length second.state.st wf2
        generalize Known.enter rules _ _ = k3
        have scope3 := (scope.mono (grows1.trans (grows2.trans grows3)).next).bind results _
          (by simp [fresh]) made3
        obtain ⟨-, grows4⟩ := walk_grows rules checks definition role blocks rest none _ k3
          { second.state with st := (fresh mid.length second.state.st).2 } scope3 wf3
          FollowedBelow.none
        obtain ⟨below4, apart4, inOrder4⟩ := walk_built blocks rest _ k3
          { second.state with st := (fresh mid.length second.state.st).2 } scope3 wf3
        have after1 := grows2.trans (grows3.trans grows4)
        have after2 := grows3.trans grows4
        exact ⟨⟨below1.mono after1.next, below2.mono after2.next, grows4.next, below4⟩,
          ⟨Skel.Apart.grows after1 _ apart1 below1, Skel.Apart.grows after2 _ apart2 below2,
            LeavesApart.of_fresh mid.length wf2 grows4, apart4⟩,
          ⟨inOrder1, inOrder2.mono grows1.next, (grows1.trans grows2).next, inOrder4⟩⟩
    | _, _, .cases (mid := mid) key w x _ _ arms results rest, ids, k, s, scope, wf => by
        simp only [walk, casesEntry_none, Option.isSome_none, miss_not_following,
          Option.map_none, leaves_none, kept_none]
        obtain ⟨wf1, grows1⟩ := walkArms_grows rules checks definition role blocks arms none ids k
          s scope wf ArmsFollowedBelow.none
        obtain ⟨below1, apart1, inOrder1⟩ := walkArms_built blocks arms ids k s scope wf
        generalize walkArms rules checks definition role blocks arms none ids k s = regions
          at wf1 grows1 below1 apart1 inOrder1 ⊢
        obtain ⟨wf3, grows3, made3⟩ := fresh_grows mid.length regions.state.st wf1
        generalize Known.enter rules _ _ = k3
        have scope3 := (scope.mono (grows1.trans grows3).next).bind results _ (by simp [fresh])
          made3
        obtain ⟨-, grows4⟩ := walk_grows rules checks definition role blocks rest none _ k3
          { regions.state with st := (fresh mid.length regions.state.st).2 } scope3 wf3
          FollowedBelow.none
        obtain ⟨below4, apart4, inOrder4⟩ := walk_built blocks rest _ k3
          { regions.state with st := (fresh mid.length regions.state.st).2 } scope3 wf3
        have after1 := grows3.trans grows4
        exact ⟨⟨below1.mono after1.next, grows4.next, below4⟩,
          ⟨SkelArms.Apart.grows after1 _ apart1 below1, LeavesApart.of_fresh mid.length wf1 grows4,
            apart4⟩,
          ⟨inOrder1, grows1.next, inOrder4⟩⟩
    | _, _, .loop (carried := carried) (each := each) key w times _ init inputs body results rest,
        ids, k, s, scope, wf => by
        simp only [walk, loopEntry_none, Option.isSome_none, miss_not_following,
          Option.map_none, leaves_none, kept_none]
        obtain ⟨wf0, grows0, made0⟩ := fresh_grows (carried.length + 1) s.st wf
        generalize bodyKnown rules _ _ _ _ _ _ = k1
        have scope0 := (scope.mono grows0.next).bind inputs _ (by simp [fresh]) made0
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks body none _ k1
          { s with st := (fresh (carried.length + 1) s.st).2 } scope0 wf0 FollowedBelow.none
        obtain ⟨below1, apart1, inOrder1⟩ := walk_built blocks body _ k1
          { s with st := (fresh (carried.length + 1) s.st).2 } scope0 wf0
        generalize walk rules checks definition role blocks body none _ k1 _ = e
          at wf1 grows1 below1 apart1 inOrder1 ⊢
        obtain ⟨tableSame, nextSame, -, -⟩ :=
          recordBound_state ⟨definition, blocks, some key, role⟩ k ids e.state.st times
        generalize recordBound _ k ids e.state.st times = st₁ at tableSame nextSame ⊢
        have grows2 : St.Grows e.state.st st₁ :=
          ⟨by rw [nextSame]; exact Nat.le_refl _, [], by rw [tableSame]; rfl,
            fun _ m => nomatch m⟩
        have wf2 : Table.WF st₁.next st₁.table := by rw [tableSame, nextSame]; exact wf1
        obtain ⟨wf3, grows3, made3⟩ := fresh_grows (carried.length + each.length) st₁ wf2
        generalize Known.enter rules _ _ = k3
        have toRest := grows0.trans (grows1.trans (grows2.trans grows3))
        have scope3 := (scope.mono toRest.next).bind results _ (by simp [fresh]) made3
        obtain ⟨-, grows4⟩ := walk_grows rules checks definition role blocks rest none _ k3
          { e.state with st := (fresh (carried.length + each.length) st₁).2 } scope3 wf3
          FollowedBelow.none
        obtain ⟨below4, apart4, inOrder4⟩ := walk_built blocks rest _ k3
          { e.state with st := (fresh (carried.length + each.length) st₁).2 } scope3 wf3
        have after1 := grows2.trans (grows3.trans grows4)
        have apart3 := LeavesApart.of_fresh (carried.length + each.length) wf2 grows4
        generalize walk rules checks definition role blocks rest none _ k3 _ = after
          at grows4 below4 apart4 inOrder4 after1 apart3 ⊢
        have resultsBelow :
            e.state.st.next + (carried.length + each.length) ≤ after.state.st.next := by
          rw [← nextSame]
          exact grows4.next
        have restFresh :
            after.skel.Fresh (e.state.st.next + (carried.length + each.length)) := by
          rw [← nextSame]
          exact inOrder4
        rw [nextSame] at apart3
        exact ⟨⟨(grows1.trans after1).next, below1.mono after1.next, resultsBelow, below4⟩,
          ⟨LeavesApart.of_fresh _ wf (grows1.trans after1), Skel.Apart.grows after1 _ apart1 below1,
            apart3, apart4⟩,
          ⟨Nat.le_refl _, inOrder1, (grows0.trans grows1).next, restFresh⟩⟩
    | _, _, .block (mid := mid) key number body results rest, ids, k, s, scope, wf => by
        simp only [walk, blockEntry_none, Option.isSome_none, miss_not_following,
          Option.map_none, leaves_none, kept_none]
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role (blocks ++ [(key, number)])
          body none ids k s scope wf FollowedBelow.none
        obtain ⟨below1, apart1, inOrder1⟩ := walk_built (blocks ++ [(key, number)]) body ids k s
          scope wf
        generalize walk rules checks definition role (blocks ++ [(key, number)]) body none ids k
          s = e at wf1 grows1 below1 apart1 inOrder1 ⊢
        obtain ⟨wf3, grows3, made3⟩ := fresh_grows mid.length e.state.st wf1
        generalize Known.enter rules _ _ = k3
        have scope3 := (scope.mono (grows1.trans grows3).next).bind results _ (by simp [fresh])
          made3
        obtain ⟨-, grows4⟩ := walk_grows rules checks definition role blocks rest none _ k3
          { e.state with st := (fresh mid.length e.state.st).2 } scope3 wf3 FollowedBelow.none
        obtain ⟨below4, apart4, inOrder4⟩ := walk_built blocks rest _ k3
          { e.state with st := (fresh mid.length e.state.st).2 } scope3 wf3
        have after1 := grows3.trans grows4
        exact ⟨⟨below1.mono after1.next, grows4.next, below4⟩,
          ⟨Skel.Apart.grows after1 _ apart1 below1, LeavesApart.of_fresh mid.length wf1 grows4,
            apart4⟩,
          ⟨inOrder1, grows1.next, inOrder4⟩⟩
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, ids, k, s, scope, wf => by
        simp only [walk, attemptEntry_none, Option.isSome_none, miss_not_following,
          Option.map_none, leaves_none, kept_none]
        obtain ⟨wf0, grows0, made0⟩ := fresh_grows 1 s.st wf
        generalize Known.enter rules (Known.addRanges k _ _) _ = k1
        have scope0 := (scope.mono grows0.next).bind inputs _ (by simp [fresh]) made0
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks body none _ k1
          { s with st := (fresh 1 s.st).2 } scope0 wf0 FollowedBelow.none
        obtain ⟨below1, apart1, inOrder1⟩ := walk_built blocks body _ k1
          { s with st := (fresh 1 s.st).2 } scope0 wf0
        generalize walk rules checks definition role blocks body none _ k1 _ = e
          at wf1 grows1 below1 apart1 inOrder1 ⊢
        obtain ⟨wf3, grows3, made3⟩ := fresh_grows mid.length e.state.st wf1
        generalize Known.enter rules _ _ = k3
        have toRest := grows0.trans (grows1.trans grows3)
        have scope3 := (scope.mono toRest.next).bind results _ (by simp [fresh]) made3
        obtain ⟨-, grows4⟩ := walk_grows rules checks definition role blocks rest none _ k3
          { e.state with st := (fresh mid.length e.state.st).2 } scope3 wf3 FollowedBelow.none
        obtain ⟨below4, apart4, inOrder4⟩ := walk_built blocks rest _ k3
          { e.state with st := (fresh mid.length e.state.st).2 } scope3 wf3
        have after1 := grows3.trans grows4
        exact ⟨⟨(grows1.trans after1).next, below1.mono after1.next, grows4.next, below4⟩,
          ⟨LeavesApart.of_fresh 1 wf (grows1.trans after1), Skel.Apart.grows after1 _ apart1 below1,
            LeavesApart.of_fresh mid.length wf1 grows4, apart4⟩,
          ⟨Nat.le_refl _, inOrder1, (grows0.trans grows1).next, inOrder4⟩⟩
  /-- Without arms to follow, the walk of arms builds them above its state, as the walk of a
  term. -/
  theorem walkArms_built (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads) (ids : Ctx Nat)
        (k : Known) (s : State D.Ty Raw),
        InScope Γ ids s.st.next → Table.WF s.st.next s.st.table →
        (walkArms rules checks definition role blocks arms none ids k s).skel.Below
            (walkArms rules checks definition role blocks arms none ids k s).state.st.next ∧
          (walkArms rules checks definition role blocks arms none ids k s).skel.Apart
            (walkArms rules checks definition role blocks arms none ids k s).state.st.table ∧
          (walkArms rules checks definition role blocks arms none ids k s).skel.Fresh s.st.next
    | _, _, _, .nil, _, _, _, _, _ => by
        simp only [walkArms]
        exact ⟨trivial, trivial, trivial⟩
    | _, _, _, .cons inputs arm rest, ids, k, s, scope, wf => by
        simp only [walkArms, armEntry_none, Option.map_none, leaves_none, Option.getD_none]
        obtain ⟨wf0, grows0, made0⟩ := fresh_grows 1 s.st wf
        generalize Known.enter rules _ _ = k1
        have scope0 := (scope.mono grows0.next).bind inputs _ (by simp [fresh]) made0
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks arm none _ k1
          { s with st := (fresh 1 s.st).2 } scope0 wf0 FollowedBelow.none
        obtain ⟨below1, apart1, inOrder1⟩ := walk_built blocks arm _ k1
          { s with st := (fresh 1 s.st).2 } scope0 wf0
        generalize walk rules checks definition role blocks arm none _ k1 _ = e
          at wf1 grows1 below1 apart1 inOrder1 ⊢
        obtain ⟨-, grows2⟩ := walkArms_grows rules checks definition role blocks rest none ids k
          e.state (scope.mono (grows0.trans grows1).next) wf1 ArmsFollowedBelow.none
        obtain ⟨below2, apart2, inOrder2⟩ := walkArms_built blocks rest ids k e.state
          (scope.mono (grows0.trans grows1).next) wf1
        exact ⟨⟨(grows1.trans grows2).next, below1.mono grows2.next, below2⟩,
          ⟨LeavesApart.of_fresh 1 wf (grows1.trans grows2), Skel.Apart.grows grows2 _ apart1 below1,
            apart2⟩,
          ⟨Nat.le_refl _, inOrder1, inOrder2.mono (grows0.trans grows1).next⟩⟩
end

end

end

end Zkc.Core.Analysis.ValueSide
