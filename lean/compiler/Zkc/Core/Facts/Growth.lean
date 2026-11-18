module

public import Zkc.Core.Facts.Walk
public import Zkc.Core.Facts.Learning
public import Zkc.Core.Value.Leaves

@[expose] public section

/-!
What the walk of the analysis does to its state, to the places that differ and to the skeleton,
whatever the run: the lemmas, in the namespace `Analysis.Facts`, on which both the runs of the
walk (`Facts/WalkRuns.lean`) and its soundness (`Facts/Soundness.lean`,
`Facts/SoundnessFollowing.lean`) rest.

It only adds refusals, bounds at the addresses of the loops that it walks, and places that differ
(`Analysis.Facts.walk_adds`); so the bounds that the check of facts gives a body are at the
places of its definition (`checkFacts_places`). A place that differs is added only where a
skeleton is followed and the next entry is not found, so where none is added the entry was found
(`found_of_differs`, `hit_of_no_place`), and where no skeleton is followed none is added
(`walk_free_differs`). From a well-formed state where every name in scope has an identifier below
the next (`FactCheck.Scoped`), and a followed skeleton whose leaves are below the next, it keeps
the table well formed, makes identifiers and entries above those that it had, and returns
identifiers below the next (`Analysis.Facts.walk_grows`). The skeleton that it builds when it
follows none has its leaves made in order from the state's next identifier on, below its next at
the end, and apart from its table (`Analysis.Facts.walk_skeleton`): what following a skeleton
relies on, below the next identifier (`Skel.Ordered.below`) and made in order as the runs of a
followed skeleton ask (`Skel.Ordered.fresh`). And a skeleton that is followed is, at a kept
instruction that is found, that instruction's entry, with the parts that the walk takes (the
lemmas `*Entry_hit`). That new identifiers and a shared application keep the table well formed,
and that binding names keeps every name in scope with an identifier below the next
(`FactCheck.InScope`), is in `Value/Valuation.lean`; that deciding the requirements of an
application does, and learning requirements that hold, here (`FactCheck.checkRequirements_grows`,
`FactCheck.learnRequirements_grows`).
-/

namespace Zkc.Core

namespace FactCheck

theorem idsOf_length {α : Type} {Γ : Ctx α} (ids : Ctx Nat) :
    ∀ {items : List α} (xs : HList (Var Γ) items), (idsOf ids xs).length = items.length
  | [], .nil => rfl
  | _ :: _, .cons _ rest => by simp [idsOf, idsOf_length ids rest]

section
variable {Raw : Type} [DecidableEq Raw] {T : Type}

/-! ## Steps that keep the table well formed -/

/-- The state and the identifiers that a region returns are well formed: the table, and every
identifier below the next. -/
def WellFormed (ids : List Nat) (st : St T Raw) : Prop :=
  Table.WF st.next st.table ∧ ∀ i, i ∈ ids → i < st.next

/-- The state and the identifiers of the names in scope are well formed: the table, and every
name in scope with an identifier below the next. -/
def Scoped (Γ : Ctx T) (ids : Ctx Nat) (st : St T Raw) : Prop :=
  Table.WF st.next st.table ∧ InScope Γ ids st.next

theorem operandId_grows (argIds : List Nat) (st : St T Raw) (o : Operand Raw)
    (wf : Table.WF st.next st.table) (hlt : ∀ a, a ∈ argIds → a < st.next) :
    Table.WF (operandId argIds st o).2.next (operandId argIds st o).2.table ∧
      St.Grows st (operandId argIds st o).2 := by
  cases o with
  | arg => exact ⟨wf, St.Grows.refl st⟩
  | apply w ps =>
      simp only [operandId]
      split
      · next ids' e =>
          obtain ⟨wf', grows, _⟩ := share_grows w ids' 1 st wf
            (fun a m => hlt a (atPositions_mem e a m))
          exact ⟨wf', grows⟩
      · exact ⟨wf, St.Grows.refl st⟩

theorem operandIds_grows (argIds : List Nat) :
    ∀ (os : List (Operand Raw)) (st : St T Raw), Table.WF st.next st.table →
      (∀ a, a ∈ argIds → a < st.next) →
      Table.WF (operandIds argIds os st).2.next (operandIds argIds os st).2.table ∧
        St.Grows st (operandIds argIds os st).2
  | [], st, wf, _ => ⟨wf, St.Grows.refl st⟩
  | o :: os, st, wf, hlt => by
      simp only [operandIds]
      obtain ⟨wf1, g1⟩ := operandId_grows argIds st o wf hlt
      obtain ⟨wf2, g2⟩ := operandIds_grows argIds os _ wf1
        (fun a m => Nat.lt_of_lt_of_le (hlt a m) g1.next)
      exact ⟨wf2, g1.trans g2⟩

theorem checkRequirements_grows (ops : OpFacts Raw) (k : Known) (place : Place) (written : Raw)
    (argIds : List Nat) :
    ∀ (reqs : List (Requirement Raw)) (st : St T Raw), Table.WF st.next st.table →
      (∀ a, a ∈ argIds → a < st.next) →
      Table.WF (checkRequirements ops k place written argIds reqs st).next
          (checkRequirements ops k place written argIds reqs st).table ∧
        St.Grows st (checkRequirements ops k place written argIds reqs st)
  | [], st, wf, _ => ⟨wf, St.Grows.refl st⟩
  | req :: rest, st, wf, hlt => by
      simp only [checkRequirements]
      obtain ⟨wf1, g1⟩ := operandIds_grows argIds req.operands st wf hlt
      generalize operandIds argIds req.operands st = resolved at wf1 g1 ⊢
      split
      · obtain ⟨wf2, g2⟩ := checkRequirements_grows ops k place written argIds rest resolved.2
          wf1 (fun a m => Nat.lt_of_lt_of_le (hlt a m) g1.next)
        exact ⟨wf2, g1.trans g2⟩
      · obtain ⟨wf2, g2⟩ := checkRequirements_grows ops k place written argIds rest
          { resolved.2 with refusals := _ :: resolved.2.refusals }
          wf1 (fun a m => Nat.lt_of_lt_of_le (hlt a m) g1.next)
        exact ⟨wf2, ⟨Nat.le_trans g1.next g2.next, by
          obtain ⟨n1, e1, l1⟩ := g1.table
          obtain ⟨n2, e2, l2⟩ := g2.table
          refine ⟨n2 ++ n1, by rw [e2]; simp only; rw [e1, List.append_assoc], ?_⟩
          intro e m
          rcases List.mem_append.mp m with m | m
          · exact Nat.le_trans g1.next (l2 e m)
          · exact l1 e m⟩⟩

theorem learnRequirements_grows (ops : OpFacts Raw) (ids : List Nat) :
    ∀ (reqs : List (Requirement Raw)) (k : Known) (st : St T Raw), Table.WF st.next st.table →
      (∀ a, a ∈ ids → a < st.next) →
      Table.WF (learnRequirements ops ids reqs k st).2.next
          (learnRequirements ops ids reqs k st).2.table ∧
        St.Grows st (learnRequirements ops ids reqs k st).2
  | [], _, st, wf, _ => ⟨wf, St.Grows.refl st⟩
  | req :: rest, k, st, wf, hlt => by
      simp only [learnRequirements]
      obtain ⟨wf1, g1⟩ := operandIds_grows ids req.operands st wf hlt
      obtain ⟨wf2, g2⟩ := learnRequirements_grows ops ids rest _ _ wf1
        (fun a m => Nat.lt_of_lt_of_le (hlt a m) g1.next)
      exact ⟨wf2, g1.trans g2⟩

end

section
variable {D : Dialect} {Raw : Type} (definition : Key) (role : Option Role)

/-- What a loop adds to the state: a bound at its place, or nothing. -/
theorem recordBound_state {w : D.Who} {Γ : Ctx D.Ty} (place : Place) (k : Known)
    (ids : Ctx Nat) (st : St D.Ty Raw) (times : Times D w Γ) :
    (recordBound place k ids st times).table = st.table ∧
      (recordBound place k ids st times).next = st.next ∧
      (recordBound place k ids st times).refusals = st.refusals ∧
      ∃ new, (recordBound place k ids st times).bounds = new ++ st.bounds ∧
        ∀ q, q ∈ new → q.1 = place := by
  cases times with
  | fixed => exact ⟨rfl, rfl, rfl, [], rfl, fun _ m => nomatch m⟩
  | value count ok =>
      simp only [recordBound]
      split
      · next bound _ =>
          refine ⟨rfl, rfl, rfl, [(place, bound)], rfl, fun q m => ?_⟩
          simp at m
          rw [m]
      · exact ⟨rfl, rfl, rfl, [], rfl, fun _ m => nomatch m⟩

/-- Bounds at the addresses of a term. -/
def BoundsAt (addresses : List (List (Key × Nat) × Key))
    (new : List (Place × Nat)) : Prop :=
  ∀ q, q ∈ new → ∃ bl key, q.1 = ⟨definition, bl, some key, role⟩ ∧ (bl, key) ∈ addresses

end

end FactCheck

namespace Analysis.Facts

open FactCheck

section
variable {D : Dialect} {Raw : Type}

/-! ## The leaves of a skeleton, made in order -/

mutual
  /-- The leaves of a skeleton are made in order from `lo` on and are below `hi`: the leaves of an
  entry are at or above `lo`, its regions have theirs from `lo` (or above their inputs) to below
  its own leaves, and what follows it has its leaves above them. Of two regions of which one runs,
  each has its leaves in that span; what follows has none of them. -/
  def Skel.Ordered : {outs : List D.Ty} → Skel D outs → Nat → Nat → Prop
    | _, .ret _, lo, hi => lo ≤ hi
    | _, .effect (res := res) _ _ _ results rest, lo, hi =>
        lo ≤ results ∧ Skel.Ordered rest (results + res.length) hi
    | _, .guard _ _ _ _ _ rest, lo, hi => Skel.Ordered rest lo hi
    | _, .choose (mid := mid) _ _ _ _ onTrue onFalse results rest, lo, hi =>
        Skel.Ordered onTrue lo results ∧ Skel.Ordered onFalse lo results ∧
          Skel.Ordered rest (results + mid.length) hi
    | _, .cases (mid := mid) _ _ _ _ arms results rest, lo, hi =>
        SkelArms.Ordered arms lo results ∧ Skel.Ordered rest (results + mid.length) hi
    | _, .loop (carried := carried) (each := each) _ _ _ _ inputs body results rest, lo, hi =>
        lo ≤ inputs ∧ Skel.Ordered body (inputs + (carried.length + 1)) results ∧
          Skel.Ordered rest (results + (carried.length + each.length)) hi
    | _, .block (mid := mid) _ _ body results rest, lo, hi =>
        Skel.Ordered body lo results ∧ Skel.Ordered rest (results + mid.length) hi
    | _, .attempt (mid := mid) _ _ input body results rest, lo, hi =>
        lo ≤ input ∧ Skel.Ordered body (input + 1) results ∧ Skel.Ordered rest (results + mid.length) hi
  /-- The leaves of the arms of a skeleton are made in order from `lo` on and are below `hi`, each
  arm's above its input. -/
  def SkelArms.Ordered : {mid payloads : List D.Ty} → SkelArms D mid payloads → Nat → Nat → Prop
    | _, _, .nil, lo, hi => lo ≤ hi
    | _, _, .cons input arm rest, lo, hi =>
        lo ≤ input ∧ Skel.Ordered arm (input + 1) hi ∧ SkelArms.Ordered rest lo hi
end

mutual
  /-- Leaves made in order are from their lower bound to their upper bound. -/
  theorem Skel.Ordered.le : ∀ {outs : List D.Ty} {skel : Skel D outs} {lo hi : Nat},
      Skel.Ordered skel lo hi → lo ≤ hi
    | _, .ret _, _, _, h => h
    | _, .effect _ _ _ _ rest, _, _, h => by
        have := h.1
        have := Skel.Ordered.le (skel := rest) h.2
        omega
    | _, .guard _ _ _ _ _ rest, _, _, h => Skel.Ordered.le (skel := rest) h
    | _, .choose _ _ _ _ onTrue _ _ rest, _, _, h => by
        have := Skel.Ordered.le (skel := onTrue) h.1
        have := Skel.Ordered.le (skel := rest) h.2.2
        omega
    | _, .cases _ _ _ _ arms _ rest, _, _, h => by
        have := SkelArms.Ordered.le (arms := arms) h.1
        have := Skel.Ordered.le (skel := rest) h.2
        omega
    | _, .loop _ _ _ _ _ body _ rest, _, _, h => by
        have := h.1
        have := Skel.Ordered.le (skel := body) h.2.1
        have := Skel.Ordered.le (skel := rest) h.2.2
        omega
    | _, .block _ _ body _ rest, _, _, h => by
        have := Skel.Ordered.le (skel := body) h.1
        have := Skel.Ordered.le (skel := rest) h.2
        omega
    | _, .attempt _ _ _ body _ rest, _, _, h => by
        have := h.1
        have := Skel.Ordered.le (skel := body) h.2.1
        have := Skel.Ordered.le (skel := rest) h.2.2
        omega
  /-- Leaves of arms made in order are from their lower bound to their upper bound. -/
  theorem SkelArms.Ordered.le : ∀ {mid payloads : List D.Ty} {arms : SkelArms D mid payloads}
      {lo hi : Nat}, SkelArms.Ordered arms lo hi → lo ≤ hi
    | _, _, .nil, _, _, h => h
    | _, _, .cons _ _ rest, _, _, h => SkelArms.Ordered.le (arms := rest) h.2.2
end

mutual
  /-- Leaves made in order from a number on are made in order from every smaller number on. -/
  theorem Skel.Ordered.low : ∀ {outs : List D.Ty} {skel : Skel D outs} {lo lo' hi : Nat},
      Skel.Ordered skel lo hi → lo' ≤ lo → Skel.Ordered skel lo' hi
    | _, .ret _, _, _, _, h, le => Nat.le_trans le h
    | _, .effect _ _ _ _ _, _, _, _, h, le => ⟨Nat.le_trans le h.1, h.2⟩
    | _, .guard _ _ _ _ _ rest, _, _, _, h, le => Skel.Ordered.low (skel := rest) h le
    | _, .choose _ _ _ _ onTrue onFalse _ _, _, _, _, h, le =>
        ⟨Skel.Ordered.low (skel := onTrue) h.1 le, Skel.Ordered.low (skel := onFalse) h.2.1 le,
          h.2.2⟩
    | _, .cases _ _ _ _ arms _ _, _, _, _, h, le => ⟨SkelArms.Ordered.low (arms := arms) h.1 le, h.2⟩
    | _, .loop _ _ _ _ _ _ _ _, _, _, _, h, le => ⟨Nat.le_trans le h.1, h.2⟩
    | _, .block _ _ body _ _, _, _, _, h, le => ⟨Skel.Ordered.low (skel := body) h.1 le, h.2⟩
    | _, .attempt _ _ _ _ _ _, _, _, _, h, le => ⟨Nat.le_trans le h.1, h.2⟩
  /-- Leaves of arms made in order from a number on are made in order from every smaller number
  on. -/
  theorem SkelArms.Ordered.low : ∀ {mid payloads : List D.Ty} {arms : SkelArms D mid payloads}
      {lo lo' hi : Nat}, SkelArms.Ordered arms lo hi → lo' ≤ lo → SkelArms.Ordered arms lo' hi
    | _, _, .nil, _, _, _, h, le => Nat.le_trans le h
    | _, _, .cons _ _ rest, _, _, _, h, le =>
        ⟨Nat.le_trans le h.1, h.2.1, SkelArms.Ordered.low (arms := rest) h.2.2 le⟩
end

mutual
  /-- Leaves made in order below a number are made in order below every larger number. -/
  theorem Skel.Ordered.high : ∀ {outs : List D.Ty} {skel : Skel D outs} {lo hi hi' : Nat},
      Skel.Ordered skel lo hi → hi ≤ hi' → Skel.Ordered skel lo hi'
    | _, .ret _, _, _, _, h, le => Nat.le_trans h le
    | _, .effect _ _ _ _ rest, _, _, _, h, le => ⟨h.1, Skel.Ordered.high (skel := rest) h.2 le⟩
    | _, .guard _ _ _ _ _ rest, _, _, _, h, le => Skel.Ordered.high (skel := rest) h le
    | _, .choose _ _ _ _ _ _ _ rest, _, _, _, h, le =>
        ⟨h.1, h.2.1, Skel.Ordered.high (skel := rest) h.2.2 le⟩
    | _, .cases _ _ _ _ _ _ rest, _, _, _, h, le => ⟨h.1, Skel.Ordered.high (skel := rest) h.2 le⟩
    | _, .loop _ _ _ _ _ _ _ rest, _, _, _, h, le =>
        ⟨h.1, h.2.1, Skel.Ordered.high (skel := rest) h.2.2 le⟩
    | _, .block _ _ _ _ rest, _, _, _, h, le => ⟨h.1, Skel.Ordered.high (skel := rest) h.2 le⟩
    | _, .attempt _ _ _ _ _ rest, _, _, _, h, le =>
        ⟨h.1, h.2.1, Skel.Ordered.high (skel := rest) h.2.2 le⟩
  /-- Leaves of arms made in order below a number are made in order below every larger number. -/
  theorem SkelArms.Ordered.high : ∀ {mid payloads : List D.Ty} {arms : SkelArms D mid payloads}
      {lo hi hi' : Nat}, SkelArms.Ordered arms lo hi → hi ≤ hi' → SkelArms.Ordered arms lo hi'
    | _, _, .nil, _, _, _, h, le => Nat.le_trans h le
    | _, _, .cons _ arm rest, _, _, _, h, le =>
        ⟨h.1, Skel.Ordered.high (skel := arm) h.2.1 le, SkelArms.Ordered.high (arms := rest) h.2.2 le⟩
end

mutual
  /-- Leaves made in order below a number are below it. -/
  theorem Skel.Ordered.below : ∀ {outs : List D.Ty} {skel : Skel D outs} {lo hi : Nat},
      Skel.Ordered skel lo hi → skel.Below hi
    | _, .ret _, _, _, _ => trivial
    | _, .effect _ _ _ _ rest, _, _, h =>
        ⟨Skel.Ordered.le (skel := rest) h.2, Skel.Ordered.below (skel := rest) h.2⟩
    | _, .guard _ _ _ _ _ rest, _, _, h => Skel.Ordered.below (skel := rest) h
    | _, .choose _ _ _ _ onTrue onFalse _ rest, _, _, h =>
        have r := Skel.Ordered.le (skel := rest) h.2.2
        ⟨(Skel.Ordered.below (skel := onTrue) h.1).mono (by omega),
          (Skel.Ordered.below (skel := onFalse) h.2.1).mono (by omega), r,
          Skel.Ordered.below (skel := rest) h.2.2⟩
    | _, .cases _ _ _ _ arms _ rest, _, _, h =>
        have r := Skel.Ordered.le (skel := rest) h.2
        ⟨(SkelArms.Ordered.below (arms := arms) h.1).mono (by omega), r,
          Skel.Ordered.below (skel := rest) h.2⟩
    | _, .loop _ _ _ _ _ body _ rest, _, _, h =>
        have b := Skel.Ordered.le (skel := body) h.2.1
        have r := Skel.Ordered.le (skel := rest) h.2.2
        ⟨by omega, (Skel.Ordered.below (skel := body) h.2.1).mono (by omega), r,
          Skel.Ordered.below (skel := rest) h.2.2⟩
    | _, .block _ _ body _ rest, _, _, h =>
        have r := Skel.Ordered.le (skel := rest) h.2
        ⟨(Skel.Ordered.below (skel := body) h.1).mono (by omega), r,
          Skel.Ordered.below (skel := rest) h.2⟩
    | _, .attempt _ _ _ body _ rest, _, _, h =>
        have b := Skel.Ordered.le (skel := body) h.2.1
        have r := Skel.Ordered.le (skel := rest) h.2.2
        ⟨by omega, (Skel.Ordered.below (skel := body) h.2.1).mono (by omega), r,
          Skel.Ordered.below (skel := rest) h.2.2⟩
  /-- Leaves of arms made in order below a number are below it. -/
  theorem SkelArms.Ordered.below : ∀ {mid payloads : List D.Ty} {arms : SkelArms D mid payloads}
      {lo hi : Nat}, SkelArms.Ordered arms lo hi → arms.Below hi
    | _, _, .nil, _, _, _ => trivial
    | _, _, .cons _ arm rest, _, _, h =>
        ⟨Nat.le_trans (Nat.succ_le_succ (Nat.le_refl _)) (Skel.Ordered.le (skel := arm) h.2.1),
          Skel.Ordered.below (skel := arm) h.2.1, SkelArms.Ordered.below (arms := rest) h.2.2⟩
end

mutual
  /-- Leaves made in order from a number on are made in order from it as following a skeleton
  asks (`Skel.Fresh`). -/
  theorem Skel.Ordered.fresh : ∀ {outs : List D.Ty} {skel : Skel D outs} {lo hi : Nat},
      Skel.Ordered skel lo hi → skel.Fresh lo
    | _, .ret _, _, _, _ => trivial
    | _, .effect _ _ _ _ rest, _, _, h => ⟨h.1, Skel.Ordered.fresh (skel := rest) h.2⟩
    | _, .guard _ _ _ _ _ rest, _, _, h => Skel.Ordered.fresh (skel := rest) h
    | _, .choose _ _ _ _ onTrue onFalse _ rest, _, _, h =>
        ⟨Skel.Ordered.fresh (skel := onTrue) h.1, Skel.Ordered.fresh (skel := onFalse) h.2.1,
          Skel.Ordered.le (skel := onTrue) h.1, Skel.Ordered.fresh (skel := rest) h.2.2⟩
    | _, .cases _ _ _ _ arms _ rest, _, _, h =>
        ⟨SkelArms.Ordered.fresh (arms := arms) h.1, SkelArms.Ordered.le (arms := arms) h.1,
          Skel.Ordered.fresh (skel := rest) h.2⟩
    | _, .loop _ _ _ _ _ body _ rest, _, _, h =>
        have b := Skel.Ordered.le (skel := body) h.2.1
        ⟨h.1, Skel.Ordered.fresh (skel := body) h.2.1, by have := h.1; omega,
          Skel.Ordered.fresh (skel := rest) h.2.2⟩
    | _, .block _ _ body _ rest, _, _, h =>
        ⟨Skel.Ordered.fresh (skel := body) h.1, Skel.Ordered.le (skel := body) h.1,
          Skel.Ordered.fresh (skel := rest) h.2⟩
    | _, .attempt _ _ _ body _ rest, _, _, h =>
        have b := Skel.Ordered.le (skel := body) h.2.1
        ⟨h.1, Skel.Ordered.fresh (skel := body) h.2.1, by have := h.1; omega,
          Skel.Ordered.fresh (skel := rest) h.2.2⟩
  /-- Leaves of arms made in order from a number on are made in order from it as following a
  skeleton asks (`SkelArms.Fresh`). -/
  theorem SkelArms.Ordered.fresh : ∀ {mid payloads : List D.Ty} {arms : SkelArms D mid payloads}
      {lo hi : Nat}, SkelArms.Ordered arms lo hi → arms.Fresh lo
    | _, _, .nil, _, _, _ => trivial
    | _, _, .cons _ arm rest, _, _, h =>
        ⟨h.1, Skel.Ordered.fresh (skel := arm) h.2.1, SkelArms.Ordered.fresh (arms := rest) h.2.2⟩
end

end

/-! ## The places that differ -/

section
variable {D : Dialect} {Raw : Type}

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

/-- A state with another table adds no place that differs. -/
theorem AddsPlaces.with_st {T : Type} (s : State T Raw) (st : St T Raw) :
    AddsPlaces s { s with st := st } := AddsPlaces.refl _

/-- The places that a state added to another are none when the second has none: the first has
none either. -/
theorem AddsPlaces.none_before {T : Type} {s s' : State T Raw} (adds : AddsPlaces s s')
    (none : s'.differs = []) : s.differs = [] := by
  obtain ⟨new, e⟩ := adds
  rw [none] at e
  exact (List.append_eq_nil_iff.mp e.symm).2

/-- A place where the term differs is added only when a skeleton is followed and its entry was not
found; the table, the identifiers, the refusals and the bounds stay. -/
theorem miss_st {T : Type} (place : Place) (following found : Bool) (s : State T Raw) :
    (miss place following found s).st = s.st := by
  unfold miss
  split <;> rfl

/-- A place that is missed is added, at most. -/
theorem miss_differs {T : Type} (place : Place) (following found : Bool) (s : State T Raw) :
    AddsPlaces s (miss place following found s) := by
  unfold miss
  split
  · exact ⟨[place], rfl⟩
  · exact AddsPlaces.refl s

/-- Where the entry is found, no place is added. -/
theorem miss_found {T : Type} (place : Place) (following : Bool) (s : State T Raw) :
    miss place following true s = s := by
  unfold miss
  simp

/-- Where no skeleton is followed, no place is added. -/
theorem miss_free {T : Type} (place : Place) (found : Bool) (s : State T Raw) :
    miss place false found s = s := by
  unfold miss
  simp

/-- Where a skeleton is followed and its entry is not found, a place is added. -/
theorem miss_lost {T : Type} (place : Place) (s : State T Raw) :
    (miss place true false s).differs = place :: s.differs := by
  unfold miss
  simp

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

/-- A walk that follows a skeleton and adds no place that differs found the entry of each kept
instruction. -/
theorem found_of_differs {s s' : State D.Ty Raw} {place : Place} {found : Bool}
    (adds : AddsPlaces (miss place true found s) s') (same : s'.differs = s.differs) :
    found = true := by
  cases found with
  | true => rfl
  | false =>
      obtain ⟨n, e⟩ := adds
      rw [miss_lost, same] at e
      have := congrArg List.length e
      simp only [List.length_append, List.length_cons] at this
      omega

/-- The leaves of a followed entry are the entry's. -/
theorem leaves_some {T : Type} (lo count : Nat) (s : State T Raw) :
    leaves (some lo) count s = (List.range' lo count, s) := rfl

/-- Without a followed entry, the leaves are new identifiers. -/
theorem leaves_none {T : Type} (count : Nat) (s : State T Raw) :
    leaves none count s = ((fresh count s.st).1, { s with st := (fresh count s.st).2 }) := rfl

/-- The leaves of an entry keep the places that differ. -/
theorem leaves_differs {T : Type} (followed : Option Nat) (count : Nat) (s : State T Raw) :
    (leaves followed count s).2.differs = s.differs := by
  cases followed <;> rfl

/-- Leaves add no place that differs. -/
theorem leaves_adds {T : Type} (followed : Option Nat) (count : Nat) (s : State T Raw) :
    AddsPlaces s (leaves followed count s).2 :=
  ⟨[], leaves_differs followed count s⟩

/-- What follows the leaves of an entry adds places that differ to those of the state before the
leaves. -/
theorem adds_after_leaves {T : Type} {s' : State T Raw} {followed : Option Nat} {count : Nat}
    {s : State T Raw} (adds : AddsPlaces (leaves followed count s).2 s') : AddsPlaces s s' :=
  (leaves_adds followed count s).trans adds

end

/-! ## What the walk adds to the state -/

section
variable {D : Dialect} {Raw : Type} (definition : Key) (role : Option Role)

/-- What a step of the walk adds to the state: refusals, bounds at the addresses, and places where
the term differs, each before what was there. -/
def Adds (addresses : List (List (Key × Nat) × Key)) (s s' : State D.Ty Raw) : Prop :=
  (∃ new, s'.st.refusals = new ++ s.st.refusals) ∧
    (∃ new, s'.st.bounds = new ++ s.st.bounds ∧ BoundsAt definition role addresses new) ∧
    AddsPlaces s s'

variable {definition role}

theorem Adds.refl (addresses : List (List (Key × Nat) × Key)) (s : State D.Ty Raw) :
    Adds definition role addresses s s :=
  ⟨⟨[], rfl⟩, ⟨[], rfl, fun _ m => nomatch m⟩, ⟨[], rfl⟩⟩

theorem Adds.trans {A B C : List (List (Key × Nat) × Key)} {s s' s'' : State D.Ty Raw}
    (first : Adds definition role A s s') (second : Adds definition role B s' s'')
    (subA : ∀ x, x ∈ A → x ∈ C) (subB : ∀ x, x ∈ B → x ∈ C) :
    Adds definition role C s s'' := by
  obtain ⟨⟨r1, e1⟩, ⟨b1, f1, at1⟩, ⟨d1, g1⟩⟩ := first
  obtain ⟨⟨r2, e2⟩, ⟨b2, f2, at2⟩, ⟨d2, g2⟩⟩ := second
  refine ⟨⟨r2 ++ r1, by rw [e2, e1, List.append_assoc]⟩,
    ⟨b2 ++ b1, by rw [f2, f1, List.append_assoc], fun q m => ?_⟩,
    ⟨d2 ++ d1, by rw [g2, g1, List.append_assoc]⟩⟩
  rcases List.mem_append.mp m with m | m
  · obtain ⟨bl, key, eq, mem⟩ := at2 q m
    exact ⟨bl, key, eq, subB _ mem⟩
  · obtain ⟨bl, key, eq, mem⟩ := at1 q m
    exact ⟨bl, key, eq, subA _ mem⟩

/-- A step that keeps the bounds and the places, and adds refusals, adds to the state. -/
theorem Adds.of_refusals {A : List (List (Key × Nat) × Key)} {s s' : State D.Ty Raw}
    (refusals : ∃ new, s'.st.refusals = new ++ s.st.refusals) (bounds : s'.st.bounds = s.st.bounds)
    (differs : s'.differs = s.differs) : Adds definition role A s s' :=
  ⟨refusals, ⟨[], by rw [bounds]; rfl, fun _ m => nomatch m⟩, ⟨[], by rw [differs]; rfl⟩⟩

theorem Adds.miss (A : List (List (Key × Nat) × Key)) (place : Place) (following found : Bool)
    (s : State D.Ty Raw) : Adds definition role A s (miss place following found s) := by
  exact ⟨⟨[], by rw [miss_st]; rfl⟩, ⟨[], by rw [miss_st]; rfl, fun _ m => nomatch m⟩,
    miss_differs place following found s⟩

theorem Adds.leaves (A : List (List (Key × Nat) × Key)) (followed : Option Nat) (count : Nat)
    (s : State D.Ty Raw) : Adds definition role A s (leaves followed count s).2 := by
  cases followed
  · exact Adds.of_refusals ⟨[], rfl⟩ rfl rfl
  · exact Adds.refl A s

/-- Deciding the requirements of an application adds refusals, and keeps the bounds and the
places. -/
theorem Adds.requirements [DecidableEq Raw] (A : List (List (Key × Nat) × Key))
    (ops : OpFacts Raw) (k : Known) (place : Place) (written : Raw) (argIds : List Nat)
    (reqs : List (Requirement Raw)) (s : State D.Ty Raw) :
    Adds definition role A s
      { s with st := checkRequirements ops k place written argIds reqs s.st } :=
  Adds.of_refusals (checkRequirements_state ops k place written argIds reqs s.st).1
    (checkRequirements_state ops k place written argIds reqs s.st).2 rfl

end

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : FactRules D Raw)

/-- A value keeps the refusals and the bounds. -/
theorem valueStep_state (written : Raw) (res : List D.Ty) (argIds : List Nat) (k : Known)
    (st : St D.Ty Raw) :
    (valueStep rules written res argIds k st).2.2.refusals = st.refusals ∧
      (valueStep rules written res argIds k st).2.2.bounds = st.bounds := by
  simp only [valueStep]
  obtain ⟨r1, b1⟩ := share_state written (rules.values.order written argIds) res.length st
  obtain ⟨r2, b2⟩ := learnRequirements_state rules.ops _ (rules.ops.ensures written) _
    (share written (rules.values.order written argIds) res.length st).2
  exact ⟨r2.trans r1, b2.trans b1⟩

/-- An operation kept in order, once its results have their identifiers, keeps the refusals and
the bounds. -/
theorem effectStep_state (written : Raw) (res : List D.Ty) (argIds made : List Nat) (k : Known)
    (st : St D.Ty Raw) :
    (effectStep rules written res argIds made k st).2.refusals = st.refusals ∧
      (effectStep rules written res argIds made k st).2.bounds = st.bounds :=
  learnRequirements_state rules.ops _ _ _ st

/-- What an operation kept in order learns once its results have their identifiers adds nothing
to the state. -/
theorem Adds.effect {definition : Key} {role : Option Role} (A : List (List (Key × Nat) × Key))
    (written : Raw) (res : List D.Ty) (argIds made : List Nat) (k : Known) (s : State D.Ty Raw) :
    Adds definition role A s
      { s with st := (effectStep rules written res argIds made k s.st).2 } := by
  obtain ⟨r, b⟩ := effectStep_state rules written res argIds made k s.st
  exact Adds.of_refusals ⟨[], by rw [r]; rfl⟩ b rfl

variable (checks : SkelRules D) (definition : Key) (role : Option Role)

omit [DecidableEq Raw] in
theorem bounds_at_loop {blocks : List (Key × Nat)} {key : Key} {k : Known} {ids : Ctx Nat}
    {w : D.Who} {Γ : Ctx D.Ty} {times : Times D w Γ} {A : List (List (Key × Nat) × Key)}
    (here : (blocks, key) ∈ A) (s : State D.Ty Raw) :
    Adds definition role A s
      { s with st := recordBound ⟨definition, blocks, some key, role⟩ k ids s.st times } := by
  obtain ⟨_, _, refs, new, e, at_⟩ :=
    recordBound_state (D := D) ⟨definition, blocks, some key, role⟩ k ids s.st times
  exact ⟨⟨[], by rw [refs]; rfl⟩, ⟨new, e, fun q m => ⟨blocks, key, at_ q m, here⟩⟩, ⟨[], rfl⟩⟩

mutual
  /-- **What the walk adds.** Whatever skeleton it follows, the walk adds refusals, bounds at the
  addresses of the loops of the term, and places that differ. -/
  theorem walk_adds (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (followed : Option (Skel D outs))
        (ids : Ctx Nat) (k : Known) (s : State D.Ty Raw),
        Adds definition role (t.addresses blocks) s
          (walk rules checks definition role blocks t followed ids k s).state
    | _, _, .ret _, followed, ids, k, s => by
        simp only [walk]
        exact Adds.miss _ _ _ _ s
    | _, _, .op (res := res) key o args results rest, followed, ids, k, s => by
        have checked := Adds.requirements (definition := definition) (role := role) [] rules.ops k
          ⟨definition, blocks, some key, role⟩ (rules.written o) (idsOf ids args)
          (rules.ops.requires (rules.written o)) s
        cases hs : rules.shared o with
        | true =>
            simp only [walk, hs]
            obtain ⟨r, b⟩ := valueStep_state rules (rules.written o) res (idsOf ids args) k
              (checkRequirements rules.ops k ⟨definition, blocks, some key, role⟩ (rules.written o)
                (idsOf ids args) (rules.ops.requires (rules.written o)) s.st)
            refine Adds.trans (A := []) ?_ (walk_adds blocks rest _ _ _ _) (fun _ m => nomatch m)
              (fun _ m => List.mem_cons_of_mem _ m)
            exact checked.trans (Adds.of_refusals ⟨[], by rw [r]; rfl⟩ b rfl) (fun _ m => m)
              (fun _ m => m)
        | false =>
            simp only [walk, hs]
            refine Adds.trans (A := []) ?_ (walk_adds blocks rest _ _ _ _) (fun _ m => nomatch m)
              (fun _ m => List.mem_cons_of_mem _ m)
            exact checked.trans (((Adds.miss [] _ _ _ _).trans (Adds.leaves [] _ _ _)
              (fun _ m => m) (fun _ m => m)).trans (Adds.effect rules [] _ _ _ _ _ _)
              (fun _ m => m) (fun _ m => m)) (fun _ m => m) (fun _ m => m)
    | _, _, .guard key _ c _ _ rest, followed, ids, k, s => by
        simp only [walk]
        exact (Adds.miss [] _ _ _ s).trans (walk_adds blocks rest _ _ _ _) (fun _ m => nomatch m)
          (fun _ m => List.mem_cons_of_mem _ m)
    | _, _, .choose key _ c _ _ onTrue onFalse results rest, followed, ids, k, s => by
        simp only [walk]
        refine Adds.trans (A := onTrue.addresses blocks ++ onFalse.addresses blocks) ?_
          (walk_adds blocks rest _ _ _ _) ?_ ?_
        · refine Adds.trans (B := []) ?_ (Adds.leaves [] _ _ _) (fun _ m => m)
            (fun _ m => nomatch m)
          refine Adds.trans (A := onTrue.addresses blocks) ?_ (walk_adds blocks onFalse _ _ _ _)
            (fun _ m => List.mem_append_left _ m) (fun _ m => List.mem_append_right _ m)
          exact (Adds.miss [] _ _ _ s).trans (walk_adds blocks onTrue _ _ _ _)
            (fun _ m => nomatch m) (fun _ m => m)
        all_goals intro x m; simp only [Term.addresses, List.mem_cons, List.mem_append] at m ⊢
        · exact Or.inr (Or.inl m)
        · exact Or.inr (Or.inr m)
    | _, _, .cases key _ _ _ _ arms results rest, followed, ids, k, s => by
        simp only [walk]
        refine Adds.trans (A := Arms.addresses blocks arms) ?_ (walk_adds blocks rest _ _ _ _)
          (fun _ m => List.mem_cons_of_mem _ (List.mem_append_left _ m))
          (fun _ m => List.mem_cons_of_mem _ (List.mem_append_right _ m))
        refine Adds.trans (B := []) ?_ (Adds.leaves [] _ _ _) (fun _ m => m) (fun _ m => nomatch m)
        exact (Adds.miss [] _ _ _ s).trans (walkArms_adds blocks arms _ _ _ _)
          (fun _ m => nomatch m) (fun _ m => m)
    | _, _, .loop key _ times _ init inputs body results rest, followed, ids, k, s => by
        simp only [walk]
        refine Adds.trans (A := (blocks, key) :: body.addresses blocks) ?_
          (walk_adds blocks rest _ _ _ _) ?_ ?_
        · refine Adds.trans (B := []) ?_ (Adds.leaves [] _ _ _) (fun _ m => m)
            (fun _ m => nomatch m)
          refine Adds.trans (A := body.addresses blocks) ?_
            (bounds_at_loop definition role List.mem_cons_self _)
            (fun _ m => List.mem_cons_of_mem _ m) (fun _ m => m)
          refine Adds.trans (A := []) ?_ (walk_adds blocks body _ _ _ _) (fun _ m => nomatch m)
            (fun _ m => m)
          exact (Adds.miss [] _ _ _ s).trans (Adds.leaves [] _ _ _) (fun _ m => m) (fun _ m => m)
        all_goals intro x m; simp only [Term.addresses, List.mem_cons, List.mem_append] at m ⊢
        · rcases m with m | m
          · exact Or.inl m
          · exact Or.inr (Or.inl m)
        · exact Or.inr (Or.inr m)
    | _, _, .block key number body results rest, followed, ids, k, s => by
        simp only [walk]
        refine Adds.trans (A := body.addresses (blocks ++ [(key, number)])) ?_
          (walk_adds blocks rest _ _ _ _) (fun _ m => List.mem_append_left _ m)
          (fun _ m => List.mem_append_right _ m)
        refine Adds.trans (B := []) ?_ (Adds.leaves [] _ _ _) (fun _ m => m) (fun _ m => nomatch m)
        exact (Adds.miss [] _ _ _ s).trans (walk_adds (blocks ++ [(key, number)]) body _ _ _ _)
          (fun _ m => nomatch m) (fun _ m => m)
    | _, _, .attempt key _ _ inputs body results rest, followed, ids, k, s => by
        simp only [walk]
        refine Adds.trans (A := body.addresses blocks) ?_ (walk_adds blocks rest _ _ _ _)
          (fun _ m => List.mem_cons_of_mem _ (List.mem_append_left _ m))
          (fun _ m => List.mem_cons_of_mem _ (List.mem_append_right _ m))
        refine Adds.trans (B := []) ?_ (Adds.leaves [] _ _ _) (fun _ m => m) (fun _ m => nomatch m)
        refine Adds.trans (A := []) ?_ (walk_adds blocks body _ _ _ _) (fun _ m => nomatch m)
          (fun _ m => m)
        exact (Adds.miss [] _ _ _ s).trans (Adds.leaves [] _ _ _) (fun _ m => m) (fun _ m => m)
  /-- What the walk of arms adds, as `walk_adds`. -/
  theorem walkArms_adds (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads)
        (followed : Option (SkelArms D mid payloads)) (ids : Ctx Nat) (k : Known)
        (s : State D.Ty Raw),
        Adds definition role (Arms.addresses blocks arms) s
          (walkArms rules checks definition role blocks arms followed ids k s).state
    | _, _, _, .nil, _, _, _, s => by
        simp only [walkArms]
        exact Adds.refl _ s
    | _, _, _, .cons inputs arm rest, followed, ids, k, s => by
        simp only [walkArms]
        refine Adds.trans (A := arm.addresses blocks) ?_ (walkArms_adds blocks rest _ _ _ _)
          (fun _ m => List.mem_append_left _ m) (fun _ m => List.mem_append_right _ m)
        exact (Adds.leaves [] _ _ s).trans (walk_adds blocks arm _ _ _ _) (fun _ m => nomatch m)
          (fun _ m => m)
end

end

/-! ## The entry that a kept instruction matches -/

section
variable {D : Dialect} (checks : SkelRules D)

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

/-- No arm is found where no arms are followed. -/
theorem armEntry_none {mid payloads : List D.Ty} {payload : D.Ty} :
    armEntry (none : Option (SkelArms D mid (payload :: payloads))) = none := rfl

/-- Without a skeleton to follow, the skeleton of a region is the one built. -/
theorem kept_none {outs : List D.Ty} (built : Skel D outs) : kept none built = built := rfl

end

/-! ## The walk builds above its state -/

section
variable {D : Dialect}

/-- The leaves of the skeleton that is followed, if one is, are below a number. -/
def FollowedBelow {outs : List D.Ty} : Option (Skel D outs) → Nat → Prop
  | none, _ => True
  | some skel, next => skel.Below next

/-- The leaves of the arms that are followed, if some are, are below a number. -/
def FollowedArmsBelow {mid payloads : List D.Ty} : Option (SkelArms D mid payloads) → Nat → Prop
  | none, _ => True
  | some arms, next => arms.Below next

theorem FollowedBelow.mono {outs : List D.Ty} {followed : Option (Skel D outs)} {n n' : Nat}
    (h : FollowedBelow followed n) (le : n ≤ n') : FollowedBelow followed n' := by
  cases followed with
  | none => trivial
  | some skel => exact Skel.Below.mono (skel := skel) h le

theorem FollowedArmsBelow.mono {mid payloads : List D.Ty}
    {followed : Option (SkelArms D mid payloads)} {n n' : Nat} (h : FollowedArmsBelow followed n)
    (le : n ≤ n') : FollowedArmsBelow followed n' := by
  cases followed with
  | none => trivial
  | some arms => exact SkelArms.Below.mono (arms := arms) h le

variable (checks : SkelRules D)

theorem effectEntry_below {outs ins res : List D.Ty} {key : Key} {o : D.Op ins res}
    {operands : List Nat} {followed : Option (Skel D outs)} {n : Nat}
    (below : FollowedBelow followed n) :
    (∀ lo, (effectEntry checks key o operands followed).map (·.1) = some lo →
      lo + res.length ≤ n) ∧
      FollowedBelow ((effectEntry checks key o operands followed).map (·.2)) n := by
  cases hit : effectEntry checks key o operands followed with
  | none => simp [FollowedBelow]
  | some h =>
      obtain ⟨r, rest⟩ := h
      obtain ⟨_, _, rfl⟩ := effectEntry_hit checks hit
      refine ⟨fun lo e => ?_, below.2⟩
      simp only [Option.map_some, Option.some.injEq] at e
      subst e
      exact below.1

theorem guardEntry_below {outs : List D.Ty} {t : D.Ty} {key : Key} {w : D.Who} {condition : Nat}
    {why : Reason} {followed : Option (Skel D outs)} {n : Nat} (below : FollowedBelow followed n) :
    FollowedBelow (guardEntry checks (t := t) key w condition why followed) n := by
  cases hit : guardEntry checks (t := t) key w condition why followed with
  | none => trivial
  | some rest =>
      obtain ⟨_, rfl⟩ := guardEntry_hit checks hit
      exact below

theorem chooseEntry_below {outs mid : List D.Ty} {t : D.Ty} {key : Key} {w : D.Who}
    {condition : Nat} {followed : Option (Skel D outs)} {n : Nat}
    (below : FollowedBelow followed n) :
    FollowedBelow ((chooseEntry checks (mid := mid) (t := t) key w condition followed).map
        (·.1)) n ∧
      FollowedBelow ((chooseEntry checks (mid := mid) (t := t) key w condition followed).map
        (·.2.1)) n ∧
      (∀ lo, (chooseEntry checks (mid := mid) (t := t) key w condition followed).map
        (·.2.2.1) = some lo → lo + mid.length ≤ n) ∧
      FollowedBelow ((chooseEntry checks (mid := mid) (t := t) key w condition followed).map
        (·.2.2.2)) n := by
  cases hit : chooseEntry checks (mid := mid) (t := t) key w condition followed with
  | none => simp [FollowedBelow]
  | some h =>
      obtain ⟨a, b, r, rest⟩ := h
      obtain ⟨_, rfl⟩ := chooseEntry_hit checks hit
      refine ⟨below.1, below.2.1, fun lo e => ?_, below.2.2.2⟩
      simp only [Option.map_some, Option.some.injEq] at e
      subst e
      exact below.2.2.1

theorem casesEntry_below {outs mid payloads : List D.Ty} {t : D.Ty} {key : Key} {w : D.Who}
    {subject : Nat} {followed : Option (Skel D outs)} {n : Nat}
    (below : FollowedBelow followed n) :
    FollowedArmsBelow ((casesEntry checks (mid := mid) (t := t) (payloads := payloads) key w
        subject followed).map (·.1)) n ∧
      (∀ lo, (casesEntry checks (mid := mid) (t := t) (payloads := payloads) key w subject
        followed).map (·.2.1) = some lo → lo + mid.length ≤ n) ∧
      FollowedBelow ((casesEntry checks (mid := mid) (t := t) (payloads := payloads) key w subject
        followed).map (·.2.2)) n := by
  cases hit : casesEntry checks (mid := mid) (t := t) (payloads := payloads) key w subject
    followed with
  | none => simp [FollowedBelow, FollowedArmsBelow]
  | some h =>
      obtain ⟨a, r, rest⟩ := h
      obtain ⟨_, rfl⟩ := casesEntry_hit checks hit
      refine ⟨below.1, fun lo e => ?_, below.2.2⟩
      simp only [Option.map_some, Option.some.injEq] at e
      subst e
      exact below.2.1

theorem loopEntry_below {outs carried each : List D.Ty} {key : Key} {w : D.Who}
    {sameTimes : Count D w → Bool} {initial : List Nat} {followed : Option (Skel D outs)} {n : Nat}
    (below : FollowedBelow followed n) :
    (∀ lo, (loopEntry checks (carried := carried) (each := each) key w sameTimes initial
      followed).map (·.1) = some lo → lo + (carried.length + 1) ≤ n) ∧
      FollowedBelow ((loopEntry checks (carried := carried) (each := each) key w sameTimes initial
        followed).map (·.2.1)) n ∧
      (∀ lo, (loopEntry checks (carried := carried) (each := each) key w sameTimes initial
        followed).map (·.2.2.1) = some lo → lo + (carried.length + each.length) ≤ n) ∧
      FollowedBelow ((loopEntry checks (carried := carried) (each := each) key w sameTimes initial
        followed).map (·.2.2.2)) n := by
  cases hit : loopEntry checks (carried := carried) (each := each) key w sameTimes initial
    followed with
  | none => simp [FollowedBelow]
  | some h =>
      obtain ⟨i, b, r, rest⟩ := h
      obtain ⟨_, _, rfl⟩ := loopEntry_hit checks hit
      refine ⟨fun lo e => ?_, below.2.1, fun lo e => ?_, below.2.2.2⟩
      · simp only [Option.map_some, Option.some.injEq] at e
        subst e
        exact below.1
      · simp only [Option.map_some, Option.some.injEq] at e
        subst e
        exact below.2.2.1

theorem blockEntry_below {outs mid : List D.Ty} {key : Key} {number : Nat}
    {followed : Option (Skel D outs)} {n : Nat} (below : FollowedBelow followed n) :
    FollowedBelow ((blockEntry checks (mid := mid) key number followed).map (·.1)) n ∧
      (∀ lo, (blockEntry checks (mid := mid) key number followed).map (·.2.1) = some lo →
        lo + mid.length ≤ n) ∧
      FollowedBelow ((blockEntry checks (mid := mid) key number followed).map (·.2.2)) n := by
  cases hit : blockEntry checks (mid := mid) key number followed with
  | none => simp [FollowedBelow]
  | some h =>
      obtain ⟨b, r, rest⟩ := h
      obtain rfl := blockEntry_hit checks hit
      refine ⟨below.1, fun lo e => ?_, below.2.2⟩
      simp only [Option.map_some, Option.some.injEq] at e
      subst e
      exact below.2.1

theorem attemptEntry_below {outs mid : List D.Ty} {key : Key} {w : D.Who}
    {followed : Option (Skel D outs)} {n : Nat} (below : FollowedBelow followed n) :
    (∀ lo, (attemptEntry checks (mid := mid) key w followed).map (·.1) = some lo → lo + 1 ≤ n) ∧
      FollowedBelow ((attemptEntry checks (mid := mid) key w followed).map (·.2.1)) n ∧
      (∀ lo, (attemptEntry checks (mid := mid) key w followed).map (·.2.2.1) = some lo →
        lo + mid.length ≤ n) ∧
      FollowedBelow ((attemptEntry checks (mid := mid) key w followed).map (·.2.2.2)) n := by
  cases hit : attemptEntry checks (mid := mid) key w followed with
  | none => simp [FollowedBelow]
  | some h =>
      obtain ⟨i, b, r, rest⟩ := h
      obtain rfl := attemptEntry_hit checks hit
      refine ⟨fun lo e => ?_, below.2.1, fun lo e => ?_, below.2.2.2⟩
      · simp only [Option.map_some, Option.some.injEq] at e
        subst e
        exact below.1
      · simp only [Option.map_some, Option.some.injEq] at e
        subst e
        exact below.2.2.1

theorem armEntry_below {mid payloads : List D.Ty} {payload : D.Ty}
    {followed : Option (SkelArms D mid (payload :: payloads))} {n : Nat}
    (below : FollowedArmsBelow followed n) :
    (∀ lo, (armEntry followed).map (·.1) = some lo → lo + 1 ≤ n) ∧
      FollowedBelow ((armEntry followed).map (·.2.1)) n ∧
      FollowedArmsBelow ((armEntry followed).map (·.2.2)) n := by
  cases hit : armEntry followed with
  | none => simp [FollowedBelow, FollowedArmsBelow]
  | some h =>
      obtain ⟨i, a, rest⟩ := h
      obtain rfl := armEntry_hit hit
      refine ⟨fun lo e => ?_, below.2.1, below.2.2⟩
      simp only [Option.map_some, Option.some.injEq] at e
      subst e
      exact below.1

end

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : FactRules D Raw)

omit [DecidableEq Raw] in
/-- The leaves of an entry are new identifiers, or those of the entry that is followed, below the
next identifier: as many as asked, and the state stays well formed. -/
theorem leaves_fits {T : Type} (hit : Option Nat) (count : Nat) (s : State T Raw)
    (wf : Table.WF s.st.next s.st.table) (below : ∀ lo, hit = some lo → lo + count ≤ s.st.next) :
    Table.WF (leaves hit count s).2.st.next (leaves hit count s).2.st.table ∧
      St.Grows s.st (leaves hit count s).2.st ∧ (leaves hit count s).1.length = count ∧
      ∀ i, i ∈ (leaves hit count s).1 → i < (leaves hit count s).2.st.next := by
  cases hit with
  | none =>
      obtain ⟨wf', grows, lt⟩ := fresh_grows count s.st wf
      exact ⟨wf', grows, by simp [leaves, fresh], lt⟩
  | some lo =>
      refine ⟨wf, St.Grows.refl _, by simp [leaves], fun i m => ?_⟩
      simp only [leaves] at m ⊢
      have := mem_range'_bounds m
      have := below lo rfl
      omega

/-- A value builds above the state: the table stays well formed and grows, and its results are as
many as its types and below the next identifier. -/
theorem valueStep_grows (written : Raw) (res : List D.Ty) (argIds : List Nat) (k : Known)
    (st : St D.Ty Raw) (wf : Table.WF st.next st.table) (hlt : ∀ a, a ∈ argIds → a < st.next) :
    Table.WF (valueStep rules written res argIds k st).2.2.next
        (valueStep rules written res argIds k st).2.2.table ∧
      St.Grows st (valueStep rules written res argIds k st).2.2 ∧
      (∀ i, i ∈ (valueStep rules written res argIds k st).1 →
        i < (valueStep rules written res argIds k st).2.2.next) ∧
      (valueStep rules written res argIds k st).1.length = res.length := by
  simp only [valueStep]
  obtain ⟨wf2, g2, lt⟩ := share_grows written (rules.values.order written argIds) res.length _ wf
    (rules.values.order_lt hlt)
  obtain ⟨wf3, g3⟩ := learnRequirements_grows rules.ops _ (rules.ops.ensures written) _ _ wf2
    (fun a m => by
      rcases List.mem_append.mp m with m | m
      · exact Nat.lt_of_lt_of_le (hlt a m) g2.next
      · exact lt a m)
  exact ⟨wf3, g2.trans g3, fun i m => Nat.lt_of_lt_of_le (lt i m) g3.next, share_length _ _ _ _⟩

/-- An operation kept in order, once its results have their identifiers below the next, builds
above the state. -/
theorem effectStep_grows (written : Raw) (res : List D.Ty) (argIds made : List Nat) (k : Known)
    (st : St D.Ty Raw) (wf : Table.WF st.next st.table)
    (hlt : ∀ a, a ∈ argIds ++ made → a < st.next) :
    Table.WF (effectStep rules written res argIds made k st).2.next
        (effectStep rules written res argIds made k st).2.table ∧
      St.Grows st (effectStep rules written res argIds made k st).2 :=
  learnRequirements_grows rules.ops _ _ _ st wf hlt

variable (checks : SkelRules D) (definition : Key) (role : Option Role)

mutual
  /-- **The walk builds above its state.** From a well-formed state where every name in scope has
  an identifier below the next, and a followed skeleton, if any, whose leaves are below the next:
  the table stays well formed and grows, and the identifiers returned are below the next. -/
  theorem walk_grows (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (followed : Option (Skel D outs))
        (ids : Ctx Nat) (k : Known) (s : State D.Ty Raw),
        Scoped Γ ids s.st → FollowedBelow followed s.st.next →
        WellFormed (walk rules checks definition role blocks t followed ids k s).rets
            (walk rules checks definition role blocks t followed ids k s).state.st ∧
          St.Grows s.st (walk rules checks definition role blocks t followed ids k s).state.st
    | _, _, .ret xs, followed, ids, k, s, fits, _ => by
        simp only [walk, miss_st]
        exact ⟨⟨fits.1, idsOf_lt fits.2 xs⟩, St.Grows.refl _⟩
    | _, _, .op (res := res) key o args results rest, followed, ids, k, s, fits, below => by
        obtain ⟨wf₁, g₁⟩ := checkRequirements_grows rules.ops k ⟨definition, blocks, some key, role⟩
          (rules.written o) (idsOf ids args) (rules.ops.requires (rules.written o)) s.st fits.1
          (idsOf_lt fits.2 args)
        cases hs : rules.shared o with
        | true =>
            simp only [walk, hs]
            generalize checkRequirements rules.ops k ⟨definition, blocks, some key, role⟩
              (rules.written o) (idsOf ids args) (rules.ops.requires (rules.written o)) s.st = st₁
              at wf₁ g₁ ⊢
            obtain ⟨wf2, g2, lt2, len2⟩ := valueStep_grows rules (rules.written o) res
              (idsOf ids args) k st₁ wf₁
              (fun a m => Nat.lt_of_lt_of_le (idsOf_lt fits.2 args a m) g₁.next)
            generalize valueStep rules (rules.written o) res (idsOf ids args) k st₁ = step
              at wf2 g2 lt2 len2 ⊢
            obtain ⟨fits3, g3⟩ := walk_grows blocks rest followed (bindIds ids results step.1)
              step.2.1 { s with st := step.2.2 }
              ⟨wf2, (fits.2.mono (g₁.trans g2).next).bind results _ len2 lt2⟩
              (below.mono (g₁.trans g2).next)
            exact ⟨fits3, (g₁.trans g2).trans g3⟩
        | false =>
            simp only [walk, hs]
            generalize checkRequirements rules.ops k ⟨definition, blocks, some key, role⟩
              (rules.written o) (idsOf ids args) (rules.ops.requires (rules.written o)) s.st = st₁
              at wf₁ g₁ ⊢
            obtain ⟨atLeaves, belowRest⟩ :=
              effectEntry_below checks (key := key) (o := o) (operands := idsOf ids args)
                (below.mono g₁.next)
            generalize effectEntry checks key o (idsOf ids args) followed = hit
              at atLeaves belowRest ⊢
            have s1 := miss_st ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome
              { s with st := st₁ }
            generalize miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome
              { s with st := st₁ } = s₁ at s1 ⊢
            obtain ⟨wf2, g2, len2, lt2⟩ := leaves_fits (hit.map (·.1)) res.length s₁
              (by rw [s1]; exact wf₁) (by rw [s1]; exact atLeaves)
            rw [s1] at g2
            generalize leaves (hit.map (·.1)) res.length s₁ = made at wf2 g2 len2 lt2 ⊢
            obtain ⟨wf4, g4⟩ := effectStep_grows rules (rules.written o) res (idsOf ids args) made.1
              k made.2.st wf2 (fun a m => by
                rcases List.mem_append.mp m with m | m
                · exact Nat.lt_of_lt_of_le (idsOf_lt fits.2 args a m) (g₁.trans g2).next
                · exact lt2 a m)
            generalize effectStep rules (rules.written o) res (idsOf ids args) made.1 k made.2.st =
              learned at wf4 g4 ⊢
            obtain ⟨fits3, g3⟩ := walk_grows blocks rest (hit.map (·.2))
              (bindIds ids results made.1) learned.1 { made.2 with st := learned.2 }
              ⟨wf4, (fits.2.mono ((g₁.trans g2).trans g4).next).bind results _ len2
                (fun i m => Nat.lt_of_lt_of_le (lt2 i m) g4.next)⟩
              (belowRest.mono (g2.trans g4).next)
            exact ⟨fits3, ((g₁.trans g2).trans g4).trans g3⟩
    | _, _, .guard (t := t) key w c _ why rest, followed, ids, k, s, fits, below => by
        simp only [walk]
        have belowRest := guardEntry_below checks (t := t) (key := key) (w := w)
          (condition := idOf ids c.name) (why := why) below
        generalize guardEntry checks (t := t) key w (idOf ids c.name) why followed = hit
          at belowRest ⊢
        have s1 := miss_st ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s
        generalize miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s = s₁
          at s1 ⊢
        obtain ⟨fits2, g2⟩ := walk_grows blocks rest hit ids
          (assume rules.ops s.st.table s.st.next k (idOf ids c.name) true) s₁
          (by rw [s1]; exact fits) (by rw [s1]; exact belowRest)
        rw [s1] at g2
        exact ⟨fits2, g2⟩
    | _, _, .choose (mid := mid) (t := t) key w c _ _ onTrue onFalse results rest, followed, ids,
        k, s, fits, below => by
        simp only [walk]
        obtain ⟨belowTrue, belowFalse, atLeaves, belowRest⟩ :=
          chooseEntry_below checks (mid := mid) (t := t) (key := key) (w := w)
            (condition := idOf ids c.name) below
        generalize chooseEntry checks (mid := mid) (t := t) key w (idOf ids c.name) followed = hit
          at belowTrue belowFalse atLeaves belowRest ⊢
        have s1 := miss_st ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s
        generalize miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s = s₁
          at s1 ⊢
        obtain ⟨fa, ga⟩ := walk_grows blocks onTrue (hit.map (·.1)) ids
          (assume rules.ops s₁.st.table s₁.st.next k (idOf ids c.name) true) s₁
          (by rw [s1]; exact fits) (by rw [s1]; exact belowTrue)
        generalize walk rules checks definition role blocks onTrue (hit.map (·.1)) ids
          (assume rules.ops s₁.st.table s₁.st.next k (idOf ids c.name) true) s₁ = first
          at fa ga ⊢
        rw [s1] at ga
        obtain ⟨fb, gb⟩ := walk_grows blocks onFalse (hit.map (·.2.1)) ids
          (assume rules.ops first.state.st.table first.state.st.next k (idOf ids c.name) false)
          first.state ⟨fa.1, fits.2.mono ga.next⟩ (belowFalse.mono ga.next)
        generalize walk rules checks definition role blocks onFalse (hit.map (·.2.1)) ids
          (assume rules.ops first.state.st.table first.state.st.next k (idOf ids c.name) false)
          first.state = second at fb gb ⊢
        have up : s.st.next ≤ second.state.st.next := Nat.le_trans ga.next gb.next
        obtain ⟨wfm, gm, lenm, ltm⟩ := leaves_fits (hit.map (·.2.2.1)) mid.length second.state fb.1
          fun lo e => Nat.le_trans (atLeaves lo e) up
        obtain ⟨fr, gr⟩ := walk_grows blocks rest (hit.map (·.2.2.2))
          (bindIds ids results (leaves (hit.map (·.2.2.1)) mid.length second.state).1)
          ((afterChoice rules k (idOf ids c.name) first.region second.region
            (leaves (hit.map (·.2.2.1)) mid.length second.state).1 mid).enter rules mid)
          (leaves (hit.map (·.2.2.1)) mid.length second.state).2
          ⟨wfm, (fits.2.mono (Nat.le_trans up gm.next)).bind results _ lenm ltm⟩
          (belowRest.mono (Nat.le_trans up gm.next))
        exact ⟨fr, ga.trans (gb.trans (gm.trans gr))⟩
    | _, _, .cases (mid := mid) (t := t) (payloads := payloads) key w x _ _ arms results rest,
        followed, ids, k, s, fits, below => by
        simp only [walk]
        obtain ⟨belowArms, atLeaves, belowRest⟩ :=
          casesEntry_below checks (mid := mid) (t := t) (payloads := payloads) (key := key) (w := w)
            (subject := idOf ids x.name) below
        generalize casesEntry checks (mid := mid) (t := t) (payloads := payloads) key w
          (idOf ids x.name) followed = hit at belowArms atLeaves belowRest ⊢
        have s1 := miss_st ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s
        generalize miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s = s₁
          at s1 ⊢
        obtain ⟨_, fa, ga⟩ := walkArms_grows blocks arms (hit.map (·.1)) ids k s₁
          (by rw [s1]; exact fits) (by rw [s1]; exact belowArms)
        generalize walkArms rules checks definition role blocks arms (hit.map (·.1)) ids k s₁ =
          regions at fa ga ⊢
        rw [s1] at ga
        obtain ⟨wfm, gm, lenm, ltm⟩ := leaves_fits (hit.map (·.2.1)) mid.length regions.state fa.1
          fun lo e => Nat.le_trans (atLeaves lo e) ga.next
        obtain ⟨fr, gr⟩ := walk_grows blocks rest (hit.map (·.2.2))
          (bindIds ids results (leaves (hit.map (·.2.1)) mid.length regions.state).1)
          ((afterRegions rules regions.exits k
            (leaves (hit.map (·.2.1)) mid.length regions.state).1 mid 0).enter rules mid)
          (leaves (hit.map (·.2.1)) mid.length regions.state).2
          ⟨wfm, (fits.2.mono (Nat.le_trans ga.next gm.next)).bind results _ lenm ltm⟩
          (belowRest.mono (Nat.le_trans ga.next gm.next))
        exact ⟨fr, ga.trans (gm.trans gr)⟩
    | _, _, .loop (carried := carried) (each := each) key w times _ init inputs body results rest,
        followed, ids, k, s, fits, below => by
        simp only [walk]
        obtain ⟨atInputs, belowBody, atLeaves, belowRest⟩ :=
          loopEntry_below checks (carried := carried) (each := each) (key := key) (w := w)
            (sameTimes := fun count => times.follows checks ids count) (initial := idsOf ids init)
            below
        generalize loopEntry checks (carried := carried) (each := each) key w
          (fun count => times.follows checks ids count) (idsOf ids init) followed = hit
          at atInputs belowBody atLeaves belowRest ⊢
        have s1 := miss_st ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s
        generalize miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s = s₁
          at s1 ⊢
        obtain ⟨wfi, gi, leni, lti⟩ := leaves_fits (hit.map (·.1)) (carried.length + 1) s₁
          (by rw [s1]; exact fits.1) (by rw [s1]; exact atInputs)
        rw [s1] at gi
        generalize leaves (hit.map (·.1)) (carried.length + 1) s₁ = inBody at wfi gi leni lti ⊢
        obtain ⟨fb, gb⟩ := walk_grows blocks body (hit.map (·.2.1)) (bindIds ids inputs inBody.1)
          (bodyKnown rules k ids times (inBody.1.headD 0) inBody.1.tail carried) inBody.2
          ⟨wfi, (fits.2.mono gi.next).bind inputs _ leni lti⟩ (belowBody.mono gi.next)
        generalize walk rules checks definition role blocks body (hit.map (·.2.1))
          (bindIds ids inputs inBody.1)
          (bodyKnown rules k ids times (inBody.1.headD 0) inBody.1.tail carried) inBody.2 = e
          at fb gb ⊢
        obtain ⟨rbt, rbn, -, -⟩ :=
          recordBound_state (D := D) ⟨definition, blocks, some key, role⟩ k ids e.state.st times
        generalize recordBound ⟨definition, blocks, some key, role⟩ k ids e.state.st times = st₁
          at rbt rbn ⊢
        have g1 : St.Grows e.state.st st₁ :=
          ⟨by rw [rbn]; exact Nat.le_refl _, [], by rw [rbt]; rfl, fun _ m => nomatch m⟩
        have up : s.st.next ≤ e.state.st.next := Nat.le_trans gi.next gb.next
        obtain ⟨wfm, gm, lenm, ltm⟩ := leaves_fits (hit.map (·.2.2.1))
          (carried.length + each.length) { e.state with st := st₁ }
          (by simp only; rw [rbt, rbn]; exact fb.1)
          fun lo e' => by simp only; rw [rbn]; exact Nat.le_trans (atLeaves lo e') up
        have up2 := Nat.le_trans up (Nat.le_trans g1.next gm.next)
        obtain ⟨fr, gr⟩ := walk_grows blocks rest (hit.map (·.2.2.2))
          (bindIds ids results
            (leaves (hit.map (·.2.2.1)) (carried.length + each.length) { e.state with st := st₁ }).1)
          ((afterLoop rules e.region k (timesBound k ids times)
            (leaves (hit.map (·.2.2.1)) (carried.length + each.length)
              { e.state with st := st₁ }).1
            ((idsOf ids init).map k.rangeOf) inBody.1.tail e.rets
            (carried ++ each.map (D.collected times.size))).enter rules
            (carried ++ each.map (D.collected times.size)))
          (leaves (hit.map (·.2.2.1)) (carried.length + each.length) { e.state with st := st₁ }).2
          ⟨wfm, (fits.2.mono up2).bind results _ (by rw [lenm, List.length_append,
            List.length_map]) ltm⟩
          (belowRest.mono up2)
        exact ⟨fr, gi.trans (gb.trans (g1.trans (gm.trans gr)))⟩
    | _, _, .block (mid := mid) key number body results rest, followed, ids, k, s, fits, below => by
        simp only [walk]
        obtain ⟨belowBody, atLeaves, belowRest⟩ :=
          blockEntry_below checks (mid := mid) (key := key) (number := number) below
        generalize blockEntry checks (mid := mid) key number followed = hit
          at belowBody atLeaves belowRest ⊢
        have s1 := miss_st ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s
        generalize miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s = s₁
          at s1 ⊢
        obtain ⟨fb, gb⟩ := walk_grows (blocks ++ [(key, number)]) body (hit.map (·.1)) ids k s₁
          (by rw [s1]; exact fits) (by rw [s1]; exact belowBody)
        generalize walk rules checks definition role (blocks ++ [(key, number)]) body
          (hit.map (·.1)) ids k s₁ = e at fb gb ⊢
        rw [s1] at gb
        obtain ⟨wfm, gm, lenm, ltm⟩ := leaves_fits (hit.map (·.2.1)) mid.length e.state fb.1
          fun lo e' => Nat.le_trans (atLeaves lo e') gb.next
        obtain ⟨fr, gr⟩ := walk_grows blocks rest (hit.map (·.2.2))
          (bindIds ids results (leaves (hit.map (·.2.1)) mid.length e.state).1)
          ((afterRegions rules [e.region] k (leaves (hit.map (·.2.1)) mid.length e.state).1
            mid 0).enter rules mid)
          (leaves (hit.map (·.2.1)) mid.length e.state).2
          ⟨wfm, (fits.2.mono (Nat.le_trans gb.next gm.next)).bind results _ lenm ltm⟩
          (belowRest.mono (Nat.le_trans gb.next gm.next))
        exact ⟨fr, gb.trans (gm.trans gr)⟩
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, followed, ids, k, s, fits,
        below => by
        simp only [walk]
        obtain ⟨atInput, belowBody, atLeaves, belowRest⟩ :=
          attemptEntry_below checks (mid := mid) (key := key) (w := w) below
        generalize attemptEntry checks (mid := mid) key w followed = hit
          at atInput belowBody atLeaves belowRest ⊢
        have s1 := miss_st ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s
        generalize miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s = s₁
          at s1 ⊢
        obtain ⟨wfi, gi, leni, lti⟩ := leaves_fits (hit.map (·.1)) 1 s₁
          (by rw [s1]; exact fits.1) (by rw [s1]; exact atInput)
        rw [s1] at gi
        generalize leaves (hit.map (·.1)) 1 s₁ = inBody at wfi gi leni lti ⊢
        obtain ⟨fb, gb⟩ := walk_grows blocks body (hit.map (·.2.1)) (bindIds ids inputs inBody.1)
          ((k.addRanges inBody.1 [rules.range (D.index w)]).enter rules [D.index w])
          inBody.2 ⟨wfi, (fits.2.mono gi.next).bind inputs _ leni lti⟩ (belowBody.mono gi.next)
        generalize walk rules checks definition role blocks body (hit.map (·.2.1))
          (bindIds ids inputs inBody.1)
          ((k.addRanges inBody.1 [rules.range (D.index w)]).enter rules [D.index w])
          inBody.2 = e at fb gb ⊢
        have up : s.st.next ≤ e.state.st.next := Nat.le_trans gi.next gb.next
        obtain ⟨wfm, gm, lenm, ltm⟩ := leaves_fits (hit.map (·.2.2.1)) mid.length e.state fb.1
          fun lo e' => Nat.le_trans (atLeaves lo e') up
        obtain ⟨fr, gr⟩ := walk_grows blocks rest (hit.map (·.2.2.2))
          (bindIds ids results (leaves (hit.map (·.2.2.1)) mid.length e.state).1)
          ((afterRegions rules [e.region] k (leaves (hit.map (·.2.2.1)) mid.length e.state).1
            mid 0).enter rules mid)
          (leaves (hit.map (·.2.2.1)) mid.length e.state).2
          ⟨wfm, (fits.2.mono (Nat.le_trans up gm.next)).bind results _ lenm ltm⟩
          (belowRest.mono (Nat.le_trans up gm.next))
        exact ⟨fr, gi.trans (gb.trans (gm.trans gr))⟩
  /-- The walk of arms builds above its state, as `walk_grows`, and keeps every name in scope. -/
  theorem walkArms_grows (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads)
        (followed : Option (SkelArms D mid payloads)) (ids : Ctx Nat) (k : Known)
        (s : State D.Ty Raw),
        Scoped Γ ids s.st → FollowedArmsBelow followed s.st.next →
        (∀ e, e ∈ (walkArms rules checks definition role blocks arms followed ids k s).exits →
          ∀ i, i ∈ e.rets →
            i < (walkArms rules checks definition role blocks arms followed ids k s).state.st.next) ∧
          Scoped Γ ids (walkArms rules checks definition role blocks arms followed ids k s).state.st ∧
          St.Grows s.st (walkArms rules checks definition role blocks arms followed ids k s).state.st
    | _, _, _, .nil, _, _, _, s, fits, _ => by
        simp only [walkArms]
        exact ⟨fun _ m => (nomatch m), fits, St.Grows.refl _⟩
    | _, _, _, .cons (payload := payload) inputs arm rest, followed, ids, k, s, fits, below => by
        simp only [walkArms]
        obtain ⟨atInput, belowArm, belowRest⟩ := armEntry_below below
        generalize armEntry followed = hit at atInput belowArm belowRest ⊢
        obtain ⟨wfi, gi, leni, lti⟩ := leaves_fits (hit.map (·.1)) 1 s fits.1 atInput
        generalize leaves (hit.map (·.1)) 1 s = made at wfi gi leni lti ⊢
        obtain ⟨fb, gb⟩ := walk_grows blocks arm (hit.map (·.2.1)) (bindIds ids inputs made.1)
          ((k.addRanges made.1 [rules.range payload]).enter rules [payload]) made.2
          ⟨wfi, (fits.2.mono gi.next).bind inputs _ leni lti⟩ (belowArm.mono gi.next)
        generalize walk rules checks definition role blocks arm (hit.map (·.2.1))
          (bindIds ids inputs made.1)
          ((k.addRanges made.1 [rules.range payload]).enter rules [payload]) made.2 = e
          at fb gb ⊢
        obtain ⟨rets, fr, gr⟩ := walkArms_grows blocks rest (hit.map (·.2.2)) ids k e.state
          ⟨fb.1, fits.2.mono (Nat.le_trans gi.next gb.next)⟩
          (belowRest.mono (Nat.le_trans gi.next gb.next))
        refine ⟨fun e' m i mi => ?_, fr, gi.trans (gb.trans gr)⟩
        rcases List.mem_cons.mp m with rfl | m
        · exact Nat.lt_of_lt_of_le (fb.2 i mi) gr.next
        · exact rets e' m i mi
end

end

/-! ## The skeleton that the walk builds -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D)
  (definition : Key) (role : Option Role)

omit [DecidableEq Raw] in
/-- Leaves of a skeleton made in order below the next identifier are apart from every table that
grows from the state. -/
theorem Skel.Ordered.apart {outs : List D.Ty} {skel : Skel D outs} {lo hi : Nat}
    {st st' : St D.Ty Raw} (ordered : Skel.Ordered skel lo hi) (below : hi ≤ st.next)
    (apart : skel.Apart st.table) (grows : St.Grows st st') : skel.Apart st'.table :=
  Skel.Apart.grows grows skel apart ((Skel.Ordered.below ordered).mono below)

omit [DecidableEq Raw] in
/-- Leaves of arms made in order below the next identifier are apart from every table that grows
from the state. -/
theorem SkelArms.Ordered.apart {mid payloads : List D.Ty} {arms : SkelArms D mid payloads}
    {lo hi : Nat} {st st' : St D.Ty Raw} (ordered : SkelArms.Ordered arms lo hi)
    (below : hi ≤ st.next) (apart : arms.Apart st.table) (grows : St.Grows st st') :
    arms.Apart st'.table :=
  SkelArms.Apart.grows grows arms apart ((SkelArms.Ordered.below ordered).mono below)

mutual
  /-- **The skeleton of a term.** Where no skeleton is followed, the walk builds one whose leaves
  are made in order from the state's next identifier on, below its next identifier at the end,
  and apart from its table. -/
  theorem walk_skeleton (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (ids : Ctx Nat) (k : Known)
        (s : State D.Ty Raw), Scoped Γ ids s.st →
        Skel.Ordered (walk rules checks definition role blocks t none ids k s).skel s.st.next
            (walk rules checks definition role blocks t none ids k s).state.st.next ∧
          (walk rules checks definition role blocks t none ids k s).skel.Apart
            (walk rules checks definition role blocks t none ids k s).state.st.table
    | _, _, .ret xs, ids, k, s, _ => by
        simp only [walk, kept, Option.map_none, Option.getD_none, Option.isSome_none, miss_free]
        exact ⟨Nat.le_refl _, trivial⟩
    | _, _, .op (res := res) key o args results rest, ids, k, s, fits => by
        obtain ⟨wf₁, g₁⟩ := checkRequirements_grows rules.ops k ⟨definition, blocks, some key, role⟩
          (rules.written o) (idsOf ids args) (rules.ops.requires (rules.written o)) s.st fits.1
          (idsOf_lt fits.2 args)
        cases hs : rules.shared o with
        | true =>
            simp only [walk, hs]
            generalize checkRequirements rules.ops k ⟨definition, blocks, some key, role⟩
              (rules.written o) (idsOf ids args) (rules.ops.requires (rules.written o)) s.st = st₁
              at wf₁ g₁ ⊢
            obtain ⟨wf2, g2, lt2, len2⟩ := valueStep_grows rules (rules.written o) res
              (idsOf ids args) k st₁ wf₁
              (fun a m => Nat.lt_of_lt_of_le (idsOf_lt fits.2 args a m) g₁.next)
            generalize valueStep rules (rules.written o) res (idsOf ids args) k st₁ = step
              at wf2 g2 lt2 len2 ⊢
            obtain ⟨ordered, apart⟩ := walk_skeleton blocks rest (bindIds ids results step.1)
              step.2.1 { s with st := step.2.2 }
              ⟨wf2, (fits.2.mono (g₁.trans g2).next).bind results _ len2 lt2⟩
            exact ⟨Skel.Ordered.low ordered (g₁.trans g2).next, apart⟩
        | false =>
            simp only [walk, hs, effectEntry, kept, Option.map_none, Option.getD_none,
              Option.isSome_none, miss_free, leaves]
            generalize checkRequirements rules.ops k ⟨definition, blocks, some key, role⟩
              (rules.written o) (idsOf ids args) (rules.ops.requires (rules.written o)) s.st = st₁
              at wf₁ g₁ ⊢
            obtain ⟨wf2, g2, lt2⟩ := fresh_grows res.length st₁ wf₁
            obtain ⟨wf4, g4⟩ := effectStep_grows rules (rules.written o) res (idsOf ids args)
              (fresh res.length st₁).1 k (fresh res.length st₁).2 wf2 (fun a m => by
                rcases List.mem_append.mp m with m | m
                · exact Nat.lt_of_lt_of_le (idsOf_lt fits.2 args a m) (g₁.trans g2).next
                · exact lt2 a m)
            generalize effectStep rules (rules.written o) res (idsOf ids args)
              (fresh res.length st₁).1 k (fresh res.length st₁).2 = learned at wf4 g4 ⊢
            have scope := (fits.2.mono ((g₁.trans g2).trans g4).next).bind results
              (fresh res.length st₁).1 (by simp [fresh])
              (fun i m => Nat.lt_of_lt_of_le (lt2 i m) g4.next)
            obtain ⟨ordered, apart⟩ := walk_skeleton blocks rest
              (bindIds ids results (fresh res.length st₁).1) learned.1
              { s with st := learned.2 } ⟨wf4, scope⟩
            obtain ⟨-, g3⟩ := walk_grows rules checks definition role blocks rest none
              (bindIds ids results (fresh res.length st₁).1) learned.1
              { s with st := learned.2 } ⟨wf4, scope⟩ trivial
            exact ⟨⟨g₁.next, Skel.Ordered.low ordered g4.next⟩,
              LeavesApart.of_fresh res.length wf₁ (g4.trans g3), apart⟩
    | _, _, .guard key w c _ why rest, ids, k, s, fits => by
        simp only [walk, guardEntry, kept, Option.getD_none, Option.isSome_none, miss_free]
        exact walk_skeleton blocks rest ids _ s fits
    | _, _, .choose (mid := mid) key w c _ _ onTrue onFalse results rest, ids, k, s, fits => by
        simp only [walk, chooseEntry, kept, Option.map_none, Option.getD_none, Option.isSome_none,
          miss_free, leaves]
        obtain ⟨fa, ga⟩ := walk_grows rules checks definition role blocks onTrue none ids
          (assume rules.ops s.st.table s.st.next k (idOf ids c.name) true) s fits trivial
        obtain ⟨orderedA, apartA⟩ := walk_skeleton blocks onTrue ids
          (assume rules.ops s.st.table s.st.next k (idOf ids c.name) true) s fits
        generalize walk rules checks definition role blocks onTrue none ids
          (assume rules.ops s.st.table s.st.next k (idOf ids c.name) true) s = first
          at fa ga orderedA apartA ⊢
        have fitsB : Scoped _ ids first.state.st := ⟨fa.1, fits.2.mono ga.next⟩
        obtain ⟨fb, gb⟩ := walk_grows rules checks definition role blocks onFalse none ids
          (assume rules.ops first.state.st.table first.state.st.next k (idOf ids c.name) false)
          first.state fitsB trivial
        obtain ⟨orderedB, apartB⟩ := walk_skeleton blocks onFalse ids
          (assume rules.ops first.state.st.table first.state.st.next k (idOf ids c.name) false)
          first.state fitsB
        generalize walk rules checks definition role blocks onFalse none ids
          (assume rules.ops first.state.st.table first.state.st.next k (idOf ids c.name) false)
          first.state = second at fb gb orderedB apartB ⊢
        obtain ⟨wfm, gm, ltm⟩ := fresh_grows mid.length second.state.st fb.1
        have scope := (fits.2.mono (Nat.le_trans (Nat.le_trans ga.next gb.next) gm.next)).bind
          results (fresh mid.length second.state.st).1 (by simp [fresh]) ltm
        have known := (afterChoice rules k (idOf ids c.name) first.region second.region
          (fresh mid.length second.state.st).1 mid).enter rules mid
        obtain ⟨orderedR, apartR⟩ := walk_skeleton blocks rest
          (bindIds ids results (fresh mid.length second.state.st).1)
          ((afterChoice rules k (idOf ids c.name) first.region second.region
            (fresh mid.length second.state.st).1 mid).enter rules mid)
          { second.state with st := (fresh mid.length second.state.st).2 } ⟨wfm, scope⟩
        obtain ⟨-, gr⟩ := walk_grows rules checks definition role blocks rest none
          (bindIds ids results (fresh mid.length second.state.st).1)
          ((afterChoice rules k (idOf ids c.name) first.region second.region
            (fresh mid.length second.state.st).1 mid).enter rules mid)
          { second.state with st := (fresh mid.length second.state.st).2 } ⟨wfm, scope⟩ trivial
        have toEnd := gm.trans gr
        exact ⟨⟨Skel.Ordered.high orderedA gb.next, Skel.Ordered.low orderedB ga.next, orderedR⟩,
          Skel.Ordered.apart orderedA (Nat.le_refl _) apartA (gb.trans toEnd),
          Skel.Ordered.apart orderedB (Nat.le_refl _) apartB toEnd,
          LeavesApart.of_fresh mid.length fb.1 gr, apartR⟩
    | _, _, .cases (mid := mid) key w x _ _ arms results rest, ids, k, s, fits => by
        simp only [walk, casesEntry, kept, Option.map_none, Option.getD_none, Option.isSome_none,
          miss_free, leaves]
        obtain ⟨_, fa, ga⟩ := walkArms_grows rules checks definition role blocks arms none ids k s
          fits trivial
        obtain ⟨orderedA, apartA⟩ := walkArms_skeleton blocks arms ids k s fits
        generalize walkArms rules checks definition role blocks arms none ids k s = regions
          at fa ga orderedA apartA ⊢
        obtain ⟨wfm, gm, ltm⟩ := fresh_grows mid.length regions.state.st fa.1
        have scope := (fits.2.mono (Nat.le_trans ga.next gm.next)).bind
          results (fresh mid.length regions.state.st).1 (by simp [fresh]) ltm
        obtain ⟨orderedR, apartR⟩ := walk_skeleton blocks rest
          (bindIds ids results (fresh mid.length regions.state.st).1)
          ((afterRegions rules regions.exits k (fresh mid.length regions.state.st).1 mid
            0).enter rules mid)
          { regions.state with st := (fresh mid.length regions.state.st).2 } ⟨wfm, scope⟩
        obtain ⟨-, gr⟩ := walk_grows rules checks definition role blocks rest none
          (bindIds ids results (fresh mid.length regions.state.st).1)
          ((afterRegions rules regions.exits k (fresh mid.length regions.state.st).1 mid
            0).enter rules mid)
          { regions.state with st := (fresh mid.length regions.state.st).2 } ⟨wfm, scope⟩ trivial
        exact ⟨⟨orderedA, orderedR⟩,
          SkelArms.Ordered.apart orderedA (Nat.le_refl _) apartA (gm.trans gr),
          LeavesApart.of_fresh mid.length fa.1 gr, apartR⟩
    | _, _, .loop (carried := carried) (each := each) key w times _ init inputs body results rest,
        ids, k, s, fits => by
        simp only [walk, loopEntry, kept, Option.map_none, Option.getD_none, Option.isSome_none,
          miss_free, leaves]
        obtain ⟨wfi, gi, lti⟩ := fresh_grows (carried.length + 1) s.st fits.1
        have scopeB := (fits.2.mono gi.next).bind inputs (fresh (carried.length + 1) s.st).1
          (by simp [fresh]) lti
        obtain ⟨fb, gb⟩ := walk_grows rules checks definition role blocks body none
          (bindIds ids inputs (fresh (carried.length + 1) s.st).1)
          (bodyKnown rules k ids times ((fresh (carried.length + 1) s.st).1.headD 0)
            (fresh (carried.length + 1) s.st).1.tail carried)
          { s with st := (fresh (carried.length + 1) s.st).2 } ⟨wfi, scopeB⟩ trivial
        obtain ⟨orderedB, apartB⟩ := walk_skeleton blocks body
          (bindIds ids inputs (fresh (carried.length + 1) s.st).1)
          (bodyKnown rules k ids times ((fresh (carried.length + 1) s.st).1.headD 0)
            (fresh (carried.length + 1) s.st).1.tail carried)
          { s with st := (fresh (carried.length + 1) s.st).2 } ⟨wfi, scopeB⟩
        generalize walk rules checks definition role blocks body none
          (bindIds ids inputs (fresh (carried.length + 1) s.st).1)
          (bodyKnown rules k ids times ((fresh (carried.length + 1) s.st).1.headD 0)
            (fresh (carried.length + 1) s.st).1.tail carried)
          { s with st := (fresh (carried.length + 1) s.st).2 } = e at fb gb orderedB apartB ⊢
        obtain ⟨rbt, rbn, -, -⟩ :=
          recordBound_state (D := D) ⟨definition, blocks, some key, role⟩ k ids e.state.st times
        generalize recordBound ⟨definition, blocks, some key, role⟩ k ids e.state.st times = st₁
          at rbt rbn ⊢
        have wf1 : Table.WF st₁.next st₁.table := by rw [rbt, rbn]; exact fb.1
        have g1 : St.Grows e.state.st st₁ :=
          ⟨by rw [rbn]; exact Nat.le_refl _, [], by rw [rbt]; rfl, fun _ m => nomatch m⟩
        obtain ⟨wfm, gm, ltm⟩ := fresh_grows (carried.length + each.length) st₁ wf1
        have up := Nat.le_trans gi.next (Nat.le_trans gb.next (Nat.le_trans g1.next gm.next))
        have scope := (fits.2.mono up).bind results
          (fresh (carried.length + each.length) st₁).1 (by simp [fresh]) ltm
        obtain ⟨orderedR, apartR⟩ := walk_skeleton blocks rest
          (bindIds ids results (fresh (carried.length + each.length) st₁).1)
          ((afterLoop rules e.region k (timesBound k ids times)
            (fresh (carried.length + each.length) st₁).1 ((idsOf ids init).map k.rangeOf)
            (fresh (carried.length + 1) s.st).1.tail e.rets
            (carried ++ each.map (D.collected times.size))).enter rules
            (carried ++ each.map (D.collected times.size)))
          { e.state with st := (fresh (carried.length + each.length) st₁).2 } ⟨wfm, scope⟩
        obtain ⟨-, gr⟩ := walk_grows rules checks definition role blocks rest none
          (bindIds ids results (fresh (carried.length + each.length) st₁).1)
          ((afterLoop rules e.region k (timesBound k ids times)
            (fresh (carried.length + each.length) st₁).1 ((idsOf ids init).map k.rangeOf)
            (fresh (carried.length + 1) s.st).1.tail e.rets
            (carried ++ each.map (D.collected times.size))).enter rules
            (carried ++ each.map (D.collected times.size)))
          { e.state with st := (fresh (carried.length + each.length) st₁).2 } ⟨wfm, scope⟩ trivial
        have nextE : e.state.st.next = st₁.next := by rw [rbn]
        refine ⟨⟨Nat.le_refl _, ?_, ?_⟩, LeavesApart.of_fresh _ fits.1 (gb.trans (g1.trans
          (gm.trans gr))), Skel.Ordered.apart orderedB (Nat.le_refl _) apartB
            (g1.trans (gm.trans gr)), by rw [nextE]; exact LeavesApart.of_fresh _ wf1 gr, apartR⟩
        · exact orderedB
        · rw [nextE]; exact orderedR
    | _, _, .block (mid := mid) key number body results rest, ids, k, s, fits => by
        simp only [walk, blockEntry, kept, Option.map_none, Option.getD_none, Option.isSome_none,
          miss_free, leaves]
        obtain ⟨fb, gb⟩ := walk_grows rules checks definition role (blocks ++ [(key, number)]) body
          none ids k s fits trivial
        obtain ⟨orderedB, apartB⟩ := walk_skeleton (blocks ++ [(key, number)]) body ids k s fits
        generalize walk rules checks definition role (blocks ++ [(key, number)]) body none ids k s =
          e at fb gb orderedB apartB ⊢
        obtain ⟨wfm, gm, ltm⟩ := fresh_grows mid.length e.state.st fb.1
        have scope := (fits.2.mono (Nat.le_trans gb.next gm.next)).bind
          results (fresh mid.length e.state.st).1 (by simp [fresh]) ltm
        obtain ⟨orderedR, apartR⟩ := walk_skeleton blocks rest
          (bindIds ids results (fresh mid.length e.state.st).1)
          ((afterRegions rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
            rules mid)
          { e.state with st := (fresh mid.length e.state.st).2 } ⟨wfm, scope⟩
        obtain ⟨-, gr⟩ := walk_grows rules checks definition role blocks rest none
          (bindIds ids results (fresh mid.length e.state.st).1)
          ((afterRegions rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
            rules mid)
          { e.state with st := (fresh mid.length e.state.st).2 } ⟨wfm, scope⟩ trivial
        exact ⟨⟨orderedB, orderedR⟩,
          Skel.Ordered.apart orderedB (Nat.le_refl _) apartB (gm.trans gr),
          LeavesApart.of_fresh mid.length fb.1 gr, apartR⟩
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, ids, k, s, fits => by
        simp only [walk, attemptEntry, kept, Option.map_none, Option.getD_none, Option.isSome_none,
          miss_free, leaves]
        obtain ⟨wfi, gi, lti⟩ := fresh_grows 1 s.st fits.1
        have scopeB := (fits.2.mono gi.next).bind inputs (fresh 1 s.st).1 (by simp [fresh]) lti
        obtain ⟨fb, gb⟩ := walk_grows rules checks definition role blocks body none
          (bindIds ids inputs (fresh 1 s.st).1)
          ((k.addRanges (fresh 1 s.st).1 [rules.range (D.index w)]).enter rules [D.index w])
          { s with st := (fresh 1 s.st).2 } ⟨wfi, scopeB⟩ trivial
        obtain ⟨orderedB, apartB⟩ := walk_skeleton blocks body
          (bindIds ids inputs (fresh 1 s.st).1)
          ((k.addRanges (fresh 1 s.st).1 [rules.range (D.index w)]).enter rules [D.index w])
          { s with st := (fresh 1 s.st).2 } ⟨wfi, scopeB⟩
        generalize walk rules checks definition role blocks body none
          (bindIds ids inputs (fresh 1 s.st).1)
          ((k.addRanges (fresh 1 s.st).1 [rules.range (D.index w)]).enter rules [D.index w])
          { s with st := (fresh 1 s.st).2 } = e at fb gb orderedB apartB ⊢
        obtain ⟨wfm, gm, ltm⟩ := fresh_grows mid.length e.state.st fb.1
        have scope := (fits.2.mono (Nat.le_trans gi.next (Nat.le_trans gb.next gm.next))).bind
          results (fresh mid.length e.state.st).1 (by simp [fresh]) ltm
        obtain ⟨orderedR, apartR⟩ := walk_skeleton blocks rest
          (bindIds ids results (fresh mid.length e.state.st).1)
          ((afterRegions rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
            rules mid)
          { e.state with st := (fresh mid.length e.state.st).2 } ⟨wfm, scope⟩
        obtain ⟨-, gr⟩ := walk_grows rules checks definition role blocks rest none
          (bindIds ids results (fresh mid.length e.state.st).1)
          ((afterRegions rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
            rules mid)
          { e.state with st := (fresh mid.length e.state.st).2 } ⟨wfm, scope⟩ trivial
        exact ⟨⟨Nat.le_refl _, orderedB, orderedR⟩,
          LeavesApart.of_fresh 1 fits.1 (gb.trans (gm.trans gr)),
          Skel.Ordered.apart orderedB (Nat.le_refl _) apartB (gm.trans gr),
          LeavesApart.of_fresh mid.length fb.1 gr, apartR⟩
  /-- The skeletons of the arms of a case analysis, as `walk_skeleton`. -/
  theorem walkArms_skeleton (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads) (ids : Ctx Nat)
        (k : Known) (s : State D.Ty Raw), Scoped Γ ids s.st →
        SkelArms.Ordered (walkArms rules checks definition role blocks arms none ids k s).skel
            s.st.next (walkArms rules checks definition role blocks arms none ids k s).state.st.next ∧
          (walkArms rules checks definition role blocks arms none ids k s).skel.Apart
            (walkArms rules checks definition role blocks arms none ids k s).state.st.table
    | _, _, _, .nil, _, _, s, _ => by
        simp only [walkArms]
        exact ⟨Nat.le_refl _, trivial⟩
    | _, _, _, .cons (payload := payload) inputs arm rest, ids, k, s, fits => by
        simp only [walkArms, armEntry, Option.map_none, Option.getD_none, leaves]
        obtain ⟨wfi, gi, lti⟩ := fresh_grows 1 s.st fits.1
        have scopeA := (fits.2.mono gi.next).bind inputs (fresh 1 s.st).1 (by simp [fresh]) lti
        obtain ⟨fa, ga⟩ := walk_grows rules checks definition role blocks arm none
          (bindIds ids inputs (fresh 1 s.st).1)
          ((k.addRanges (fresh 1 s.st).1 [rules.range payload]).enter rules [payload])
          { s with st := (fresh 1 s.st).2 } ⟨wfi, scopeA⟩ trivial
        obtain ⟨orderedA, apartA⟩ := walk_skeleton blocks arm
          (bindIds ids inputs (fresh 1 s.st).1)
          ((k.addRanges (fresh 1 s.st).1 [rules.range payload]).enter rules [payload])
          { s with st := (fresh 1 s.st).2 } ⟨wfi, scopeA⟩
        generalize walk rules checks definition role blocks arm none
          (bindIds ids inputs (fresh 1 s.st).1)
          ((k.addRanges (fresh 1 s.st).1 [rules.range payload]).enter rules [payload])
          { s with st := (fresh 1 s.st).2 } = e at fa ga orderedA apartA ⊢
        have fitsR : Scoped _ ids e.state.st := ⟨fa.1, fits.2.mono (Nat.le_trans gi.next ga.next)⟩
        obtain ⟨_, _, gr⟩ := walkArms_grows rules checks definition role blocks rest none ids k
          e.state fitsR trivial
        obtain ⟨orderedR, apartR⟩ := walkArms_skeleton blocks rest ids k e.state fitsR
        exact ⟨⟨Nat.le_refl _, Skel.Ordered.high orderedA gr.next,
            SkelArms.Ordered.low orderedR (Nat.le_trans gi.next ga.next)⟩,
          LeavesApart.of_fresh 1 fits.1 (ga.trans gr),
          Skel.Ordered.apart orderedA (Nat.le_refl _) apartA gr, apartR⟩
end

end

/-! ## No place differs where no skeleton is followed -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D)
  (definition : Key) (role : Option Role)

mutual
  /-- Where no skeleton is followed, the walk adds no place that differs. -/
  theorem walk_free_differs (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (ids : Ctx Nat) (k : Known)
        (s : State D.Ty Raw),
        (walk rules checks definition role blocks t none ids k s).state.differs = s.differs
    | _, _, .ret _, ids, k, s => by
        simp only [walk, Option.isSome_none, miss_free]
    | _, _, .op key o args results rest, ids, k, s => by
        cases hs : rules.shared o with
        | true =>
            simp only [walk, hs]
            exact walk_free_differs blocks rest _ _ _
        | false =>
            simp only [walk, hs, effectEntry, Option.map_none, Option.isSome_none, miss_free,
              leaves]
            exact walk_free_differs blocks rest _ _ _
    | _, _, .guard key _ c _ _ rest, ids, k, s => by
        simp only [walk, guardEntry, Option.isSome_none, miss_free]
        exact walk_free_differs blocks rest _ _ _
    | _, _, .choose key _ c _ _ onTrue onFalse results rest, ids, k, s => by
        simp only [walk, chooseEntry, Option.map_none, Option.isSome_none, miss_free, leaves]
        rw [walk_free_differs blocks rest]
        show (walk rules checks definition role blocks onFalse none ids _ _).state.differs = _
        rw [walk_free_differs blocks onFalse, walk_free_differs blocks onTrue]
    | _, _, .cases key _ _ _ _ arms results rest, ids, k, s => by
        simp only [walk, casesEntry, Option.map_none, Option.isSome_none, miss_free, leaves]
        rw [walk_free_differs blocks rest]
        exact walkArms_free_differs blocks arms ids k s
    | _, _, .loop key _ times _ init inputs body results rest, ids, k, s => by
        simp only [walk, loopEntry, Option.map_none, Option.isSome_none, miss_free, leaves]
        rw [walk_free_differs blocks rest]
        exact walk_free_differs blocks body _ _ _
    | _, _, .block key number body results rest, ids, k, s => by
        simp only [walk, blockEntry, Option.map_none, Option.isSome_none, miss_free, leaves]
        rw [walk_free_differs blocks rest]
        exact walk_free_differs (blocks ++ [(key, number)]) body _ _ _
    | _, _, .attempt key _ _ inputs body results rest, ids, k, s => by
        simp only [walk, attemptEntry, Option.map_none, Option.isSome_none, miss_free, leaves]
        rw [walk_free_differs blocks rest]
        exact walk_free_differs blocks body _ _ _
  /-- Where no arms are followed, the walk of arms adds no place that differs. -/
  theorem walkArms_free_differs (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads) (ids : Ctx Nat)
        (k : Known) (s : State D.Ty Raw),
        (walkArms rules checks definition role blocks arms none ids k s).state.differs = s.differs
    | _, _, _, .nil, _, _, s => by simp only [walkArms]
    | _, _, _, .cons inputs arm rest, ids, k, s => by
        simp only [walkArms, armEntry, Option.map_none, leaves]
        rw [walkArms_free_differs blocks rest]
        exact walk_free_differs blocks arm _ _ _
end

end

end Analysis.Facts

open Analysis in
/-- What the check of facts accepts: the analysis refuses nothing, and the bounds are those that
it recorded, in the order of the term. -/
theorem checkFacts_ok {D : Dialect} {Raw : Type} [DecidableEq Raw] {rules : FactRules D Raw}
    {checks : SkelRules D} {definition : Key} {role : Option Role} {types outs : List D.Ty}
    {summary : Summary Raw} {inputs : Names types} {body : Term D (Ctx.empty.extend inputs) outs}
    {bounds : List (Place × Nat)}
    (accepted : checkFacts rules checks definition role summary inputs body = .ok bounds) :
    (analyse rules checks definition role summary inputs body).state.st.refusals = [] ∧
      bounds =
        (analyse rules checks definition role summary inputs body).state.st.bounds.reverse := by
  simp only [checkFacts] at accepted
  split at accepted
  · next refused =>
      simp only [Except.ok.injEq] at accepted
      exact ⟨refused, accepted.symm⟩
  · cases accepted

open FactCheck Analysis Analysis.Facts in
/-- The bounds that the check of facts gives a body are at the places of its definition, with
its role. -/
theorem checkFacts_places {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : FactRules D Raw)
    (checks : SkelRules D) (definition : Key) (role : Option Role) {types outs : List D.Ty}
    (summary : Summary Raw) (inputs : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    {bounds : List (Place × Nat)}
    (accepted : checkFacts rules checks definition role summary inputs body = .ok bounds) :
    ∀ q, q ∈ bounds → q.1.definition = definition ∧ q.1.role = role := by
  obtain ⟨_, ⟨new, enew, at_⟩, _⟩ := walk_adds rules checks definition role [] body none
    (bindIds Ctx.empty inputs (List.range types.length))
    (startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).1
    ⟨(startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).2, []⟩
  have started : (startUnder rules summary types
      ⟨Table.empty rules.place, types.length, [], []⟩).2.bounds = [] :=
    (learnRequirements_state rules.ops _ _ _ _).2
  intro q m
  rw [(checkFacts_ok accepted).2, List.mem_reverse] at m
  simp only [analyse, exitUnder] at m
  rw [enew, started, List.append_nil] at m
  obtain ⟨bl, key, eq, _⟩ := at_ q m
  rw [eq]
  exact ⟨rfl, rfl⟩

end Zkc.Core
