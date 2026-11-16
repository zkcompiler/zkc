module

public import Zkc.Core.Facts.Walk
public import Zkc.Core.Facts.Learning

@[expose] public section

/-!
What the walk does to its state, whatever the run: it only adds refusals, it adds bounds only
at the addresses of the loops it walks, and it makes identifiers and entries above those it
had, keeping the table well formed and every name in scope with an identifier below the next
(`Scoped`). That new identifiers and a shared application do so, and that binding names keeps
every name in scope with an identifier below the next (`InScope`), is in `Value/Valuation.lean`.
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

end

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : FactRules D Raw)
  (definition : Key) (role : Option Role)

theorem opStep_grows (place : Place) {ins res : List D.Ty} (o : D.Op ins res)
    (argIds : List Nat) (k : Known) (st : St D.Ty Raw) (wf : Table.WF st.next st.table)
    (hlt : ∀ a, a ∈ argIds → a < st.next) :
    Table.WF (opStep rules place o argIds k st).2.2.next
        (opStep rules place o argIds k st).2.2.table ∧
      St.Grows st (opStep rules place o argIds k st).2.2 ∧
      (∀ i, i ∈ (opStep rules place o argIds k st).1 →
        i < (opStep rules place o argIds k st).2.2.next) ∧
      (opStep rules place o argIds k st).1.length = res.length := by
  simp only [opStep]
  split
  · obtain ⟨wf', g, lt⟩ := fresh_grows res.length st wf
    exact ⟨wf', g, lt, by simp [fresh]⟩
  · next written _ =>
      obtain ⟨wf1, g1⟩ := checkRequirements_grows rules.ops k place written argIds
        (rules.ops.requires written) st wf hlt
      obtain ⟨wf2, g2, lt⟩ := share_grows written argIds res.length _ wf1
        (fun a m => Nat.lt_of_lt_of_le (hlt a m) g1.next)
      refine ⟨wf2, g1.trans g2, lt, ?_⟩
      simp only [share]
      split <;> simp

theorem opStep_state (place : Place) {ins res : List D.Ty} (o : D.Op ins res)
    (argIds : List Nat) (k : Known) (st : St D.Ty Raw) :
    (∃ new, (opStep rules place o argIds k st).2.2.refusals = new ++ st.refusals) ∧
      (opStep rules place o argIds k st).2.2.bounds = st.bounds := by
  simp only [opStep]
  split
  · exact ⟨⟨[], rfl⟩, rfl⟩
  · next written _ =>
      obtain ⟨⟨new, e⟩, b⟩ := checkRequirements_state rules.ops k place written argIds
        (rules.ops.requires written) st
      obtain ⟨r2, b2⟩ := share_state written argIds res.length
        (checkRequirements rules.ops k place written argIds (rules.ops.requires written) st)
      exact ⟨⟨new, by rw [r2, e]⟩, by rw [b2, b]⟩

omit [DecidableEq Raw] in
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

/-- What the walk does to the state: it adds refusals; it adds bounds at the addresses of the
term; on a well-formed state where every name in scope has an identifier below the next
(`Scoped`), it keeps the table
well formed, makes identifiers and entries above the old ones, and returns identifiers below the
next. -/
def WalkState (addresses : List (List (Key × Nat) × Key))
    (st st' : St D.Ty Raw) : Prop :=
  (∃ new, st'.refusals = new ++ st.refusals) ∧
    (∃ new, st'.bounds = new ++ st.bounds ∧ BoundsAt definition role addresses new)

mutual
  theorem walk_state (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (ids : Ctx Nat) (k : Known)
        (st : St D.Ty Raw),
        WalkState definition role (t.addresses blocks) st
            (walk rules definition role blocks t ids k st).st ∧
          (Scoped Γ ids st →
            WellFormed (walk rules definition role blocks t ids k st).rets
              (walk rules definition role blocks t ids k st).st ∧
            St.Grows st (walk rules definition role blocks t ids k st).st)
    | _, _, .ret xs, ids, k, st => by
        refine ⟨⟨⟨[], rfl⟩, [], rfl, fun _ m => nomatch m⟩, fun fits => ?_⟩
        exact ⟨⟨fits.1, idsOf_lt fits.2 xs⟩, St.Grows.refl st⟩
    | _, _, .op key o args results rest, ids, k, st => by
        simp only [walk]
        have s1 := opStep_state rules ⟨definition, blocks, some key, role⟩ o (idsOf ids args) k st
        have g1 := opStep_grows rules ⟨definition, blocks, some key, role⟩ o (idsOf ids args) k st
        generalize opStep rules ⟨definition, blocks, some key, role⟩ o (idsOf ids args) k st =
          step at s1 g1 ⊢
        obtain ⟨⟨n1, e1⟩, b1⟩ := s1
        obtain ⟨⟨⟨n2, e2⟩, n3, e3, at3⟩, inner⟩ := walk_state blocks rest
          (bindIds ids results step.1) step.2.1 step.2.2
        refine ⟨⟨⟨n2 ++ n1, by rw [e2, e1, List.append_assoc]⟩, n3, by rw [e3, b1], ?_⟩,
          fun fits => ?_⟩
        · intro q m
          obtain ⟨bl, key', eq, mem⟩ := at3 q m
          exact ⟨bl, key', eq, List.mem_cons_of_mem _ mem⟩
        · obtain ⟨wf1, gr1, lt1, len1⟩ := g1 fits.1 (idsOf_lt fits.2 args)
          obtain ⟨fits2, gr2⟩ := inner ⟨wf1, (fits.2.mono gr1.next).bind results step.1 len1 lt1⟩
          exact ⟨fits2, gr1.trans gr2⟩
    | _, _, .guard key _ c _ _ rest, ids, k, st => by
        simp only [walk]
        obtain ⟨⟨r, n, e, at_⟩, inner⟩ := walk_state blocks rest ids
          (assume rules.ops st.table st.next k (idOf ids c.name) true) st
        refine ⟨⟨r, n, e, fun q m => ?_⟩, inner⟩
        obtain ⟨bl, key', eq, mem⟩ := at_ q m
        exact ⟨bl, key', eq, List.mem_cons_of_mem _ mem⟩
    | _, _, .choose (mid := mid) key _ c _ _ onTrue onFalse results rest, ids, k, st => by
        simp only [walk]
        obtain ⟨⟨⟨ra, ea⟩, na, eba, ata⟩, ga⟩ := walk_state blocks onTrue ids
          (assume rules.ops st.table st.next k (idOf ids c.name) true) st
        generalize walk rules definition role blocks onTrue ids
          (assume rules.ops st.table st.next k (idOf ids c.name) true) st = first
          at ea eba ata ga ⊢
        obtain ⟨⟨⟨rb, eb⟩, nb, ebb, atb⟩, gb⟩ := walk_state blocks onFalse ids
          (assume rules.ops first.st.table first.st.next k (idOf ids c.name) false) first.st
        generalize walk rules definition role blocks onFalse ids
          (assume rules.ops first.st.table first.st.next k (idOf ids c.name) false)
            first.st = second at eb ebb atb gb ⊢
        generalize hm : fresh mid.length second.st = made
        obtain ⟨⟨⟨rr, er⟩, nr, ebr, atr⟩, gr⟩ := walk_state blocks rest (bindIds ids results made.1)
          ((afterChoice rules k (idOf ids c.name) first second made.1 mid).enter rules mid)
          made.2
        have m2r : made.2.refusals = second.st.refusals := by rw [← hm]; rfl
        have m2b : made.2.bounds = second.st.bounds := by rw [← hm]; rfl
        refine ⟨⟨⟨rr ++ rb ++ ra, by rw [er, m2r, eb, ea]; simp⟩, nr ++ nb ++ na,
          by rw [ebr, m2b, ebb, eba]; simp, ?_⟩, fun fits => ?_⟩
        · intro q m
          simp only [List.mem_append] at m
          rcases m with (m | m) | m
          · obtain ⟨bl, key', eq, mem⟩ := atr q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
          · obtain ⟨bl, key', eq, mem⟩ := atb q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
          · obtain ⟨bl, key', eq, mem⟩ := ata q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
        · obtain ⟨fa, gra⟩ := ga fits
          obtain ⟨fb, grb⟩ := gb ⟨fa.1, fits.2.mono gra.next⟩
          obtain ⟨wfm, grm, ltm⟩ := fresh_grows mid.length second.st fb.1
          rw [hm] at wfm grm ltm
          have len : made.1.length = mid.length := by rw [← hm]; simp [fresh]
          obtain ⟨fr, grr⟩ := gr ⟨wfm, (fits.2.mono (Nat.le_trans gra.next
            (Nat.le_trans grb.next grm.next))).bind results made.1 len ltm⟩
          exact ⟨fr, gra.trans (grb.trans (grm.trans grr))⟩
    | _, _, .cases (mid := mid) key _ _ _ _ arms results rest, ids, k, st => by
        simp only [walk]
        obtain ⟨⟨⟨ra, ea⟩, na, eba, ata⟩, ga⟩ := walkArms_state blocks arms ids k st
        generalize walkArms rules definition role blocks arms ids k st = regions
          at ea eba ata ga ⊢
        generalize hm : fresh mid.length regions.2 = made
        obtain ⟨⟨⟨rr, er⟩, nr, ebr, atr⟩, gr⟩ := walk_state blocks rest (bindIds ids results made.1)
          ((afterRegions rules regions.1 k made.1 mid 0).enter rules mid) made.2
        have m2r : made.2.refusals = regions.2.refusals := by rw [← hm]; rfl
        have m2b : made.2.bounds = regions.2.bounds := by rw [← hm]; rfl
        refine ⟨⟨⟨rr ++ ra, by rw [er, m2r, ea]; simp⟩, nr ++ na,
          by rw [ebr, m2b, eba]; simp, ?_⟩, fun fits => ?_⟩
        · intro q m
          rcases List.mem_append.mp m with m | m
          · obtain ⟨bl, key', eq, mem⟩ := atr q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
          · obtain ⟨bl, key', eq, mem⟩ := ata q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
        · obtain ⟨_, fa, gra⟩ := ga fits
          obtain ⟨wfm, grm, ltm⟩ := fresh_grows mid.length regions.2 fa.1
          rw [hm] at wfm grm ltm
          have len : made.1.length = mid.length := by rw [← hm]; simp [fresh]
          obtain ⟨fr, grr⟩ := gr ⟨wfm, (fits.2.mono (Nat.le_trans gra.next grm.next)).bind
            results made.1 len ltm⟩
          exact ⟨fr, gra.trans (grm.trans grr)⟩
    | _, _, .loop (carried := carried) (each := each) key _ times _ init inputs body results rest,
        ids, k, st => by
        simp only [walk]
        generalize hin : fresh (carried.length + 1) st = inBody
        obtain ⟨⟨⟨ra, ea⟩, na, eba, ata⟩, ga⟩ := walk_state blocks body (bindIds ids inputs inBody.1)
          (bodyKnown rules k ids times (inBody.1.headD 0) inBody.1.tail carried) inBody.2
        generalize walk rules definition role blocks body (bindIds ids inputs inBody.1)
          (bodyKnown rules k ids times (inBody.1.headD 0) inBody.1.tail carried) inBody.2 = e
          at ea eba ata ga ⊢
        obtain ⟨rbt, rbn, rbr, nbd, ebd, atd⟩ :=
          recordBound_state ⟨definition, blocks, some key, role⟩ k ids e.st times
        generalize recordBound ⟨definition, blocks, some key, role⟩ k ids e.st times = st₁
          at rbt rbn rbr ebd ⊢
        generalize hm : fresh (carried.length + each.length) st₁ = made
        obtain ⟨⟨⟨rr, er⟩, nr, ebr, atr⟩, gr⟩ := walk_state blocks rest (bindIds ids results made.1)
          ((afterLoop rules e k (timesBound k ids times) made.1 ((idsOf ids init).map k.rangeOf)
            inBody.1.tail e.rets (carried ++ each.map (D.collected times.size))).enter rules
            (carried ++ each.map (D.collected times.size))) made.2
        have m2r : made.2.refusals = st₁.refusals := by rw [← hm]; rfl
        have m2b : made.2.bounds = st₁.bounds := by rw [← hm]; rfl
        have i2r : inBody.2.refusals = st.refusals := by rw [← hin]; rfl
        have i2b : inBody.2.bounds = st.bounds := by rw [← hin]; rfl
        refine ⟨⟨⟨rr ++ ra, by rw [er, m2r, rbr, ea, i2r]; simp⟩, nr ++ nbd ++ na,
          by rw [ebr, m2b, ebd, eba, i2b]; simp, ?_⟩, fun fits => ?_⟩
        · intro q m
          simp only [List.mem_append] at m
          rcases m with (m | m) | m
          · obtain ⟨bl, key', eq, mem⟩ := atr q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
          · exact ⟨blocks, key, atd q m, by simp [Term.addresses]⟩
          · obtain ⟨bl, key', eq, mem⟩ := ata q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
        · obtain ⟨wfi, gri, lti⟩ := fresh_grows (carried.length + 1) st fits.1
          rw [hin] at wfi gri lti
          have leni : inBody.1.length = carried.length + 1 := by rw [← hin]; simp [fresh]
          obtain ⟨fb, grb⟩ := ga ⟨wfi, (fits.2.mono gri.next).bind inputs inBody.1
            (by simp [leni]) lti⟩
          have g1 : St.Grows e.st st₁ :=
            ⟨by rw [rbn]; exact Nat.le_refl _, [], by rw [rbt]; rfl, fun _ m => nomatch m⟩
          have wf1 : Table.WF st₁.next st₁.table := by rw [rbt, rbn]; exact fb.1
          obtain ⟨wfm, grm, ltm⟩ := fresh_grows (carried.length + each.length) st₁ wf1
          rw [hm] at wfm grm ltm
          have len : made.1.length = carried.length + each.length := by rw [← hm]; simp [fresh]
          obtain ⟨fr, grr⟩ := gr ⟨wfm, (fits.2.mono (Nat.le_trans gri.next
            (Nat.le_trans grb.next (Nat.le_trans g1.next grm.next)))).bind results made.1
            (by simp [len]) ltm⟩
          exact ⟨fr, gri.trans (grb.trans (g1.trans (grm.trans grr)))⟩
    | _, _, .block (mid := mid) key number body results rest, ids, k, st => by
        simp only [walk]
        obtain ⟨⟨⟨ra, ea⟩, na, eba, ata⟩, ga⟩ :=
          walk_state (blocks ++ [(key, number)]) body ids k st
        generalize walk rules definition role (blocks ++ [(key, number)]) body ids k st = e
          at ea eba ata ga ⊢
        generalize hm : fresh mid.length e.st = made
        obtain ⟨⟨⟨rr, er⟩, nr, ebr, atr⟩, gr⟩ := walk_state blocks rest (bindIds ids results made.1)
          ((afterRegions rules [e] k made.1 mid 0).enter rules mid) made.2
        have m2r : made.2.refusals = e.st.refusals := by rw [← hm]; rfl
        have m2b : made.2.bounds = e.st.bounds := by rw [← hm]; rfl
        refine ⟨⟨⟨rr ++ ra, by rw [er, m2r, ea]; simp⟩, nr ++ na,
          by rw [ebr, m2b, eba]; simp, ?_⟩, fun fits => ?_⟩
        · intro q m
          rcases List.mem_append.mp m with m | m
          · obtain ⟨bl, key', eq, mem⟩ := atr q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
          · obtain ⟨bl, key', eq, mem⟩ := ata q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
        · obtain ⟨fa, gra⟩ := ga fits
          obtain ⟨wfm, grm, ltm⟩ := fresh_grows mid.length e.st fa.1
          rw [hm] at wfm grm ltm
          have len : made.1.length = mid.length := by rw [← hm]; simp [fresh]
          obtain ⟨fr, grr⟩ := gr ⟨wfm, (fits.2.mono (Nat.le_trans gra.next grm.next)).bind
            results made.1 len ltm⟩
          exact ⟨fr, gra.trans (grm.trans grr)⟩
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, ids, k, st => by
        simp only [walk]
        generalize hin : fresh 1 st = inBody
        obtain ⟨⟨⟨ra, ea⟩, na, eba, ata⟩, ga⟩ := walk_state blocks body (bindIds ids inputs inBody.1)
          ((k.addRanges inBody.1 [rules.range (D.index w)]).enter rules [D.index w]) inBody.2
        generalize walk rules definition role blocks body (bindIds ids inputs inBody.1)
          ((k.addRanges inBody.1 [rules.range (D.index w)]).enter rules [D.index w]) inBody.2 = e
          at ea eba ata ga ⊢
        generalize hm : fresh mid.length e.st = made
        obtain ⟨⟨⟨rr, er⟩, nr, ebr, atr⟩, gr⟩ := walk_state blocks rest (bindIds ids results made.1)
          ((afterRegions rules [e] k made.1 mid 0).enter rules mid) made.2
        have m2r : made.2.refusals = e.st.refusals := by rw [← hm]; rfl
        have m2b : made.2.bounds = e.st.bounds := by rw [← hm]; rfl
        have i2r : inBody.2.refusals = st.refusals := by rw [← hin]; rfl
        have i2b : inBody.2.bounds = st.bounds := by rw [← hin]; rfl
        refine ⟨⟨⟨rr ++ ra, by rw [er, m2r, ea, i2r]; simp⟩, nr ++ na,
          by rw [ebr, m2b, eba, i2b]; simp, ?_⟩, fun fits => ?_⟩
        · intro q m
          rcases List.mem_append.mp m with m | m
          · obtain ⟨bl, key', eq, mem⟩ := atr q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
          · obtain ⟨bl, key', eq, mem⟩ := ata q m
            exact ⟨bl, key', eq, by simp [Term.addresses, mem]⟩
        · obtain ⟨wfi, gri, lti⟩ := fresh_grows 1 st fits.1
          rw [hin] at wfi gri lti
          have leni : inBody.1.length = 1 := by rw [← hin]; simp [fresh]
          obtain ⟨fb, grb⟩ := ga ⟨wfi, (fits.2.mono gri.next).bind inputs inBody.1 leni lti⟩
          obtain ⟨wfm, grm, ltm⟩ := fresh_grows mid.length e.st fb.1
          rw [hm] at wfm grm ltm
          have len : made.1.length = mid.length := by rw [← hm]; simp [fresh]
          obtain ⟨fr, grr⟩ := gr ⟨wfm, (fits.2.mono (Nat.le_trans gri.next
            (Nat.le_trans grb.next grm.next))).bind results made.1 len ltm⟩
          exact ⟨fr, gri.trans (grb.trans (grm.trans grr))⟩
  theorem walkArms_state (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads) (ids : Ctx Nat)
        (k : Known) (st : St D.Ty Raw),
        WalkState definition role (Arms.addresses blocks arms) st
            (walkArms rules definition role blocks arms ids k st).2 ∧
          (Scoped Γ ids st →
            (∀ e, e ∈ (walkArms rules definition role blocks arms ids k st).1 →
              ∀ i, i ∈ e.rets → i < (walkArms rules definition role blocks arms ids k st).2.next) ∧
            Scoped Γ ids (walkArms rules definition role blocks arms ids k st).2 ∧
            St.Grows st (walkArms rules definition role blocks arms ids k st).2)
    | _, _, _, .nil, _, _, st =>
        ⟨⟨⟨[], rfl⟩, [], rfl, fun _ m => nomatch m⟩,
          fun fits => ⟨fun _ m => (nomatch m), fits, St.Grows.refl st⟩⟩
    | _, _, _, .cons (payload := payload) inputs arm rest, ids, k, st => by
        simp only [walkArms]
        generalize hin : fresh 1 st = made
        obtain ⟨⟨⟨ra, ea⟩, na, eba, ata⟩, ga⟩ := walk_state blocks arm (bindIds ids inputs made.1)
          ((k.addRanges made.1 [rules.range payload]).enter rules [payload]) made.2
        generalize walk rules definition role blocks arm (bindIds ids inputs made.1)
          ((k.addRanges made.1 [rules.range payload]).enter rules [payload]) made.2 = e
          at ea eba ata ga ⊢
        obtain ⟨⟨⟨rr, er⟩, nr, ebr, atr⟩, gr⟩ := walkArms_state blocks rest ids k e.st
        have i2r : made.2.refusals = st.refusals := by rw [← hin]; rfl
        have i2b : made.2.bounds = st.bounds := by rw [← hin]; rfl
        refine ⟨⟨⟨rr ++ ra, by rw [er, ea, i2r]; simp⟩, nr ++ na,
          by rw [ebr, eba, i2b]; simp, ?_⟩, fun fits => ?_⟩
        · intro q m
          rcases List.mem_append.mp m with m | m
          · obtain ⟨bl, key', eq, mem⟩ := atr q m
            exact ⟨bl, key', eq, by simp [Arms.addresses, mem]⟩
          · obtain ⟨bl, key', eq, mem⟩ := ata q m
            exact ⟨bl, key', eq, by simp [Arms.addresses, mem]⟩
        · obtain ⟨wfi, gri, lti⟩ := fresh_grows 1 st fits.1
          rw [hin] at wfi gri lti
          have leni : made.1.length = 1 := by rw [← hin]; simp [fresh]
          obtain ⟨fb, grb⟩ := ga ⟨wfi, (fits.2.mono gri.next).bind inputs made.1 leni lti⟩
          obtain ⟨rets, fr, grr⟩ := gr ⟨fb.1, fits.2.mono (Nat.le_trans gri.next grb.next)⟩
          refine ⟨fun e' m i mi => ?_, fr, gri.trans (grb.trans grr)⟩
          rcases List.mem_cons.mp m with rfl | m
          · exact Nat.lt_of_lt_of_le (fb.2 i mi) grr.next
          · exact rets e' m i mi
end

end

end FactCheck

end Zkc.Core
