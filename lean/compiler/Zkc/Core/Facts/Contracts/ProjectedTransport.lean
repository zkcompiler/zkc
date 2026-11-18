module

public import Zkc.Core.Facts.Contracts.Roles
public import Zkc.Core.Facts.Knowledge.DialectReadings
public import Zkc.Core.Facts.Contracts.FunctionLaws

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts

section
variable {V : Vocabulary} (M : Model V) (r : Role)

/-- A value of a role with its located type. -/
abbrev RDyn : Type := (a : LTy V) × RV M r a

/-- A value of a function with its type. -/
abbrev LDyn : Type := (τ : V.Ty) × M.Val τ

/-- Values of a role are the values of a function that they hold, one by one: each is held. -/
def Corr : List (RDyn M r) → List (LDyn M) → Prop
  | [], [] => True
  | d :: ds, l :: ls => heldValue M r d = some l ∧ Corr ds ls
  | _, _ => False

/-- A value of a function, held by `R`, as a value of the role. -/
def liftAt (R : Holders) (d : LDyn M) : RDyn M r := ⟨⟨d.1, R⟩, hide M r ⟨d.1, R⟩ d.2⟩

/-- A value that the role does not hold is valid. -/
theorem valid_out {a : LTy V} (h : r ∉ a.holders) (x : RV M r a) : RoleValueValid M r ⟨a, x⟩ :=
  fun h' => absurd h' h

/-- A value hidden at a type that the role holds is valid exactly when the value is. -/
theorem valid_hide {a : LTy V} (h : r ∈ a.holders) (v : M.Val a.ty) :
    RoleValueValid M r ⟨a, hide M r a v⟩ ↔ M.Valid a.ty v := by
  change (∀ h : r ∈ a.holders, M.Valid a.ty (reveal M h (hide M r a v))) ↔ _
  constructor
  · intro hv
    have := hv h
    rwa [reveal_hide] at this
  · intro hv h'
    rwa [reveal_hide]

/-- What the role holds of a value, as a value of a function. -/
theorem toLocal_held {a : LTy V} (h : r ∈ a.holders) (x : RV M r a) :
    heldValue M r ⟨a, x⟩ = some ⟨a.ty, reveal M h x⟩ := by
  simp only [heldValue, h, ↓reduceDIte]

theorem toLocal_out {a : LTy V} (h : r ∉ a.holders) (x : RV M r a) : heldValue M r ⟨a, x⟩ = none := by
  simp only [heldValue, h, ↓reduceDIte]

/-- A value of a function lifted to holders that have the role is held as itself. -/
theorem toLocal_liftAt {R : Holders} (h : r ∈ R) (d : LDyn M) :
    heldValue M r (liftAt M r R d) = some d := by
  obtain ⟨τ, v⟩ := d
  simp only [liftAt]
  rw [toLocal_held M r (a := ⟨τ, R⟩) h, reveal_hide]

/-- Validity is the same on both sides of a held value. -/
theorem valid_toLocal {d : RDyn M r} {l : LDyn M} (e : heldValue M r d = some l) :
    RoleValueValid M r d ↔ ValidDyn M l := by
  obtain ⟨a, x⟩ := d
  by_cases h : r ∈ a.holders
  · rw [toLocal_held M r h] at e
    cases e
    exact ⟨fun hv => hv h, fun hv _ => hv⟩
  · rw [toLocal_out M r h] at e
    cases e

variable {M r}

theorem corr_nil_left {ls : List (LDyn M)} : Corr M r [] ls ↔ ls = [] := by
  cases ls <;> simp [Corr]

theorem corr_cons_left {d : RDyn M r} {ds : List (RDyn M r)} {ls : List (LDyn M)} :
    Corr M r (d :: ds) ls ↔ ∃ l ls', ls = l :: ls' ∧ heldValue M r d = some l ∧ Corr M r ds ls' := by
  cases ls with
  | nil => simp [Corr]
  | cons l ls =>
      exact ⟨fun ⟨e, c⟩ => ⟨l, ls, rfl, e, c⟩, fun ⟨_, _, h, e, c⟩ => by cases h; exact ⟨e, c⟩⟩

theorem corr_functional : ∀ {ds : List (RDyn M r)} {ls ls' : List (LDyn M)},
    Corr M r ds ls → Corr M r ds ls' → ls = ls'
  | [], _, _, c, c' => by rw [corr_nil_left.mp c, corr_nil_left.mp c']
  | _ :: _, _, _, c, c' => by
      obtain ⟨l, ls, rfl, e, c1⟩ := corr_cons_left.mp c
      obtain ⟨l', ls', rfl, e', c2⟩ := corr_cons_left.mp c'
      rw [e] at e'
      cases e'
      rw [corr_functional c1 c2]

theorem corr_getElem : ∀ {ds : List (RDyn M r)} {ls : List (LDyn M)}, Corr M r ds ls →
    ∀ (i : Nat) (d : RDyn M r), ds[i]? = some d → ∃ l, ls[i]? = some l ∧ heldValue M r d = some l
  | [], _, _, _, _, e => by simp at e
  | _ :: _, _, c, i, d, e => by
      obtain ⟨l, ls, rfl, el, c⟩ := corr_cons_left.mp c
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          subst e
          exact ⟨l, rfl, el⟩
      | succ i =>
          simp only [List.getElem?_cons_succ] at e ⊢
          exact corr_getElem c i d e

theorem corr_getElem' : ∀ {ds : List (RDyn M r)} {ls : List (LDyn M)}, Corr M r ds ls →
    ∀ (i : Nat) (l : LDyn M), ls[i]? = some l → ∃ d, ds[i]? = some d ∧ heldValue M r d = some l
  | [], _, c, _, _, e => by rw [corr_nil_left.mp c] at e; simp at e
  | d :: _, _, c, i, l, e => by
      obtain ⟨l', ls, rfl, el, c⟩ := corr_cons_left.mp c
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          subst e
          exact ⟨d, rfl, el⟩
      | succ i =>
          simp only [List.getElem?_cons_succ] at e ⊢
          exact corr_getElem' c i l e

theorem corr_append : ∀ {ds : List (RDyn M r)} {ls : List (LDyn M)} {es : List (RDyn M r)}
    {ms : List (LDyn M)}, Corr M r ds ls → Corr M r es ms → Corr M r (ds ++ es) (ls ++ ms)
  | [], _, _, _, c, c' => by rw [corr_nil_left.mp c]; exact c'
  | _ :: _, _, _, _, c, c' => by
      obtain ⟨l, ls, rfl, el, c⟩ := corr_cons_left.mp c
      exact ⟨el, corr_append c c'⟩

theorem corr_valid : ∀ {ds : List (RDyn M r)} {ls : List (LDyn M)}, Corr M r ds ls →
    ((∀ d, d ∈ ds → RoleValueValid M r d) ↔ ∀ l, l ∈ ls → ValidDyn M l)
  | [], _, c => by rw [corr_nil_left.mp c]; simp
  | _ :: _, _, c => by
      obtain ⟨l, ls, rfl, el, c⟩ := corr_cons_left.mp c
      simp only [List.mem_cons, forall_eq_or_imp]
      rw [valid_toLocal M r el, corr_valid c]

theorem corr_liftAt {R : Holders} (h : r ∈ R) :
    ∀ (ls : List (LDyn M)), Corr M r (ls.map (liftAt M r R)) ls
  | [] => trivial
  | l :: ls => ⟨toLocal_liftAt M r h l, corr_liftAt h ls⟩

end

variable {V : Vocabulary} {hs : Headers V} {M : Model V} {r : Role}
variable {fns : FnTable M hs.fns} {roles : RTable M hs.protocols}

variable (M r fns roles) in
theorem compute_corr : ∀ {ins : List (LTy V)} (here : ∀ a ∈ ins, r ∈ a.holders)
    (args : HList (RV M r) ins), Corr M r ((roleSem M r fns roles).dyns args)
      ((localSem M hs.fns fns).dyns (HList.ofLocated M (revealAll M here args)))
  | [], _, .nil => trivial
  | a :: _, here, .cons x xs =>
    ⟨toLocal_held M r (here a (by simp)) x, compute_corr (fun b m => here b (by simp [m])) xs⟩

variable (M r fns roles) in
theorem located_outputs (holders : Holders) : ∀ {outs : List V.Ty} (xs : HList M.Val outs),
    (roleSem M r fns roles).dyns (hideAll M r (HList.located M holders xs)) =
      ((localSem M hs.fns fns).dyns xs).map (liftAt M r holders)
  | [], .nil => rfl
  | _ :: _, .cons _ xs => congrArg (List.cons _) (located_outputs holders xs)

variable (fns roles) in
private theorem pack : ∀ {ds ls}, Corr M r ds ls →
    ∃ (items : List (LTy V)) (vs : HList (RV M r) items) (here : ∀ a ∈ items, r ∈ a.holders),
      (roleSem M r fns roles).dyns vs = ds ∧
      (localSem M hs.fns fns).dyns (HList.ofLocated M (revealAll M here vs)) = ls
  | [], _, c => ⟨[], .nil, (fun _ m => nomatch m), rfl, (corr_nil_left.mp c).symm⟩
  | ⟨a,x⟩ :: ds, ls, c => by
    obtain ⟨l, ls, rfl, el, rest⟩ := corr_cons_left.mp c
    obtain ⟨items, vs, tail, rfl, rfl⟩ := pack rest
    by_cases mine : r ∈ a.holders
    · rw [toLocal_held M r mine] at el
      cases el
      exact ⟨a :: items, .cons x vs, fun b m => (List.mem_cons.mp m).elim
        (fun eq => eq ▸ mine) (tail b), rfl, rfl⟩
    · rw [toLocal_out M r mine] at el
      cases el

/-- A computation returns exactly the located results of the local operation on the held inputs. -/
theorem returns_compute {R : Holders} {w : LocalRaw V} {ds rs} :
    RoleReturns M r fns roles (.compute R w) ds rs ↔
      r ∈ R ∧ ∃ ls ys, Corr M r ds ls ∧ LocalReturns M fns w ls ys ∧
        rs = ys.map (liftAt M r R) := by
  constructor
  · rintro ⟨ins, outs, instr, args, result, form, rfl, rfl, exec⟩
    cases instr <;> cases form
    next =>
      rename_i op types here mine
      subst types
      have step := exec ⟨0⟩ []
      change ((liftLocal id (localOp M fns op (HList.ofLocated M (revealAll M here args)))).map
        fun vs => hideAll M r (HList.located M R vs)) = .done result at step
      cases ran : localOp M fns op (HList.ofLocated M (revealAll M here args)) with
      | done ys =>
        rw [ran] at step
        cases step
        exact ⟨mine, _, _, compute_corr M r fns roles here args,
          ⟨_, _, op, _, ys, rfl, rfl, rfl, ran⟩, located_outputs M r fns roles R ys⟩
      | halt h => rw [ran] at step; cases step
      | call impossible => cases impossible
  · rintro ⟨mine, ls, ys, corr, ⟨ins, outs, op, args, result, rfl, rfl, rfl, ran⟩, rfl⟩
    obtain ⟨items, vs, here, rfl, eq⟩ := pack fns roles corr
    obtain ⟨rfl, same⟩ := (localSem M hs.fns fns).dyns_heq _ _ eq
    cases eq_of_heq same
    refine ⟨_, _, .compute R op items rfl mine here, vs, hideAll M r (HList.located M R result),
      rfl, rfl, located_outputs M r fns roles R result, fun key path => ?_⟩
    change ((liftLocal id (localOp M fns op (HList.ofLocated M (revealAll M here vs)))).map _) = _
    rw [ran]
    rfl

variable {R : Holders}
variable {ds : List (RDyn M r)} {ls : List (LDyn M)}

abbrev RoleRuns (M : Model V) (r : Role) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) :=
  ValidRun (roleSem M r fns roles) (RoleReturns M r fns roles) (RoleValueValid M r)

mutual
  theorem denotes_toRole (mine : r ∈ R) (inputs : Corr M r ds ls) (e : Expr (LocalRaw V)) {v}
      (den : e.Denotes (HeaderContracts.Runs M fns) ls v) :
      ∃ d, (expression R e).Denotes (RoleRuns M r fns roles) ds d ∧ heldValue M r d = some v := by
    cases e with
    | arg i =>
      cases den with
      | arg found =>
        obtain ⟨d, atD, eq⟩ := corr_getElem' inputs i _ found
        exact ⟨d, .arg atD, eq⟩
    | apply op args j =>
      cases den with
      | apply named ran picked =>
        obtain ⟨vs, names, corr⟩ := denote_toRole mine inputs args named
        have run := (returns_compute (roles := roles)).mpr ⟨mine, _, _, corr, ran.1, rfl⟩
        exact ⟨_, .apply names ⟨run, (corr_valid corr).mpr ran.2.1,
          (corr_valid (corr_liftAt mine _)).mpr ran.2.2⟩ (by rw [List.getElem?_map, picked]; rfl),
          toLocal_liftAt M r mine v⟩
  theorem denote_toRole (mine : r ∈ R) (inputs : Corr M r ds ls) (es : Exprs (LocalRaw V)) {vs}
      (den : es.Denote (HeaderContracts.Runs M fns) ls vs) :
      ∃ located, (expressions R es).Denote (RoleRuns M r fns roles) ds located ∧ Corr M r located vs := by
    cases es with
    | nil => cases den; exact ⟨[], .nil, trivial⟩
    | cons e es =>
      cases den with
      | cons one rest =>
        obtain ⟨d, atD, eq⟩ := denotes_toRole mine inputs e one
        obtain ⟨ds, atDs, corr⟩ := denote_toRole mine inputs es rest
        exact ⟨d :: ds, .cons atD atDs, eq, corr⟩
end

mutual
  theorem denotes_toLocal (inputs : Corr M r ds ls) (e : Expr (LocalRaw V)) {d}
      (den : (expression R e).Denotes (RoleRuns M r fns roles) ds d) :
      ∃ l, e.Denotes (HeaderContracts.Runs M fns) ls l ∧ heldValue M r d = some l := by
    cases e with
    | arg i =>
      cases den with
      | arg found =>
        obtain ⟨l, atL, eq⟩ := corr_getElem inputs i _ found
        exact ⟨l, .arg atL, eq⟩
    | apply op args j =>
      cases den with
      | apply named ran picked =>
        obtain ⟨vs, names, corr⟩ := denote_toLocal inputs args named
        obtain ⟨here, _, ys, other, ret, rfl⟩ := returns_compute.mp ran.1
        cases corr_functional corr other
        obtain ⟨l, atL, eq⟩ := corr_getElem (corr_liftAt here ys) j _ picked
        exact ⟨_, .apply names ⟨ret, (corr_valid corr).mp ran.2.1,
          (corr_valid (corr_liftAt here ys)).mp ran.2.2⟩ atL, eq⟩
  theorem denote_toLocal (inputs : Corr M r ds ls) (es : Exprs (LocalRaw V)) {vs}
      (den : (expressions R es).Denote (RoleRuns M r fns roles) ds vs) :
      ∃ locals, es.Denote (HeaderContracts.Runs M fns) ls locals ∧ Corr M r vs locals := by
    cases es with
    | nil => cases den; exact ⟨[], .nil, trivial⟩
    | cons e es =>
      cases den with
      | cons one rest =>
        obtain ⟨l, atL, eq⟩ := denotes_toLocal inputs e one
        obtain ⟨ls, atLs, corr⟩ := denote_toLocal inputs es rest
        exact ⟨l :: ls, .cons atL atLs, eq, corr⟩
end

theorem holds_iff (mine : r ∈ R) (inputs : Corr M r ds ls) (e : Expr (LocalRaw V)) :
    (expression R e).Holds (RoleRuns M r fns roles) (roleReading M r) ds ↔
      e.Holds (HeaderContracts.Runs M fns) (localReading M) ls := by
  constructor
  · rintro ⟨d, den, truth⟩
    obtain ⟨l, named, eq⟩ := denotes_toLocal inputs e den
    exact ⟨l, named, by simpa [roleReading, eq] using truth⟩
  · rintro ⟨l, den, truth⟩
    obtain ⟨d, named, eq⟩ := denotes_toRole (roles := roles) mine inputs e den
    exact ⟨d, named, by simpa [roleReading, eq] using truth⟩

end Zkc.Core.BodyAnalysis.RoleContracts
