module

public import Zkc.Core.Facts.Contracts.ProjectedControl
public import Zkc.Core.Facts.Contracts.RoleOperationLaws

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts
open HeaderContracts

variable {V : Vocabulary} {hs : Headers V} {M : Model V} {r : Role}
variable {fns : FnTable M hs.fns} {roles : RTable M hs.protocols}
variable {catalog : FunctionContracts hs.fns}

/-- A located call carries both clause lists of the resolved header, including their bound demands. -/
theorem contract_call_member {header : FnHeader V} (m : Member hs.fns header) (R : Holders) :
    contract catalog (.compute R (.call header.key)) =
      ⟨(catalog.entry m).val.preconditions.map (clause R),
       (catalog.entry m).val.postconditions.map (clause R)⟩ := by
  simp [contract, catalog.call_member m]

theorem requires_compute (R : Holders) (w : LocalRaw V) :
    (contract catalog (.compute R w)).requires = (catalog.contract w).requires.map (expression R) := by
  simp [contract, Contract.requires, List.map_map, Function.comp_def, clause]

theorem ensures_compute (R : Holders) (w : LocalRaw V) :
    (contract catalog (.compute R w)).ensures = (catalog.contract w).ensures.map (expression R) := by
  simp [contract, Contract.ensures, List.map_map, Function.comp_def, clause]

theorem localRequired {op : LocalRaw V} {R : Holders} (mine : r ∈ R) {ds ls}
    (corr : Corr M r ds ls)
    (held : ∀ e ∈ (contract catalog (.compute R op)).requires,
      e.Holds (RoleRuns M r fns roles) (roleReading M r) ds) :
    ∀ e ∈ (catalog.contract op).requires, e.Holds (Runs M fns) (localReading M) ls := by
  rw [requires_compute] at held
  exact fun e m => (holds_iff mine corr e).mp (held _ (List.mem_map_of_mem m))

theorem roleEnsured {op : LocalRaw V} {R : Holders} (mine : r ∈ R) {ds ls}
    (corr : Corr M r ds ls)
    (held : ∀ e ∈ (catalog.contract op).ensures, e.Holds (Runs M fns) (localReading M) ls) :
    ∀ e ∈ (contract catalog (.compute R op)).ensures,
      e.Holds (RoleRuns M r fns roles) (roleReading M r) ds := by
  rw [ensures_compute]
  rintro _ m
  obtain ⟨e, mem, rfl⟩ := List.mem_map.mp m
  exact (holds_iff mine corr e).mpr (held e mem)

variable (M r fns roles) in
private theorem compute_done {R : Holders} {ins : List (LTy V)} {outs : List V.Ty}
    (op : LocalOp V hs.fns (ins.map LTy.ty) outs) (mine : r ∈ R) (here : ∀ a ∈ ins, r ∈ a.holders)
    (args : HList (RV M r) ins) {result : HList M.Val outs}
    (ran : localOp M fns op (HList.ofLocated M (revealAll M here args)) = .done result) :
    let sem := roleSem M r fns roles
    let instr : RoleOp V hs r _ _ := .compute R op ins rfl mine here
    let located := hideAll M r (HList.located M R result)
    (∀ key path, sem.op key instr path args = .done located) ∧
      RoleReturns M r fns roles (.compute R op.print) (sem.dyns args) (sem.dyns located) := by
  dsimp only
  have exec : ∀ key path, (roleSem M r fns roles).op key (.compute R op ins rfl mine here) path args =
      .done (hideAll M r (HList.located M R result)) := by
    intro key path
    change ((liftLocal id (localOp M fns op (HList.ofLocated M (revealAll M here args)))).map _) = _
    rw [ran]
    rfl
  exact ⟨exec, ⟨_, _, .compute R op ins rfl mine here, args, _, rfl, rfl, rfl, exec⟩⟩

variable (M r fns roles catalog) (callees : Callees M fns)

include callees in
theorem computes {ins outs} (op : RoleOp V hs r ins outs) (shared : roleShared op = true)
    (key : Key) (path : List Frame) (args : HList (RV M r) ins) :
    let sem := roleSem M r fns roles
    (∃ ys, sem.op key op path args = .done ys ∧
      RoleReturns M r fns roles (roleWritten op) (sem.dyns args) (sem.dyns ys)) ∨
      ∃ h, sem.op key op path args = .halt h ∧ h = .undefined := by
  cases op with
  | give | get | own | hear | apply => cases shared
  | compute R op ins types mine here =>
    subst types
    have only := localOp_stops_undefined M fns callees.quiet op
      (HList.ofLocated M (revealAll M here args)) (by simpa [roleShared] using shared)
    cases ran : localOp M fns op (HList.ofLocated M (revealAll M here args)) with
    | done result =>
      have h := compute_done M r fns roles op mine here args ran
      exact .inl ⟨_, h.1 key path, h.2⟩
    | halt h =>
      rw [ran] at only
      refine .inr ⟨h, ?_, only⟩
      change ((liftLocal id (localOp M fns op (HList.ofLocated M (revealAll M here args)))).map _) = _
      rw [ran]
      rfl
    | call impossible => cases impossible
  | absent items out =>
    exact .inl ⟨_, rfl, ⟨_, _, .absent _ out, args, _, rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  | keep H same =>
    obtain ⟨v, rfl⟩ := HList.one args
    exact .inl ⟨_, rfl, ⟨_, _, .keep H same, .cons v .nil, _, rfl, rfl, rfl, fun _ _ => rfl⟩⟩

include callees in
theorem commutative (raw : RoleRaw V) (swap : (rules catalog r).commutes raw = true) (a b ys)
    (ret : RoleReturns M r fns roles raw [a,b] ys) : RoleReturns M r fns roles raw [b,a] ys := by
  cases raw <;> try cases swap
  case compute R w =>
    obtain ⟨mine, ls, rs, c, run, rfl⟩ := returns_compute.mp ret
    obtain ⟨x, _, rfl, ex, tail⟩ := corr_cons_left.mp c
    obtain ⟨y, _, rfl, ey, empty⟩ := corr_cons_left.mp tail
    cases corr_nil_left.mp empty
    have ret' := (catalog.lawful M fns callees (fun _ _ => True)).commutative w swap x y rs run
    exact returns_compute.mpr ⟨mine, [y,x], rs, ⟨ey, ex, trivial⟩, ret', rfl⟩

theorem nothings_valid : ∀ {items : List (LTy V)} (out : ∀ a ∈ items, r ∉ a.holders),
    (nothings M out).All (RV.Valid M r)
  | [], _ => trivial
  | a :: _, out => ⟨valid_out M r (out a (by simp)) _, nothings_valid (fun b m => out b (by simp [m]))⟩

include catalog callees in
theorem keeps (raw : RoleRaw V) (xs ys) (ret : RoleReturns M r fns roles raw xs ys)
    (ok : ∀ v ∈ xs, RoleValueValid M r v) :
    (∀ v ∈ ys, RoleValueValid M r v) ∧ ys.length = roleResultCount hs raw := by
  refine ⟨?_, roleResultCount_correct M fns roles catalog.distinct ret⟩
  cases raw with
  | compute R w =>
    obtain ⟨mine, ls, rs, c, run, rfl⟩ := returns_compute.mp ret
    exact (corr_valid (corr_liftAt mine rs)).mpr
      ((catalog.lawful M fns callees (fun _ _ => True)).keeps w ls rs run ((corr_valid c).mp ok)).1
  | absent items =>
    obtain ⟨_, _, op, args, result, form, rfl, rfl, exec⟩ := ret
    cases op <;> cases form
    next out =>
      have step := exec ⟨0⟩ []
      cases step
      exact ((roleSem M r fns roles).dyns_valid_iff _).mpr (nothings_valid M r out)
  | effect | apply =>
    obtain ⟨_, _, op, _, _, form, _⟩ := ret
    cases op <;> cases form
  | keep H =>
    obtain ⟨_, _, op, args, result, form, rfl, rfl, exec⟩ := ret
    cases op <;> cases form
    next same =>
      have step := exec ⟨0⟩ []
      obtain ⟨v, rfl⟩ := HList.one args
      cases step
      intro d m
      obtain rfl := List.mem_singleton.mp m
      exact (valid_carry M same v).mpr (ok _ (List.mem_singleton.mpr rfl))

include callees in
theorem defined {ins outs} (op : RoleOp V hs r ins outs) (shared : roleShared op = true)
    (key : Key) (path : List Frame) (args : HList (RV M r) ins)
    (valid : ∀ v ∈ (roleSem M r fns roles).dyns args, RoleValueValid M r v)
    (required : (rules catalog r).Required (roleSem M r fns roles) (roleReading M r)
      (RoleReturns M r fns roles) (RoleValueValid M r) op args) :
    let sem := roleSem M r fns roles
    ∃ ys, sem.op key op path args = .done ys ∧
      RoleReturns M r fns roles (roleWritten op) (sem.dyns args) (sem.dyns ys) ∧
      (rules catalog r).Ensured sem (roleReading M r) (RoleReturns M r fns roles)
        (RoleValueValid M r) op args ys := by
  cases op with
  | give | get | own | hear | apply => cases shared
  | compute R op ins types mine here =>
    subst types
    have c := compute_corr M r fns roles here args
    obtain ⟨ys, ran, _, ens⟩ := (catalog.lawful M fns callees (fun _ _ => True)).defined
      op shared key path _ ((corr_valid c).mp valid) (localRequired mine c required)
    have h := compute_done M r fns roles op mine here args ran
    refine ⟨_, h.1 key path, h.2, roleEnsured mine (corr_append c ?_) ens⟩
    rw [located_outputs]
    exact corr_liftAt mine _
  | absent items out =>
    exact ⟨_, rfl, ⟨_, _, .absent _ out, args, _, rfl, rfl, rfl, fun _ _ => rfl⟩,
      fun _ h => nomatch h⟩
  | keep H same =>
    obtain ⟨v, rfl⟩ := HList.one args
    exact ⟨_, rfl, ⟨_, _, .keep H same, .cons v .nil, _, rfl, rfl, rfl, fun _ _ => rfl⟩,
      fun _ h => nomatch h⟩

end Zkc.Core.BodyAnalysis.RoleContracts
