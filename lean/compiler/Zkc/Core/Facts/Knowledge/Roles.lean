module

public import Zkc.Core.Facts.Domains.MeasurementLaws
public import Zkc.Core.Facts.Knowledge.Functions
public import Zkc.Core.Facts.Contracts.RoleOperationLaws

@[expose] public section

namespace Zkc.Core.BodyAnalysis
open FactCheck (FormHolds)
variable {V : Vocabulary}

namespace RoleKnowledge
variable (M : Model V) (r : Role)
private abbrev Located := (a : LTy V) × RV M r a
private abbrev LocalValue := (t : V.Ty) × M.Val t

/-- The role can reveal exactly the local values of these operands in order. -/
private def Reveals : List (Located M r) → List (LocalValue M) → Prop
  | [], [] => True
  | d :: ds, l :: ls => heldValue M r d = some l ∧ Reveals ds ls
  | _, _ => False

private abbrev located (holders : Holders) (v : LocalValue M) : Located M r :=
  ⟨⟨v.1,holders⟩, hide M r ⟨v.1,holders⟩ v.2⟩

private theorem held_located {holders : Holders} (here : r ∈ holders) (v : LocalValue M) :
    heldValue M r (located M r holders v) = some v := by
  obtain ⟨t, x⟩ := v
  simp [located, heldValue, here, reveal_hide]

private theorem held_valid {d : Located M r} {v : LocalValue M} (h : heldValue M r d = some v)
    (ok : RoleValueValid M r d) : ValidDyn M v := by
  obtain ⟨a, x⟩ := d
  unfold heldValue at h
  split at h
  · rename_i here
    cases h
    exact ok here
  · cases h

private theorem reveals_valid : ∀ {ds ls}, Reveals M r ds ls → (∀ d ∈ ds, RoleValueValid M r d) →
    ∀ l ∈ ls, ValidDyn M l
  | [], [], _, _, _, mem => nomatch mem
  | d :: ds, l :: ls, h, ok, _, mem => by
    rcases List.mem_cons.mp mem with rfl | rest
    · exact held_valid M r h.1 (ok _ (by simp))
    · exact reveals_valid h.2 (fun x hx => ok x (List.mem_cons_of_mem _ hx)) _ rest

private theorem reveals_at : ∀ {ds ls}, Reveals M r ds ls → ∀ (i : Nat) d, ds[i]? = some d →
    ∃ l, ls[i]? = some l ∧ heldValue M r d = some l
  | [], [], _, _, _, h => by simp at h
  | _ :: _, _ :: _, h, 0, _, eq => by cases eq; exact ⟨_,rfl,h.1⟩
  | _ :: _, _ :: _, h, _+1, _, eq => reveals_at h.2 _ _ eq

private theorem reading_corr {d : Located M r} {l : LocalValue M} (e : heldValue M r d = some l) :
    (roleReading M r).nat d = (localReading M).nat l ∧ (roleReading M r).bool d = (localReading M).bool l := by
  simp [roleReading, e]

variable {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
private abbrev localS := localSem M hs.fns fnTable
private abbrev roleS := roleSem M r fnTable rTable

private theorem reveal_inputs : ∀ {ins : List (LTy V)} (here : ∀ a ∈ ins, r ∈ a.holders)
    (as : HList (RV M r) ins), Reveals M r ((roleS M r fnTable rTable).dyns as)
      ((localS M fnTable).dyns (HList.ofLocated M (revealAll M here as)))
  | [], _, .nil => trivial
  | a :: _, here, .cons x xs =>
    ⟨by simp [heldValue, here a (by simp)], reveal_inputs (fun b m => here b (List.mem_cons_of_mem _ m)) xs⟩

private theorem locate_outputs (holders : Holders) : ∀ {outs : List V.Ty} (xs : HList M.Val outs),
    (roleS M r fnTable rTable).dyns (hideAll M r (HList.located M holders xs)) =
      ((localS M fnTable).dyns xs).map (located M r holders)
  | [], .nil => rfl
  | _ :: _, .cons _ xs => congrArg (List.cons _) (locate_outputs holders xs)

private theorem computation {holders : Holders} {op : LocalRaw V} {xs ys}
    (run : ValidRun (roleS M r fnTable rTable) (RoleReturns M r fnTable rTable)
      (RoleValueValid M r) (.compute holders op) xs ys) :
    r ∈ holders ∧ ∃ as bs, Reveals M r xs as ∧
      ValidRun (localS M fnTable) (LocalReturns M fnTable) (ValidDyn M) op as bs ∧
      ys = bs.map (located M r holders) := by
  obtain ⟨⟨ins,outs,instr,args,result,form,rfl,rfl,exec⟩,validArgs,validResult⟩ := run
  cases instr <;> cases form
  case compute =>
    rename_i localOp' types here mine
    subst types
    have step := exec ⟨0⟩ []
    change ((liftLocal id (localOp M fnTable localOp' (HList.ofLocated M (revealAll M here args)))).map
      fun vs => hideAll M r (HList.located M holders vs)) = .done result at step
    cases ran : localOp M fnTable localOp' (HList.ofLocated M (revealAll M here args)) with
    | done returned =>
      rw [ran] at step
      cases step
      refine ⟨mine, _, _, reveal_inputs M r fnTable rTable here args,
        ⟨⟨_, _, localOp', _, returned, rfl, rfl, rfl, ran⟩, reveals_valid M r
          (reveal_inputs M r fnTable rTable here args) validArgs, ?_⟩, locate_outputs M r fnTable rTable holders returned⟩
      intro v mem
      rw [locate_outputs M r fnTable rTable] at validResult
      exact held_valid M r (held_located M r mine v) (validResult _ (List.mem_map_of_mem mem))
    | halt stop => rw [ran] at step; cases step
    | call impossible => cases impossible

private theorem corr_two {ds : List (Located M r)} {a b : LocalValue M} (c : Reveals M r ds [a, b]) :
    ∃ da db, ds = [da, db] ∧ heldValue M r da = some a ∧ heldValue M r db = some b := by
  match ds, c with
  | [da, db], ⟨ea, eb, _⟩ => exact ⟨da, db, rfl, ea, eb⟩

private theorem corr_one {ds : List (Located M r)} {a : LocalValue M} (c : Reveals M r ds [a]) :
    ∃ da, ds = [da] ∧ heldValue M r da = some a := by
  match ds, c with
  | [da], ⟨ea, _⟩ => exact ⟨da, rfl, ea⟩

/-- How the first result of a computation reads, from its local operation's. -/
private theorem formHolds_toRole {ds : List (Located M r)} {ls : List (LocalValue M)} (c : Reveals M r ds ls)
    {d : Located M r} {l : LocalValue M} (e : heldValue M r d = some l) :
    ∀ f : ResultForm, FormHolds (localReading M) f ls l → FormHolds (roleReading M r) f ds d
  | .sum, ⟨a, b, x, y, h, ha, hb, hr⟩ => by
      subst h
      obtain ⟨da, db, rfl, ea, eb⟩ := corr_two M r c
      exact ⟨da, db, x, y, rfl, by rw [(reading_corr M r ea).1]; exact ha,
        by rw [(reading_corr M r eb).1]; exact hb, by rw [(reading_corr M r e).1]; exact hr⟩
  | .difference, ⟨a, b, x, y, h, ha, hb, le, hr⟩ => by
      subst h
      obtain ⟨da, db, rfl, ea, eb⟩ := corr_two M r c
      exact ⟨da, db, x, y, rfl, by rw [(reading_corr M r ea).1]; exact ha,
        by rw [(reading_corr M r eb).1]; exact hb, le, by rw [(reading_corr M r e).1]; exact hr⟩
  | .less, ⟨a, b, x, y, h, ha, hb, hr⟩ => by
      subst h
      obtain ⟨da, db, rfl, ea, eb⟩ := corr_two M r c
      exact ⟨da, db, x, y, rfl, by rw [(reading_corr M r ea).1]; exact ha,
        by rw [(reading_corr M r eb).1]; exact hb, by rw [(reading_corr M r e).2]; exact hr⟩
  | .equal, ⟨a, b, x, y, h, ha, hb, hr⟩ => by
      subst h
      obtain ⟨da, db, rfl, ea, eb⟩ := corr_two M r c
      exact ⟨da, db, x, y, rfl, by rw [(reading_corr M r ea).1]; exact ha,
        by rw [(reading_corr M r eb).1]; exact hb, by rw [(reading_corr M r e).2]; exact hr⟩
  | .negation, ⟨a, x, h, ha, hr⟩ => by
      subst h
      obtain ⟨da, rfl, ea⟩ := corr_one M r c
      exact ⟨da, x, rfl, by rw [(reading_corr M r ea).2]; exact ha, by rw [(reading_corr M r e).2]; exact hr⟩
  | .conjunction, ⟨a, b, x, y, h, ha, hb, hr⟩ => by
      subst h
      obtain ⟨da, db, rfl, ea, eb⟩ := corr_two M r c
      exact ⟨da, db, x, y, rfl, by rw [(reading_corr M r ea).2]; exact ha,
        by rw [(reading_corr M r eb).2]; exact hb, by rw [(reading_corr M r e).2]; exact hr⟩
  | .disjunction, ⟨a, b, x, y, h, ha, hb, hr⟩ => by
      subst h
      obtain ⟨da, db, rfl, ea, eb⟩ := corr_two M r c
      exact ⟨da, db, x, y, rfl, by rw [(reading_corr M r ea).2]; exact ha,
        by rw [(reading_corr M r eb).2]; exact hb, by rw [(reading_corr M r e).2]; exact hr⟩
  | .truth _, hr => by
      show (roleReading M r).bool d = _
      rw [(reading_corr M r e).2]
      exact hr

theorem observations (distinct : (hs.fns.map (·.key)).Nodup) :
    (roleKnowledgeOperations hs.fns).Lawful (roleReading M r)
      (ValidRun (roleSem M r fnTable rTable) (RoleReturns M r fnTable rTable) (RoleValueValid M r)) where
  functional := fun _ _ _ _ a b => roleReturns_functional M fnTable rTable distinct a.1 b.1
  form := by
    intro op xs ys f form run
    cases op with
    | compute holders op =>
      obtain ⟨here, as, bs, corr, ret, rfl⟩ := computation M r fnTable rTable run
      obtain ⟨v, first, meaning⟩ := FactCheck.localReturns_form form ret.1
      exact ⟨_, by rw [List.head?_map, first]; rfl, formHolds_toRole M r corr (held_located M r here v) f meaning⟩
    | _ => cases form
  preservesNumber := by
    intro op xs ys preserves run
    cases op with
    | compute holders op =>
      obtain ⟨here, as, bs, corr, ret, rfl⟩ := computation M r fnTable rTable run
      obtain ⟨a, b, rfl, head, same⟩ := localReturns_preservesNumber preserves ret.1
      obtain ⟨source, rfl, atSource⟩ := corr_one M r corr
      exact ⟨source, located M r holders b, rfl, by rw [List.head?_map, head]; rfl,
        (reading_corr M r atSource).1.trans
          (same.trans (reading_corr M r (held_located M r here b)).1.symm)⟩
    | _ => cases preserves
  ranges := by
    intro op xs ys known run inputs i bound found
    cases op with
    | compute holders op =>
      obtain ⟨here, as, bs, corr, ret, rfl⟩ := computation M r fnTable rTable run
      obtain ⟨v,n,atV,reads,fits⟩ := FactCheck.localRun_ranges known ret (by
        intro j b atB
        obtain ⟨x,n,atX,reads,fits⟩ := inputs j b atB
        obtain ⟨l,atL,reveals⟩ := reveals_at M r corr j x atX
        exact ⟨l,n,atL,(reading_corr M r reveals).1 ▸ reads,fits⟩) i bound found
      exact ⟨_,n,by rw [List.getElem?_map, atV]; rfl, (reading_corr M r (held_located M r here v)).1.trans reads,fits⟩
    | _ => simp [roleKnowledgeOperations] at found
def lengthOf : ((t : V.Ty) × M.Val t) → Option Nat
  | ⟨.seq item _, xs⟩ => some (xs : List (M.Val item)).length
  | _ => none

private theorem local_length {types params xs ys v}
    (run : LocalReturns M fnTable (.owned .seqLength types params) xs ys) (atZero : ys[0]? = some v) :
    ∃ x, xs = [x] ∧ (localReading M).nat v = lengthOf M x := by
  obtain ⟨ins, res, op, args, result, printed, rfl, rfl, step⟩ := run
  cases op with
  | row | literal | call => cases printed
  | owned op =>
    cases op <;> simp [LocalOp.print, OwnedOp.name] at printed
    obtain ⟨values, rfl⟩ := HList.one args
    simp only [localOp, ownedOp, Process.done.injEq] at step
    subst result
    cases atZero
    exact ⟨_, rfl, rfl⟩

theorem measures_length {op x ys v} (kind : measuresLength op = true)
    (run : ValidRun (roleSem M r fnTable rTable) (RoleReturns M r fnTable rTable)
      (RoleValueValid M r) op [x] ys) (first : ys[0]? = some v) :
    (roleReading M r).nat v = (heldValue M r x).bind (lengthOf M) := by
  unfold measuresLength at kind
  split at kind
  · obtain ⟨mine, as, bs, corr, ret, rfl⟩ := computation M r fnTable rTable run
    obtain ⟨l,atL,rfl⟩ := Option.map_eq_some_iff.mp (List.getElem?_map ▸ first)
    obtain ⟨a,rfl,eq⟩ := local_length M fnTable ret.1 atL
    obtain ⟨dx,matched,reveals⟩ := corr_one M r corr
    cases matched
    rw [(reading_corr M r (held_located M r mine l)).1, reveals]
    exact eq
  · cases kind

end RoleKnowledge

/-- Numeric and Boolean inference for a role body, justified by actual role evaluation. -/
def roleKnowledgeLawful (M : Model V) (r : Role) {hs : Headers V} (fns : FnTable M hs.fns)
    (roles : RTable M hs.protocols) (distinct : (hs.fns.map (·.key)).Nodup) :
    (Knowledge.domain (roleKnowledgeTypes V r) (roleKnowledgeOperations hs.fns)).Lawful
      (ValidRun (roleSem M r fns roles) (RoleReturns M r fns roles) (RoleValueValid M r))
      (roleReading M r) (TypedValue (roleSem M r fns roles) (RoleValueValid M r)) :=
  Knowledge.lawful (RoleKnowledge.observations M r fns roles distinct) (roleKnowledgeTypes_lawful M r fns roles)

def roleDomainLawful (M : Model V) (r : Role) {hs : Headers V} (fns : FnTable M hs.fns)
    (roles : RTable M hs.protocols) (distinct : (hs.fns.map (·.key)).Nodup) :
    (roleDomain hs.fns r).Lawful (ValidRun (roleSem M r fns roles) (RoleReturns M r fns roles)
      (RoleValueValid M r)) (roleReading M r)
      (TypedValue (roleSem M r fns roles) (RoleValueValid M r)) :=
  (roleKnowledgeLawful M r fns roles distinct).prod <|
    UnaryMeasurements.lawful (RoleKnowledge.observations M r fns roles distinct).functional
      (fun _ _ _ _ => RoleKnowledge.measures_length M r fns roles)
      (fun eq => congrArg (fun v => v.bind (RoleKnowledge.lengthOf M)) eq) _

end Zkc.Core.BodyAnalysis
