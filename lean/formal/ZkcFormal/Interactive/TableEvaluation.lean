module

public import ZkcFormal.Interactive.TableEvaluationStep

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.TableEvaluation
open Zkc.Core
open TableHalves (table)
open ReductionRound.PointReturn (boundVar bound_get)
variable {V : Vocabulary} {hs : Headers V} {t : V.Ty} {Γ : Ctx V.Ty} {total : Nat}
variable (free : Ty.isLinear V t = false)

def last (fns : List (FnHeader V)) (site : Nat → Key) :
    Term (localDialect V fns) (Ctx.empty.insert 0 (table t 0)) [t] :=
  .op (site 0) (.literal .nat [0] rfl) .nil (.cons 1 .nil) <|
  .op (site 1) (.owned (.seqAt t (some 1) free)) (.cons ⟨0,rfl⟩ (.cons ⟨1,rfl⟩ .nil)) (.cons 2 .nil) <|
  .ret (.cons ⟨2,rfl⟩ .nil)

def LastLaw (ds : Defs V hs) (tab : Var Γ (table t 0)) (actual : Term (localDialect V hs.fns) Γ [t]) : Prop :=
  ∀ (M : Model V) path (env : Env M.Val Γ) (v : M.Val t), env.get tab = [v] →
    actual.denote (localSem M _ (Defs.fnTable M ds)) path env = .done (.cons v .nil)

def readLast (ds : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup)
    (tab : Var Γ (table t 0)) (actual : Term (localDialect V hs.fns) Γ [t]) : Option (PLift (LastLaw ds tab actual)) := do
  let site := siteOf actual
  let ⟨same⟩ ← StraightLine.compare (checks _) (checks_lawful unique) [(0,tab.name)] (last free _ site) actual
  return ⟨by
    intro M path env v atTab
    let left := (Env.empty : Env M.Val Ctx.empty).insert 0 (τ := table t 0) [v]
    have aligned : StraightLine.Agrees [(0,tab.name)] left env := by
      intro a b h ty ha hb
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
      have type := Option.some.inj (hb.symm.trans tab.typed)
      subst ty
      exact atTab.symm
    exact (same _ _ _ _ aligned).symm.trans (by rfl)⟩

variable (rows : (n : Nat) → TableRestriction.Rows t n)

def BodyLaw (ds : Defs V hs) (i n : Nat) (tab : Var Γ (table t n)) (pt : Var Γ (point t total))
    (actual : Term (localDialect V hs.fns) Γ [t]) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (M.Val t)], (∀ d, d < n → TableRestriction.Arithmetic (rows d) M) →
    ∀ path (env : Env M.Val Γ) (x : Cube (M.Val t) n) (before remaining : List (M.Val t)) (v : M.Val t),
      before.length = i → env.get pt = before ++ remaining → env.get tab = Cube.flatten n x →
      Cube.evaluate n x remaining = some v →
      actual.denote (localSem M _ (Defs.fnTable M ds)) path env = .done (.cons v .nil)

def readBody (ds : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup) : (n i : Nat) → {Γ : Ctx V.Ty} →
    (tab : Var Γ (table t n)) → (pt : Var Γ (point t total)) → (actual : Term (localDialect V hs.fns) Γ [t]) →
      Option (PLift (BodyLaw rows ds i n tab pt actual))
  | 0, i, _, tab, pt, actual => do
    let ⟨leaf⟩ ← readLast free ds unique tab actual
    return ⟨by
      intro M _ _ path env x before remaining v _ _ tableValue value
      cases remaining with
      | nil =>
        have equal : x = v := Option.some.inj value
        subst v
        exact leaf M path env x tableValue
      | cons r rs => contradiction⟩
  | n+1, i, Γ, tab, pt, .block (mid := mid) key iteration inside ns rest => by
    exact if resultTypes : mid = [table t n] then by
      subst mid
      match ns with
      | .cons name .nil => exact do
        guard (iteration == i)
        let ⟨stepLaw⟩ ← readStep free (rows n) ds unique i tab pt inside
        let kept ← ReductionRound.PointReturn.retain pt (types := [table t n]) (.cons name .nil)
        let next := boundVar Γ name (table t n)
        let ⟨tail⟩ ← readBody ds unique n (i+1) next kept.after rest
        return ⟨by
          intro M _ math path env x before remaining v atIndex atPoint atTable evaluates
          cases remaining with
          | nil => contradiction
          | cons r rs =>
            have draw : (env.get pt)[i]? = some r := by rw [atPoint,← atIndex,List.getElem?_append_right (Nat.le_refl _)]; simp
            have stepValue := stepLaw M (math n (Nat.lt_succ_self _)) (path ++ [.iteration key iteration]) env x r atTable draw
            rw [Term.denote_block,stepValue]
            let vs : HList M.Val [table t n] := .cons (Cube.flatten n (Cube.restrict n x r)) .nil
            apply tail M (fun d h => math d (Nat.lt_succ_of_lt h)) path (env.extend (.cons name .nil) vs) (Cube.restrict n x r) (before++[r]) rs v
            · simp [atIndex]
            · exact (kept.get env vs).trans (by rw [atPoint,List.append_assoc,List.singleton_append])
            · exact bound_get env name (a := table t n) (Cube.flatten n (Cube.restrict n x r))
            · exact evaluates⟩
    else none
  | _+1, _, _, _, _, _ => none

abbrev header (t : V.Ty) (key : Key) (n : Nat) (width : Nat := n) : FnHeader V := ⟨key,[table t n,point t width],[t],false,none,⟨[],[]⟩⟩

def Law (key : Key) (n width : Nat) (run : FunctionMeaning (header t key n width)) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (M.Val t)], (∀ d, d < n → TableRestriction.Arithmetic (rows d) M) →
    ∀ (x : Cube (M.Val t) n) (pt : List (M.Val t)) v, Cube.evaluate n x pt = some v →
      run M (.cons (Cube.flatten n x) (.cons pt .nil)) = .done (.cons v .nil)

def check (ds : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup) (key : Key) (n : Nat) (width : Nat := n) :
    Option {ref : Member hs.fns (header t key n width) // Law rows key n width (fun M => Defs.fnTable M ds _ ref)} := do
  let ref ← FunctionEntry.resolve hs.fns (header t key n width)
  let entry := ds.functionEntry unique ref
  let source ← entry.atInputs (.cons 0 (.cons 1 .nil))
  let ⟨holds⟩ ← readBody free rows entry.definitions entry.distinct n 0 ⟨0,rfl⟩ ⟨1,rfl⟩ source.body
  return ⟨ref,by
    intro M _ math x pt v value
    dsimp only
    rw [source.meaning M]
    exact holds M math [] _ x [] pt v rfl rfl rfl value⟩

#print axioms check
end ZkcFormal.Interactive.Sumcheck.TableEvaluation
