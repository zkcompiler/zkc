module

public import ZkcFormal.Interactive.TableRestriction
public import ZkcFormal.Interactive.ReductionExit

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.TableEvaluation
open Zkc.Core
open TableHalves (table)
variable {V : Vocabulary} {t : V.Ty} {hs : Headers V} {n total : Nat}

def checks (fns : List (FnHeader V)) : SkelRules (localDialect V fns) where
  sameTy := inferInstance
  sameWho := inferInstance
  sameOp := fun a b => decide (a.print = b.print)

theorem checks_lawful {fns : List (FnHeader V)} (unique : (fns.map (·.key)).Nodup) : (checks fns).Lawful := by
  intro _ _ _ a b ok
  exact Sigma.mk.inj (LocalOp.print_injective unique a b (of_decide_eq_true ok))

abbrev point (t : V.Ty) (n : Nat) : V.Ty := .seq t (some n)
abbrev names (t : V.Ty) (n total : Nat) : Names [table t (n+1),point t total] := .cons 0 (.cons 1 .nil)
abbrev ctx (t : V.Ty) (n total : Nat) := Ctx.empty.extend (names t n total)

variable (free : Ty.isLinear V t = false) (rows : TableRestriction.Rows t n) {k : Key}
variable (fix : Member hs.fns (TableRestriction.header t k n))
local macro "varAt " n:term:max : term => `(⟨$n,rfl⟩)

def step (total i : Nat) (site : Nat → Key) : Term (localDialect V hs.fns) (ctx t n total) [table t n] :=
  .op (site 0) (.literal .nat [i] rfl) .nil (.cons 2 .nil) <|
  .op (site 1) (.owned (.seqAt t (some total) free)) (.cons (varAt 1) (.cons (varAt 2) .nil)) (.cons 3 .nil) <|
  .op (site 2) (.call fix) (.cons (varAt 0) (.cons (varAt 3) .nil)) (.cons 4 .nil) <|
  .ret (.cons (varAt 4) .nil)

theorem step_value (defs : Defs V hs) (law : TableRestriction.Law rows k (fun M => Defs.fnTable M defs _ fix))
    (M : Model V) [Lean.Grind.Field (M.Val t)] (math : TableRestriction.Arithmetic rows M)
    (x : Cube (M.Val t) (n+1)) (pt : List (M.Val t)) (i : Nat) (r : M.Val t) (found : pt[i]? = some r)
    (site : Nat → Key) (path : List Frame) :
    (step free fix total i site).denote (localSem M _ (Defs.fnTable M defs)) path
      (Env.empty.extend (names t n total) (.cons (Cube.flatten (n+1) x) (.cons pt .nil))) =
      .done (.cons (Cube.flatten n (Cube.restrict n x r)) .nil) := by
  have get : localOp M (Defs.fnTable M defs) (.owned (.seqAt t (some total) free)) (.cons pt (.cons i .nil)) =
      .done (.cons r .nil) := by
    simp only [localOp,ownedOp,found]
  change (localOp M (Defs.fnTable M defs) (.owned (.seqAt t (some total) free)) (.cons pt (.cons i .nil))).bind _ = _
  rw [get]
  change (Defs.fnTable M defs _ fix (.cons (Cube.flatten (n+1) x) (.cons r .nil))).bind _ = _
  have applied := law M math x r
  dsimp only at applied
  rw [applied]
  rfl

variable {Γ : Ctx V.Ty}
def StepLaw (defs : Defs V hs) (i : Nat) (tab : Var Γ (table t (n+1))) (pt : Var Γ (point t total))
    (inside : Term (localDialect V hs.fns) Γ [table t n]) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (M.Val t)], TableRestriction.Arithmetic rows M → ∀ path (env : Env M.Val Γ)
    (x : Cube (M.Val t) (n+1)) (r : M.Val t), env.get tab = Cube.flatten (n+1) x → (env.get pt)[i]? = some r →
    inside.denote (localSem M _ (Defs.fnTable M defs)) path env = .done (.cons (Cube.flatten n (Cube.restrict n x r)) .nil)

def siteOf {fns : List (FnHeader V)} {Γ : Ctx V.Ty} {outs : List V.Ty}
    (term : Term (localDialect V fns) Γ outs) (i : Nat) : Key :=
  match (eraseBody (D := localDialect V fns) (fun o => o.print) id term).1[i]? with
  | some (.op key ..) => key
  | _ => ⟨i⟩

def readStep (defs : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup) (i : Nat)
    (tab : Var Γ (table t (n+1))) (pt : Var Γ (point t total)) (inside : Term (localDialect V hs.fns) Γ [table t n]) :
    Option (PLift (StepLaw rows defs i tab pt inside)) := do
  let ops : List (Instruction (LocalRaw V) Unit) := (eraseBody (D := localDialect V hs.fns) (fun o => o.print) id inside).1
  let .op _ _ (.call k) _ ← ops[2]? | none
  let ⟨fix,law⟩ ← TableRestriction.check rows free defs unique k
  let site := siteOf inside
  let ⟨same⟩ ← StraightLine.compare (checks _) (checks_lawful unique) [(0,tab.name),(1,pt.name)]
    (step free fix total i site) inside
  return ⟨by
    intro M field math path env x r tabValue draw
    let args : HList M.Val [table t (n+1),point t total] := .cons (Cube.flatten (n+1) x) (.cons (env.get pt) .nil)
    let left := Env.empty.extend (names t n total) args
    have aligned : StraightLine.Agrees [(0,tab.name),(1,pt.name)] left env := by
      intro a b mem ty ha hb
      rcases List.mem_cons.mp mem with h | h
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
        have type := Option.some.inj (hb.symm.trans tab.typed)
        subst ty
        exact tabValue.symm
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
        have type := Option.some.inj (hb.symm.trans pt.typed)
        subst ty
        rfl
    exact (same _ _ _ _ aligned).symm.trans (step_value free rows fix defs law M math x (env.get pt) i r draw site path)⟩

end ZkcFormal.Interactive.Sumcheck.TableEvaluation
