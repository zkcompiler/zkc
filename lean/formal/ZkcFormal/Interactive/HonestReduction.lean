module

public import ZkcFormal.Interactive.HonestExit

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.HonestPairs
open Zkc.Core ReductionRound PointReturn JointEntry
open TableHalves (table)
variable {V : Vocabulary} {hs : Headers V} (rows : ScalarRows V)
variable (sums : (n : Nat) → SumRow rows n) (vectors : (n : Nat) → TableRestriction.Rows rows.scalarTy n)
variable (events : Events rows.scalarTy) (ds : Defs V hs)
local notation "t" => rows.scalarTy

structure Arithmetic (n : Nat) (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] : Prop where
  scalar : 0 < n → rows.Arithmetic M
  sum : ∀ d, d < n → (sums d).Arithmetic rows M
  vector : ∀ d, d < n → TableRestriction.Arithmetic (vectors d) M
  equal : ScalarEquality.Law t events.equal events.equalType M

theorem Arithmetic.tail {n : Nat} {M : Model V} [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)]
    (h : Arithmetic rows sums vectors events (n+1) M) : Arithmetic rows sums vectors events n M :=
  ⟨fun hp => h.scalar (Nat.lt_succ_of_lt hp),fun d hd => h.sum d (Nat.lt_succ_of_lt hd),
    fun d hd => h.vector d (Nat.lt_succ_of_lt hd),h.equal⟩

def ReductionLaw {Γ : Ctx (LTy V)} {total : Nat} (n : Nat)
    (st : Var Γ ⟨table t n,[0]⟩) (pt : Var Γ (point t 0)) (v : Var Γ (shared t))
    (past : List (Var Γ (shared t))) (actual : Term (protocolDialect V hs) Γ (ports t (table t 0) total)) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)],
    Arithmetic rows sums vectors events n M → ∀ path (env : Env (LVal M) Γ) (x : Cube (rows.F M) n),
    env.get st = Cube.flatten n x → env.get pt = [] → env.get v = Cube.sum n x →
    Returns (actual.denote (protocolSem M (Defs.fnTable M ds) (Defs.gTable M ds)) path env)
      (fun vs => ∃ rs value, Cube.evaluate n x rs = some value ∧
        vs = fullResult M (past.map env.get ++ rs) value)

def retainList {T : Type} {Γ : Ctx T} {a : T} {types : List T} (ns : Names types) :
    (xs : List (Var Γ a)) → Option {ys : List (Var (Γ.extend ns) a) //
      ∀ {F : T → Type} (env : Env F Γ) (vs : HList F types), ys.map (env.extend ns vs).get = xs.map env.get}
  | [] => some ⟨[],fun _ _ => rfl⟩
  | x::xs => do
    let head ← retain x ns
    let ⟨ys,tail⟩ ← retainList ns xs
    return ⟨head.after::ys,fun env vs => by simp only [List.map_cons,head.get,tail]⟩

local macro "vAt " n:term:max : term => `(⟨$n,rfl⟩)
def readReduction (distinct : hs.keys.Nodup) (evaluation : ∀ k, FunctionReadback _ (rows.EvaluationLaw k))
    {total : Nat} : (n : Nat) → {Γ : Ctx (LTy V)} → (st : Var Γ ⟨table t n,[0]⟩) →
    (pt : Var Γ (point t 0)) → (v : Var Γ (shared t)) → (past : List (Var Γ (shared t))) →
    (actual : Term (protocolDialect V hs) Γ (ports t (table t 0) total)) →
    Option (PLift (ReductionLaw rows sums vectors events ds n st pt v past actual))
  | 0, _, st, pt, v, past, actual => do
    let ⟨exit⟩ ← checkExit distinct st pt v past actual
    return ⟨by
      intro M _ _ _ path env x atS atP atV
      rw [exit M _ _ path env x atP atS atV]
      exact ⟨[],x,rfl,by rw [List.append_nil]⟩⟩
  | n+1, Γ, st, pt, v, past, .block (mid := mid) key index inside ns rest => by
    exact if out : mid = outputs (table t n) t then by
      subst mid
      match ns with
      | .cons stateName (.cons valueName (.cons drawName .nil)) => exact do
        let rules := protocolRules hs
        let steps := (eraseBody rules.printOp rules.printWho inside).1
        let raw ← Operations.read steps
        let ⟨ops,law⟩ ← readMembers rows (sums n) (vectors n) ds (List.nodup_append.mp distinct).1 raw evaluation
        let sites := instructionSite steps
        let pairs := [(0,st.name),(2,v.name)]
        let ⟨same⟩ ← StraightLine.compare rules.skel (rules.skel_lawful (protocolRules_lawful distinct))
          pairs (body ops events (emptyPoint t) sites) inside
        let names' : Names (outputs (table t n) t) := .cons stateName (.cons valueName (.cons drawName .nil))
        let state' := boundVar Γ stateName (⟨table t n,[0]⟩ : LTy V)
        let afterState := Γ.insert stateName (⟨table t n,[0]⟩ : LTy V)
        let value' := boundVar afterState valueName (shared t)
        let draw' : Var (Γ.extend names') (shared t) := boundVar (afterState.insert valueName (shared t)) drawName (shared t)
        let sk ← retain state' (.cons valueName (.cons drawName .nil) : Names [shared t,shared t])
        let vk ← retain value' (.cons drawName .nil : Names [shared t])
        let pk ← retain pt names'
        let ⟨saved,keep⟩ ← retainList names' past
        let ⟨tail⟩ ← readReduction distinct evaluation n sk.after pk.after vk.after (saved ++ [draw']) rest
        return ⟨by
          intro M _ _ math path env x atS atP atV
          let sem := protocolSem M (Defs.fnTable M ds) (Defs.gTable M ds)
          let left := Env.empty.extend (names (state := table t (n+1)) (point := emptyPoint t) («t» := t))
            (HList.cons (V := LVal M) (Cube.flatten (n+1) x) (.cons [] (.cons (Cube.sum (n+1) x) .nil)))
          have aligned : StraightLine.Agrees pairs left env := by
            apply agreeCons (l := left) (r := env) (vAt 0 : Var _ (⟨table t (n+1),[0]⟩ : LTy V)) st
            · exact atS.symm
            apply agreeCons (vAt 2 : Var _ (shared t)) v
            · exact atV.symm
            intro _ _ h; contradiction
          rw [Term.denote_block]
          apply (Process.every_bind ..).mpr
          rw [← same sem _ left env aligned]
          apply Process.every_mono _ _ _ (fun _ h => h)
            (roundReturns rows law events M (math.scalar (Nat.zero_lt_succ _))
              (math.sum n (Nat.lt_succ_self _)) (math.vector n (Nat.lt_succ_self _)) math.equal _ sites x)
          rintro _ ⟨r,rfl⟩
          let y := Cube.restrict n x r
          let vs := result rows M x r
          let env' := env.extend names' vs
          let e1 := env.insert stateName (τ := (⟨table t n,[0]⟩ : LTy V)) (Cube.flatten n y)
          let e2 := e1.insert valueName (τ := shared t) (Cube.sum n y)
          have stateAt : env'.get sk.after = Cube.flatten n y :=
            (sk.get e1 (.cons (Cube.sum n y) (.cons r .nil))).trans (bound_get env _ _)
          have valAt : env'.get vk.after = Cube.sum n y :=
            (vk.get e2 (.cons r .nil)).trans (bound_get e1 _ _)
          have drawAt : env'.get draw' = r := bound_get e2 drawName (a := shared t) r
          have next := tail M (math.tail rows sums vectors events) path env' y stateAt ((pk.get env vs).trans atP) valAt
          apply Process.every_mono _ _ _ (fun _ h => h) next
          rintro _ ⟨rs,value,evaluated,rfl⟩
          refine ⟨r::rs,value,evaluated,?_⟩
          have joined : (saved ++ [draw']).map env'.get ++ rs = past.map env.get ++ r :: rs := by
            simp only [List.map_append,List.map_cons,List.map_nil,drawAt,List.append_assoc,List.cons_append,List.nil_append]
            rw [show saved.map env'.get = past.map env.get from keep env vs]
          exact congrArg (fun ls => fullResult M (total := total) ls value) joined⟩
    else none
  | _+1, _, _, _, _, _, _ => none

end ZkcFormal.Interactive.Sumcheck.HonestPairs
