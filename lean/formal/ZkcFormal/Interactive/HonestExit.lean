module

public import ZkcFormal.Interactive.HonestRound

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.HonestPairs
open Zkc.Core ReductionRound PointReturn
open TableHalves (table)
variable {V : Vocabulary} {hs : Headers V} {t : V.Ty} {Γ : Ctx (LTy V)} {total : Nat}

theorem agreeCons {T : Type} {F : T → Type} {C D : Ctx T} {a : T}
    {l : Env F C} {r : Env F D} (v : Var C a) (w : Var D a) {pairs : StraightLine.NamesMap}
    (same : l.get v = r.get w) (rest : StraightLine.Agrees pairs l r) :
    StraightLine.Agrees ((v.name,w.name)::pairs) l r := by
  intro x y mem ty hx hy
  rcases List.mem_cons.mp mem with eq | mem
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    obtain rfl := Option.some.inj (hx.symm.trans v.typed)
    exact same
  · exact rest x y mem ty hx hy

def fullResult (M : Model V) (xs : List (M.Val t)) (v : M.Val t) :
    HList (LVal M) (ports t (table t 0) total) := .cons xs (.cons v (.cons [v] .nil))

def assembleOp (t : V.Ty) (n : Nat) : ProtocolOp V hs (List.replicate n (shared t)) [point t n] :=
  .compute [0,1] (.owned (.makeSeq t n)) _ (operandTypes n) (by
    intro a h
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp h
    exact fun _ h => h)

private theorem computeCons (M : Model V) {a : LTy V} {as : List (LTy V)} {ts : List V.Ty}
    (types : as.map (·.ty) = ts) (v : LVal M a) (vs : HList (LVal M) as) :
    computeArgs M (operands := a::as) (congrArg (List.cons a.ty) types) (.cons v vs) =
      .cons v (computeArgs M types vs) := by subst ts; rfl

private theorem items (M : Model V) (env : Env (LVal M) Γ) (xs : List (Var Γ (shared t))) :
    HList.toItems M xs.length (computeArgs M (operandTypes _) (env.all (locations xs))) =
      xs.map env.get := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change HList.toItems M (xs.length+1) (computeArgs M _ (.cons _ _)) = _
    rw [computeCons M (operandTypes xs.length)]
    exact congrArg (List.cons (env.get a)) ih

abbrev tailInputs (t : V.Ty) (n : Nat) : Names [point t 0,point t n,shared t,⟨table t 0,[0]⟩] :=
  .cons 0 (.cons 1 (.cons 2 (.cons 3 .nil)))
local macro "vAt " n:term:max : term => `(⟨$n,rfl⟩)

def exitTail (t : V.Ty) (n : Nat) (key : Nat → Key) :
    Term (protocolDialect V hs) (Ctx.empty.extend (tailInputs t n)) (ports t (table t 0) (0+n)) :=
  .op (key 0) (.compute [0,1] (.owned (.seqConcat t (some 0) (some n)))
    [point t 0,point t n] rfl (by intro a h; rcases List.mem_cons.mp h with rfl | h
                                  · exact fun _ h => h
                                  · obtain rfl := List.mem_singleton.mp h; exact fun _ h => h))
    (.cons (vAt 0) (.cons (vAt 1) .nil)) (.cons 4 .nil) <|
  .op (key 1) (.narrow [0,1] (fun _ h => h)) (.cons (vAt 4) .nil) (.cons 5 .nil) <|
  .op (key 2) (.narrow [0,1] (fun _ h => h)) (.cons (vAt 2) .nil) (.cons 6 .nil) <|
  .op (key 3) (.narrow [0] (fun _ h => h)) (.cons (vAt 3) .nil) (.cons 7 .nil) <|
  .ret (.cons (vAt 5) (.cons (vAt 6) (.cons (vAt 7) .nil)))

def ExitLaw (st : Var Γ ⟨table t 0,[0]⟩) (pt : Var Γ (point t 0)) (v : Var Γ (shared t))
    (xs : List (Var Γ (shared t))) (actual : Term (protocolDialect V hs) Γ (ports t (table t 0) total)) :=
  ∀ (M : Model V) (f : FnTable M hs.fns) (g : GTable M hs.protocols) path (env : Env (LVal M) Γ)
    (x : M.Val t), env.get pt = [] → env.get st = [x] → env.get v = x →
    actual.denote (protocolSem M f g) path env = .done (fullResult M (xs.map env.get) x)

def checkExit (distinct : hs.keys.Nodup) (st : Var Γ ⟨table t 0,[0]⟩) (pt : Var Γ (point t 0))
    (v : Var Γ (shared t)) (xs : List (Var Γ (shared t))) :
    (actual : Term (protocolDialect V hs) Γ (ports t (table t 0) total)) →
      Option (PLift (ExitLaw st pt v xs actual))
  | .op (ins := ins) (res := mid) key op args ns rest => by
    let n := xs.length
    exact if size : total = 0+n then by
      subst total
      exact if inputs : ins = List.replicate n (shared t) then by
        subst ins
        let rules := protocolRules hs
        let expected := assembleOp (hs := hs) t n
        exact if same : rules.printOp expected = rules.printOp op then by
          obtain ⟨rfl,eq⟩ := (rules.skel_lawful (protocolRules_lawful distinct)) expected op (decide_eq_true same)
          cases eq_of_heq eq
          match ns with
          | .cons name .nil => exact do
            let seen := diagonal (xs.map Var.name)
            if argsOk : StraightLine.arguments seen (locations xs) args then
              let ps ← retain pt (.cons name .nil)
              let vs ← retain v (.cons name .nil)
              let ss ← retain st (.cons name .nil)
              let ds := boundVar Γ name (point t n)
              let pairs := [(0,ps.after.name),(1,ds.name),(2,vs.after.name),(3,ss.after.name)]
              let keys := instructionSite (eraseBody rules.printOp rules.printWho rest).1
              let ⟨tail⟩ ← StraightLine.compare rules.skel (rules.skel_lawful (protocolRules_lawful distinct))
                pairs (exitTail t n keys) rest
              return ⟨by
                intro M f g path env x atP atS atV
                have operands := (agrees env (xs.map Var.name)).arguments _ _ argsOk
                let draws := xs.map env.get
                have head : protocolOp M f g key expected path (env.all args) = .done (.cons draws .nil) := by
                  rw [← operands]
                  exact congrArg (fun a => Process.done (A := HList (LVal M) [point t n]) (.cons a .nil))
                    (items M env xs)
                change (protocolOp M f g key expected path (env.all args)).bind _ = _
                rw [head]
                let vals : HList (LVal M) [point t n] := .cons draws .nil
                let right := env.extend (.cons name .nil) vals
                let left := Env.empty.extend (tailInputs t n) (HList.cons (V := LVal M) [] (.cons draws (.cons x (.cons [x] .nil))))
                have aligned : StraightLine.Agrees pairs left right := by
                  apply agreeCons (vAt 0 : Var _ (point t 0)) ps.after
                  · exact ((ps.get env vals).trans atP).symm
                  apply agreeCons (vAt 1 : Var _ (point t n)) ds
                  · exact (bound_get env name (a := point t n) draws).symm
                  apply agreeCons (vAt 2 : Var _ (shared t)) vs.after
                  · exact ((vs.get env vals).trans atV).symm
                  apply agreeCons (vAt 3 : Var (Ctx.empty.extend (tailInputs t n)) ⟨table t 0,[0]⟩) ss.after
                  · exact ((ss.get env vals).trans atS).symm
                  · intro _ _ h; contradiction
                exact (tail (protocolSem M f g) path left right aligned).symm⟩
            else none
        else none
      else none
    else none
  | _ => none

end ZkcFormal.Interactive.Sumcheck.HonestPairs
