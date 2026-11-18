module

public import Zkc.Formal.Interactive.PointReturn

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound.PointReturn
open Core
variable {T : Type} {Γ : Ctx T} {a : T} {types : List T}

/-- Transport a port through a block result binding only if its old SSA value is still
available under that name. -/
structure Retained (v : Var Γ a) (ns : Names types) where
  after : Var (Γ.extend ns) a
  get : ∀ {F : T → Type} (env : Env F Γ) (vs : HList F types), (env.extend ns vs).get after = env.get v

def retain {Γ : Ctx T} (v : Var Γ a) : {types : List T} → (ns : Names types) → Option (Retained v ns)
  | [], .nil => some ⟨v,fun _ .nil => rfl⟩
  | b::_, .cons name rest =>
    if apart : v.name ≠ name then do
      let kept ← retain (older v name b apart) rest
      return ⟨kept.after,fun env (.cons w vs) => (kept.get (env.insert name w) vs).trans (older_get env v name w apart)⟩
    else none

variable {V : Vocabulary} {hs : Headers V} {t residual : V.Ty} {Δ : Ctx (LTy V)}

structure RetainedDraws (xs : List (Var Δ (shared t))) {ts : List (LTy V)} (ns : Names ts) where
  after : List (Var (Δ.extend ns) (shared t))
  get : ∀ (M : Model V) (env : Env (RV M 1) Δ) (vs : HList (RV M 1) ts),
    after.map (Sequence.scalar M (env.extend ns vs)) = xs.map (Sequence.scalar M env)

def retainDraws {ts : List (LTy V)} (ns : Names ts) : (xs : List (Var Δ (shared t))) → Option (RetainedDraws xs ns)
  | [] => some ⟨[],fun _ _ _ => rfl⟩
  | v::xs => do
    let kept ← retain v ns
    let tail ← retainDraws ns xs
    return ⟨kept.after::tail.after,fun M env vs => by simp only [List.map_cons,Sequence.scalar,kept.get,tail.get]⟩

def diagonal (names : List Name) := names.map fun n => (n,n)

theorem agrees {F : T → Type} (env : Env F Γ) (names : List Name) : StraightLine.Agrees (diagonal names) env env := by
  intro a b mem ty ha hb
  obtain ⟨n,_,eq⟩ := List.mem_map.mp mem
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
  rfl

def ExitLaw {k total : Nat} (initial : Var Δ (point t k)) (running : Var Δ (shared t)) (xs : List (Var Δ (shared t)))
    (actual : Term (protocolDialect V hs) Δ (ports t residual total)) : Prop :=
  ∀ (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) path (env : Env (RV M 1) Δ),
    (project 1 actual).denote (roleSem M 1 fns roles) path env = .done (values M t residual total
      (reveal M (a := point t k) (by simp) (env.get initial) ++ xs.map (Sequence.scalar M env)) (Sequence.scalar M env running))

def checkExit (unique : (hs.fns.map (·.key)).Nodup) {k total : Nat} (initial : Var Δ (point t k))
    (running : Var Δ (shared t)) (xs : List (Var Δ (shared t)))
    (actual : Term (protocolDialect V hs) Δ (ports t residual total)) : Option (PLift (ExitLaw initial running xs actual)) := do
  if size : total = k + xs.length then
    return ← show Option _ from by
      subst total
      let keys := instructionSite (eraseBody (protocolRules hs).printOp (protocolRules hs).printWho actual).1
      let observed := initial.name :: running.name :: xs.map Var.name
      exact do
        let ⟨same⟩ ← StraightLine.compare (BodyAnalysis.roleChecks 1) (BodyAnalysis.roleChecks_lawful unique)
          (diagonal observed) (body (residual := residual) initial running xs keys) (project 1 actual)
        return ⟨fun M fns roles path env =>
          (same _ _ _ _ (agrees env observed)).symm.trans (result initial running xs keys M fns roles path env)⟩
  else none

variable {events : Events t} {state : V.Ty} {running : Var Δ (shared t)} {k total count : Nat}
variable {actual : Term (protocolDialect V hs) Δ (ports t residual total)}

/-- The actual reduction returns the original public prefix, each freshly returned
challenge in source order, and the claim of the last block. -/
def ReductionLaw (rounds : Sequence hs events state running actual count) (initial : Var Δ (point t k))
    (prior : List (Var Δ (shared t))) : Prop :=
  ∀ (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) path (env : Env (RV M 1) Δ),
    (project 1 actual).denote (roleSem M 1 fns roles) path env =
    (rounds.collect M fns roles path env).map fun (_,rs,v) => values M t residual total
      (reveal M (a := point t k) (by simp) (env.get initial) ++ (prior.map (Sequence.scalar M env) ++ rs)) v

def checkReduction (unique : (hs.fns.map (·.key)).Nodup) {Δ : Ctx (LTy V)} {state : V.Ty}
    {running : Var Δ (shared t)} {actual : Term (protocolDialect V hs) Δ (ports t residual total)} {count : Nat}
    (rounds : Sequence hs events state running actual count) (initial : Var Δ (point t k))
    (prior : List (Var Δ (shared t))) : Option (PLift (ReductionLaw rounds initial prior)) :=
  match rounds with
  | .done rest => do
    let ⟨exit⟩ ← checkExit unique initial running prior rest
    return ⟨by
      intro M fns roles path env
      simpa only [Sequence.collect,Process.map,List.append_nil] using exit M fns roles path env⟩
  | .more round key index ns binders next => do
    let pointPort ← retain initial ns
    let draws ← retainDraws ns prior
    let ⟨tail⟩ ← checkReduction unique next pointPort.after (draws.after ++ [binders.draw])
    return ⟨by
      intro M fns roles path env
      change Process.bind _ _ = _
      simp only [Sequence.collect,Process.map_bind]
      apply congrArg (Process.bind _)
      funext vs
      rw [tail M fns roles path (env.extend ns vs),Process.map_map]
      apply congrArg (fun f => (next.collect M fns roles path (env.extend ns vs)).map f)
      funext (last,rs,v)
      simp only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append,draws.get,pointPort.get]⟩

#print axioms checkReduction
end Zkc.Formal.Interactive.Sumcheck.ReductionRound.PointReturn
