module

public import ZkcFormal.Interactive.ReductionExit
public import ZkcFormal.Interactive.RoundFamily

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.ReductionRound
open Zkc.Core
variable {V : Vocabulary} {t state residual : V.Ty} {k n : Nat}

abbrev reduction (key : Key) (state t residual : V.Ty) (k n : Nat) (shape : Shape V) : ProtocolHeader V :=
  caller key state (.seq t (some k)) t (PointReturn.ports t residual (k+n)) shape

abbrev initialNames (state t : V.Ty) (k : Nat) := names (state := state) (point := .seq t (some k)) (t := t)
abbrev initialPoint (state t : V.Ty) (k : Nat) : Var (Ctx.empty.extend (initialNames state t k)) (PointReturn.point t k) :=
  ⟨1,rfl⟩
abbrev initialClaim (state t : V.Ty) (k : Nat) : Var (Ctx.empty.extend (initialNames state t k)) (shared t) := ⟨2,rfl⟩

structure Linked (p : Zkc.Core.Typed V) (key : Key) (state t residual : V.Ty) (k n : Nat) (events : Events t) where
  shape : Shape V
  ref : Member p.headers.protocols (reduction key state t residual k n shape)
  entry : ProtocolEntry p.defs ref
  source : entry.AtInputs (initialNames state t k)
  rounds : Sequence entry.earlier events state (initialClaim state t k) source.body n
  exit : PointReturn.ReductionLaw rounds (initialPoint state t k) []

def link (p : Zkc.Core.Typed V) (key : Key) (state t residual : V.Ty) (k n : Nat) (events : Events t) :
    Option (Linked p key state t residual k n events) := do
  let ⟨shape,ref⟩ ← ProtocolEntry.locatePorts p.headers key 2 (inputs state (.seq t (some k)) t) (PointReturn.ports t residual (k+n))
  let entry := p.defs.protocolEntry p.distinct (show Member _ (reduction key state t residual k n shape) from ref)
  let source ← entry.atInputs (initialNames state t k)
  let unique := (List.nodup_append.mp entry.distinct).1
  let rounds ← readSequence unique events n state (initialClaim state t k) source.body
  let ⟨exit⟩ ← PointReturn.checkReduction unique rounds (initialPoint state t k) []
  return ⟨shape,ref,entry,source,rounds,exit⟩

variable {p : Zkc.Core.Typed V} {key : Key} {events : Events t}

def publicArgs (M : Model V) (hidden : RV M 1 ⟨state,[0]⟩) (point : List (M.Val t)) (claim : M.Val t) :
    HList (RV M 1) (inputs state (.seq t (some k)) t) :=
  .cons hidden (.cons (hide M 1 (PointReturn.point t k) point) (.cons (hide M 1 (shared t) claim) .nil))

theorem Linked.process (linked : Linked p key state t residual k n events) (M : Model V) (path : List Frame)
    (hidden : RV M 1 ⟨state,[0]⟩) (point : List (M.Val t)) (claim : M.Val t) :
    roleMeaning M p linked.ref 1 path (publicArgs M hidden point claim) =
    (linked.rounds.collect M (Defs.fnTable M linked.entry.definitions) (Defs.rTable M linked.entry.definitions)
      path (Env.empty.extend (initialNames state t k) (publicArgs M hidden point claim))).map
        fun (_,rs,v) => PointReturn.values M t residual (k+n) (point ++ rs) v := by
  rw [roleMeaning,linked.source.meaning,linked.exit]
  rfl

def correctReturn (M : Model V) [DecidableEq (M.Val t)] (q : Claims (M.Val t)) (x : q.State n) (prior : Nat) :
    HList (RV M 1) (PointReturn.ports t residual (k+n)) → Bool
  | .cons pt (.cons v (.cons _ .nil)) => decide (q.evaluate n x
      ((reveal M (a := PointReturn.point t (k+n)) (by simp) pt).drop prior) = some (reveal M (a := shared t) (by simp) v))

abbrev initialEnv (M : Model V) (hidden : RV M 1 ⟨state,[0]⟩) (k : Nat)
    (point : List (M.Val t)) (claim : M.Val t) :=
  Env.empty.extend (initialNames state t k) (publicArgs M hidden point claim)

/-- A bound on the returned point and scalar of the actual callee selected by its caller.
The public state is the remaining mathematical instance after the supplied prefix. -/
theorem Linked.soundFrom (linked : Linked p key state t residual k n events) (M : Model V) [DecidableEq (M.Val t)]
    (q : Claims (M.Val t)) (cost : Mass) (nonneg : 0 ≤ cost) {σ : Type} (K : Experiment (RSig M) σ)
    (path : List Frame)
    (s : σ) (hidden : RV M 1 ⟨state,[0]⟩) (point : List (M.Val t)) (claim : M.Val t) (x : q.State n)
    (wrong : claim ≠ q.value n x)
    (bounds : linked.rounds.BoundsFrom M (Defs.fnTable M linked.entry.definitions) (Defs.rTable M linked.entry.definitions)
      K q cost path (initialEnv M hidden k point claim) s x) :
    K.probability (roleMeaning M p linked.ref 1 path (publicArgs M hidden point claim)) s
      (fun vs _ => correctReturn M q x point.length vs) ≤ (n : Mass) * cost := by
  rw [linked.process]
  let env := Env.empty.extend (initialNames state t k) (publicArgs M hidden point claim)
  have charged := linked.rounds.soundFrom M _ _ K q cost path nonneg env s x bounds wrong
  apply Mass.le_trans _ charged
  simp only [Experiment.probability,Process.map_eq_bind,Experiment.expect_bind,Experiment.expect_done]
  apply K.expect_mono
  intro (last,rs,v) _ _
  simp [correctReturn,PointReturn.values,reveal_hide]

/-- A bound on the returned point and scalar of the actual callee selected by its caller.
The public state is the remaining mathematical instance after the supplied prefix. -/
theorem Linked.sound (linked : Linked p key state t residual k n events) (M : Model V) [DecidableEq (M.Val t)]
    (q : Claims (M.Val t)) (cost : Mass) (nonneg : 0 ≤ cost) {σ : Type} (K : Experiment (RSig M) σ)
    (path : List Frame) (bounds : linked.rounds.RoundBounds M (Defs.fnTable M linked.entry.definitions)
      (Defs.rTable M linked.entry.definitions) K q cost path)
    (s : σ) (hidden : RV M 1 ⟨state,[0]⟩) (point : List (M.Val t)) (claim : M.Val t) (x : q.State n)
    (wrong : claim ≠ q.value n x) :
    K.probability (roleMeaning M p linked.ref 1 path (publicArgs M hidden point claim)) s
      (fun vs _ => correctReturn M q x point.length vs) ≤ (n : Mass) * cost := by
  exact linked.soundFrom M q cost nonneg K path s hidden point claim x wrong (bounds _ s x)

#print axioms Linked.sound
end ZkcFormal.Interactive.Sumcheck.ReductionRound
