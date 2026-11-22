module

public import ZkcFormal.Interactive.RoundCharge

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.ReductionRound
open Zkc.Core
variable {V : Vocabulary} {hs : Headers V} {t : V.Ty}

/-- A property of the actual operation references, independent of SSA names at a call. -/
abbrev MemberLaw (hs : Headers V) (t : V.Ty) :=
  ∀ {msg state residual : V.Ty}, Members hs t msg state residual → Prop

namespace Sequence
variable {events : Events t} {outs : List (LTy V)}
def AllMembers (law : MemberLaw hs t) {Γ : Ctx (LTy V)} {state : V.Ty} {claim : Var Γ (shared t)}
    {term : Term (protocolDialect V hs) Γ outs} {count : Nat} (rounds : Sequence hs events state claim term count) : Prop :=
  match rounds with
  | .done _ => True
  | .more round _ _ _ _ next => law round.members ∧ next.AllMembers law

def checkMembers (law : MemberLaw hs t)
    (check : ∀ {msg state residual} (ops : Members hs t msg state residual), Option (PLift (law ops)))
    {Γ : Ctx (LTy V)} {state : V.Ty} {claim : Var Γ (shared t)}
    {term : Term (protocolDialect V hs) Γ outs} {count : Nat} (rounds : Sequence hs events state claim term count) :
    Option (PLift (rounds.AllMembers law)) :=
  match rounds with
  | .done _ => some ⟨True.intro⟩
  | .more round _ _ _ _ next => do
    let ⟨head⟩ ← check round.members
    let ⟨tail⟩ ← next.checkMembers law check
    return ⟨head,tail⟩

end Sequence

/-- An interpretation uses the collision law only at the depths selected by its index. -/
structure RoundInterpretationOn (M : Model V) [DecidableEq (M.Val t)] (fns : FnTable M hs.fns) (q : Claims (M.Val t))
    (points : List (M.Val t)) (degree : Nat) {msg state residual : V.Ty} (ops : Members hs t msg state residual)
    {ι : Type} (depth : ι → Nat) where
  boundary : M.Val msg → M.Val t
  evaluate : M.Val msg → M.Val t → M.Val t
  ends : ∀ m, localOp M fns ops.boundary (.cons m .nil) = .done (.cons (boundary m) .nil)
  atPoint : ∀ m r, localOp M fns ops.evaluate (.cons m (.cons r .nil)) = .done (.cons (evaluate m r) .nil)
  roots : ∀ i (x : q.State (depth i + 1)) m, boundary m ≠ q.value (depth i + 1) x →
    points.countP (fun r => decide (evaluate m r = q.value (depth i) (q.restrict (depth i) x r))) ≤ degree

/-- A uniform interpretation supplies the same laws at every natural depth. -/
abbrev RoundInterpretation (M : Model V) [DecidableEq (M.Val t)] (fns : FnTable M hs.fns) (q : Claims (M.Val t))
    (points : List (M.Val t)) (degree : Nat) {msg state residual : V.Ty} (ops : Members hs t msg state residual) :=
  RoundInterpretationOn M fns q points degree ops (id : Nat → Nat)

def RoundInterpretationOn.reindex {M : Model V} [DecidableEq (M.Val t)] {fns : FnTable M hs.fns}
    {q : Claims (M.Val t)} {points : List (M.Val t)} {degree : Nat} {msg state residual : V.Ty}
    {ops : Members hs t msg state residual} {ι κ : Type} {depth : ι → Nat}
    (law : RoundInterpretationOn M fns q points degree ops depth) (select : κ → ι) :
    RoundInterpretationOn M fns q points degree ops (fun i => depth (select i)) :=
  { law with roots := fun i => law.roots (select i) }

namespace Sequence
variable {events : Events t} {Γ : Ctx (LTy V)} {state : V.Ty} {claim : Var Γ (shared t)}
variable {outs : List (LTy V)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat}

/-- Uniformity is needed only after a supported message whose actual boundary passes.
Each recursive obligation starts after a supported return of the preceding source block. -/
def FreshFrom (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) {σ : Type}
    (K : Experiment (RSig M) σ) (points : List (M.Val t)) (positive : 0 < points.length)
    {Γ : Ctx (LTy V)} {state : V.Ty} {claim : Var Γ (shared t)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat}
    (rounds : Sequence hs events state claim term count) (path : List Frame) (env : Env (RV M 1) Γ) (s : σ) : Prop :=
  match rounds with
  | .done _ => True
  | @more _ _ _ _ _ _ _ _ _ _ inside round key index ns _ _ next =>
    let atBlock := path ++ [Frame.iteration key index]
    (∀ m after, K.Reaches (receive M round.msg atBlock (round.sites 1)) s m after →
      localOp M fns round.members.boundary (.cons m .nil) = .done (.cons (scalar M env claim) .nil) →
      Fresh K points positive (challenge M events atBlock (challengeSite round.sites)) after) ∧
    ∀ vs after, K.Reaches ((project 1 inside).denote (roleSem M 1 fns roles) atBlock env) s vs after →
      next.FreshFrom M fns roles K points positive path (env.extend ns vs) after

theorem freshFromService (rounds : Sequence hs events state claim term count) (M : Model V)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) {σ : Type}
    (K : Experiment (RSig M) σ) (points : List (M.Val t)) (positive : 0 < points.length)
    (fresh : ∀ path coin s, Fresh K points positive (challenge M events path coin) s)
    (path : List Frame) (env : Env (RV M 1) Γ) (s : σ) : rounds.FreshFrom M fns roles K points positive path env s := by
  induction rounds generalizing s with
  | done => trivial
  | more round key index ns binders rest ih => exact ⟨fun _ after _ _ => fresh _ _ after,fun _ _ _ => ih _ _⟩

/-- One interpretation for each executed member, indexed by its remaining depth. -/
def AtDepth (M : Model V) [DecidableEq (M.Val t)] (fns : FnTable M hs.fns)
    (q : Claims (M.Val t)) (points : List (M.Val t)) (degree : Nat)
    {Γ : Ctx (LTy V)} {state : V.Ty} {claim : Var Γ (shared t)}
    {outs : List (LTy V)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat}
    (rounds : Sequence hs events state claim term count) : Type :=
  match rounds with
  | .done _ => PUnit
  | @more _ _ _ _ _ _ _ _ _ n _ round _ _ _ _ _ next =>
      RoundInterpretationOn M fns q points degree round.members (fun _ : Unit => n) ×
        AtDepth M fns q points degree next

def checkAtDepth (M : Model V) [DecidableEq (M.Val t)] (fns : FnTable M hs.fns)
    (q : Claims (M.Val t)) (points : List (M.Val t)) (degree : Nat)
    (supply : ∀ {msg st residual}, (ops : Members hs t msg st residual) →
      Key → Nat → (n : Nat) → Option (RoundInterpretationOn M fns q points degree ops (fun _ : Unit => n)))
    {Γ : Ctx (LTy V)} {state : V.Ty} {claim : Var Γ (shared t)} {outs : List (LTy V)}
    {term : Term (protocolDialect V hs) Γ outs} {count : Nat} (rounds : Sequence hs events state claim term count) :
    Option (AtDepth M fns q points degree rounds) :=
  match rounds with
  | .done _ => some PUnit.unit
  | @more _ _ _ _ _ _ _ _ _ n _ round key index _ _ _ next => do
    let head ← supply round.members key index n
    let tail ← checkAtDepth M fns q points degree supply next
    return ⟨head, tail⟩

theorem boundsAtDepth (rounds : Sequence hs events state claim term count) (M : Model V)
    [DecidableEq (M.Val t)] (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (q : Claims (M.Val t))
    (points : List (M.Val t)) (positive : 0 < points.length) (degree : Nat)
    (cert : AtDepth M fns q points degree rounds)
    (equalLaw : ScalarEquality.Law t events.equal events.equalType M) {σ : Type} (K : Experiment (RSig M) σ)
    (path : List Frame) (env : Env (RV M 1) Γ) (s : σ) (x : q.State count)
    (fresh : rounds.FreshFrom M fns roles K points positive path env s) :
    rounds.BoundsFrom M fns roles K q (roundCost degree points) path env s x := by
  induction rounds generalizing s with
  | done => trivial
  | @more _ _ _ _ _ n inside round key index ns binders rest next ih =>
    obtain ⟨head,tail⟩ := cert
    obtain ⟨here,later⟩ := fresh
    refine ⟨?_,fun values after reached => ih tail _ after _ (later values after reached)⟩
    intro wrong
    apply round.charge ns binders M fns roles equalLaw head.boundary head.evaluate head.ends head.atPoint K s points positive
      (path ++ [Frame.iteration key index]) env (fun r => q.value n (q.restrict n x r)) degree
    · intro m after received passed
      exact here m after received ((head.ends m).trans (by rw [passed]))
    · intro m passed
      exact head.roots () x m (passed ▸ wrong)

noncomputable def adaptMembers (rounds : Sequence hs events state claim term count) (law : MemberLaw hs t)
    (verified : rounds.AllMembers law) (M : Model V) [DecidableEq (M.Val t)]
    (fns : FnTable M hs.fns) (q : Claims (M.Val t)) (points : List (M.Val t)) (degree : Nat)
    (interpret : ∀ {msg st residual} (ops : Members hs t msg st residual), law ops →
      RoundInterpretationOn M fns q points degree ops (Fin.val (n := count))) :
    AtDepth M fns q points degree rounds := by
  induction rounds with
  | done => exact PUnit.unit
  | @more _ _ _ _ _ n inside round key index ns binders rest next ih =>
    exact ⟨(interpret round.members verified.1).reindex (fun _ : Unit => Fin.last n),
      ih verified.2 (fun ops ok => (interpret ops ok).reindex (Fin.castLE (Nat.le_succ n)))⟩

theorem boundsFromMembers (rounds : Sequence hs events state claim term count) (law : MemberLaw hs t)
    (verified : rounds.AllMembers law) (M : Model V) [DecidableEq (M.Val t)]
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (q : Claims (M.Val t))
    (points : List (M.Val t)) (positive : 0 < points.length) (degree : Nat)
    (interpret : ∀ {msg st residual} (ops : Members hs t msg st residual), law ops →
      RoundInterpretationOn M fns q points degree ops (Fin.val (n := count)))
    (equalLaw : ScalarEquality.Law t events.equal events.equalType M) {σ : Type} (K : Experiment (RSig M) σ)
    (path : List Frame) (env : Env (RV M 1) Γ) (s : σ) (x : q.State count)
    (fresh : rounds.FreshFrom M fns roles K points positive path env s) :
    rounds.BoundsFrom M fns roles K q (roundCost degree points) path env s x := by
  exact rounds.boundsAtDepth M fns roles q points positive degree
    (rounds.adaptMembers law verified M fns q points degree interpret) equalLaw K path env s x fresh

theorem boundsOfMembers (rounds : Sequence hs events state claim term count) (law : MemberLaw hs t)
    (verified : rounds.AllMembers law) (M : Model V) [DecidableEq (M.Val t)]
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (q : Claims (M.Val t))
    (points : List (M.Val t)) (positive : 0 < points.length) (degree : Nat)
    (interpret : ∀ {msg st residual} (ops : Members hs t msg st residual), law ops →
      RoundInterpretationOn M fns q points degree ops (Fin.val (n := count)))
    (equalLaw : ScalarEquality.Law t events.equal events.equalType M) {σ : Type} (K : Experiment (RSig M) σ)
    (fresh : ∀ path key s, Fresh K points positive (challenge M events path key) s) (path : List Frame) :
    rounds.RoundBounds M fns roles K q (roundCost degree points) path := by
  intro env s x
  exact rounds.boundsFromMembers law verified M fns roles q points positive degree interpret equalLaw K path env s x
    (rounds.freshFromService M fns roles K points positive fresh path env s)

#print axioms boundsOfMembers
end Sequence
end ZkcFormal.Interactive.Sumcheck.ReductionRound
