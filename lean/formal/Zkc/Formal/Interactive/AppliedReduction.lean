module

public import Zkc.Formal.Interactive.MappedReduction
public import Zkc.Formal.Interactive.GateSequence

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Core

-- This file passes between the meaning of a program and its tables by definitional unfolding.
unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning

variable {V : Vocabulary} {state t residual : V.Ty} {k n : Nat} {p : Core.Typed V} {key : Key} {events : Events t}

/-- The private state and shared public reduction ports used by the GKR layer call. -/
def Linked.application (linked : Linked p key state t residual k n events) :
    RoleOp V p.headers 1 (inputs state (.seq t (some k)) t) (PointReturn.ports t residual (k+n)) :=
  .apply linked.ref [0,1] (by decide) rfl (inputs state (.seq t (some k)) t) (by
    change (_ = _ ∧ ∀ r, r ∈ [0] → r ∈ [0]) ∧ (_ = _ ∧ ∀ r, r ∈ [0,1] → r ∈ [0,1]) ∧
      (_ = _ ∧ ∀ r, r ∈ [0,1] → r ∈ [0,1]) ∧ True
    simp)

abbrev peerMap := RoleMap.ofList [0,1] (by decide)

theorem Linked.applied_soundFrom (linked : Linked p key state t residual k n events) (M : Model V) [DecidableEq (M.Val t)]
    (q : Claims (M.Val t)) (cost : Mass) (nonneg : 0 ≤ cost) {σ : Type} (K : Experiment (RSig M) σ)
    (site : Key) (path : List Frame)
    (s : σ) (hidden : RV M 1 ⟨state,[0]⟩) (point : List (M.Val t)) (claim : M.Val t) (x : q.State n)
    (wrong : claim ≠ q.value n x)
    (bounds : linked.rounds.BoundsFrom M (Defs.fnTable M linked.entry.definitions) (Defs.rTable M linked.entry.definitions)
      (K.renamePeers peerMap.to) q cost (path ++ [.application site]) (initialEnv M hidden k point claim) s x) :
    K.probability (roleOp M 1 (Defs.fnTable M p.defs) (Defs.rTable M p.defs) site linked.application path
      (publicArgs M hidden point claim)) s (fun vs _ => correctReturn M q x point.length vs) ≤ (n : Mass) * cost := by
  unfold Linked.application
  have atCall := K.probability_application 1 (Defs.fnTable M p.defs) (Defs.rTable M p.defs) linked.ref [0,1] (by decide) rfl
    (inputs state (.seq t (some k)) t) (by
      change (_ = _ ∧ ∀ r, r ∈ [0] → r ∈ [0]) ∧ (_ = _ ∧ ∀ r, r ∈ [0,1] → r ∈ [0,1]) ∧
        (_ = _ ∧ ∀ r, r ∈ [0,1] → r ∈ [0,1]) ∧ True
      simp) site path (publicArgs M hidden point claim) s (fun vs _ => correctReturn M q x point.length vs)
  refine (congrArg (fun a : Mass => a ≤ (n : Mass) * cost) atCall).mpr ?_
  have charged := linked.soundFrom M q cost nonneg (K.renamePeers peerMap.to) (path ++ [.application site])
    s hidden point claim x wrong bounds
  apply Mass.le_trans _ charged
  apply (K.renamePeers peerMap.to).expect_mono
  intro vs _ _
  cases vs with
  | cons pt rest =>
    cases rest with
    | cons v rest =>
      cases rest with
      | cons z rest =>
        cases rest
        exact Mass.le_refl

theorem Linked.applied_sound (linked : Linked p key state t residual k n events) (M : Model V) [DecidableEq (M.Val t)]
    (q : Claims (M.Val t)) (cost : Mass) (nonneg : 0 ≤ cost) {σ : Type} (K : Experiment (RSig M) σ)
    (site : Key) (path : List Frame) (bounds : linked.rounds.RoundBounds M (Defs.fnTable M linked.entry.definitions)
      (Defs.rTable M linked.entry.definitions) (K.renamePeers peerMap.to) q cost (path ++ [.application site]))
    (s : σ) (hidden : RV M 1 ⟨state,[0]⟩) (point : List (M.Val t)) (claim : M.Val t) (x : q.State n)
    (wrong : claim ≠ q.value n x) :
    K.probability (roleOp M 1 (Defs.fnTable M p.defs) (Defs.rTable M p.defs) site linked.application path
      (publicArgs M hidden point claim)) s (fun vs _ => correctReturn M q x point.length vs) ≤ (n : Mass) * cost := by
  exact linked.applied_soundFrom M q cost nonneg K site path s hidden point claim x wrong (bounds _ s x)

structure AtSite (p : Core.Typed V) {hdr : ProtocolHeader V} (root : Member p.headers.protocols hdr)
    (key site : Key) (state t residual : V.Ty) (k n : Nat) (events : Events t) (args : List Name) (moves : List OperationSite.Move) where
  callerEntry : ProtocolEntry p.defs root
  linked : Linked (earlier callerEntry) key state t residual k n events
  found : OperationSite.Contains site linked.application args moves (project 1 callerEntry.body)

def atSite (p : Core.Typed V) {hdr : ProtocolHeader V} (root : Member p.headers.protocols hdr)
    (key site : Key) (state t residual : V.Ty) (k n : Nat) (events : Events t) (args : List Name) (moves : List OperationSite.Move) :
    Option (AtSite p root key site state t residual k n events args moves) := do
  let ⟨caller,linked,operands,_,_,_,_,found⟩ ← mappedReduction root key site state t residual k n events
    1 [0,1] args moves
  return ← show Option _ from by
    if same : operands = inputs state (.seq t (some k)) t then
      subst operands
      exact some ⟨caller,linked,found⟩
    else exact none

def loopRoute (before : Nat) (loopKey : Key) (count inside : Nat) : List OperationSite.Move :=
  List.replicate before .next ++ .fixedLoop loopKey count :: List.replicate inside .next

/-- Reuse the degree-two reduction at the selected instruction of a reached layer iteration.
The public relation and gate model are supplied for that layer. -/
theorem AtSite.gate_soundFrom (rows : ScalarRows V) {hdr : ProtocolHeader V} {root : Member p.headers.protocols hdr}
    {events : Events rows.scalarTy} {site loopKey : Key} {args : List Name} {before layers inside : Nat}
    (atCall : AtSite p root key site state rows.scalarTy residual k n events args (loopRoute before loopKey layers inside))
    {primitive : V.RowKey} {bound : V.row primitive = some (Gate.signature rows)}
    (checked : atCall.linked.rounds.AllMembers (fun ops => Gate.Laws rows primitive bound atCall.linked.entry.definitions ops))
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] (math : rows.Arithmetic M)
    (model : Gate.Evaluation rows primitive bound M) (equalLaw : ScalarEquality.Law rows.scalarTy events.equal events.equalType M)
    (i : Fin layers) (q : Claims (rows.F M)) (honest : ∀ d : Fin n, q.State (d.val+1) → Quadratic (rows.F M))
    (sum : ∀ d x, q.value (d.val+1) x = (honest d x).boundary)
    (restricted : ∀ d x r, q.value d.val (q.restrict d.val x r) = (honest d x).eval r)
    {σ : Type} (K : Experiment (RSig M) σ) (points : List (rows.F M)) (distinct : points.Nodup) (positive : 0 < points.length)
    (path : List Frame) (s : σ) (hidden : RV M 1 ⟨state,[0]⟩) (point : List (rows.F M)) (claim : rows.F M)
    (x : q.State n) (wrong : claim ≠ q.value n x)
    (fresh : atCall.linked.rounds.FreshFrom M (Defs.fnTable M atCall.linked.entry.definitions)
      (Defs.rTable M atCall.linked.entry.definitions) (K.renamePeers peerMap.to) points positive
      ((path ++ [.iteration loopKey i.val]) ++ [.application site]) (initialEnv M hidden k point claim) s)
    (collisions : CollisionBound (Quadratic.boundary (F := rows.F M)) Quadratic.eval 2 := Quadratic.collisions) :
    K.probability (roleOp M 1 (Defs.fnTable M atCall.callerEntry.definitions) (Defs.rTable M atCall.callerEntry.definitions)
      site atCall.linked.application (path ++ [.iteration loopKey i.val]) (publicArgs M hidden point claim)) s
      (fun vs _ => correctReturn M q x point.length vs) ≤ (n : Mass) * roundCost 2 points := by
  apply atCall.linked.applied_soundFrom M q _ _ K site _ s hidden point claim x wrong _
  · exact Mass.mul_nonneg Mass.natCast_nonneg (Mass.le_of_lt (Mass.inv_pos.mpr (Mass.natCast_pos.mpr positive)))
  · exact atCall.linked.rounds.boundsFromMembers _ checked M _ _ q points positive 2
      (fun _ law => Gate.Laws.interpretOn rows law M math model q Fin.val honest sum restricted points distinct collisions) equalLaw _ _ _ s x fresh

/-- Reuse the degree-two reduction at the selected instruction of a reached layer iteration.
The public relation and gate model are supplied for that layer. -/
theorem AtSite.gate_sound (rows : ScalarRows V) {hdr : ProtocolHeader V} {root : Member p.headers.protocols hdr}
    {events : Events rows.scalarTy} {site loopKey : Key} {args : List Name} {before layers inside : Nat}
    (atCall : AtSite p root key site state rows.scalarTy residual k n events args (loopRoute before loopKey layers inside))
    {primitive : V.RowKey} {bound : V.row primitive = some (Gate.signature rows)}
    (checked : atCall.linked.rounds.AllMembers (fun ops => Gate.Laws rows primitive bound atCall.linked.entry.definitions ops))
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] (math : rows.Arithmetic M)
    (model : Gate.Evaluation rows primitive bound M) (equalLaw : ScalarEquality.Law rows.scalarTy events.equal events.equalType M)
    (i : Fin layers) (q : Claims (rows.F M)) (honest : ∀ d, q.State (d+1) → Quadratic (rows.F M))
    (sum : ∀ d x, q.value (d+1) x = (honest d x).boundary)
    (restricted : ∀ d x r, q.value d (q.restrict d x r) = (honest d x).eval r)
    {σ : Type} (K : Experiment (RSig M) σ) (points : List (rows.F M)) (distinct : points.Nodup) (positive : 0 < points.length)
    (fresh : ∀ path coin s, Fresh (K.renamePeers peerMap.to) points positive (challenge M events path coin) s)
    (path : List Frame) (s : σ) (hidden : RV M 1 ⟨state,[0]⟩) (point : List (rows.F M)) (claim : rows.F M)
    (x : q.State n) (wrong : claim ≠ q.value n x) :
    K.probability (roleOp M 1 (Defs.fnTable M atCall.callerEntry.definitions) (Defs.rTable M atCall.callerEntry.definitions)
      site atCall.linked.application (path ++ [.iteration loopKey i.val]) (publicArgs M hidden point claim)) s
      (fun vs _ => correctReturn M q x point.length vs) ≤ (n : Mass) * roundCost 2 points := by
  apply atCall.gate_soundFrom rows checked M math model equalLaw i q (fun d => honest d.val)
    (fun d => sum d.val) (fun d => restricted d.val) K points distinct positive
    path s hidden point claim x wrong
  exact atCall.linked.rounds.freshFromService M _ _ _ points positive fresh _ _ _

#print axioms AtSite.gate_sound
#print axioms Linked.applied_sound
#print axioms atSite
end Zkc.Formal.Interactive.Sumcheck.ReductionRound
