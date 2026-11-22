module

public import Zkc.Core.Evidence.ProtocolReadback
public import ZkcFormal.Interactive.ScalarEquality
public import ZkcFormal.Interactive.Sumcheck

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.ReductionRound
open Zkc.Core
variable {V : Vocabulary}

/-- The operations selected by the source instance may be ordinary calls or vocabulary rows. -/
structure Members (hs : Headers V) (scalar message state residual : V.Ty) where
  sendValue : LocalOp V hs.fns [state] [message]
  bindState : LocalOp V hs.fns [state,scalar] [residual]
  boundary : LocalOp V hs.fns [message] [scalar]
  evaluate : LocalOp V hs.fns [message,scalar] [scalar]

structure Events (scalar : V.Ty) where
  equal : V.RowKey
  equalType : V.row equal = some (ScalarEquality.signature scalar)
  law : V.LawKey
  coinType : (GivenKind.coin (V := V) law).Typed [] scalar

variable {hs : Headers V} {t msg state residual : V.Ty}
variable (ops : Members hs t msg state residual) (events : Events t)

abbrev inputs (state point t : V.Ty) : List (LTy V) := [⟨state,[0]⟩, ⟨point,[0,1]⟩, ⟨t,[0,1]⟩]
abbrev outputs (residual t : V.Ty) : List (LTy V) := [⟨residual,[0]⟩, ⟨t,[0,1]⟩, ⟨t,[0,1]⟩]
abbrev names {point : V.Ty} : Names (inputs state point t) := .cons 0 (.cons 1 (.cons 2 .nil))
local macro "varAt " n:term:max : term => `(⟨$n, rfl⟩)
local macro "available" : tactic => `(tactic|
  (intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
   first | (rcases ha with ha | ha <;> simp [ha]) | simp [ha]))

abbrev beforeDraw (state point t msg : V.Ty) : Ctx (LTy V) :=
  let start := Ctx.empty.extend (names (state := state) (point := point) (t := t))
  let sent := (start.insert 3 ⟨msg,[0]⟩).insert 4 ⟨msg,[0,1]⟩
  (sent.insert 5 ⟨t,[1]⟩).insert 6 ⟨.bool,[1]⟩

abbrev afterDraw (state point t msg : V.Ty) := (beforeDraw state point t msg).insert 7 ⟨t,[0,1]⟩

def finish (point : V.Ty) (sites : Nat → Key := Key.mk) : Term (protocolDialect V hs) (afterDraw state point t msg) (outputs residual t) :=
  .op (sites 6) (.compute [0] ops.bindState [⟨state,[0]⟩,⟨t,[0,1]⟩] rfl (by available))
    (.cons (varAt 0) (.cons (varAt 7) .nil)) (.cons 8 .nil) <|
  .op (sites 7) (.compute [0,1] ops.evaluate [⟨msg,[0,1]⟩,⟨t,[0,1]⟩] rfl (by available))
    (.cons (varAt 4) (.cons (varAt 7) .nil)) (.cons 9 .nil) <|
  .op (sites 8) (.narrow [0,1] (fun _ h => h)) (.cons (varAt 7) .nil) (.cons 10 .nil) <|
  .op (sites 9) (.narrow [0] (fun _ h => h)) (.cons (varAt 8) .nil) (.cons 11 .nil) <|
  .op (sites 10) (.narrow [0,1] (fun _ h => h)) (.cons (varAt 9) .nil) (.cons 12 .nil) <|
  .ret (.cons (varAt 11) (.cons (varAt 12) (.cons (varAt 10) .nil)))

/-- The draw in the common round layout. The argument maps instruction positions to the
keys recovered from this particular admitted block. -/
abbrev challengeSite (sites : Nat → Key) : Key := sites 5

def drawThenFinish (point : V.Ty) (sites : Nat → Key := Key.mk) : Term (protocolDialect V hs) (beforeDraw state point t msg) (outputs residual t) :=
  .op (challengeSite sites) (.given (.coin events.law) 1 [0] [] t events.coinType (by simp) (by decide)) .nil (.cons 7 .nil) <|
  finish ops point sites

def body (point : V.Ty) (sites : Nat → Key := Key.mk) :
    Term (protocolDialect V hs) (Ctx.empty.extend (names (state := state) (point := point) (t := t))) (outputs residual t) :=
  .op (sites 0) (.compute [0] ops.sendValue [⟨state,[0]⟩] rfl (by available))
    (.cons (varAt 0) .nil) (.cons 3 .nil) <|
  .op (sites 1) (.flow .message 0 [1] (by simp) (by decide)) (.cons (varAt 3) .nil) (.cons 4 .nil) <|
  .op (sites 2) (.compute [1] ops.boundary [⟨msg,[0,1]⟩] rfl (by available))
    (.cons (varAt 4) .nil) (.cons 5 .nil) <|
  .op (sites 3) (.compute [1] (.row events.equal _ events.equalType) [⟨t,[0,1]⟩,⟨t,[1]⟩] rfl (by available))
    (.cons (varAt 2) (.cons (varAt 5) .nil)) (.cons 6 .nil) <|
  .guard (sites 4) [1] (varAt 6) (by simp) .reject <|
  drawThenFinish ops events point sites


def receive (M : Model V) (msg : V.Ty) (path : List Frame) (key : Key := ⟨1⟩) : Program M (M.Val msg) :=
  .call (.get .message 0 ⟨path,key⟩ msg) Process.done

def challenge (M : Model V) (events : Events t) (path : List Frame) (key : Key := ⟨5⟩) : Program M (M.Val t) :=
  .call (.own (.coin events.law) [0] ⟨path,key⟩ [] .nil t) Process.done

def returned (M : Model V) (residual : V.Ty) (out : M.Val t × M.Val t) :
    HList (RV M 1) (outputs residual t) :=
  .cons (nothing M (by simp)) (.cons (hide M 1 ⟨t,[0,1]⟩ out.2) (.cons (hide M 1 ⟨t,[0,1]⟩ out.1) .nil))

set_option maxRecDepth 4096 in
private theorem finish_value (point : V.Ty) (M : Model V)
    (fns : FnTable M hs.fns) (protocols : RTable M hs.protocols) (path : List Frame)
    (env : Env (RV M 1) (afterDraw state point t msg)) (m : M.Val msg) (r : M.Val t)
    (msgAt : env.get (varAt 4) = hide M 1 ⟨msg,[0,1]⟩ m)
    (drawAt : env.get (varAt 7) = hide M 1 ⟨t,[0,1]⟩ r)
    (evaluate : M.Val msg → M.Val t → M.Val t)
    (law : ∀ a x, localOp M fns ops.evaluate (.cons a (.cons x .nil)) = .done (.cons (evaluate a x) .nil))
    (sites : Nat → Key := Key.mk) :
    (project 1 (finish ops point sites)).denote (roleSem M 1 fns protocols) path env =
      .done (returned M residual (r,evaluate m r)) := by
  let x := reveal M (r := 1) (a := ⟨msg,[0,1]⟩) (by simp) (env.get (varAt 4))
  let y := reveal M (r := 1) (a := ⟨t,[0,1]⟩) (by simp) (env.get (varAt 7))
  have hx : x = m := by simp [x,msgAt,reveal_hide]
  have hy : y = r := by simp [y,drawAt,reveal_hide]
  change ((liftLocal id (localOp M fns ops.evaluate (.cons x (.cons y .nil)))).map _).bind _ = _
  rw [law]
  change Process.done (returned M residual (y,evaluate x y)) = _
  rw [hx,hy]

private theorem call_ext {S : Sig} {H A : Type} (op : S.Op) {k l : S.Reply op → Process S H A}
    (agree : ∀ x, k x = l x) : Process.call op k = Process.call op l :=
  congrArg (Process.call op) (funext agree)

set_option maxRecDepth 4096 in
private theorem draw_value (point : V.Ty) (M : Model V) (fns : FnTable M hs.fns) (protocols : RTable M hs.protocols)
    (path : List Frame) (env : Env (RV M 1) (beforeDraw state point t msg)) (m : M.Val msg)
    (atMessage : env.get (varAt 4) = hide M 1 ⟨msg,[0,1]⟩ m)
    (evaluate : M.Val msg → M.Val t → M.Val t)
    (law : ∀ a x, localOp M fns ops.evaluate (.cons a (.cons x .nil)) = .done (.cons (evaluate a x) .nil))
    (sites : Nat → Key := Key.mk) :
    (project 1 (drawThenFinish ops events point sites)).denote (roleSem M 1 fns protocols) path env =
    ((challenge M events path (challengeSite sites)).map fun r => (r,evaluate m r)).map (returned M residual) := by
  change Process.call (S := RSig M) (H := Stop) (.own (.coin events.law) [0] ⟨path,sites 5⟩ [] .nil t) _ = Process.call _ _
  apply call_ext
  intro r
  let env' := env.extend (.cons 7 .nil) (.cons (hide M 1 ⟨t,[0,1]⟩ r) .nil)
  exact finish_value ops point M fns protocols path env' m r atMessage rfl evaluate law sites

set_option maxHeartbeats 600000 in
set_option maxRecDepth 4096 in
/-- At the verifier, the source block receives an arbitrary message, checks its boundary,
then draws at the actual occurrence and updates the claim. The prover's two private calls
are unconstrained. -/
theorem verifier (point : V.Ty) (M : Model V) [DecidableEq (M.Val t)]
    (fns : FnTable M hs.fns) (protocols : RTable M hs.protocols)
    (boundary : M.Val msg → M.Val t) (evaluate : M.Val msg → M.Val t → M.Val t)
    (equalLaw : ScalarEquality.Law t events.equal events.equalType M)
    (boundaryLaw : ∀ m, localOp M fns ops.boundary (.cons m .nil) = .done (.cons (boundary m) .nil))
    (evaluateLaw : ∀ m r, localOp M fns ops.evaluate (.cons m (.cons r .nil)) = .done (.cons (evaluate m r) .nil))
    (path : List Frame) (hidden : RV M 1 ⟨state,[0]⟩) (initialPoint : M.Val point) (claim : M.Val t) (sites : Nat → Key := Key.mk) :
    (project 1 (body ops events point sites)).denote (roleSem M 1 fns protocols) path
      (Env.empty.extend names (.cons hidden (.cons (hide M 1 ⟨point,[0,1]⟩ initialPoint) (.cons (hide M 1 ⟨t,[0,1]⟩ claim) .nil)))) =
    (verifierRound (receive M msg path (sites 1)) (fun _ => challenge M events path (challengeSite sites)) (.declared .reject ⟨path,sites 4⟩)
      boundary evaluate claim).map (returned M residual) := by
  change Process.call (S := RSig M) (H := Stop) (.get .message 0 ⟨path,sites 1⟩ msg) _ = Process.call _ _
  apply call_ext
  intro m
  change ((liftLocal id (localOp M fns ops.boundary (.cons m .nil))).map _).bind _ = _
  rw [boundaryLaw]
  have eqValue : localOp M fns (.row events.equal _ events.equalType)
      (.cons claim (.cons (boundary m) .nil)) = .done (.cons (decide (claim = boundary m)) .nil) := by
    simp only [localOp, equalLaw claim (boundary m)]
  change ((liftLocal id (localOp M fns (.row events.equal _ events.equalType)
    (.cons claim (.cons (boundary m) .nil)))).map _).bind _ = _
  rw [eqValue]
  change (bif decide (claim = boundary m) then Process.done HList.nil else
    .halt (Stop.declared .reject ⟨path,sites 4⟩)).bind _ =
    (if boundary m = claim then (challenge M events path (challengeSite sites)).map (fun r => (r,evaluate m r))
     else .halt (.declared .reject ⟨path,sites 4⟩)).map _
  by_cases h : boundary m = claim
  · conv => rhs; rw [ite_eq_left h]
    conv => lhs; arg 1; rw [decide_eq_true h.symm]
    dsimp only [Bool.cond_true,Process.bind]
    refine draw_value ops events point M fns protocols path _ m ?_ evaluate evaluateLaw sites
    rfl
  · have reverse : claim ≠ boundary m := Ne.symm h
    conv => rhs; rw [ite_eq_right h]
    conv => lhs; arg 1; rw [decide_eq_false reverse]
    rfl

#print axioms verifier
end ZkcFormal.Interactive.Sumcheck.ReductionRound
