module

public import Zkc.Formal.Interactive.AppliedReduction
public import Zkc.Formal.Interactive.PairSequence
public import Zkc.Formal.Interactive.TableEvaluation
public import Zkc.Formal.Interactive.TraceLength

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.TableVerifier
open Core ReductionRound
open TableHalves (table)
variable {V : Vocabulary} {t : V.Ty} {n : Nat} {red eval : Key} {sh : Shape V} {hs : Headers V}
abbrev header (t : V.Ty) (n : Nat) (key : Key) (shape : Shape V) : ProtocolHeader V :=
  ⟨key,2,[shared (table t n),shared t],[],shape⟩
abbrev reduction (t : V.Ty) (n : Nat) (key : Key) (shape : Shape V) :=
  ReductionRound.reduction key (table t n) t (table t 0) 0 n shape
abbrev start (t : V.Ty) (n : Nat) := Ctx.empty.extend (.cons 0 (.cons 1 .nil) : Names [shared (table t n),shared t])
abbrev ready (t : V.Ty) (n : Nat) := (start t n).insert 2 (PointReturn.point t 0)
abbrev outputs (t : V.Ty) (n : Nat) : Names (PointReturn.ports t (table t 0) (0+n)) := .cons 3 (.cons 4 (.cons 5 .nil))

variable (events : Events t) (callee : Member hs.protocols (reduction t n red sh))
variable (evaluate : Member hs.fns (TableEvaluation.header t eval n (0+n)))
local macro "varAt " n:term:max : term => `(⟨$n,rfl⟩)

def tail : Term (protocolDialect V hs) ((ready t n).extend (outputs t n)) [] :=
  .op ⟨2⟩ (.compute [1] (.call evaluate) [shared (table t n),PointReturn.point t (0+n)] rfl (by
    intro a h; rcases List.mem_cons.mp h with rfl | h
    · simp
    · obtain rfl := List.mem_singleton.mp h; simp)) (.cons (varAt 0) (.cons (varAt 3) .nil)) (.cons 6 .nil) <|
  .op ⟨3⟩ (.compute [1] (.row events.equal _ events.equalType) [shared t,⟨t,[1]⟩] rfl (by
    intro a h; rcases List.mem_cons.mp h with rfl | h
    · simp
    · obtain rfl := List.mem_singleton.mp h; simp)) (.cons (varAt 4) (.cons (varAt 6) .nil)) (.cons 7 .nil) <|
  .guard ⟨4⟩ [1] (varAt 7) (by simp) .reject (.ret .nil)

def body (key : Key) (shape : Shape V) : Prot V hs (header t n key shape) (.cons 0 (.cons 1 .nil)) :=
  .op ⟨0⟩ (.compute [0,1] (.owned (.makeSeq t 0)) [] rfl (by simp)) .nil (.cons 2 .nil) <|
  .op ⟨1⟩ (.apply callee [0,1] (by decide) rfl [shared (table t n),PointReturn.point t 0,shared t] (by
    change (_ = _ ∧ ∀ r, r ∈ [0] → r ∈ [0,1]) ∧
      (_ = _ ∧ ∀ r, r ∈ [0,1] → r ∈ [0,1]) ∧ (_ = _ ∧ ∀ r, r ∈ [0,1] → r ∈ [0,1]) ∧ True
    simp)) (.cons (varAt 0) (.cons (varAt 2) (.cons (varAt 1) .nil))) (outputs t n) <| tail events evaluate

def args (M : Model V) (data : List (M.Val t)) (claim : M.Val t) : HList (RV M 1) [shared (table t n),shared t] :=
  .cons (hide M 1 (shared (table t n)) data) (.cons (hide M 1 (shared t) claim) .nil)

def atCall (M : Model V) (data : List (M.Val t)) (claim : M.Val t) : Env (RV M 1) (ready t n) :=
  (Env.empty.extend (.cons 0 (.cons 1 .nil)) (args (n := n) M data claim)).insert 2 (hide M 1 (PointReturn.point t 0) [])

def witness (key : Key) (shape : Shape V) : ProtocolEntry.Body hs (header t n key shape) :=
  ⟨.cons 0 (.cons 1 .nil), body events callee evaluate key shape,rfl⟩

def onReturn (M : Model V) (ds : Defs V hs) (path : List Frame) (data : List (M.Val t)) (claim : M.Val t)
    (vs : HList (RV M 1) (PointReturn.ports t (table t 0) (0+n))) : Program M (HList (RV M 1) []) :=
  (project 1 (tail events evaluate)).denote (roleSem M 1 (Defs.fnTable M ds) (Defs.rTable M ds)) path
    ((atCall M data claim).extend (outputs t n) vs)

theorem callerProcess (key : Key) (shape : Shape V) (M : Model V) (ds : Defs V hs)
    (path : List Frame) (data : List (M.Val t)) (claim : M.Val t) :
    (witness events callee evaluate key shape).meaning ds 1 M path (args M data claim) =
    (mapR M peerMap.to (Defs.rTable M ds _ callee 1 (path ++ [.application ⟨1⟩])
      (publicArgs M (nothing M (by simp)) [] claim))).bind
      fun vs => onReturn events evaluate M ds path data claim (leaveAll M peerMap 1 vs) := by
  let run := mapR M peerMap.to (Defs.rTable M ds _ callee 1 (path ++ [.application ⟨1⟩]) (publicArgs M (nothing M (by simp)) [] claim))
  exact Process.bind_map (leaveAll M peerMap 1 (items := PointReturn.ports t (table t 0) (0+n))) (onReturn events evaluate M ds path data claim) run

theorem guardValue (M : Model V) [DecidableEq (M.Val t)] (ds : Defs V hs) (path : List Frame)
    (data : List (M.Val t)) (claim : M.Val t) (rs : List (M.Val t)) (v expected : M.Val t)
    (equality : ScalarEquality.Law t events.equal events.equalType M)
    (computed : Defs.fnTable M ds _ evaluate (.cons data (.cons rs .nil)) = .done (.cons expected .nil)) :
    onReturn events evaluate M ds path data claim (leaveAll M peerMap 1 (PointReturn.values M t (table t 0) (0+n) rs v)) =
    if v = expected then .done .nil else .halt (.declared .reject ⟨path,⟨4⟩⟩) := by
  change ((liftLocal id (Defs.fnTable M ds _ evaluate (.cons data (.cons rs .nil)))).map _).bind _ = _
  rw [computed]
  have eqRow : localOp M (Defs.fnTable M ds) (.row events.equal _ events.equalType) (.cons v (.cons expected .nil)) =
      .done (.cons (decide (v = expected)) .nil) := by simp only [localOp,equality v expected]
  change ((liftLocal id (localOp M (Defs.fnTable M ds) (.row events.equal _ events.equalType)
    (.cons v (.cons expected .nil)))).map _).bind _ = _
  rw [eqRow]
  change (bif decide (v = expected) then Process.done HList.nil else .halt (Stop.declared .reject ⟨path,⟨4⟩⟩)).bind _ = _
  by_cases same : v = expected <;> simp [same,Process.bind] <;> rfl

end Zkc.Formal.Interactive.Sumcheck.TableVerifier
