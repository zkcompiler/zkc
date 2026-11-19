module

public import Zkc.Formal.Interactive.RoundPrefix

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Core
variable {V : Vocabulary} {hs : Headers V} {t state : V.Ty}
def instructionSite (steps : List (Instruction (ProtocolRaw V) (List Role))) (i : Nat) : Key :=
  match steps[i]? with
  | some (.op k ..) | some (.guard k ..) => k
  | _ => ⟨i⟩

def readLocated (distinct : (hs.fns.map (·.key)).Nodup) {Γ : Ctx (LTy V)} {mid : List (LTy V)}
    (state : V.Ty) (events : Events t) (running : Var Γ ⟨t,[0,1]⟩)
    (actual : Term (protocolDialect V hs) Γ mid) : Option (Located state events running actual) :=
  readCompared distinct state (emptyPoint t) events running actual

theorem Located.process {Γ : Ctx (LTy V)} {mid : List (LTy V)} {events : Events t}
    {running : Var Γ ⟨t,[0,1]⟩} {actual : Term (protocolDialect V hs) Γ mid}
    (round : Located state events running actual) (M : Model V) [DecidableEq (M.Val t)]
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (path : List Frame) (env : Env (RV M 1) Γ)
    (claim : M.Val t) (atClaim : env.get running = hide M 1 ⟨t,[0,1]⟩ claim)
    (boundary : M.Val round.msg → M.Val t) (evaluate : M.Val round.msg → M.Val t → M.Val t)
    (equalLaw : ScalarEquality.Law t events.equal events.equalType M)
    (ends : ∀ m, localOp M fns round.members.boundary (.cons m .nil) = .done (.cons (boundary m) .nil))
    (atPoint : ∀ m r, localOp M fns round.members.evaluate (.cons m (.cons r .nil)) = .done (.cons (evaluate m r) .nil)) :
    (project 1 (round.types ▸ actual)).denote (roleSem M 1 fns roles) path env =
      (verifierRound (receive M round.msg path (round.sites 1)) (fun _ => challenge M events path (challengeSite round.sites))
        (.declared .reject ⟨path,round.sites 4⟩) boundary evaluate claim).map (returned M round.residual) := by
  let hidden := nothing M (r := 1) (a := ⟨state,[0]⟩) (by simp)
  let args := HList.cons hidden (.cons (hide M 1 ⟨emptyPoint t,[0,1]⟩ [])
    (.cons (hide M 1 ⟨t,[0,1]⟩ claim) .nil))
  let left := Env.empty.extend (names (state := state) (point := emptyPoint t) (t := t)) args
  have aligned : StraightLine.Agrees [(2,running.name)] left env := by
    intro a b mem ty ha hb
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (List.mem_singleton.mp mem)
    have same := (Option.some.inj (hb.symm.trans running.typed))
    subst ty
    exact atClaim.symm
  exact (round.same _ ⟨M,fns,roles,rfl⟩ _ _ _ aligned).symm.trans
    (verifier round.members events (emptyPoint t) M fns roles boundary evaluate equalLaw ends atPoint
      path hidden [] claim round.sites)

#print axioms Located.process
end Zkc.Formal.Interactive.Sumcheck.ReductionRound
