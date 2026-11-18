module

public import Zkc.Core.Meaning.Role
public import Zkc.Core.Facts.Contracts.Expressions
public import Zkc.Core.Program.NamedProgram

@[expose] public section

namespace Zkc.Core.BodyAnalysis

variable {V : Vocabulary} {hs : Headers V} {r : Role}

/-- The role keeps its natural count at the holders of this loop's index. -/
def roleIndexFromCount {who : Holders} {t : LTy V} (ok : (roleDialect V hs r).Count who t) :
    RoleOp V hs r [t] [LTy.index who] := by
  obtain ⟨ty, holders⟩ := t
  obtain ⟨type, held, participating⟩ := ok
  cases type
  exact .keep who ⟨fun _ => participating, fun _ => held⟩

/-- The operation returns the final index in the actual role semantics, for any legal count. -/
theorem roleIndexFromCount_denote (M : Model V) (fns : FnTable M hs.fns)
    (roles : RTable M hs.protocols) {who : Holders} {t : LTy V}
    (ok : (roleDialect V hs r).Count who t) (value : RV M r t) (key : Key) (path : List Frame) :
    let sem := roleSem M r fns roles
    sem.op key (roleIndexFromCount ok) path (.cons value .nil) =
      .done (.cons (sem.index who (sem.count ok value)) .nil) := by
  obtain ⟨ty, holders⟩ := t
  obtain ⟨type, held, participating⟩ := ok
  cases type
  apply congrArg (fun v : RV M r (LTy.index who) =>
      (Process.done (.cons v .nil) : Program M (HList (RV M r) [LTy.index who])))
  simp [carry, hide, reveal, asNat, participating, LTy.index]

/-- Construct a fixed index through computation at a participating role and through the ordinary
absent-value operation at every other role. -/
def roleIndexAt (who : Holders) (n : Nat) : RoleOp V hs r [] [LTy.index who] :=
  if here : r ∈ who then
    .compute who (.literal .nat [n] rfl) [] rfl here (fun _ h => nomatch h)
  else
    .absent [LTy.index who] (fun a member => by
      obtain rfl := List.mem_singleton.mp member
      exact here)

/-- The same construction handles zero, positive counts and an absent role. -/
theorem roleIndexAt_denote (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (who : Holders) (n : Nat) (key : Key) (path : List Frame) :
    let sem := roleSem M r fns roles
    sem.op key (roleIndexAt who n) path .nil = .done (.cons (sem.index who n) .nil) := by
  by_cases here : r ∈ who
  · simp only [roleIndexAt, dite_eq_left here]
    rfl
  · simp only [roleIndexAt, dite_eq_right here]
    apply congrArg (fun v : RV M r (LTy.index who) =>
      (Process.done (.cons v .nil) : Program M (HList (RV M r) [LTy.index who])))
    rw [hide_out M here]

namespace RoleIndex

def atIteration (r : Role) (who : Holders) (n : Nat) : Expr (RoleRaw V) :=
  let raw := if r ∈ who then RoleRaw.compute who (.literal .nat [n]) else .absent [LTy.index who]
  .apply raw .nil 0

def fromCount (who : Holders) : Expr (RoleRaw V) := .apply (.keep who) (.cons (.arg 0) .nil) 0

def next (r : Role) (who : Holders) : Expr (RoleRaw V) :=
  if r ∈ who then .apply (.compute who (.owned .natAdd [] []))
      (.cons (.arg 0) (.cons (atIteration r who 1) .nil)) 0
  else .arg 0

end RoleIndex

end Zkc.Core.BodyAnalysis
