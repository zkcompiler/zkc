module

public import Zkc.Core.Facts.Knowledge.DialectReadings
public import Zkc.Core.Facts.Contracts.IndexExpressions
public import Zkc.Core.Facts.Contracts.RoleOperations
public import Zkc.Core.Facts.Contracts.RoleIndex

@[expose] public section

namespace Zkc.Core.BodyAnalysis

variable {V : Vocabulary} {hs : Headers V} {r : Role}

namespace RoleIndex
variable (M : Model V) (r : Role) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)

local notation "indexRuns" => ValidRun (roleSem M r fns roles) (RoleReturns M r fns roles) (RoleValueValid M r)
abbrev valueAt (who : Holders) (i : Nat) : (roleSem M r fns roles).Dyn :=
  ⟨LTy.index who, (roleSem M r fns roles).index who i⟩

private theorem idx_valid (who : Holders) (i : Nat) :
    RoleValueValid M r (valueAt M r fns roles who i) := by
  intro held
  trivial

theorem atIteration_denotes (inputs : List (roleSem M r fns roles).Dyn) (who : Holders) (i : Nat) :
    (atIteration r who i).Denotes indexRuns inputs (valueAt M r fns roles who i) := by
  apply Expr.Denotes.apply (results := [valueAt M r fns roles who i]) .nil _ rfl
  refine ⟨⟨_, _, roleIndexAt who i, .nil, .cons ((roleSem M r fns roles).index who i) .nil,
    ?_, rfl, rfl, roleIndexAt_denote M fns roles who i⟩, (fun _ m => nomatch m),
    fun _ m => List.mem_singleton.mp m ▸ idx_valid M r fns roles who i⟩
  by_cases held : r ∈ who <;> simp [roleIndexAt, held, roleValueForm, LocalOp.print]

theorem fromCount_denotes {who : Holders} {t : LTy V} (ok : (roleDialect V hs r).Count who t)
    (x : RV M r t) (valid : RV.Valid M r t x) :
    (fromCount who).Denotes indexRuns [⟨t, x⟩]
      (valueAt M r fns roles who ((roleSem M r fns roles).count ok x)) := by
  apply Expr.Denotes.apply (results := [valueAt M r fns roles who ((roleSem M r fns roles).count ok x)])
    (.cons (.arg rfl) .nil) _ rfl
  refine ⟨⟨_, _, roleIndexFromCount ok, .cons x .nil, .cons _ .nil, ?_, rfl, rfl,
    roleIndexFromCount_denote M fns roles ok x⟩,
    (fun _ m => List.mem_singleton.mp m ▸ valid), fun _ m => List.mem_singleton.mp m ▸
      idx_valid M r fns roles who _⟩
  obtain ⟨ty, holders⟩ := t
  obtain ⟨eq, held, mine⟩ := ok
  cases eq
  rfl

private def add (who : Holders) (held : r ∈ who) :
    RoleOp V hs r [LTy.index who, LTy.index who] [LTy.index who] :=
  .compute who (.owned .natAdd) _ rfl held (by simp [LTy.index, held])

private theorem add_denote (who : Holders) (held : r ∈ who) (i : Nat) (key : Key) (path : List Frame) :
    let s := roleSem M r fns roles
    s.op key (add r who held) path (.cons (s.index who i) (.cons (s.index who 1) .nil)) =
      .done (.cons (s.index who (i+1)) .nil) := by
  simp only [roleSem, add, roleOp, revealAll, reveal_hide]
  rfl

theorem next_denotes (who : Holders) (i : Nat) :
    (next r who).Denotes indexRuns [valueAt M r fns roles who i] (valueAt M r fns roles who (i+1)) := by
  by_cases held : r ∈ who
  · simp only [next, ite_eq_left held]
    apply Expr.Denotes.apply (results := [valueAt M r fns roles who (i+1)])
      (.cons (.arg rfl) (.cons (atIteration_denotes M r fns roles _ who 1) .nil)) _ rfl
    refine ⟨⟨_, _, add r who held, .cons _ (.cons _ .nil), .cons _ .nil, rfl, rfl, rfl,
      add_denote M r fns roles who held i⟩, ?_, (fun _ m => List.mem_singleton.mp m ▸
        idx_valid M r fns roles who _)⟩
    intro value member
    rcases List.mem_cons.mp member with rfl | h
    · exact idx_valid M r fns roles who _
    · exact List.mem_singleton.mp h ▸ idx_valid M r fns roles who _
  · simp only [next, ite_eq_right held]
    apply Expr.Denotes.arg
    simp [valueAt, roleSem, hide_out M (a := LTy.index who) held]

#print axioms atIteration_denotes
#print axioms fromCount_denotes
#print axioms next_denotes
end RoleIndex
end Zkc.Core.BodyAnalysis
