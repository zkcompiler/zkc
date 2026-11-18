module

public import Zkc.Core.Facts.Contracts.Functions
public import Zkc.Core.Facts.Body.InvariantsSound
public import Zkc.Core.Meaning.Validity

@[expose] public section

namespace Zkc.Core.BodyAnalysis

variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)
    (rules : σ.cfg.rules.Lawful σ.sem σ.permitted σ.R σ.Run σ.Valid σ.undefined)

private theorem Config.apply_length (cfg : Config D Raw) (op : Raw) (args : List Ident)
    (n : Nat) (v : Values Raw) (k : cfg.domain.State) : (cfg.apply op args n v k).1.length = n :=
  (Ident.vals_length _ _).trans (Values.share_entry (.app op (placed (cfg.rules.commutes op) args))
    n v).2.1

set_option linter.unusedSectionVars false in
include rules in
mutual
  /-- Every available admissible expression whose arguments have identifiers can be entered.
  This also proves availability for index expressions assembled out of ordinary operations. -/
  theorem Expr.Denotes.enter {xs : List σ.sem.Dyn} {ids : List Ident} (length : ids.length = xs.length)
      {expr : Expr Raw} {x : σ.sem.Dyn} (den : expr.Denotes σ.Runs xs x)
      (allowed : expr.UsesOnly σ.cfg.rules.assertable = true) (v : Values Raw) (k : σ.cfg.domain.State) :
      ∃ result, enterExpr σ.cfg (ids.map some) expr v k = some result :=
    match den with
    | .arg (position := i) at_ => by
      have lt : i < ids.length := length ▸ (List.getElem?_eq_some_iff.mp at_).1
      exact ⟨(ids[i], v, k), by simp [enterExpr, List.getElem?_eq_getElem lt]⟩
    | .apply (written := op) (result := j) named ran picked => by
      obtain ⟨allowedOp, allowedArgs⟩ := Bool.and_eq_true_iff.mp allowed
      obtain ⟨⟨operands, v', k'⟩, entered⟩ := Exprs.Denote.enter length named allowedArgs v k
      let made := σ.cfg.apply op operands (σ.cfg.rules.results op) v' k'
      have lt : j < made.1.length := by
        rw [Config.apply_length, ← (rules.keeps _ _ _ ran.1 ran.2.1).2]
        exact (List.getElem?_eq_some_iff.mp picked).1
      refine ⟨(made.1[j], made.2.1, made.2.2), ?_⟩
      simp only [enterExpr_apply_eq, allowedOp, ↓reduceIte, entered]
      change (made.1[j]?.map _) = _
      rw [List.getElem?_eq_getElem lt]
      rfl
  theorem Exprs.Denote.enter {xs : List σ.sem.Dyn} {ids : List Ident} (length : ids.length = xs.length)
      {exprs : Exprs Raw} {ys : List σ.sem.Dyn} (den : exprs.Denote σ.Runs xs ys)
      (allowed : exprs.UsesOnly σ.cfg.rules.assertable = true) (v : Values Raw) (k : σ.cfg.domain.State) :
      ∃ result, enterExprs σ.cfg (ids.map some) exprs v k = some result :=
    match den with
    | .nil => ⟨_, rfl⟩
    | .cons first rest => by
      obtain ⟨ok, oks⟩ := Bool.and_eq_true_iff.mp allowed
      obtain ⟨⟨id, v', k'⟩, one⟩ := Expr.Denotes.enter length first ok v k
      obtain ⟨⟨others, v'', k''⟩, more⟩ := Exprs.Denote.enter length rest oks v' k'
      exact ⟨(id :: others, v'', k''), by simp [enterExprs, one, more]⟩
end

include rules in
theorem indexValue_available {expr : Expr Raw} {args : List Ident} {inputs : List σ.sem.Dyn}
    {result : σ.sem.Dyn} (arity : args.length = inputs.length) (den : expr.Denotes σ.Runs inputs result)
    (allowed : expr.UsesOnly σ.cfg.rules.assertable = true) (s : State Raw) (k : σ.cfg.domain.State) :
    ∃ id, (indexValue σ.cfg (some expr) args s k).1 = some id := by
  obtain ⟨⟨id, vs, k'⟩, found⟩ := den.enter σ rules arity allowed s.values k
  exact ⟨id, by simp [indexValue, found]⟩

namespace LocalIndex
variable {V : Vocabulary}
variable (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)
local notation "localRuns" => ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M)

theorem atIteration_denotes (inputs : List (localSem M fns table).Dyn) (n : Nat) :
    (atIteration n).Denotes localRuns inputs ⟨.nat, n⟩ := by
  apply Expr.Denotes.apply (results := [⟨.nat, n⟩]) .nil _ rfl
  refine ⟨⟨_, _, .literal .nat [n] rfl, .nil, .cons n .nil, rfl, rfl, rfl, rfl⟩,
    (fun _ m => nomatch m), ?_⟩
  intro v m
  obtain rfl := List.mem_singleton.mp m
  trivial

theorem fromCount_denotes (n : Nat) :
    fromCount.Denotes localRuns [⟨.nat, n⟩] ⟨.nat, n⟩ := .arg rfl

theorem next_denotes (n : Nat) : next.Denotes localRuns [⟨.nat, n⟩] ⟨.nat, n+1⟩ := by
  apply Expr.Denotes.apply (results := [⟨.nat, n+1⟩])
    (.cons (.arg rfl) (.cons (atIteration_denotes M table _ 1) .nil)) _ rfl
  refine ⟨⟨_, _, .owned .natAdd, .cons n (.cons 1 .nil), .cons (n+1) .nil, rfl, rfl, rfl, rfl⟩,
    ?_, ?_⟩
  · intro v m
    rcases List.mem_cons.mp m with rfl | m
    · trivial
    · obtain rfl := List.mem_singleton.mp m
      trivial
  · intro v m
    obtain rfl := List.mem_singleton.mp m
    trivial

#print axioms next_denotes
end LocalIndex
#print axioms indexValue_available
end Zkc.Core.BodyAnalysis
