module

public import Zkc.Core.Facts.Contracts.Stored
public import Zkc.Core.Facts.Contracts.IndexExpressions
public import Zkc.Core.Facts.LocalLaws

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop}
    (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs)

set_option linter.unusedSectionVars false in
include functional in
mutual
  theorem Expr.Denotes.unique {args : List Val} {e : Expr Raw} {v : Val} (den : e.Denotes Run args v) :
      ∀ {w}, e.Denotes Run args w → v = w :=
    match den with
    | .arg at_ => by
      intro other
      cases other with | arg same => exact Option.some.inj (at_.symm.trans same)
    | .apply named ran picked => by
      intro other
      cases other with | apply named' ran' picked' =>
        obtain rfl := Exprs.Denote.unique named named'
        obtain rfl := functional _ _ _ _ ran ran'
        exact Option.some.inj (picked.symm.trans picked')
  theorem Exprs.Denote.unique {args : List Val} {es : Exprs Raw} {vs : List Val} (den : es.Denote Run args vs) :
      ∀ {ws}, es.Denote Run args ws → vs = ws :=
    match den with
    | .nil => by intro other; cases other; rfl
    | .cons one more => by
      intro other
      cases other with | cons first rest =>
        rw [Expr.Denotes.unique one first, Exprs.Denote.unique more rest]
end

namespace HeaderContracts
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)
abbrev Runs := ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M)
variable {args : List (localSem M fns table).Dyn}

/-- Build a result-port witness from the typed operation that actually computes it. -/
private theorem port {ins : List V.Ty} {out : V.Ty} (op : LocalOp V fns ins [out])
    {es : Exprs (LocalRaw V)} (xs : HList M.Val ins) (y : M.Val out)
    (inputs : es.Denote (Runs M table) args ((localSem M fns table).dyns xs))
    (valid : ∀ d ∈ (localSem M fns table).dyns xs, ValidDyn M d)
    (result : M.Valid out y) (ran : localOp M table op xs = .done (.cons y .nil)) :
    (Expr.apply op.print es 0).Denotes (Runs M table) args ⟨out,y⟩ := by
  apply Expr.Denotes.apply (results := [⟨out,y⟩]) inputs _ rfl
  exact ⟨⟨_, _, op, xs, .cons y .nil, rfl, rfl, rfl, ran⟩, valid,
    fun _ mem => List.mem_singleton.mp mem ▸ result⟩

theorem number_denotes (n : Nat) : (number n).Denotes (Runs M table) args ⟨.nat,n⟩ :=
  LocalIndex.atIteration_denotes M table args n

theorem less_denotes {a b : Assertion V} {x y : Nat} (hx : a.Denotes (Runs M table) args ⟨.nat,x⟩)
    (hy : b.Denotes (Runs M table) args ⟨.nat,y⟩) :
    (less a b).Denotes (Runs M table) args ⟨.bool,decide (x < y)⟩ := by
  refine port M table (.owned .natLess) (.cons x (.cons y .nil)) _ (.cons hx (.cons hy .nil)) ?_ trivial ?_
  · intro d m
    rcases List.mem_cons.mp m with rfl | tail
    · trivial
    · obtain rfl := List.mem_singleton.mp tail
      trivial
  · simp [localOp, ownedOp, FactCheck.blt_decide]

theorem equal_denotes {a b : Assertion V} {x y : Nat} (hx : a.Denotes (Runs M table) args ⟨.nat,x⟩)
    (hy : b.Denotes (Runs M table) args ⟨.nat,y⟩) :
    (equal a b).Denotes (Runs M table) args ⟨.bool,decide (x = y)⟩ := by
  refine port M table (.owned .natEqual) (.cons x (.cons y .nil)) _ (.cons hx (.cons hy .nil)) ?_ trivial ?_
  · intro d m
    rcases List.mem_cons.mp m with rfl | tail
    · trivial
    · obtain rfl := List.mem_singleton.mp tail
      trivial
  · simp [localOp, ownedOp, FactCheck.beq_decide]

theorem add_denotes {a b : Assertion V} {x y : Nat} (hx : a.Denotes (Runs M table) args ⟨.nat,x⟩)
    (hy : b.Denotes (Runs M table) args ⟨.nat,y⟩) : (add a b).Denotes (Runs M table) args ⟨.nat,x+y⟩ := by
  refine port M table (.owned .natAdd) (.cons x (.cons y .nil)) _ (.cons hx (.cons hy .nil)) ?_ trivial rfl
  intro d m
  rcases List.mem_cons.mp m with rfl | tail
  · trivial
  · obtain rfl := List.mem_singleton.mp tail
    trivial

theorem negate_denotes {a : Assertion V} {b : Bool} (hx : a.Denotes (Runs M table) args ⟨.bool,b⟩) :
    (negate a).Denotes (Runs M table) args ⟨.bool,!b⟩ := by
  refine port M table (.owned .boolNot) (.cons b .nil) _ (.cons hx .nil) ?_ trivial rfl
  exact fun _ m => List.mem_singleton.mp m ▸ trivial

theorem fin_denotes {a : Assertion V} {n x : Nat} (hx : a.Denotes (Runs M table) args ⟨.fin n,x⟩)
    (valid : M.Valid (.fin n) x) :
    (unary (.owned .finToNat [.fin n] []) a).Denotes (Runs M table) args ⟨.nat,x⟩ := by
  refine port M table (.owned (.finToNat n)) (.cons x .nil) _ (.cons hx .nil) ?_ trivial rfl
  exact fun _ m => List.mem_singleton.mp m ▸ valid

theorem holds_iff {e : Assertion V} {b : Bool} (distinct : (fns.map (·.key)).Nodup)
    (den : e.Denotes (Runs M table) args ⟨.bool,b⟩) :
    e.Holds (Runs M table) (localReading M) args ↔ b = true := by
  constructor
  · rintro ⟨v, other, val⟩
    obtain rfl := den.unique (fun _ _ _ _ h h' => FactCheck.localReturns_functional distinct h.1 h'.1) other
    exact Option.some.inj val
  · rintro rfl
    exact ⟨_,den,rfl⟩

end HeaderContracts
end Zkc.Core.BodyAnalysis
