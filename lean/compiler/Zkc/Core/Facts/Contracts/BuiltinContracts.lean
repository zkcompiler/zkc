module

public import Zkc.Core.Facts.Contracts.Functions
public import Zkc.Core.Facts.Contracts.HeaderPredicates

@[expose] public section

namespace Zkc.Core.BodyAnalysis
open HeaderContracts
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)
variable {args : List (localSem M fns table).Dyn}

private theorem arguments_read : ∀ {ps vs}, (argumentExpressions ps).Denote (Runs M table) args vs →
    atPositions args ps = some vs
  | [], _, .nil => rfl
  | _ :: _, _, .cons (.arg at_) more => by simp [atPositions, at_, arguments_read more]

private theorem operand_read {o : Operand (LocalRaw V)} {v} (h : (builtinOperand o).Denotes (Runs M table) args v) :
    o.Denotes (Runs M table) args v := by
  cases o with
  | arg => cases h with | arg found => exact found
  | apply op ps =>
    cases h with
    | apply named ran result =>
      exact ⟨_,_,arguments_read M table named,ran,by simpa [List.head?_eq_getElem?] using result⟩

private theorem form_read {op : LocalRaw V} {f : ResultForm} {es v}
    (decl : (localOpFacts fns).form op = some f)
    (h : (Expr.apply op es 0).Denotes (Runs M table) args v) :
    ∃ vs, es.Denote (Runs M table) args vs ∧ FactCheck.FormHolds (localReading M) f vs v := by
  cases h with
  | apply named ran result =>
    obtain ⟨w, head, form⟩ := FactCheck.localReturns_form decl ran.1
    rw [List.head?_eq_getElem?] at head
    obtain rfl := Option.some.inj (head.symm.trans result)
    exact ⟨_,named,form⟩

private theorem not_read {e v b} (h : (negate e).Denotes (Runs M table) args v)
    (reads : (localReading M).bool v = some b) :
    ∃ w, e.Denotes (Runs M table) args w ∧ (localReading M).bool w = some (!b) := by
  obtain ⟨_, named, w, y, rfl, val, out⟩ := form_read M table (f := .negation) rfl h
  cases named with | cons den more =>
    rw [out] at reads
    cases reads
    exact ⟨w,den,by simpa using val⟩

private theorem comparison_read {a b v truth} (eq : Bool)
    (h : (if eq then equal a b else less a b).Denotes (Runs M table) args v)
    (reads : (localReading M).bool v = some truth) :
    ∃ u w x y, a.Denotes (Runs M table) args u ∧ b.Denotes (Runs M table) args w ∧
      (localReading M).nat u = some x ∧ (localReading M).nat w = some y ∧
      (if eq then decide (x = y) else decide (x < y)) = truth := by
  cases eq
  all_goals
    first
    | obtain ⟨_, named, u, w, x, y, rfl, left, right, out⟩ := form_read M table (f := .less) rfl h
    | obtain ⟨_, named, u, w, x, y, rfl, left, right, out⟩ := form_read M table (f := .equal) rfl h
    cases named with | cons first more =>
      cases more with | cons second _ =>
        exact ⟨u,w,x,y,first,second,left,right,Option.some.inj (out.symm.trans reads)⟩

private theorem sum_read {a b v z} (h : (add a b).Denotes (Runs M table) args v)
    (reads : (localReading M).nat v = some z) :
    ∃ u w x y, a.Denotes (Runs M table) args u ∧ b.Denotes (Runs M table) args w ∧
      (localReading M).nat u = some x ∧ (localReading M).nat w = some y ∧ x+y=z := by
  obtain ⟨_, named, u, w, x, y, rfl, left, right, out⟩ := form_read M table (f := .sum) rfl h
  cases named with | cons first more =>
    cases more with | cons second _ =>
      exact ⟨u,w,x,y,first,second,left,right,Option.some.inj (out.symm.trans reads)⟩

private theorem number_read (distinct : (fns.map (·.key)).Nodup) {v n k}
    (h : (number n).Denotes (Runs M table) args v) (read : (localReading M).nat v = some k) : n=k := by
  obtain rfl := h.unique (fun _ _ _ _ a b => FactCheck.localReturns_functional distinct a.1 b.1) (number_denotes M table n)
  exact Option.some.inj read

/-- Every true builtin precondition implies the catalog obligation of the actual instruction.
Nested applications retain their operands in order and read their first result port. -/
theorem builtinClause_implies (distinct : (fns.map (·.key)).Nodup) (q : Requirement (LocalRaw V))
    (held : (builtinClause q).assertion.Holds (Runs M table) (localReading M) args) :
    q.Holds (Runs M table) (localReading M) args := by
  obtain ⟨v, den, yes⟩ := held
  cases q with
  | holds a => exact ⟨[_],⟨operand_read M table den,trivial⟩,yes⟩
  | le a b =>
    obtain ⟨_, positive, neg⟩ := not_read M table den yes
    obtain ⟨u,w,x,y,du,dw,ru,rw,rel⟩ := comparison_read M table false positive neg
    exact ⟨[w,u],⟨operand_read M table dw,operand_read M table du,trivial⟩,y,x,rw,ru,by simpa using rel⟩
  | lt a b =>
    obtain ⟨u,w,x,y,du,dw,ru,rw,rel⟩ := comparison_read M table false den yes
    exact ⟨[u,w],⟨operand_read M table du,operand_read M table dw,trivial⟩,x,y,ru,rw,by simpa using rel⟩
  | below a n =>
    obtain ⟨u,_,x,_,du,dw,ru,rw,rel⟩ := comparison_read M table false den yes
    obtain rfl := number_read M table distinct dw rw
    exact ⟨[u],⟨operand_read M table du,trivial⟩,x,ru,by simpa using rel⟩
  | exactly a n =>
    obtain ⟨u,_,x,_,du,dw,ru,rw,rel⟩ := comparison_read M table true den yes
    obtain rfl := number_read M table distinct dw rw
    exact ⟨[u],⟨operand_read M table du,trivial⟩,x,ru,by simpa using rel⟩
  | atLeast a n =>
    cases n with
    | zero =>
      obtain ⟨u,_,x,_,du,_,ru,_,_⟩ := comparison_read M table true den yes
      exact ⟨[u],⟨operand_read M table du,trivial⟩,x,ru,Nat.zero_le x⟩
    | succ n =>
      obtain ⟨_,u,_,x,dw,du,rw,ru,rel⟩ := comparison_read M table false den yes
      obtain rfl := number_read M table distinct dw rw
      exact ⟨[u],⟨operand_read M table du,trivial⟩,x,ru,by simpa [Nat.succ_le_iff] using rel⟩
  | bounded a =>
    obtain ⟨u,_,x,_,du,_,ru,_,_⟩ := comparison_read M table true den yes
    exact ⟨[u],⟨operand_read M table du,trivial⟩,x,ru⟩
  | difference b a n =>
    cases n with
    | zero =>
      obtain ⟨_,positive,neg⟩ := not_read M table den yes
      obtain ⟨u,w,x,y,du,dw,ru,rw,rel⟩ := comparison_read M table false positive neg
      exact ⟨[w,u],⟨operand_read M table dw,operand_read M table du,trivial⟩,y,x,rw,ru,
        Nat.sub_eq_zero_of_le (by simpa using rel)⟩
    | succ n =>
      obtain ⟨u,w,x,y,du,dw,_,rw,rel⟩ := comparison_read M table true den yes
      have eq : x=y := by simpa using rel
      obtain ⟨first,_,z,k,df,dl,rf,rl,sum⟩ := sum_read M table du (by assumption)
      have size := number_read M table distinct dl rl
      exact ⟨[w,first],⟨operand_read M table dw,operand_read M table df,trivial⟩,y,z,rw,rf,by omega⟩

end Zkc.Core.BodyAnalysis
