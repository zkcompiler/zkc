module

public import Zkc.Core.Facts.Contracts.ProjectedEffect
public import Zkc.Core.Facts.Contracts.RoleIndexExpressions

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts

variable {V : Vocabulary} {hs : Headers V} (catalog : FunctionContracts hs.fns) (r : Role)

private theorem localAllowed {ins outs} (op : LocalOp V hs.fns ins outs) :
    catalog.assertable op.print = true ↔ op.canStop = false ∧ (catalog.contract op.print).preconditions = [] := by
  simp [FunctionContracts.assertable, resolveLocal_print catalog.distinct, catalog.eligible_print]

private theorem literalAllowed (i : Nat) : catalog.assertable (.literal .nat [i]) = true :=
  (localAllowed catalog (.literal .nat [i] rfl)).mpr ⟨rfl, rfl⟩

private theorem addAllowed : catalog.assertable (.owned .natAdd [] []) = true :=
  (localAllowed catalog (.owned .natAdd)).mpr ⟨rfl, rfl⟩

private theorem assertable_shared {ins outs} (op : RoleOp V hs r ins outs)
    (ok : assertable catalog r (roleWritten op) = true) :
    roleShared op = true ∧ (contract catalog (roleWritten op)).requires = [] := by
  cases op with
  | compute R op ins types mine here =>
    have allowed : catalog.assertable op.print = true := by simpa [assertable, roleWritten, mine] using ok
    obtain ⟨quiet, empty⟩ := (localAllowed catalog op).mp allowed
    simp [roleShared, roleWritten, contract, quiet, Contract.requires, empty]
  | keep | absent => exact ⟨rfl,rfl⟩
  | give | get | own | hear | apply => cases ok

private theorem atIteration_allowed (w : Holders) (i : Nat) :
    (RoleIndex.atIteration r w i : Expr (RoleRaw V)).UsesOnly (assertable catalog r) = true := by
  by_cases here : r ∈ w <;>
    simp [RoleIndex.atIteration, Expr.UsesOnly, Exprs.UsesOnly, assertable, here, literalAllowed, LTy.index]

/-- A keep at a retained holder and a give at the sender preserve the entire local payload.
For a give, every allowed acknowledgment returns that payload. -/
private theorem observedOperand (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    {ins res} (op : RoleOp V hs r ins res) {i} (observed : (rules catalog r).observedOperand op = some i)
    {key path} {args : HList (RV M r) ins} {ys : HList (RV M r) res}
    (ran : (roleOp M r fns roles key op path args).CanReturn (Permitted M) ys)
    {x y} (src : ((roleSem M r fns roles).dyns args)[i]? = some x)
    (dst : ((roleSem M r fns roles).dyns ys)[0]? = some y) :
    (roleReading M r).Agrees x y := by
  suffices eq : heldValue M r x = heldValue M r y by
    exact ⟨by simp [roleReading, eq], by simp [roleReading, eq], eq⟩
  cases op with
  | keep holders same =>
    by_cases here : r ∈ holders
    · have atZero : 0 = i := Option.some.inj (by simpa only [rules, here, ↓reduceIte] using observed)
      subst i
      obtain ⟨v, rfl⟩ := HList.one args
      cases ran
      cases src
      cases dst
      simp [heldValue, here, same.mpr here, reveal_carry]
    · simp [rules, here] at observed
  | give kind getters here =>
    cases observed
    obtain ⟨v, rfl⟩ := HList.one args
    cases ran with
    | call _ _ _ next =>
      cases next
      cases src
      cases dst
      have resultHere := Holders.mem_ofList.mpr (List.mem_append_right getters here)
      simp [heldValue, here, resultHere, reveal_hide]
  | _ => cases observed

/-- Assertion evaluation depends only on the local function table. A role expression performs
no protocol call and asks for no external reply. -/
theorem assertionLaws (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (callees : Callees M fns) :
    (rules catalog r).AssertionLaws (roleSem M r fns roles) (roleReading M r)
      (RoleReturns M r fns roles) (RoleValueValid M r) where
  keeps := keeps M r fns roles catalog callees
  defined := defined M r fns roles catalog callees
  assertable := assertable_shared catalog r

/-- Lawfulness at the projected role, for the model's permitted replies and the actual tables. -/
theorem lawful (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (callees : Callees M fns) (rcallees : RCallees M roles) :
    (rules catalog r).Lawful (roleSem M r fns roles) (Permitted M) (roleReading M r)
      (RoleReturns M r fns roles) (RoleValueValid M r) (· = .undefined) where
  observedOperand := @observedOperand V hs catalog r M fns roles
  computes := computes M r fns roles callees
  functional := fun _ _ _ _ a b => roleReturns_functional M fns roles catalog.distinct a b
  commutative := commutative M r fns roles catalog callees
  toAssertionLaws := assertionLaws catalog r M fns roles callees
  effect := effect M r fns roles catalog callees rcallees
  condition := fun ok v _ => roleConditionsRead M r fns roles ok v
  count := by
    rintro w ⟨ty, holders⟩ ⟨eq, held, _⟩ x _
    cases eq
    simp [roleReading, heldValue, held, localReading, asNat, roleSem]
  pick := role_pick M r fns roles
  index := by
    intro w i
    refine ⟨fun _ => trivial, fun numbered => ?_⟩
    have mine : r ∈ w := of_decide_eq_true numbered
    simp [roleReading, heldValue, roleSem, LTy.index, mine, reveal_hide, localReading]
  indexAt := by
    intro w i e found
    cases found
    exact ⟨atIteration_allowed catalog r w i, RoleIndex.atIteration_denotes M r fns roles [] w i⟩
  indexFromCount := by
    intro w t ok e found
    cases found
    exact ⟨rfl, RoleIndex.fromCount_denotes M r fns roles ok⟩
  indexNext := by
    intro w e found
    cases found
    refine ⟨?_, RoleIndex.next_denotes M r fns roles w⟩
    by_cases mine : r ∈ w <;>
      simp [RoleIndex.next, mine, Expr.UsesOnly, Exprs.UsesOnly, rules, atIteration_allowed,
        assertable, addAllowed]
  collect := role_collect M r fns roles
  begin := role_begin M r fns roles
  settle := role_settle M r fns roles
  stop := fun _ _ _ h => nomatch h

#print axioms lawful

end Zkc.Core.BodyAnalysis.RoleContracts
