module

public import Zkc.Core.Facts.Contracts.RoleOperations
public import Zkc.Core.Facts.Contracts.LocalOperationLaws
public import Zkc.Core.Facts.Body.Skeleton
public import Zkc.Core.Facts.LocalLaws

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {hs : Headers V} {r : Role}

/-- Two positions in one list with the same index are one position. -/
private theorem member_index_inj {α : Type} {Γ : List α} {a b : α} (x : Member Γ a) (y : Member Γ b)
    (same : x.index = y.index) : a = b ∧ HEq x y := by
  have hx := Member.atIndex_index x
  rw [same, Member.atIndex_index y] at hx
  have := Option.some.inj hx
  cases this
  exact ⟨rfl, HEq.rfl⟩

/-- **`SkelRules.Lawful`** (proved), among callees with distinct keys: operations of a role with the
same code are the same operation. -/
theorem roleChecks_lawful (distinct : (hs.fns.map (·.key)).Nodup) : (roleChecks (hs := hs) r).Lawful := by
  intro ins res res' o o' same
  simp only [roleChecks, decide_eq_true_eq] at same
  cases o <;> cases o' <;> simp only [roleCode, RoleCode.compute.injEq, RoleCode.absent.injEq,
    RoleCode.give.injEq, RoleCode.get.injEq, RoleCode.keep.injEq, RoleCode.own.injEq,
    RoleCode.hear.injEq, RoleCode.apply.injEq, reduceCtorEq] at same
  case compute.compute =>
    rename_i i1 u1 R1 o1 m1 t1 h1 i2 u2 R2 o2 m2 t2 h2
    obtain ⟨rfl, printed⟩ := same
    subst t1
    subst t2
    obtain ⟨rfl, sameOp⟩ := Sigma.mk.inj (LocalOp.print_injective distinct o1 o2 printed)
    cases eq_of_heq sameOp
    exact ⟨rfl, HEq.rfl⟩
  case absent.absent =>
    subst same
    exact ⟨rfl, HEq.rfl⟩
  case give.give =>
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨rfl, HEq.rfl⟩
  case get.get =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
    exact ⟨rfl, HEq.rfl⟩
  case keep.keep =>
    subst same
    exact ⟨rfl, HEq.rfl⟩
  case own.own =>
    obtain ⟨rfl, rfl, rfl⟩ := same
    exact ⟨rfl, HEq.rfl⟩
  case hear.hear =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := same
    exact ⟨rfl, HEq.rfl⟩
  case apply.apply =>
    rename_i h1 c1 ro1 d1 cv1 f1 h2 c2 ro2 d2 cv2 f2
    obtain ⟨sameIndex, rfl⟩ := same
    obtain ⟨rfl, sameCallee⟩ := member_index_inj c1 c2 sameIndex
    cases eq_of_heq sameCallee
    exact ⟨rfl, HEq.rfl⟩


theorem roleChecks_exact (distinct : (hs.fns.map (·.key)).Nodup) :
    SkelRules.Exact (roleChecks (hs := hs) r) :=
  ⟨roleChecks_lawful distinct, fun _ => by simp [roleChecks]⟩

/-- Every event-free written form determines the full code of any typed operation that printed it. -/
private def valueCode : RoleRaw V → Option (RoleCode V)
  | .compute holders op => some (.compute holders op)
  | .absent types => some (.absent types)
  | .keep holders => some (.keep holders)
  | _ => none

private theorem valueCode_known {ins outs : List (LTy V)} {op : RoleOp V hs r ins outs} {raw : RoleRaw V}
    (printed : roleValueForm op = some raw) : valueCode raw = some (roleCode op) := by
  cases op <;> cases printed <;> rfl

/-- The event-free raw form and the actual input values determine all located result values. -/
theorem roleReturns_functional (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (distinct : (hs.fns.map (·.key)).Nodup) {raw : RoleRaw V} {xs ys zs : List (roleSem M r fns roles).Dyn}
    (left : RoleReturns M r fns roles raw xs ys) (right : RoleReturns M r fns roles raw xs zs) : ys = zs := by
  obtain ⟨_,_,o,as,bs,one,atA,atB,run⟩ := left
  obtain ⟨_,_,o',as',cs,two,atA',atC,run'⟩ := right
  obtain ⟨rfl,sameAs⟩ := (roleSem M r fns roles).dyns_heq as as' (atA.trans atA'.symm)
  cases eq_of_heq sameAs
  have same := Option.some.inj ((valueCode_known one).symm.trans (valueCode_known two))
  obtain ⟨rfl,sameOp⟩ := roleChecks_lawful (r := r) distinct o o' (by simpa [roleChecks] using same)
  cases eq_of_heq sameOp
  have first := run ⟨0⟩ []
  rw [run' ⟨0⟩ []] at first
  cases first
  exact atB.symm.trans atC

theorem roleResultCount_correct {hs : Headers V} {r : Role} (M : Model V)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (distinct : (hs.fns.map (·.key)).Nodup)
    {raw xs ys} (run : RoleReturns M r fns roles raw xs ys) : ys.length = roleResultCount hs raw := by
  obtain ⟨ins,outs,op,args,result,printed,rfl,rfl,_⟩ := run
  rw [Semantics.dyns_length]
  cases op <;> cases printed <;> simp [roleResultCount, localResultCount, resolveLocal_print distinct]

theorem roleValueForm_written {ins outs raw} (o : RoleOp V hs r ins outs)
    (prints : roleValueForm o = some raw) : roleWritten o = raw := by
  cases o <;> cases prints <;> rfl

theorem roleResultCount_written (distinctFns : (hs.fns.map (·.key)).Nodup)
    (distinctRoles : (hs.protocols.map (·.key)).Nodup) {ins outs} (op : RoleOp V hs r ins outs) :
    roleResultCount hs (roleWritten op) = outs.length := by
  cases op <;> simp [roleResultCount, roleWritten, localResultCount, resolveLocal_print distinctFns]
  case apply hdr callee roles distinct covers fits =>
    rw [Member.withKey_key (·.key) callee distinctRoles]

-- The final holder list agrees, but the new recipients and previous holders differ.
private def getSplit : RoleOp V hs 0 [] [⟨.nat, Holders.ofList ([0] ++ [1])⟩] :=
  .get .nat [1] .message 2 [0] (by simp)
private def getTogether : RoleOp V hs 0 [] [⟨.nat, Holders.ofList ([0,1] ++ [])⟩] :=
  .get .nat [] .message 2 [0,1] (by simp)
example : (roleChecks (V := V) (hs := hs) 0).sameOp getSplit getTogether = false := by rfl'

#print axioms roleResultCount_written
#print axioms roleResultCount_correct
#print axioms roleChecks_exact
#print axioms roleReturns_functional
end Zkc.Core.BodyAnalysis
