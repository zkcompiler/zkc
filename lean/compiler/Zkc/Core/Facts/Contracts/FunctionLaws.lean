module

public import Zkc.Core.Facts.Contracts.StoredLaws
public import Zkc.Core.Facts.Contracts.BuiltinContracts
public import Zkc.Core.Facts.Contracts.LocalOperationLaws
public import Zkc.Core.Facts.Contracts.IndexExpressions

@[expose] public section

namespace Zkc.Core.BodyAnalysis
open HeaderContracts
variable {V : Vocabulary} {hs : List (FnHeader V)}

theorem FunctionContracts.call_member (contracts : FunctionContracts hs) {h : FnHeader V} (m : Member hs h) :
    contracts.contract (.call h.key) = (contracts.entry m).val := by
  simp [FunctionContracts.contract, FunctionContracts.call?, Member.withKey_key (·.key) m contracts.distinct]

private theorem FunctionContracts.noncall (contracts : FunctionContracts hs) {raw : LocalRaw V}
    (other : ∀ k, raw ≠ .call k) :
    contracts.contract raw = ⟨((localOpFacts hs).requires raw).map builtinClause,
      ((localOpFacts hs).ensures raw).map builtinClause⟩ := by
  cases raw <;> first | rfl | exact False.elim (other _ rfl)

variable (M : Model V) (fnTable : FnTable M hs) (contracts : FunctionContracts hs)

theorem FunctionContracts.headerParts {h : FnHeader V} (m : Member hs h) :
    h.summary.requires.mapM (checkClause h.ins) = some (contracts.entry m).val.preconditions ∧
    h.summary.ensures.mapM (checkClause (h.ins ++ h.outs)) = some (contracts.entry m).val.postconditions := by
  have found := (contracts.entry m).property
  simp only [translate, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at found
  obtain ⟨_,pre,_,post,same⟩ := found
  rw [←Option.some.inj same]
  exact ⟨pre,post⟩

private theorem builtinRequired {raw : LocalRaw V} (other : ∀ k, raw ≠ .call k)
    {args : List (localSem M hs fnTable).Dyn}
    (held : ∀ e ∈ (contracts.contract raw).requires, e.Holds (Runs M fnTable) (localReading M) args) :
    ∀ q ∈ (localOpFacts hs).requires raw, q.Holds (Runs M fnTable) (localReading M) args := by
  rw [contracts.noncall other] at held
  intro q mem
  exact builtinClause_implies M fnTable contracts.distinct q (held _ (List.mem_map_of_mem (List.mem_map_of_mem mem)))

private theorem localRequired {ins outs} (op : LocalOp V hs ins outs) (as : HList M.Val ins)
    (ok : ∀ v ∈ (localSem M hs fnTable).dyns as, ValidDyn M v)
    (new : contracts.rules.Required (localSem M hs fnTable) (localReading M) (LocalReturns M fnTable) (ValidDyn M) op as) :
    FactCheck.LocalRequired (table := fnTable) op as := by
  cases op with
  | call member =>
    rename_i h
    change ∀ e ∈ (contracts.contract (.call h.key)).requires, _ at new
    rw [contracts.call_member member] at new
    exact (clauses_exact M fnTable (ArgumentsMatch.ofValues (sem := localSem M hs fnTable) as ok)
      contracts.distinct (contracts.headerParts member).1).mp new
  | row k signature arity => exact builtinRequired M fnTable contracts (raw := .row k) (by intro _ h; cases h) new
  | owned o => exact builtinRequired M fnTable contracts (raw := .owned o.name.1 o.name.2.1 o.name.2.2) (by intro _ h; cases h) new
  | literal t data reads => exact builtinRequired M fnTable contracts (raw := .literal t data) (by intro _ h; cases h) new

private theorem localEnsured {ins outs} (op : LocalOp V hs ins outs) (as : HList M.Val ins) (ys : HList M.Val outs)
    (valid : ∀ v ∈ (localSem M hs fnTable).dyns as, ValidDyn M v)
    (returned : ∀ v ∈ (localSem M hs fnTable).dyns ys, ValidDyn M v)
    (old : match op with
      | .call (hdr := h) _ => ∀ q ∈ h.summary.ensures, q.Holds M
          ((localSem M hs fnTable).dyns as ++ (localSem M hs fnTable).dyns ys)
      | _ => True) :
    contracts.rules.Ensured (localSem M hs fnTable) (localReading M) (LocalReturns M fnTable) (ValidDyn M) op as ys := by
  cases op with
  | call member =>
    rename_i h
    change ∀ e ∈ (contracts.contract (.call h.key)).ensures, _
    rw [contracts.call_member member]
    exact (clauses_exact M fnTable (appendArguments (ArgumentsMatch.ofValues (sem := localSem M hs fnTable) as valid)
      (ArgumentsMatch.ofValues (sem := localSem M hs fnTable) ys returned)) contracts.distinct
      (contracts.headerParts member).2).mpr old
  | row | literal => intro e m; cases m
  | owned owned =>
    let raw : LocalRaw V := .owned owned.name.1 owned.name.2.1 owned.name.2.2
    have other : ∀ key, raw ≠ .call key := by simp [raw]
    change ∀ e ∈ (contracts.contract raw).ensures, _
    rw [contracts.noncall other]
    simp [Contract.ensures, FactCheck.localOpFacts_ensures raw other]

theorem FunctionContracts.eligible_print {ins outs} (op : LocalOp V hs ins outs) :
    contracts.eligible op op.print = (!op.canStop && (contracts.contract op.print).preconditions.isEmpty) := by
  cases op with
  | call m => simp [FunctionContracts.eligible, LocalOp.print, contracts.call_member m]
  | row | owned | literal =>
    simp [FunctionContracts.eligible, LocalOp.print, FunctionContracts.contract]

private theorem assertable_iff {ins outs} (op : LocalOp V hs ins outs) :
    contracts.assertable op.print = true ↔ op.canStop = false ∧
      (contracts.contract op.print).preconditions = [] := by
  simp [FunctionContracts.assertable, resolveLocal_print contracts.distinct, contracts.eligible_print]

private theorem literalAllowed (n : Nat) : contracts.assertable (.literal .nat [n]) = true :=
  (assertable_iff contracts (.literal .nat [n] rfl)).mpr ⟨rfl,rfl⟩

private theorem addAllowed : contracts.assertable (.owned .natAdd [] []) = true :=
  (assertable_iff contracts (.owned .natAdd)).mpr ⟨rfl,rfl⟩

/-- The checked catalog implements each operation and loop law for actual function evaluation. -/
theorem FunctionContracts.lawful (callees : Callees M fnTable)
    (permitted : ∀ op, (localSem M hs fnTable).S.Reply op → Prop) :
    contracts.rules.Lawful (localSem M hs fnTable) permitted (localReading M)
      (LocalReturns M fnTable) (ValidDyn M) (· = .undefined) := by
  have keeps {raw xs ys} (ran : LocalReturns M fnTable raw xs ys)
      (valid : ∀ v ∈ xs, ValidDyn M v) : ∀ v ∈ ys, ValidDyn M v := by
    obtain ⟨ins, outs, o, args, returned, _, rfl, rfl, ran⟩ := ran
    exact ((localSem M hs fnTable).dyns_valid_iff returned).mpr (localOp_valid fnTable callees.keeps o
      args returned (((localSem M hs fnTable).dyns_valid_iff args).mp valid) ran)
  exact {
    computes := by
      intro ins res o shared key path values
      have stops : o.canStop = false := by simpa [rules] using shared
      have quiet := localOp_stops_undefined M fnTable callees.quiet o values stops
      change (∃ ys, localOp M fnTable o values = .done ys ∧ _) ∨ ∃ h, localOp M fnTable o values = .halt h ∧ _
      cases ran : localOp M fnTable o values with
      | done ys => exact .inl ⟨ys, rfl, ins, res, o, values, ys, rfl, rfl, rfl, ran⟩
      | halt h => rw [ran] at quiet; exact .inr ⟨h, rfl, quiet⟩
      | call op _ => exact nomatch op
    observedOperand := by
      intro ins res op i found
      cases found
    functional := fun _ _ _ _ => FactCheck.localReturns_functional contracts.distinct
    commutative := by
      intro raw commutes first second results returns
      change raw.commutes = true at commutes
      obtain ⟨ins, res, o, args, returned, printed, sameArgs, sameResults, ran⟩ := returns
      subst printed
      cases o with
      | row => simp [LocalOp.print, LocalRaw.commutes] at commutes
      | literal => simp [LocalOp.print, LocalRaw.commutes] at commutes
      | call => simp [LocalOp.print, LocalRaw.commutes] at commutes
      | owned o =>
          cases o <;> simp [LocalOp.print, OwnedOp.name,
            LocalRaw.commutes, ownedContract] at commutes
          all_goals
            rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            have sameArgs : [(⟨_, a⟩ : (τ : V.Ty) × M.Val τ), ⟨_, b⟩] = [first, second] := sameArgs
            simp only [List.cons.injEq] at sameArgs
            obtain ⟨rfl, rfl, -⟩ := sameArgs
            refine ⟨_, _, .owned _, .cons b (.cons a .nil), returned, rfl, rfl, sameResults, ?_⟩
            rw [← ran]
            simp only [localOp, ownedOp, Nat.add_comm, Nat.mul_comm, Bool.beq_comm,
              natEqual_symmetric]
    keeps := fun _ _ _ ran valid =>
      ⟨keeps ran valid, localResultCount_correct M fnTable contracts.distinct ran⟩
    defined := by
      intro ins outs op shared key path values valid known
      have req := localRequired M fnTable contracts op values valid known
      have va := ((localSem M hs fnTable).dyns_valid_iff values).mp valid
      have stops : op.canStop = false := by simpa [rules] using shared
      have defined := FactCheck.localOp_defined callees op values va req
      have quiet := localOp_stops_undefined M fnTable callees.quiet op values stops
      obtain ⟨ys, ran⟩ : ∃ ys, localOp M fnTable op values = .done ys := by
        cases h : localOp M fnTable op values with
        | done ys => exact ⟨ys, rfl⟩
        | halt h' => rw [h] at defined quiet; exact absurd quiet defined
        | call op _ => exact nomatch op
      have ret : LocalReturns M fnTable op.print ((localSem M hs fnTable).dyns values) ((localSem M hs fnTable).dyns ys) :=
        ⟨ins,outs,op,values,ys,rfl,rfl,rfl,ran⟩
      have ok := keeps ret valid
      exact ⟨ys,ran,ret,localEnsured M fnTable contracts op values ys valid ok (by
        cases op with
        | call m =>
          have post := FactCheck.localCall_holds callees m values va req
          change (fnTable _ m values).Every _ _ _ at post
          change fnTable _ m values = .done ys at ran
          rw [ran] at post
          exact post.2
        | row | literal | owned => trivial)⟩
    assertable := by
      intro ins outs op h
      obtain ⟨quiet, empty⟩ := (assertable_iff contracts op).mp h
      exact ⟨by simp [rules, quiet], by simp [rules, Contract.requires, empty]⟩
    effect := by
      intro ins outs op ordered key path values valid known
      have req := localRequired M fnTable contracts op values valid known
      cases op with
      | call m =>
        have post := FactCheck.localCall_holds callees m values
          (((localSem M hs fnTable).dyns_valid_iff values).mp valid) req
        change (fnTable _ m values).Every _ _ _ at post ⊢
        cases ran : fnTable _ m values with
        | done ys =>
          rw [ran] at post
          have ok : ∀ v ∈ (localSem M hs fnTable).dyns ys, ValidDyn M v :=
            ((localSem M hs fnTable).dyns_valid_iff ys).mpr post.1
          exact ⟨ok, localEnsured M fnTable contracts (.call m) values ys valid ok post.2⟩
        | halt h => rw [ran] at post; exact post
        | call op _ => exact nomatch op
      | row | owned | literal => cases ordered
    condition := by intro w t ok v _; subst ok; rfl
    count := by intro w t ok v _; subst ok; rfl
    pick := fun ok v valid => localPick_valid ok v valid
    index := fun _ _ => ⟨trivial, fun _ => rfl⟩
    indexAt := by
      intro w n e found
      cases found
      exact ⟨by simp [LocalIndex.atIteration, Expr.UsesOnly, Exprs.UsesOnly, rules, literalAllowed],
        LocalIndex.atIteration_denotes M fnTable [] n⟩
    indexFromCount := by
      intro w t count e found
      cases found
      change t = .nat at count
      subst t
      exact ⟨rfl, fun n _ => LocalIndex.fromCount_denotes M fnTable n⟩
    indexNext := by
      intro w e found
      cases found
      exact ⟨by simp [LocalIndex.next, LocalIndex.atIteration, Expr.UsesOnly, Exprs.UsesOnly, rules,
        addAllowed, literalAllowed], LocalIndex.next_denotes M fnTable⟩
    collect := localCollect_valid
    begin := fun _ _ _ => trivial
    settle := fun _ _ _ => trivial
    stop := fun _ _ _ => nofun }

end Zkc.Core.BodyAnalysis
