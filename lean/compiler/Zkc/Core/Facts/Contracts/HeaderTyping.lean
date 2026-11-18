module

public import Zkc.Core.Facts.Contracts.StoredLaws
public import Zkc.Core.Facts.Contracts.LocalOperationLaws
public import Zkc.Core.Facts.Body.Functions

@[expose] public section

namespace Zkc.Core.BodyAnalysis

theorem FunctionContracts.assertionTypes_eq {V : Vocabulary} {hs : List (FnHeader V)} (contracts : FunctionContracts hs) :
    contracts.assertionTypes = localAssertionTypes hs contracts.assertable := by
  have signatures (raw : LocalRaw V) (ins : List V.Ty) :
      contracts.assertionTypes.signature raw ins =
        (localAssertionTypes hs contracts.assertable).signature raw ins := by
    change (do
      let ⟨outs, op⟩ ← (LocalOp.read hs raw ins).toOption
      if contracts.eligible op raw then some outs else none) =
      (if contracts.assertable raw then (LocalOp.read hs raw ins).toOption.map Sigma.fst else none)
    cases parsed : LocalOp.read hs raw ins with
    | error _ => cases contracts.assertable raw <;> rfl
    | ok sig =>
      obtain ⟨outs, op⟩ := sig
      simp [assertable, resolveLocal_read contracts.distinct parsed, Except.toOption]
  exact congrArg (fun sig => AssertionTypes.mk sig (fun t : V.Ty => decide (t = .bool))) (funext fun raw => funext (signatures raw))

end Zkc.Core.BodyAnalysis

namespace Zkc.Core.BodyAnalysis.HeaderContracts
variable {V : Vocabulary}

/-- Re-reading an accepted header operation in a larger body reader gives exactly its
checked ports. The successful read supplies the typed row, literal or core operation. -/
private theorem signature_body {hs : List (FnHeader V)} (catalog : FunctionContracts hs)
    {raw ins outs} (ok : (stableTypes V).signature raw ins = some outs) :
    (localAssertionTypes hs catalog.assertable).signature raw ins = some outs := by
  cases read : LocalOp.read (V := V) [] raw ins with
  | error err => simp [stableTypes, localAssertionTypes, AssertionTypes.ofReader, localRules, read,
      Except.toOption] at ok
  | ok pair =>
    obtain ⟨ts, op⟩ := pair
    have print := LocalOp.print_read raw op read
    subst raw
    have checked : stableAllowed op.print = true ∧ ts = outs := by
      simpa [stableTypes, localAssertionTypes, AssertionTypes.ofReader, localRules, read, Except.toOption,
        apply_ite] using ok
    obtain ⟨allow, rfl⟩ := checked
    simp only [stableAllowed, resolveLocal_print (fns := []) List.nodup_nil] at allow
    have accept (o : LocalOp V hs ins ts) (allowed : catalog.assertable o.print = true) :
        (localAssertionTypes hs catalog.assertable).signature o.print ins = some ts := by
      simp [localAssertionTypes, AssertionTypes.ofReader, allowed, localRules,
        LocalOp.read_print catalog.distinct, Except.toOption]
    cases op
    case call m => cases m
    case' row k s h => apply accept (.row k s h)
    case' owned o => apply accept (.owned o)
    case' literal t d h => apply accept (.literal t d h)
    all_goals
      simp only [FunctionContracts.assertable, resolveLocal_print catalog.distinct]
      simpa only [LocalOp.print, LocalOp.canStop, FunctionContracts.eligible, localOpFacts] using allow

section
variable {hs : List (FnHeader V)} (catalog : FunctionContracts hs) {ctx : List V.Ty}
mutual
  private theorem infer_body : ∀ (e : Assertion V) {t}, (stableTypes V).infer ctx e = some t →
      (localAssertionTypes hs catalog.assertable).infer ctx e = some t
    | .arg _, _, ok => ok
    | .apply op es i, _, ok => by
      obtain ⟨ts, a, outs, b, p⟩ := (by
        simpa only [AssertionTypes.infer, Option.bind_eq_bind, Option.bind_eq_some_iff] using ok)
      simp [AssertionTypes.infer, inferAll_body es a, signature_body catalog b, p]
  private theorem inferAll_body : ∀ (es : Exprs (LocalRaw V)) {ts}, (stableTypes V).inferAll ctx es = some ts →
      (localAssertionTypes hs catalog.assertable).inferAll ctx es = some ts
    | .nil, _, ok => ok
    | .cons e es, _, ok => by
      obtain ⟨_, a, _, b, rfl⟩ := (by
        simpa only [AssertionTypes.inferAll, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
          Option.pure_def] using ok)
      simp [AssertionTypes.inferAll, infer_body e a, inferAll_body es b]
end
end

/-- The header certificate supplies the full contract portion of either body's preflight. -/
theorem body_check {hs : List (FnHeader V)} (catalog : FunctionContracts hs) {h : FnHeader V}
    (checked : CheckedHeader h) :
    Contract.check (D := localDialect V hs) catalog.assertionTypes checked.val h.ins h.outs = true := by
  rw [catalog.assertionTypes_eq]
  obtain ⟨pre, post⟩ := translate_typed checked.property
  let types := localAssertionTypes hs catalog.assertable
  have body {ctx c} (w : WellTyped ctx c) : types.isAssertion ctx c.assertion = true ∧
      c.boundTyped (D := localDialect V hs) types ctx = true := by
    constructor
    · unfold AssertionTypes.isAssertion
      rw [show types.infer ctx c.assertion = some .bool from infer_body catalog _ w.1]
      rfl
    · apply (Option.all_eq_true ..).mpr
      intro e pos
      obtain ⟨ty, typed, _⟩ := w.2 e pos
      rw [show types.infer ctx e = some ty from infer_body catalog _ typed]
      rfl
  simp only [Contract.check, Contract.requires, Contract.ensures, Bool.and_eq_true, List.all_eq_true,
    List.forall_mem_map]
  exact ⟨⟨fun c m => (body (pre c m)).1, fun c m => (body (post c m)).1⟩,
    fun c m => (body (pre c m)).2, fun c m => (body (post c m)).2⟩

end Zkc.Core.BodyAnalysis.HeaderContracts
