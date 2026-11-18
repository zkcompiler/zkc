module

public import Zkc.Core.Facts.Contracts.LocalOperations
public import Zkc.Core.Meaning.Validity

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {fns : List (FnHeader V)}

theorem resolveLocal_print (distinct : (fns.map (·.key)).Nodup) {ins outs : List V.Ty}
    (op : LocalOp V fns ins outs) : resolveLocal fns op.print = some ⟨ins,outs,op⟩ := by
  cases op with
  | row key sig typ =>
    simp only [LocalOp.print, resolveLocal]
    split <;> rename_i seen <;> rw [typ] at seen <;> cases seen
    rfl
  | owned op => simp [LocalOp.print, resolveLocal, OwnedOp.resolve_name]
  | literal ty data reads => simp [LocalOp.print, resolveLocal, reads]
  | call callee => simp [LocalOp.print, resolveLocal, Member.withKey_key (·.key) callee distinct]

/-- A successful executable read and the signature used for result allocation agree. -/
theorem resolveLocal_read (distinct : (fns.map (·.key)).Nodup) {raw ins outs} {op : LocalOp V fns ins outs}
    (read : LocalOp.read fns raw ins = .ok ⟨outs,op⟩) : resolveLocal fns raw = some ⟨ins,outs,op⟩ := by
  rw [← LocalOp.print_read raw op read]
  exact resolveLocal_print distinct op

theorem localResultCount_correct (M : Model V) (table : FnTable M fns) (distinct : (fns.map (·.key)).Nodup)
    {raw xs ys} (run : LocalReturns M table raw xs ys) : ys.length = localResultCount fns raw := by
  obtain ⟨ins, outs, op, args, result, rfl, rfl, rfl, _⟩ := run
  simp [localResultCount, resolveLocal_print distinct, Semantics.dyns_length]

#print axioms resolveLocal_read
#print axioms localResultCount_correct
end Zkc.Core.BodyAnalysis
