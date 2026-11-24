module

public import Zkc.Core.Facts.Knowledge.Soundness
public import Zkc.Core.Facts.Knowledge.DialectReadings

@[expose] public section

namespace Zkc.Core.BodyAnalysis

/-- Read both ends of a typed conversion from the compiler's successful execution. -/
theorem localReturns_preservesNumber {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)}
    {table : FnTable M fns} {op : LocalRaw V} {xs ys}
    (preserves : localPreservesNumber op = true) (run : LocalReturns M table op xs ys) :
    ∃ source result, xs = [source] ∧ ys.head? = some result ∧
      (localReading M).nat source = (localReading M).nat result := by
  obtain ⟨ins, outs, instr, args, results, rfl, rfl, rfl, executed⟩ := run
  cases instr with
  | owned owned =>
    simp only [LocalOp.print, localPreservesNumber, OwnedOp.resolve_name, Option.any_some] at preserves
    cases owned <;> try contradiction
    case natBelow bound =>
      obtain ⟨x, rfl⟩ := HList.one args
      simp only [localOp, ownedOp] at executed
      split at executed
      · cases executed
        exact ⟨_, _, rfl, rfl, rfl⟩
      · cases executed
    case finToNat | finWiden =>
      obtain ⟨x, rfl⟩ := HList.one args
      simp only [localOp, ownedOp, Process.done.injEq] at executed
      subst results
      exact ⟨_, _, rfl, rfl, rfl⟩
  | _ => contradiction

/-- The executable domain for function bodies, interpreted by the compiler's evaluation relation. -/
def localKnowledgeLawful {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)}
    (table : FnTable M fns) (distinct : (fns.map (·.key)).Nodup) :
    (Knowledge.domain (localKnowledgeTypes V) (localKnowledgeOperations fns)).Lawful
      (ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M))
      (localReading M) (TypedValue (localSem M fns table) (ValidDyn M)) :=
  Knowledge.lawful
    { functional := fun _ _ _ _ first second => FactCheck.localReturns_functional distinct first.1 second.1
      form := fun _ _ _ _ form run => FactCheck.localReturns_form form run.1
      preservesNumber := fun _ _ _ preserves run => localReturns_preservesNumber preserves run.1
      ranges := fun _ _ _ known run => FactCheck.localRun_ranges known run }
    (localKnowledgeTypes_lawful M table)

end Zkc.Core.BodyAnalysis
