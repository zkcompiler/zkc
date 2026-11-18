module

public import Zkc.Core.Facts.Contracts.Elaboration
public import Zkc.Core.Program.LocalRules

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {D : Dialect} {Raw Who : Type}

/-- The elaborator already resolves operations against operand types. Reuse that decision for
assertions and retain the analysis rule's separate admissibility test. -/
def AssertionTypes.ofReader (reader : Zkc.Core.Rules D Raw Who) (allowed : Raw → Bool)
    (boolean : D.Ty → Bool) : AssertionTypes D.Ty Raw where
  signature op ins :=
    if allowed op then (reader.op op ins).toOption.map Sigma.fst else none
  boolean := boolean

/-- Local assertions use the same operand and result types as local program instructions. -/
def localAssertionTypes {V : Vocabulary} (fns : List (FnHeader V)) (allowed : LocalRaw V → Bool) :
    AssertionTypes V.Ty (LocalRaw V) :=
  .ofReader (localRules fns) allowed (fun t => decide (t = .bool))

end Zkc.Core.BodyAnalysis
