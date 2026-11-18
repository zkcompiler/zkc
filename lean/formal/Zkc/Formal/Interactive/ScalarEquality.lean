module

public import Zkc.Core.Meaning.Local

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ScalarEquality
open Core
variable {V : Vocabulary} (t : V.Ty)

abbrev signature : RowSignature V.TypeKey V.RowKey := ⟨[t,t],[.bool],.pure⟩

/-- Interpretation of the exact equality row chosen by a source guard. -/
def Law (key : V.RowKey) (typed : V.row key = some (signature t))
    (M : Model V) [DecidableEq (M.Val t)] : Prop :=
  ∀ a b : M.Val t, M.apply key (signature t) typed (.cons a (.cons b .nil)) =
    some (.cons (decide (a = b)) .nil)

end Zkc.Formal.Interactive.Sumcheck.ScalarEquality
