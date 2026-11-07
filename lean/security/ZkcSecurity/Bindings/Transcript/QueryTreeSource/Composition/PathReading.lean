module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Composition.AccessLog

@[expose] public section

/-! The sequence of primitive, history-keyed scalar requests follows a single
tree on every fixed table. It still pays for each reached request. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.QueryTreeSource.Composition
open Zkc.Source Zkc.Construction QueryTree OracleComp OracleSpec
noncomputable section
variable {carriers : Structured.Carriers} {bound height : Nat} [NeZero bound]
  (segment : Segment) (request : segment.query.request = some (.sampleIndex bound))
  (root : Domain.History carriers)

def nodeKey (node : Node (Fin bound) height) : ScalarKey carriers bound :=
  ⟨encode segment (root, node), (segment.queryAt_request _).trans request⟩

/-- Each primitive address contains all earlier delivered replies and the
current draw. The embedding records the subtree reached by those replies. -/
def readPath : (depth : Nat) → (Node (Fin bound) depth → Node (Fin bound) height) →
    OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) (List (Fin bound))
  | 0, _ => pure []
  | d+1, embed => do
    let value ← typedRenaming.ask (nodeKey segment request root (embed (.inl ())))
    let tail ← readPath d (fun n ↦ embed (.inr (value, n)))
    pure (value :: tail)

variable (table : (key : Root carriers bound ⊕ OtherKey carriers bound) → fullRange carriers bound height key)

private theorem nodeValue (node : Node (Fin bound) height) :
    evalWithAnswerFn (QueryImpl.ofFn (primitiveAnswers segment table))
      (typedRenaming.ask (nodeKey segment request root node)) = table (.inl (.inl root)) (.inl node) := by
  let k := nodeKey segment request root node
  rw [ZkcSecurity.Oracle.Renaming.evalWithAnswerFn_ask, ZkcSecurity.Oracle.Renaming.pullback_some _ _ (key := k) rfl,
    primitiveAnswers_scalar, show locate (height := height) segment k = (.inl root, .inl node) from
      locate_encode segment request (root, node)]

/-- Read on the original heterogeneous table, before regrouping. -/
theorem readPath_table (depth : Nat) (embed : Node (Fin bound) depth → Node (Fin bound) height) :
    evalWithAnswerFn (QueryImpl.ofFn (primitiveAnswers segment table)) (readPath segment request root depth embed) =
      path id depth (fun n ↦ table (.inl (.inl root)) (.inl (embed n))) := by
  induction depth with
  | zero => rfl
  | succ d ih =>
    simp only [readPath, evalWithAnswerFn_bind, nodeValue, path, id_eq]
    change _ :: evalWithAnswerFn _ _ = _
    rw [ih]

private theorem singleKey (node : Node (Fin bound) height) :
    (tableQueryLog (typedRenaming.ask (nodeKey segment request root node)) (primitiveAnswers segment table)).map
      Sigma.fst = [oracleKey (encode segment (root, node))] := by
  rw [ZkcSecurity.Oracle.Renaming.ask_some typedRenaming (key := nodeKey segment request root node) rfl,
    ZkcSecurity.Commitment.tableQueryLog_map, tableQueryLog_query]
  rfl

/-- Every logical call is present in order, even on a fixed table whose
path has repeated values. Cache occupancy does not reduce this count. -/
theorem readPath_log (depth : Nat) (embed : Node (Fin bound) depth → Node (Fin bound) height) :
    (tableQueryLog (fullTranslate segment (readPath segment request root depth embed)) table).map Sigma.fst =
      List.replicate depth (Sum.inl (Sum.inl root)) := by
  rw [full_accessLog]
  induction depth with
  | zero => rfl
  | succ d ih =>
    simp only [readPath, tableQueryLog_bind, List.map_append, singleKey, List.map_cons,
      macroKey_node segment request, tableQueryLog_pure, List.append_nil, List.singleton_append, List.replicate_succ]
    exact congrArg (_ :: ·) (ih _)

end
end ZkcSecurity.FiatShamir.QueryTreeSource.Composition
