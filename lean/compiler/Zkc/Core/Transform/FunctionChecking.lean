module

public import Zkc.Core.Facts.Contracts.HeaderTyping
public import Zkc.Core.Transform.Function

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {hs : List (FnHeader V)} {header : FnHeader V}

/-- Errors distinguish an invalid stored summary from an analysis refusal in the body. -/
inductive FunctionCheckError (V : Vocabulary) where
  | header (key : Key) (source : HeaderClause V)
  | facts (reason : FactCheckError (LocalRaw V))
  | comparison (reason : FollowError (LocalRaw V))

/-- Check an already elaborated function against the catalog of its preceding declarations.
The term conversion is confined to the migration boundary. -/
def FunctionContracts.checkFunction (contracts : FunctionContracts hs) (f : TypedFn V hs header)
    (lemmas : List (Lemma V.Ty (LocalRaw V)) := []) (notes : Annotations (LocalRaw V) := []) :
    Except (FunctionCheckError V) (List (Place × Nat)) := do
  let summary ← (readHeader header).mapError (.header header.key)
  (checkFacts (contracts.config header.key lemmas header.summary.ensures) notes summary.val f.inputs f.body
    ⟨true, (HeaderContracts.body_check contracts summary).symm⟩).mapError .facts

/-- Compare a candidate with an assured source under their common header. -/
def FunctionContracts.compareFunctions (contracts : FunctionContracts hs) (source candidate : TypedFn V hs header)
    (lemmas : List (Lemma V.Ty (LocalRaw V)) := [])
    (sourceNotes candidateNotes : Annotations (LocalRaw V) := []) :
    Except (FunctionCheckError V) (List (Place × Nat)) := do
  let summary ← (readHeader header).mapError (.header header.key)
  (followChecked (contracts.config header.key lemmas header.summary.ensures) (localRules hs).skel header.key sourceNotes candidateNotes
    summary.val source.inputs candidate.inputs source.body candidate.body
    ⟨true, (HeaderContracts.body_check contracts summary).symm⟩).mapError .comparison

end Zkc.Core.BodyAnalysis
