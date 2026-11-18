module

public import Zkc.Core.Facts.Contracts.Functions
public import Zkc.Core.Facts.Body.Walk
public import Zkc.Core.Facts.Knowledge.Inference

@[expose] public section

namespace Zkc.Core.BodyAnalysis
/-- Body preflight already has operand types. One successful read supplies both
the checked operands and the operation tested for assertion admission. -/
def FunctionContracts.assertionTypes {V : Vocabulary} {hs : List (FnHeader V)}
    (contracts : FunctionContracts hs) : AssertionTypes V.Ty (LocalRaw V) where
  signature raw ins := do
    let ⟨outs, typed⟩ ← (LocalOp.read hs raw ins).toOption
    if contracts.eligible typed raw then some outs else none
  boolean t := decide (t = .bool)

/-- The same local type rules used when checking a function body. -/
def localKnowledgeTypes (V : Vocabulary) : KnowledgeTypes V.Ty :=
  ⟨localRange, Ty.noValue⟩

/-- The typed finite conversions whose successful evaluations keep the operand's number. -/
def conversionPreservesNumber {V : Vocabulary} {ins outs : List V.Ty} : OwnedOp V ins outs → Bool
  | .natBelow _ | .finToNat _ | .finWiden .. => true
  | _ => false

/-- Recognize conversions through the compiler's resolver, including its widening side condition. -/
def localPreservesNumber {V : Vocabulary} : LocalRaw V → Bool
  | .owned name types numbers =>
    (OwnedOp.resolve name types numbers).any fun resolved => conversionPreservesNumber resolved.2.2
  | _ => false

/-- Operand-sensitive entries in the local range catalog. The equality below also checks
the remaining entries against the catalog when an operation is added or changed. -/
def localNeedsOperandRanges {V : Vocabulary} : LocalRaw V → Bool
  | .owned name _ _ =>
    match name with
    | .natAdd | .natSub | .natMul | .natDiv | .natRem | .natPow | .natBelow
    | .finToNat | .finWiden => true
    | _ => false
  | _ => false

def localKnowledgeOperations {V : Vocabulary} (fns : List (FnHeader V)) :
    KnowledgeOperations (LocalRaw V) :=
  { KnowledgeOperations.ofFacts (localOpFacts fns) with
    preservesNumber := localPreservesNumber
    needsOperandRanges := localNeedsOperandRanges
    ranges_constant := by
      intro op constant rs
      cases op with
      | owned name types numbers =>
        cases name <;> simp [localNeedsOperandRanges] at constant <;> try rfl
        simp only [KnowledgeOperations.ofFacts, localOpFacts, ownedContract]
        split <;> rfl
      | row | call | literal => rfl }

/-- Use the same checked header catalog for assertion admission and operation contracts. -/
def FunctionContracts.baseConfig {V : Vocabulary} {hs : List (FnHeader V)} (contracts : FunctionContracts hs)
    (definition : Key) (lemmas : List (Lemma V.Ty (LocalRaw V))) : Config (localDialect V hs) (LocalRaw V) where
  rules := contracts.rules
  domain := Knowledge.domain (localKnowledgeTypes V) (localKnowledgeOperations hs)
  assertions := contracts.assertionTypes
  lemmas := lemmas
  definition := definition
  role := none

/-- Retrieve the original operand order of a refused local operation or stored guarantee. -/
def diagnosticClause {V : Vocabulary} (hs : List (FnHeader V))
    (guarantees : List (HeaderClause V)) (concern : Concern (LocalRaw V)) (index : Nat) :
    Option (Sum (Requirement (LocalRaw V)) (ContractClause (LocalRaw V))) :=
  let source := fun (c : HeaderClause V) => match c with
    | .positional q => Sum.inl q.lift
    | .assertion c => Sum.inr c
  match concern with
  | .requirement (.call k) => (summaryOf k hs).requires[index]?.map source
  | .requirement written => ((localOpFacts hs).requires written)[index]?.map Sum.inl
  | .guarantee => guarantees[index]?.map source
  | .premise .. | .invariant .. => none

/-- On a refusal, report the learned ranges of the source requirement's operands, including
lengths and row applications. Temporary entries used to inspect the operands are discarded. -/
def FunctionContracts.config {V : Vocabulary} {hs : List (FnHeader V)} (contracts : FunctionContracts hs)
    (definition : Key) (lemmas : List (Lemma V.Ty (LocalRaw V))) (guarantees : List (HeaderClause V) := []) :
    Config (localDialect V hs) (LocalRaw V) :=
  let cfg := contracts.baseConfig definition lemmas
  { cfg with explain := fun concern index positions values known =>
      match diagnosticClause hs guarantees concern index with
      | none | some (.inr _) => []
      | some (.inl requirement) => requirement.operands.map fun operand => do
        let (id, _, state) ← enterExpr cfg positions (builtinOperand operand) values known
        state.rangeOf id.key }

end Zkc.Core.BodyAnalysis
