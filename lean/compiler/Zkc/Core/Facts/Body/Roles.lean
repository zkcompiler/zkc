module

public import Zkc.Core.Facts.Domains.UnaryMeasurements
public import Zkc.Core.Facts.Body.Functions
public import Zkc.Core.Facts.Contracts.Roles
public import Zkc.Core.Facts.Contracts.RoleReader

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary}

def roleKnowledgeTypes (V : Vocabulary) (r : Role) : KnowledgeTypes (LTy V) where
  range t := if r ∈ t.holders then localRange t.ty else none
  empty t := decide (r ∈ t.holders) && Ty.noValue t.ty

/-- A computation uses the numeric catalog for its underlying local instruction. -/
def roleKnowledgeOperations (fns : List (FnHeader V)) : KnowledgeOperations (RoleRaw V) where
  ranges
    | .compute _ op, known => (localKnowledgeOperations fns).ranges op known
    | _, _ => []
  preservesNumber
    | .compute _ op => (localKnowledgeOperations fns).preservesNumber op
    | _ => false
  form
    | .compute _ op => (localKnowledgeOperations fns).form op
    | _ => none

def measuresLength : RoleRaw V → Bool
  | .compute _ (.owned .seqLength [.seq _ none] []) => true
  | _ => false

def roleDomain (fns : List (FnHeader V)) (r : Role) :=
  (Knowledge.domain (roleKnowledgeTypes V r) (roleKnowledgeOperations fns)).prod
    (UnaryMeasurements.domain measuresLength)

namespace RoleContracts
variable {hs : Headers V} (catalog : FunctionContracts hs.fns) (r : Role)
variable (definition : Key) (lemmas : List (Lemma (LTy V) (RoleRaw V)))

/-- The same projection role selects the reader, knowledge domain, rules and diagnostic places. -/
def config : Config (roleDialect V hs r) (RoleRaw V) where
  rules := rules catalog r
  assertions := roleAssertionTypes hs r (assertable catalog r)
  domain := roleDomain hs.fns r
  definition := definition
  role := some r
  lemmas := lemmas

end RoleContracts
end Zkc.Core.BodyAnalysis
