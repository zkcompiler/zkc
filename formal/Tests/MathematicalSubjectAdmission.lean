import Zkc.Source.Mathematical.SubjectAdmission
import Tests.MathematicalClosedInstances
import Tests.MathematicalDefinitionCalls

set_option autoImplicit false
namespace Tests.MathematicalSubjectAdmission
open Zkc.Source Zkc.Source.Mathematical
open MathematicalClosedInstances (leaf caller invoke subject diamond repeated rooted sameSignature capabilityLeaf)

structure Summary where
  preorder : List ClosedInstances.Key
  stored : List ClosedInstances.Key
  entry : Nat
  sites : List Nat
  calls : List (List Protocol.Invocation)

def storedSites {Payload contracts source header}
    {records : List (ClosedAssembly.Record (Payload := Payload) (contracts := contracts) (source := source) header)} :
    ClosedAssembly.History header records → List Nat
  | .nil => []
  | .snoc previous prepared => storedSites previous ++ [prepared.bound.body.checked.program.sites.length]

def check (source : Raw.Subject) (budget : Nat := 1000000) : Except String Summary := do
  let bytes ← Tools.Mathematical.Codec.encode (← Tools.Mathematical.SchemaEncoding.encode source)
  let raw ← Tools.Mathematical.Schema.decode (← Tools.Mathematical.Codec.decode bytes)
  let admitted ← (SubjectAdmission.admit MathematicalDeclarations.contracts raw).run' budget
    |>.mapError (fun error => toString (repr error))
  return ⟨ClosedInstances.keys admitted.assembly.graph.nodes,
    ClosedAssembly.recordKeys admitted.header admitted.assembly.table.records,
    admitted.assembly.entryPosition.val, storedSites admitted.assembly.table.history,
    admitted.assembly.closed.definitions.invocationTable⟩

def accepts (source : Raw.Subject) : Bool := (check source).isOk

def paired (roots : List Nat) : Raw.Subject := subject [MathematicalDefinitions.paired] roots

def unusedAliased : Raw.Subject := subject
  [{ MathematicalDefinitions.paired with body := (.mk
    [.local 0 ⟨0⟩ ⟨2⟩ [.parameter 0] (.object []) [⟨0⟩, ⟨0⟩] [⟨0⟩]] (.ret [⟨0⟩])) }, leaf]

def dormantPaired (roots : List Nat) : Raw.Subject := subject [MathematicalDefinitions.paired,
  { MathematicalDefinitions.paired with results := [], body := (.mk
    [.repeat 0 (.literal 0) [] [] [⟨0⟩, ⟨1⟩] (.mk
      [.invoke 1 ⟨0⟩ [.parameter 0] [⟨0⟩, ⟨1⟩] [⟨0⟩, ⟨1⟩] [⟨1⟩, ⟨2⟩]] (.ret []))]
    (.ret [])) }] roots

def arithmeticCaller : Raw.Definition :=
  { MathematicalDefinitions.definition with
    statics := 0
    capabilities := [⟨⟨⟨0⟩, [.literal 3]⟩, [⟨0⟩]⟩]
    arguments := [⟨[⟨0⟩], ⟨⟨1⟩, [.literal 3]⟩⟩, ⟨[⟨1⟩], MathematicalDeclarations.booleanUse⟩]
    relations := []
    body := .mk [.invoke 0 ⟨0⟩ [.add (.literal 1) (.literal 2)] [⟨0⟩, ⟨1⟩] [⟨0⟩] [⟨0⟩, ⟨1⟩]] (.ret [⟨0⟩]) }

def arithmeticCall : Raw.Subject := subject [MathematicalDefinitions.definition, arithmeticCaller] [0] []

def offsetCallee : Raw.Definition :=
  { leaf with
    arguments := [⟨[⟨0⟩], ⟨⟨1⟩, [.add (.parameter 0) (.literal 1)]⟩⟩]
    results := [⟨[⟨0⟩], ⟨⟨1⟩, [.add (.parameter 0) (.literal 1)]⟩⟩]
    body := .mk [] (.ret [⟨0⟩]) }

def offsetCaller : Raw.Definition :=
  { leaf with
    arguments := [⟨[⟨0⟩], ⟨⟨1⟩, [.add (.literal 2) (.parameter 0)]⟩⟩]
    results := [⟨[⟨0⟩], ⟨⟨1⟩, [.add (.parameter 0) (.literal 2)]⟩⟩]
    body := .mk [.invoke 0 ⟨0⟩ [.add (.literal 1) (.parameter 0)] [⟨0⟩, ⟨1⟩] [] [⟨0⟩]] (.ret [⟨0⟩]) }

-- Every accepted stored record's root tuple is the actual closed source key.
example {Payload contracts source} (header : DeclarationAdmission.Header (Payload := Payload) contracts source)
    {records key node} (prepared : ClosedAssembly.Prepared header records key node) :
    prepared.target.capabilities.map Protocol.Capability.root = key.roots :=
  ClosedAssembly.Prepared.target_roots header prepared

-- The complete entry uses the admitted header's actual capabilities.
example {Payload contracts source} (admitted : SubjectAdmission.Admitted (Payload := Payload) contracts source) :
    Protocol.Closed (vocabulary := RegisteredVocabulary.vocabulary admitted.header 0) admitted.header.capabilities :=
  ClosedAssembly.Result.closed admitted.header admitted.assembly

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (match check diamond with
    | .ok result => result.preorder.map (·.definition) == [3, 1, 0, 2] &&
        result.stored.map (·.definition) == [0, 1, 2, 3] && result.entry == 3 && result.sites == [0, 1, 1, 2] &&
        result.calls == [[], [⟨0, 0, []⟩], [⟨0, 0, []⟩], [⟨0, 1, []⟩, ⟨1, 2, []⟩]]
    | _ => false) "serialized subject admits an actual acyclic typed table with checked preorder mapping"
  checks.holds (match check (repeated 0) with
    | .ok result => result.sites == [0, 3] && result.calls == [[], [⟨1, 0, []⟩, ⟨2, 0, []⟩]]
    | _ => false) "closed zero repeat retains all syntactic sites and callees"
  checks.holds (match check (repeated 1000000000) with
    | .ok result => result.sites == [0, 3] && result.calls == [[], [⟨1, 0, []⟩, ⟨2, 0, []⟩]]
    | _ => false) "closed billion repeat has the same stored representation"
  checks.holds (accepts (rooted [0, 0])) "whole subject preserves shared state aliases across repeated calls"
  checks.holds (accepts (rooted [0, 1])) "whole subject preserves distinct roots with identical services"
  checks.holds (accepts sameSignature) "same-signature declarations remain distinct through typed assembly"
  checks.holds (accepts arithmeticCall) "closed arithmetic call normalizes vector and service signatures to actual literals"
  checks.holds (accepts (subject [offsetCallee, offsetCaller]))
    "caller and callee normalize different arithmetic expressions in static-dependent ports"
  checks.holds (accepts (paired [0, 1])) "registered distinct requirement discharges at actual different roots"
  checks.holds (!(accepts (paired [0, 0]))) "registered distinct requirement rejects actual root aliasing"
  checks.holds (accepts unusedAliased) "unused well-formed template retains a deferred unsatisfiable root requirement"
  checks.holds (accepts (dormantPaired [0, 1])) "valid callee under zero repeat forms and discharges actual roots"
  checks.holds (!(accepts (dormantPaired [0, 0]))) "zero repeat cannot hide a callee's failing root requirement"
  checks.holds (accepts (subject [leaf, caller [invoke 0 0 [.literal 4]]]))
    "callee may use a different static tuple when its value and service interfaces still agree"
  checks.holds (!(accepts (subject [MathematicalDefinitions.definition, MathematicalDefinitionCalls.withCall
    (MathematicalDefinitionCalls.call 0 [.literal 4])] [0])))
    "closed callee cannot disagree with actual caller value and service types"
  checks.holds (!(accepts (subject [{ leaf with body := .mk [.guard 0 ⟨0⟩ ⟨0⟩] (.ret []) }, leaf])))
    "unused malformed definition is refused before entry closure"
  let brokenRelation := { (subject [leaf]) with module.relations :=
    [{ MathematicalRelations.predicate with body := ⟨[], [.operation ⟨0⟩ [] (.object []) [⟨0⟩]], [⟨0⟩]⟩ }] }
  checks.holds (!(accepts brokenRelation)) "unused malformed relation is still checked"
  checks.holds (!(accepts (subject [capabilityLeaf] []))) "entry capability arity is checked"
  checks.holds (!(check diamond 1).isOk) "whole subject shares the declaration and closure resource allowance"
  checks.finish "mathematical whole source admission"

#eval run
end Tests.MathematicalSubjectAdmission
