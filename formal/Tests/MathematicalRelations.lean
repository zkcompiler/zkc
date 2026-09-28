import Zkc.Source.Mathematical.RelationAdmission
import Tools.Mathematical.SchemaEncoding
import Tests.MathematicalDeclarations

set_option autoImplicit false
namespace Tests.MathematicalRelations
open Zkc.Source.Mathematical

def predicate : Raw.Relation :=
  ⟨1, [MathematicalDeclarations.vectorUse], [MathematicalDeclarations.booleanUse], [],
    .mk [⟨1⟩] [.operation ⟨0⟩ [] (.object []) [⟨0⟩]] [⟨0⟩]⟩

def subject : Raw.Subject :=
  { MathematicalDeclarations.subject with module.relations := [predicate] }

-- SHA-256 of test.math.reflexivity/v1:forall x:Fin2,x=x (no newline).
def lawIdentity : Raw.Identity := ⟨"test.math.reflexivity", "1",
  "361959cd703ffc11a6955a7d5e14d736aeb2e7346ed1cc54969d04b06b0cf947"⟩

def lawContracts : RegistryAdmission.Contracts MathematicalDeclarations.Payload :=
  { MathematicalDeclarations.contracts with installation := fun category => match category with
      | .law => ⟨[⟨lawIdentity, (), []⟩], by simp⟩
      | .domain => MathematicalDeclarations.installation .domain
      | .operation => MathematicalDeclarations.installation .operation
      | .wire => MathematicalDeclarations.installation .wire
      | .service => MathematicalDeclarations.installation .service }

private def asString {α E : Type} [Repr E] (action : StateT Nat (Except E) α) : StateT Nat (Except String) α :=
  fun remaining => (action remaining).mapError (fun error => toString (repr error))

def check (source : Raw.Subject)
    (contracts : RegistryAdmission.Contracts MathematicalDeclarations.Payload := MathematicalDeclarations.contracts) : Except String Bool := do
  -- This path starts at serialized subject bytes, including the actual
  -- manifest, type table, relation declaration and region operation use.
  let bytes ← Tools.Mathematical.Codec.encode (← Tools.Mathematical.SchemaEncoding.encode source)
  let raw ← Tools.Mathematical.Schema.decode (← Tools.Mathematical.Codec.decode bytes)
  (show StateT Nat (Except String) Bool from do
    let header ← asString (DeclarationAdmission.admit contracts raw)
    let _ ← asString (RelationAdmission.all header raw.module.relations)
    let selected ← asString (RelationAdmission.use header (arity := 0) (target := 0) Fin.elim0 ⟨0⟩ [.literal 3])
    return selected.checked.body.graph.ports.length == 1).run' 1000000

def withPredicate (relation : Raw.Relation) : Raw.Subject :=
  { subject with module.relations := [relation] }

-- Successful relation admission retains exact carrier erasure and the
-- condition-result contract independently of the concrete test installation.
example {Payload contracts source} (header : DeclarationAdmission.Header (Payload := Payload) contracts source)
    {target relation parameters} (result : RelationAdmission.Instance header (target := target) relation parameters) :
    result.body.resolved.erase = relation.body := result.body.erasure

example {Payload contracts source} (header : DeclarationAdmission.Header (Payload := Payload) contracts source)
    {target relation parameters} (result : RelationAdmission.Instance header (target := target) relation parameters) :
    result.body.graph.ports.map Port.ty = [(RegisteredVocabulary.vocabulary header target).condition] := result.result

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (match check subject with | .ok value => value | .error _ => false)
    "serialized relation resolves installed operation and symbolic/closed signatures"
  checks.holds (!(check (withPredicate { predicate with assumptions := [⟨0⟩] })).isOk)
    "relation law reference must select the actual manifest"
  let assumed := { subject with manifest.laws := [lawIdentity], module.relations := [{ predicate with assumptions := [⟨0⟩] }] }
  checks.holds (match check assumed lawContracts with | .ok value => value | .error _ => false)
    "relation retains an actually installed law assumption"
  checks.holds (!(check { assumed with manifest.laws := [{ lawIdentity with digest := MathematicalDeclarations.copy.digest }] }
    lawContracts).isOk) "relation cannot replace its selected law package"
  checks.holds (!(check (withPredicate { predicate with body := .mk [⟨1⟩] [] [] })).isOk)
    "relation needs one condition result"
  checks.holds (!(check (withPredicate { predicate with body := .mk [⟨1⟩] [] [⟨0⟩, ⟨0⟩] })).isOk)
    "relation cannot return multiple conditions"
  checks.holds (!(check (withPredicate { predicate with body := .mk [⟨0⟩] [] [⟨0⟩] })).isOk)
    "vector result is not a condition"
  checks.holds (!(check (withPredicate { predicate with body := .mk [⟨2⟩] [] [⟨0⟩] })).isOk)
    "relation capture is in public plus witness input scope"
  checks.holds (!(check (withPredicate { predicate with body := .mk [⟨1⟩] [.operation ⟨0⟩ [] (.object []) [⟨1⟩]] [⟨0⟩] })).isOk)
    "relation node cannot use a forward value"
  checks.holds (!(check (withPredicate { predicate with body := .mk [⟨0⟩] [.operation ⟨1⟩ [.parameter 0] (.object []) [⟨0⟩]] [⟨0⟩] })).isOk)
    "relation cannot use an ordered operation"
  checks.holds (!(check (withPredicate { predicate with publicInputs := [⟨⟨1⟩, [.parameter 1]⟩] })).isOk)
    "unused relation input still checks its static scope"
  checks.holds (!(check { subject with module.relations := [predicate,
    { predicate with body := .mk [] [] [] }] }).isOk) "unused relation body still checked"
  checks.holds (!(check (withPredicate { predicate with statics := 0 })).isOk)
    "relation static arity belongs to the selected declaration"
  checks.finish "mathematical registered relations"

#eval run
end Tests.MathematicalRelations
