import Zkc.Source.Mathematical.DefinitionAdmission
import Tests.MathematicalRelations
import Tests.MathematicalRegisteredBodies

set_option autoImplicit false
namespace Tests.MathematicalDefinitions
open Zkc.Source.Mathematical
open MathematicalDeclarations (booleanUse vectorUse capabilityUse contracts)
open MathematicalRegisteredBodies (noCalls)

def roles : RoleResolution.Binding := ⟨[0, 1], by decide⟩
def parameters : Fin 1 → Static.Expression 0 := fun _ => .literal ⟨3, by decide⟩
def permission : Raw.Permission := ⟨capabilityUse, [⟨0⟩]⟩
def relation : Raw.RelationBinding := ⟨⟨0⟩, [.parameter 0], [⟨0⟩], [⟨1⟩]⟩
def definition : Raw.Definition :=
  ⟨1, 2, [permission], [⟨[⟨0⟩], vectorUse⟩, ⟨[⟨1⟩], booleanUse⟩],
    [⟨[⟨0⟩], booleanUse⟩], [relation], .mk [.query 0 ⟨0⟩ ⟨0⟩ [⟨0⟩]] (.ret [⟨0⟩])⟩

def source (declaration : Raw.Definition) : Raw.Subject :=
  { MathematicalRelations.subject with module := { MathematicalRelations.subject.module with definitions := [declaration], roots := MathematicalDeclarations.module.roots ++ MathematicalDeclarations.module.roots } }

private def asString {α E : Type} [Repr E] (action : StateT Nat (Except E) α) : StateT Nat (Except String) α :=
  fun remaining => (action remaining).mapError (fun error => toString (repr error))

def check (declaration : Raw.Definition) (binding : RoleResolution.Binding := roles)
    (roots : List Nat := [0]) (closed : Bool := true) : Except String Bool := do
  let bytes ← Tools.Mathematical.Codec.encode (← Tools.Mathematical.SchemaEncoding.encode (source declaration))
  let raw ← Tools.Mathematical.Schema.decode (← Tools.Mathematical.Codec.decode bytes)
  (show StateT Nat (Except String) Bool from do
    let header ← asString (DeclarationAdmission.admit contracts raw)
    let selected ← asString (SignatureAdmission.select raw.module.definitions 0)
    let template ← asString (DefinitionAdmission.template header selected.value binding noCalls [])
    if closed then
      let parameters ← asString (Static.tuple (arity := 0) (target := 0) Fin.elim0 selected.value.statics [.literal 3])
      let checked ← asString (DefinitionAdmission.bind header selected.value parameters.parameters binding noCalls []
        header.capabilities roots)
      let discharged ← checked.body.dischargeRoots.mapError (fun error => toString (repr error))
      return discharged.checked.program.sites == List.range discharged.checked.finish
    else
      return template.body.checked.program.sites == List.range template.body.checked.finish).run' 1000000

def accepts (declaration : Raw.Definition) (binding : RoleResolution.Binding := roles)
    (roots : List Nat := [0]) (closed : Bool := true) : Bool :=
  match check declaration binding roots closed with
  | .ok value => value
  | .error _ => false

def paired : Raw.Definition := { definition with
  capabilities := [permission, permission],
  body := .mk [.local 0 ⟨0⟩ ⟨2⟩ [.parameter 0] (.object []) [⟨0⟩, ⟨1⟩] [⟨0⟩]] (.ret [⟨0⟩]) }

-- Relation operands are selected from the actual definition argument table;
-- availability is not a claim about satisfaction of the bound relation.
example {Payload contracts source} (header : DeclarationAdmission.Header (Payload := Payload) contracts source)
    {arity target parameters arguments raw}
    (checked : DefinitionAdmission.Relation header (arity := arity) (target := target) parameters arguments raw) :
    Graph.inputIndices (algebra := (RegisteredVocabulary.vocabulary header target).toAlgebra) checked.publicInputs =
      raw.publicInputs.map (·.index) := checked.publicErasure

-- Binding restricts permissions while preserving the actual selected roots.
example {vocabulary : Protocol.Vocabulary} {capabilities required} (bindings : Protocol.CapabilityBindings
    (Role := Nat) (vocabulary := vocabulary) capabilities required) :
    bindings.bound.map Protocol.Capability.root = bindings.roots := bindings.bound_roots

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (accepts definition) "serialized definition forms symbolic and bound bodies with its relation"
  checks.holds (accepts definition ⟨[1, 0], by decide⟩) "definition ports and capability permissions share non-monotone role mapping"
  checks.holds (!(accepts definition ⟨[0], by decide⟩)) "definition rejects the wrong positional role arity"
  checks.holds (!(accepts { definition with arguments := [⟨[⟨1⟩, ⟨0⟩], vectorUse⟩, ⟨[⟨1⟩], booleanUse⟩] }))
    "definition rejects noncanonical local availability before mapping"
  checks.holds (!(accepts { definition with relations := [{ relation with publicInputs := [⟨1⟩] }] }))
    "relation operand type must match its selected public signature"
  checks.holds (!(accepts { definition with relations := [{ relation with witnessInputs := [⟨2⟩] }] }))
    "relation operands cannot select body-local or nonexistent values"
  checks.holds (!(accepts { definition with relations := [{ relation with witnessInputs := [] }] }))
    "relation operand arity is exact"
  checks.holds (!(accepts { definition with relations := [{ relation with relation := ⟨1⟩ }] }))
    "relation binding cannot select an absent declaration"
  checks.holds (!(accepts { definition with relations := [{ relation with statics := [.literal 4] }] }))
    "relation binding substitutes its own exact static actuals"
  checks.holds (!(accepts { definition with capabilities := [{ permission with roles := [⟨1⟩] }] }))
    "body cannot use a capability outside its declared permission"
  checks.holds (!(accepts { definition with capabilities := [{ permission with roles := [⟨2⟩] }] }))
    "capability permission role must be in the definition scope"
  checks.holds (!(accepts definition roles [2])) "bound capability reference must select the actual root table"
  checks.holds (!(accepts definition roles [])) "bound capability arity is exact"
  checks.holds (accepts paired roles [0, 1]) "identical root signatures retain distinct authored root identities"
  checks.holds (!(accepts paired roles [0, 0])) "closed local distinctness sees aliased actual root identities"
  checks.holds (accepts { paired with body := (.mk
    [.local 0 ⟨0⟩ ⟨2⟩ [.parameter 0] (.object []) [⟨0⟩, ⟨0⟩] [⟨0⟩]] (.ret [⟨0⟩])) } roles [] false)
    "symbolic template retains root requirements without pretending to discharge them"
  checks.holds (!(accepts { definition with body := .mk [] (.ret [⟨1⟩]) }))
    "result permission cannot be widened by a definition annotation"
  checks.holds (!(accepts { definition with results := [⟨[⟨0⟩], vectorUse⟩] }))
    "body result must match the instantiated result signature"
  checks.finish "mathematical definition admission"

#eval run
end Tests.MathematicalDefinitions
