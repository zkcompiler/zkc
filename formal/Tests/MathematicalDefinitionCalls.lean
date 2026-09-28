import Zkc.Source.Mathematical.DefinitionCalls
import Tests.MathematicalDefinitions

set_option autoImplicit false
namespace Tests.MathematicalDefinitionCalls
open Zkc.Source.Mathematical
open MathematicalDefinitions (definition)

def call (callee : Nat := 0) (statics : List Static.Raw := [.parameter 0])
    (roles : List (Raw.Reference .role) := [⟨0⟩, ⟨1⟩]) : Raw.Step :=
  .invoke 0 ⟨callee⟩ statics roles [⟨0⟩] [⟨0⟩, ⟨1⟩]

def caller : Raw.Definition := { definition with body := .mk [call] (.ret [⟨0⟩]) }

def check (definitions : List Raw.Definition) (budget : Nat := 1000000) : Except String Bool := do
  let source := { MathematicalDefinitions.source definition with module.definitions := definitions }
  let bytes ← Tools.Mathematical.Codec.encode (← Tools.Mathematical.SchemaEncoding.encode source)
  let raw ← Tools.Mathematical.Schema.decode (← Tools.Mathematical.Codec.decode bytes)
  (show StateT Nat (Except String) Bool from do
    let header ← fun remaining => (DeclarationAdmission.admit MathematicalDeclarations.contracts raw remaining)
      |>.mapError (fun error => toString (repr error))
    let _ ← fun remaining => (DefinitionCalls.declarations header remaining)
      |>.mapError (fun error => toString (repr error))
    return true).run' budget

def accepts (definitions : List Raw.Definition) : Bool := (check definitions).isOk

def withCall (step : Raw.Step) : Raw.Definition := { caller with body := .mk [step] (.ret [⟨0⟩]) }

def repeated (count : Nat) : Raw.Definition := { caller with body := (.mk
  [.repeat 0 (.literal count) [] [] [⟨0⟩, ⟨1⟩] (.mk
    [.invoke 1 ⟨0⟩ [.parameter 0] [⟨0⟩, ⟨1⟩] [⟨0⟩] [⟨1⟩, ⟨2⟩]] (.ret [])),
   .invoke 2 ⟨0⟩ [.parameter 0] [⟨0⟩, ⟨1⟩] [⟨0⟩] [⟨0⟩, ⟨1⟩]] (.ret [⟨0⟩])) }

-- The call resolver's successful certificate is tied to both the authored
-- earlier declaration and the actual signature in the intrinsic call scope.
example {Payload contracts source} (header : DeclarationAdmission.Header (Payload := Payload) contracts source)
    {arity target parameters roles before}
    {entries : List (DefinitionCalls.Entry header (arity := arity) (target := target) parameters roles before)}
    {raw index} (selected : (DefinitionCalls.resolver entries).Valid raw index) : raw.definition.index < before := by
  obtain ⟨_, _, _, earlier⟩ := DefinitionCalls.selected_signature selected
  exact earlier

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (accepts [definition, caller]) "serialized calls select and instantiate actual earlier definitions"
  checks.holds (accepts [definition, caller, { caller with body := .mk [call 1] (.ret [⟨0⟩]) }])
    "three-definition acyclic chain forms all bodies"
  checks.holds (accepts [definition, repeated 0]) "zero repeat retains a well-formed earlier call"
  checks.holds (accepts [definition, repeated 1000000000]) "large repeat checks call syntax without expanding iterations"
  checks.holds (!(accepts [definition, withCall (call 1)])) "self call rejected at actual caller index"
  checks.holds (!(accepts [withCall (call 1), definition])) "forward call rejected even with a valid target signature"
  checks.holds (!(accepts [definition, withCall (call 2)])) "absent callee rejected"
  checks.holds (!(accepts [definition, withCall (call 0 [])])) "callee static arity belongs to selected definition"
  checks.holds (!(accepts [definition, withCall (call 0 [.parameter 1])])) "call static parameters stay in caller scope"
  checks.holds (!(accepts [definition, withCall (call 0 [.literal 4])])) "callee substitution must agree with caller arguments and service"
  checks.holds (!(accepts [definition, withCall (call 0 [.parameter 0] [⟨0⟩])])) "callee role arity is exact"
  checks.holds (!(accepts [definition, withCall (call 0 [.parameter 0] [⟨0⟩, ⟨0⟩])])) "callee roles must remain injective"
  checks.holds (!(accepts [definition, withCall (call 0 [.parameter 0] [⟨0⟩, ⟨2⟩])])) "callee role cannot escape caller scope"
  checks.holds (!(accepts [definition, withCall (.invoke 0 ⟨0⟩ [.parameter 0] [⟨0⟩, ⟨1⟩] [] [⟨0⟩, ⟨1⟩])]))
    "callee capability arity checked against actual signature"
  checks.holds (!(accepts [definition, withCall (.invoke 0 ⟨0⟩ [.parameter 0] [⟨0⟩, ⟨1⟩] [⟨0⟩] [⟨1⟩, ⟨0⟩])]))
    "callee operand order and types checked against selected signature"
  checks.holds (!(accepts [definition, caller, { definition with body := .mk [.guard 0 ⟨0⟩ ⟨0⟩] (.ret [⟨1⟩]) }]))
    "unused malformed definition still undergoes intrinsic body formation"
  checks.holds (!(accepts [definition, { caller with body := (.mk
    [.repeat 0 (.literal 0) [] [] [] (.mk [.invoke 1 ⟨1⟩ [.parameter 0] [⟨0⟩, ⟨1⟩] [⟨0⟩] []] (.ret []))]
    (.ret [⟨1⟩])) }])) "zero repeat cannot hide a self call"
  checks.holds (!(check [definition, caller] 1).isOk) "shared declaration allowance refuses before unchecked construction"
  checks.finish "mathematical source call selection"

#eval run
end Tests.MathematicalDefinitionCalls
