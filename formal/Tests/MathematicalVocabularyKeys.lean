import Zkc.Source.Mathematical.RegisteredVocabulary
import Tests.MathematicalDeclarations
import Tools.Mathematical.Codec

set_option autoImplicit false
namespace Tests.MathematicalVocabularyKeys
open Zkc.Source.Mathematical

def parameters := DeclarationAdmission.parameters 1

def compareOperations (left right : Static.Raw) (leftIndex : Nat := 1) (rightIndex : Nat := 1)
    (leftAttributes : Raw.Attribute := .object []) (rightAttributes : Raw.Attribute := .object []) : Except String Bool :=
  (show StateT Nat (Except String) Bool from do
    let contracts := { MathematicalDeclarations.contracts with attributes := fun _ _ _ _ => true }
    let source := { MathematicalDeclarations.subject with module.operations :=
      MathematicalDeclarations.module.operations ++ [MathematicalDeclarations.module.operations[1]] }
    let header ← fun remaining => (DeclarationAdmission.admit contracts source remaining)
      |>.mapError (fun error => toString (repr error))
    let left ← RegisteredVocabulary.operation header parameters ⟨⟨leftIndex⟩, [left], leftAttributes⟩
    let right ← RegisteredVocabulary.operation header parameters ⟨⟨rightIndex⟩, [right], rightAttributes⟩
    return decide (left.val = right.val)).run' 1000000

def compareWires (left right : Static.Raw) (leftIndex : Nat := 0) (rightIndex : Nat := 0) : Except String Bool :=
  (show StateT Nat (Except String) Bool from do
    let source := { MathematicalDeclarations.subject with module.wires := MathematicalDeclarations.module.wires ++ MathematicalDeclarations.module.wires }
    let header ← fun remaining => (DeclarationAdmission.admit MathematicalDeclarations.contracts source remaining)
      |>.mapError (fun error => toString (repr error))
    let left ← RegisteredVocabulary.wire header parameters ⟨⟨leftIndex⟩, [left]⟩
    let right ← RegisteredVocabulary.wire header parameters ⟨⟨rightIndex⟩, [right]⟩
    return decide (left.val = right.val)).run' 1000000

def compareEncodedAttributes (left right : Raw.Attribute) : Except String Bool := do
  let left ← Tools.Mathematical.Codec.decode (← Tools.Mathematical.Codec.encode left)
  let right ← Tools.Mathematical.Codec.decode (← Tools.Mathematical.Codec.encode right)
  compareOperations (.parameter 0) (.parameter 0) 1 1 left right

def result (expected : Bool) (actual : Except String Bool) : Bool :=
  match actual with | .ok value => value == expected | .error _ => false

-- No interpreter of admitted operation objects can distinguish two admission
-- paths or authored static spellings once their normalized keys agree.
example {Payload contracts source} (header : DeclarationAdmission.Header (Payload := Payload) contracts source)
    {target α} (interpret : RegisteredVocabulary.Operation header target → α)
    {first second : RegisteredVocabulary.Operation header target} (same : first.val = second.val) :
    interpret first = interpret second := congrArg interpret (RegisteredVocabulary.operation_ext header target same)

example {Payload contracts source} (header : DeclarationAdmission.Header (Payload := Payload) contracts source)
    {target α} (interpret : RegisteredVocabulary.Wire header target → α)
    {first second : RegisteredVocabulary.Wire header target} (same : first.val = second.val) :
    interpret first = interpret second := congrArg interpret (RegisteredVocabulary.wire_ext header target same)

def run : IO Unit := do
  let checks ← Checks.start
  let p := Static.Raw.parameter 0
  checks.holds (result true (compareOperations (.add p (.literal 1)) (.add (.literal 1) p)))
    "commuted symbolic actuals yield equal admitted operations"
  checks.holds (result true (compareOperations (.multiply p (.literal 2)) (.add p p)))
    "algebraically normalized actuals yield equal admitted operations"
  checks.holds (result false (compareOperations p (.add p (.literal 1))))
    "different normalized static values remain different operation keys"
  checks.holds (result false (compareOperations p p 1 3))
    "distinct authored operation declarations retain separate keys"
  let nested := Raw.Attribute.object [("a", .array [.natural 3, .object [("flag", .boolean true)]])]
  checks.holds (result true (compareOperations p p 1 1 nested nested)) "equal nested opaque attributes compare structurally"
  checks.holds (result false (compareOperations p p 1 1 (.object [("a", .natural 3)]) (.object [("a", .string "3")])))
    "attribute tag differences remain part of operation identity"
  checks.holds (result false (compareOperations p p 1 1 (.object [("a", .natural 3)]) (.object [("b", .natural 3)])))
    "attribute field names remain part of operation identity"
  checks.holds (result true (compareWires (.add p (.literal 1)) (.add (.literal 1) p)))
    "commuted static actuals yield equal admitted wires"
  checks.holds (result true (compareWires (.multiply p (.literal 2)) (.add p p)))
    "normalized polynomial actuals yield equal admitted wires"
  checks.holds (result false (compareWires p (.add p (.literal 1))))
    "different payload dimensions remain different wire keys"
  let sorted := Raw.Attribute.object [("a", .natural 1), ("b", .natural 2)]
  let reversed := Raw.Attribute.object [("b", .natural 2), ("a", .natural 1)]
  checks.holds (result true (compareEncodedAttributes sorted reversed))
    "canonical serialized field order gives equal operational keys"
  checks.holds (!(compareOperations p p 1 1 reversed sorted).isOk)
    "direct raw attribute objects must already have canonical field order"
  checks.holds (!(compareOperations p p 1 1 (.object [("a", .natural 1), ("a", .natural 2)]) sorted).isOk)
    "direct raw attribute objects cannot contain duplicate keys"
  checks.holds (!(compareOperations p p 1 1 (.array [reversed]) (.array [sorted])).isOk)
    "canonicality applies recursively to nested attributes"
  checks.holds (!(compareOperations p p 1 1 (.natural Static.limit) (.natural Static.limit)).isOk)
    "opaque attribute naturals retain the carrier word bound"
  let unicode := Raw.Attribute.object [("z", .boolean true), ("é", .boolean false)]
  checks.holds (result true (compareOperations p p 1 1 unicode unicode))
    "non-ASCII object keys follow unsigned UTF-8 order"
  checks.holds (!(compareOperations p p 1 1 (.object [("é", .boolean false), ("z", .boolean true)]) unicode).isOk)
    "reversed non-ASCII field order is rejected"
  checks.holds (match (AttributeAdmission.charge "resource" 65 (.string "abc")).run' 3 with
    | .error "resource" => true | _ => false) "attribute bytes are charged before registry callbacks"
  checks.holds (result false (compareWires p p 0 1)) "distinct authored wire declarations retain separate keys"
  checks.finish "mathematical vocabulary keys"

#eval run
end Tests.MathematicalVocabularyKeys
