import Zkc.Source.Mathematical.ClosedInstances
import Tests.MathematicalDefinitions

set_option autoImplicit false
namespace Tests.MathematicalClosedInstances
open Zkc.Source.Mathematical ClosedInstances

def leaf : Raw.Definition := ⟨1, 2, [], [], [], [], .mk [] (.ret [])⟩

def invoke (site definition : Nat) (statics : List Static.Raw := [.parameter 0])
    (roles : List Nat := [0, 1]) (roots : List Nat := []) : Raw.Step :=
  .invoke site ⟨definition⟩ statics (roles.map Raw.Reference.mk) (roots.map Raw.Reference.mk) []

def caller (steps : List Raw.Step) : Raw.Definition := { leaf with body := .mk steps (.ret []) }

def subject (definitions : List Raw.Definition) (roots : List Nat := []) (statics : List Nat := [3]) : Raw.Subject :=
  { MathematicalDefinitions.source leaf with module.definitions := definitions, module.entry := ⟨⟨definitions.length - 1⟩, statics, [⟨0⟩, ⟨1⟩], roots.map Raw.Reference.mk⟩ }

def check (source : Raw.Subject) (budget : Nat := 1000000) : Except String (List Key) := do
  let bytes ← Tools.Mathematical.Codec.encode (← Tools.Mathematical.SchemaEncoding.encode source)
  let raw ← Tools.Mathematical.Schema.decode (← Tools.Mathematical.Codec.decode bytes)
  let graph ← (discover raw).run' budget |>.mapError (fun error => toString (repr error))
  return keys graph.nodes

def accepts (source : Raw.Subject) : Bool := (check source).isOk

def order (source : Raw.Subject) : Except String (List Nat) :=
  (check source).map (List.map Key.definition)

def diamond : Raw.Subject := subject [leaf, caller [invoke 0 0], caller [invoke 0 0], caller [invoke 0 1, invoke 1 2]]

def repeated (count : Nat) : Raw.Subject := subject [leaf, caller
  [.repeat 0 (.literal count) [] [] [] (.mk [invoke 1 0] (.ret [])), invoke 2 0]]

def capabilityLeaf : Raw.Definition := { leaf with capabilities := [MathematicalDefinitions.permission] }

def rooted (roots : List Nat) : Raw.Subject := subject [capabilityLeaf,
  { caller [invoke 0 0 [.parameter 0] [0, 1] [0], invoke 1 0 [.parameter 0] [0, 1] [1]] with
    capabilities := [MathematicalDefinitions.permission, MathematicalDefinitions.permission] }] roots

def rootTuples (source : Raw.Subject) : Except String (List (List Nat)) :=
  (check source).map (List.map Key.roots)

def sameSignature : Raw.Subject := subject [leaf, { leaf with body := .mk [] (.stop 0 ⟨0⟩ .reject) }, caller [invoke 0 0]]

def substitutedBody : Except Error Unit := do
  let source := sameSignature
  let result ← (show Admission (Graph source) from do
    let entry ← node source (entryKey source)
    let wrongKey : Key := ⟨1, [3], [0, 1], []⟩
    let wrong ← node source wrongKey
    certify source [⟨entryKey source, entry⟩, ⟨wrongKey, wrong⟩]).run' 1000000
  pure (let _ := result; ())

-- The target definition is the exact authored call index. Equal signatures
-- cannot replace this provenance with another body.
example {source key} {parent : Instance source key} {site} (edge : Call parent site) :
    edge.target.definition = site.use.definition.index := edge.exactDefinition

example {source key} (checked : Instance source key) :
    source.module.definitions[key.definition]? = some checked.declaration.value := checked.declaration.selected

example {source key} {parent : Instance source key} {site} (edge : Call parent site) :
    edge.target.definition < key.definition := by rw [edge.exactDefinition]; exact edge.earlier

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds ((order diamond).toOption == some [3, 1, 0, 2]) "DFS IDs preserve source order and reuse the diamond's shared leaf"
  checks.holds ((order (repeated 0)).toOption == some [1, 0]) "zero repeat retains its call in syntactic closure"
  checks.holds ((order (repeated 1000000000)).toOption == some [1, 0]) "billion repeat discovers one body without expansion"
  checks.holds ((rootTuples (rooted [0, 0])).toOption == some [[0, 0], [0]]) "aliased caller ports reuse one closed instance"
  checks.holds ((rootTuples (rooted [0, 1])).toOption == some [[0, 1], [0], [1]]) "different actual roots require different instances"
  checks.holds (match check (subject [leaf, caller [invoke 0 0 [.add (.literal 1) (.literal 2)], invoke 1 0 [.literal 3]]]) with
    | .ok [_, child] => child.statics == [3] | _ => false) "equal evaluated static tuples reuse one instance"
  checks.holds (match check (subject [leaf, caller [invoke 0 0 [.literal 3], invoke 1 0 [.literal 4]]]) with
    | .ok [_, first, second] => first.statics == [3] && second.statics == [4] | _ => false)
    "different static tuples remain different even when absent from the signature"
  checks.holds (match check (subject [leaf, caller [invoke 0 0 [.parameter 0] [1, 0], invoke 1 0]]) with
    | .ok [_, first, second] => first.roles == [1, 0] && second.roles == [0, 1] | _ => false)
    "positional role tuples distinguish instances even when participant sets agree"
  checks.holds ((order (subject [leaf, { leaf with body := .mk [] (.stop 0 ⟨0⟩ .reject) }, caller [invoke 0 0, invoke 1 1]])).toOption == some [2, 0, 1])
    "two definitions with identical signatures retain distinct bodies"
  checks.holds (match substitutedBody with | .error .missing => true | _ => false)
    "certificate refuses replacing the called body with another body of the same signature"
  checks.holds (!(accepts (subject [leaf, caller [invoke 0 1]]))) "closed discovery refuses self calls"
  checks.holds (!(accepts (subject [caller [invoke 0 1], caller [invoke 0 0]]))) "closed discovery refuses forward calls"
  checks.holds (!(accepts (subject [leaf, caller [invoke 0 0 []]]))) "closed callee static arity is exact"
  checks.holds (!(accepts (subject [leaf, caller [invoke 0 0 [.parameter 1]]]))) "closed call cannot read another static scope"
  checks.holds (!(accepts (subject [leaf, caller [invoke 0 0 [.multiply (.literal 0) (.pow2 (.literal 64))]]])))
    "closed call checks intermediate overflow even when multiplied by zero"
  checks.holds (!(accepts (subject [leaf, caller [invoke 0 0 [.parameter 0] [0, 0]]]))) "call role binding stays injective"
  checks.holds (!(accepts (subject [leaf, caller [invoke 0 0 [.parameter 0] [0, 2]]]))) "call cannot introduce a foreign role"
  checks.holds (!(accepts (rooted [0, 2]))) "actual root must exist in header root table"
  checks.holds (!(accepts (subject [capabilityLeaf, caller [invoke 0 0 [.parameter 0] [0, 1] [0]]])))
    "call capability selection cannot escape caller ports"
  checks.holds (!(accepts (subject [leaf] [] [Static.limit]))) "entry static is within word bounds"
  checks.holds (!(accepts (subject [leaf] [] []))) "entry static arity belongs to its actual declaration"
  checks.holds (!(check diamond 1).isOk) "discovery shares a finite allowance"
  checks.holds (match ((do
    let graph ← discover diamond
    certify diamond (graph.nodes ++ graph.nodes) : Admission (Graph diamond)).run' 1000000) with
    | .error .duplicate => true | _ => false) "certificate refuses duplicate instance keys"
  checks.holds (match (certify diamond []).run' 1000000 with
    | .error .missing => true | _ => false) "certificate requires the exact entry instance"
  checks.holds (match ((do
    let graph ← discover diamond
    certify diamond graph.nodes.reverse : Admission (Graph diamond)).run' 1000000) with
    | .error .order => true | _ => false) "certificate refuses reordered native instance IDs"
  checks.holds (match ((do
    let graph ← discover sameSignature
    let key : Key := ⟨1, [3], [0, 1], []⟩
    let extra ← node sameSignature key
    certify sameSignature (graph.nodes ++ [⟨key, extra⟩]) : Admission (Graph sameSignature)).run' 1000000) with
    | .error .order => true | _ => false) "certificate refuses an extra unreachable instance"
  checks.finish "mathematical closed instance discovery"

#eval run
end Tests.MathematicalClosedInstances
