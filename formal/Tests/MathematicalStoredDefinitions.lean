import Zkc.Source.Mathematical.DataBounds
import Zkc.Source.Mathematical.StoredDefinitions
import Tests.MathematicalProtocolMeaning
import Tests.Checks

set_option autoImplicit false
namespace Tests.MathematicalStoredDefinitions
open Zkc.Source Zkc.Source.Mathematical
open MathematicalGraph (number publicPort privatePort)
open MathematicalProtocol (vocabulary capabilities cap)
open MathematicalProtocolMeaning (meaning execute Event)

def helper : Protocol.Target Nat vocabulary :=
  ⟨[0, 1], [cap .counter [0] 7], [privatePort], [privatePort]⟩

def rootTable : List (Protocol.Capability Nat vocabulary.Service) :=
  [cap .counter [0] 0, cap .counter [0] 1, cap .counter [0] 2, cap .counter [0] 3,
   cap .counter [0] 4, cap .counter [0] 5, cap .counter [0] 6, cap .counter [0] 7,
   cap .counter [0, 1] 8, cap .other [0] 9]

theorem tableValid : Protocol.RootTable rootTable := rfl

theorem helperRooted : Protocol.Rooted rootTable helper.capabilities := by
  intro capability reference
  cases reference with
  | here => simp [Protocol.RootedIn, rootTable]
  | there reference => cases reference

def helpers : Except Protocol.Error (Protocol.Definitions rootTable [helper]) := do
  let checked ← Protocol.decode [0, 1] helper.capabilities [] Data.capacity
    MathematicalGraph.countValid 64 helper.arguments helper.results 0
    (.query 0 0 0 [0] (.message 1 ⟨number, ()⟩ 0 1 0 (.ret [1])))
  if valid : checked.program.callsMatch (Protocol.targetRoots (targets := [])) = true then
    return .snoc .nil helper checked.program helperRooted checked.roots valid
  else throw .alias

def caller (secondRoot : Nat) : Protocol.Raw Nat vocabulary :=
  .invoke 0 0 [0] [0] (.invoke 1 0 [secondRoot] [0]
    (.message 2 ⟨number, ()⟩ 0 1 0 (.ret [0])))

def runCaller (raw : Protocol.Raw Nat vocabulary) : Except String (Nat × Nat × List Event) := do
  let stored ← helpers.mapError (fun _ => "helper")
  let checked ← (Protocol.decode [0, 1] capabilities [helper.signature] Data.capacity
    MathematicalGraph.countValid 64 [privatePort] [publicPort] 0 raw).mapError (fun _ => "type")
  if valid : checked.program.callsMatch (Protocol.targetRoots (targets := [helper])) = true then
    let inputs : Values (Component meaning.Value 0) [privatePort] := .cons (fun _ => 9) .nil
    have callProof : checked.program.CallsSatisfy
        (fun callee bindings => bindings.roots = Protocol.targetRoots (targets := [helper]) callee) :=
      (Protocol.Program.callsMatch_iff (Protocol.targetRoots (targets := [helper])) checked.program).mp valid
    let process := checked.program.denoteChecked meaning 0 (stored.denote meaning 0) [] callProof (fun ref => inputs.get ref)
    let (values, state, trace) ← execute 64 process (fun _ => 0)
    return (values.get .here (by decide), state 7, trace)
  else throw "root-closure"

def closedHelper (roots : List Nat) : Except Protocol.Error (Protocol.Closed rootTable) := do
  let stored ← helpers
  let selected ← (Protocol.entry rootTable [helper] 0 roots).run' 64
  return ⟨tableValid, [helper], stored, 0, roots, selected⟩

def runEntry : Except String (Nat × Nat × List Event) := do
  let closed ← (closedHelper [7]).mapError (fun _ => "entry")
  -- The entry signature is selected by admission, so inputs use that actual
  -- signature. This test requires the specific one-argument/result shape.
  if inputsEqual : closed.entry.signature.arguments = [privatePort] then
    if outputsEqual : closed.entry.signature.results = [privatePort] then
      let inputs : Values (Component meaning.Value 0) closed.entry.signature.arguments :=
        inputsEqual ▸ (.cons (fun _ => 9) .nil)
      let (values, state, trace) ← execute 64 (closed.denote meaning 0 inputs) (fun _ => 0)
      let output : Values (Component meaning.Value 0) [privatePort] := outputsEqual ▸ values
      return (output.get .here (by decide), state 7, trace)
    else throw "signature"
  else throw "signature"

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (match runCaller (caller 1) with
    | .ok (1, 2, [⟨⟨[.invocation 0], 0⟩, some 7⟩, ⟨⟨[.invocation 0], 1⟩, none⟩,
        ⟨⟨[.invocation 1], 0⟩, some 7⟩, ⟨⟨[.invocation 1], 1⟩, none⟩, ⟨⟨[], 2⟩, none⟩]) => true
    | _ => false) "stored helper keeps root aliases and invocation paths"
  checks.holds (match runCaller (caller 2) with
    | .error "root-closure" => true | _ => false) "same service with a different root is a different target"
  checks.holds (match runCaller (.repeat 0 0 [privatePort] [0] []
    (.invoke 1 0 [2] [1] (.ret [0])) (.message 2 ⟨number, ()⟩ 0 1 0 (.ret [0]))) with
    | .error "root-closure" => true | _ => false) "dormant calls still check stored roots"
  checks.holds (match runEntry with
    | .ok (0, 1, [⟨⟨[], 0⟩, some 7⟩, ⟨⟨[], 1⟩, none⟩]) => true
    | _ => false) "admitted entry executes with its certified table root"
  checks.holds (match closedHelper [8] with
    | .error .alias => true | _ => false) "entry cannot substitute another root with compatible permissions"
  checks.holds (match closedHelper [9] with
    | .error .service => true | _ => false) "entry rejects a different service"
  checks.holds (match closedHelper [] with
    | .error (.graph .arity) => true | _ => false) "entry capability arity is exact"
  checks.holds (match closedHelper [10] with
    | .error (.graph .scope) => true | _ => false) "entry root must exist in actual table"
  checks.holds (match (Protocol.entry rootTable [helper] 1 [7]).run' 64 with
    | .error (.graph .scope) => true | _ => false) "entry target must exist in stored table"
  checks.holds (match (Protocol.entry rootTable [helper] 0 [7]).run' 1 with
    | .error .resource => true | _ => false) "entry lookup spends shared resource allowance"
  checks.finish "mathematical stored definitions"

#eval run
end Tests.MathematicalStoredDefinitions
