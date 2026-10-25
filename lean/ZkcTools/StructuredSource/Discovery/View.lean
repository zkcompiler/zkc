module

public import ZkcTools.StructuredSource.Discovery.Address

@[expose] public section

/-! A bounded query over real admitted Region trees, with a separately materialized
search visibility boundary. There is no evaluator here. The proposer receives
only View, not Program, and therefore cannot inspect a hidden producer closure.
Dependency edges are conservative search hints, never independence proofs. -/

namespace ZkcTools.StructuredSource.Discovery
open Zkc.Source Zkc.Source.Structured

inductive Arm where
  | manual | verifier | joint
  deriving DecidableEq, Repr

structure Value where
  address : Address
  type : Ty
  scopes : List Nat
  dependencies : List Address
  unknownDependencies : Bool := false
  deriving Repr

structure Node where
  address : Address
  context : List Address := []
  selectedRole : Nat := 0
  tag : String
  calculation : Option Op := none
  helper : Option String := none
  arguments : List Value := []
  operandPositions : List Nat := []
  results : List Value := []
  roleMap : List Nat := []
  privateResults : List Nat := []

structure Cut where
  receive : Address
  type : Ty
  sender : Nat
  receiver : Nat
  /-- Present only in joint/manual views; never an adversarial equality. -/
  honestSource : Option Address := none
  deriving Repr

structure View where
  snapshot : String
  entry : String
  arm : Arm
  role : Nat
  nodes : List Node := []
  cuts : List Cut := []
  inputs : List Value := []
  relations : List Relation := []
  contracts : List ProtocolContract := []
  helperBodies : List CheckedDefinition := []
  steps : Nat := 0

structure Work where
  view : View
  remaining : Nat

abbrev Query := StateT Work (Except String)

def spend : Query Unit := do
  let state ← get
  if state.remaining == 0 then throw "discovery-timeout"
  set { state with     remaining := state.remaining - 1, view := { state.view with steps := state.view.steps + 1 } }

def allowed (arm : Arm) (role : Nat) (scopes : List Nat) : Bool :=
  arm != .verifier || scopes.contains role

def addressAt (snapshot definition : String) (path : List Nat) (coordinate : Coordinate) : Address :=
  ⟨snapshot, definition, path, coordinate⟩

def lookupValues (environment : List Value) (indices : List Nat) : Query (List Value) :=
  indices.mapM fun index => do
    spend
    match environment[index]? with
    | some value => pure value
    | none => throw "discovery-operand"

def recordNode (node : Node) : Query Unit :=
  modify fun state => { state with view := { state.view with nodes := node :: state.view.nodes } }

def dependencyUnion (arguments : List Value) : List Address :=
  (arguments.flatMap (·.dependencies)).eraseDups

def outputValues (address : Address) (types : List Ty) (scopes : List (List Nat))
    (arguments : List Value) : List Value :=
  (types.zipIdx).map fun (ty, index) =>
    let origin := { address with coordinate := .result index }
    ⟨origin, ty, scopes[index]?.getD [], dependencyUnion arguments, false⟩

/-- Only the exact accessible helper closure is exported to search. -/
def addHelper (program : Program) : Nat → String → Query Unit
  | 0, _ => throw "discovery-helper-depth"
  | fuel + 1, name => do
    spend
    let state ← get
    if state.view.helperBodies.any (·.name == name) then return
    let some body := program.payload.definitions.find? (·.name == name)
      | throw "discovery-unknown-helper"
    modify fun state => { state with view :=       { state.view with helperBodies := body :: state.view.helperBodies } }
    for dependency in body.dependencies do
      addHelper program fuel dependency

def calcTag : Op → String
  | .fieldAdd _ => "add" | .fieldSubtract _ => "subtract"
  | .fieldMultiply _ => "multiply" | .fieldEqual _ => "equal"
  | .fold _ => "fold" | .map _ => "map" | .invoke _ => "helper"
  | .exec (.vectorSum _) => "vector-sum" | .exec (.vectorSplit _) => "vector-split"
  | .exec _ => "primitive" | .guard => "guard" | _ => "calculation"

/-- Scope computation reuses admission's existing operation-specific transfer. -/
def scopesFor (summaries : List DependencySummary) (roster : List String)
    (active : List Nat) (op : ProtocolOp) (arguments : List Value) : Query (List (List Nat)) := do
  match (Availability.operation summaries roster op (arguments.map (·.scopes)) active).run {} with
  | .ok (scopes, _) => pure scopes
  | .error error => throw error

mutual
  partial def visitRegion (program : Program) (summaries : List DependencySummary)
      (fuel : Nat) (definition : String) (roster : List String) (selectedRole : Nat)
      (active : List Nat) (context : List Address) (path : List Nat)
      (environment : List Value) (body : RawRegion Ty ProtocolOp) : Query (List Value) := do
    spend
    let arm := (← get).view.arm
    let snapshot := (← get).view.snapshot
    match body with
    | .ret indices => lookupValues environment indices
    | .stop _ =>
      recordNode { address := addressAt snapshot definition path .instruction,         context, tag := "stop" }
      pure []
    | .bind _ body next =>
      let values ← visitRegion program summaries fuel definition roster selectedRole active context
        (path ++ [0]) environment body
      visitRegion program summaries fuel definition roster selectedRole active context
        (path ++ [1]) (values ++ environment) next
    | .letOp op indices types bodies next =>
      let address := addressAt snapshot definition path .instruction
      let arguments ← lookupValues environment indices
      let visibleArguments := arguments.filter fun value => allowed arm selectedRole value.scopes
      let resultScopes ← match op with
        | .repeat spec _ => pure spec.stateScopes
        | _ => scopesFor summaries roster active op arguments
      let values := (outputValues address types resultScopes visibleArguments).map fun value =>
        { value with unknownDependencies := visibleArguments.length != arguments.length ||           visibleArguments.any (·.unknownDependencies) }
      let visibleResults := values.filter fun value => allowed arm selectedRole value.scopes
      let privateResults := (resultScopes.zipIdx).filterMap fun (scopes, index) =>
        if scopes.contains selectedRole then none else some index
      let mut node : Node := { address, context, selectedRole, tag := "", arguments := visibleArguments,         results := visibleResults, privateResults,         operandPositions := (arguments.zipIdx).filterMap fun (value, i) =>           if allowed arm selectedRole value.scopes then some i else none }
      let visible := !visibleResults.isEmpty || match op with
        | .guard owner _ => arm != .verifier || owner == selectedRole
        | .statement .. | .mark .. | .repeat .. | .protocolApply .. => true
        | _ => false
      let mut outgoing := values
      match op with
      | .calculate calculation _ =>
        node := { node with tag := calcTag calculation, calculation := some calculation }
        if visible then
          for helper in calculation.helpers do addHelper program 32 helper.name
      | .localCall helper _ owner _ =>
        node := { node with tag := "local-helper", helper := some helper.name }
        if arm != .verifier || owner == selectedRole then addHelper program 32 helper.name
      | .guard _ _ => node := { node with tag := "guard" }
      | .exchange ty sender receiver _ =>
        let origin := { address with coordinate := .result 0 }
        -- The received value is independent even in the joint view.
        outgoing := [⟨origin, ty, [sender, receiver], [origin], false⟩]
        node := { node with tag := "receive", roleMap := [sender, receiver], arguments := [], operandPositions := [],           results := outgoing.filter fun value => allowed arm selectedRole value.scopes }
        if arm != .verifier || receiver == selectedRole then
          modify fun state => { state with view := { state.view with cuts :=             { receive := origin, type := ty, sender, receiver,               honestSource := if arm == .verifier then none else arguments.head?.map (·.address) } ::                 state.view.cuts } }
      | .restrict _ _ => node := { node with tag := "restrict-scope" }
      | .draw _ _ _ =>
        outgoing := values.map fun value => { value with dependencies := [value.address] }
        node := { node with tag := "draw", results := outgoing.filter fun value =>           allowed arm selectedRole value.scopes }
      | .statement .. => node := { node with tag := "statement" }
      | .mark _ => node := { node with tag := "mark" }
      | .protocolApply signature roles _ =>
        node := { node with tag := "call", helper := some signature.name, roleMap := roles }
        match fuel with
        | 0 => throw "discovery-call-depth"
        | fuel + 1 =>
          let some callee := program.payload.protocols.find? (·.name == signature.name)
            | throw "discovery-unknown-callee"
          let localRole := roles.findIdx (· == selectedRole)
          -- Port substitution uses actual operands; addresses remain static.
          let calleeInputs := arguments.zipWith (fun value scopes =>
            { value with scopes }) signature.inputScopes
          let _ ← visitRegion program summaries fuel callee.name callee.roles localRole
            (List.range callee.roles.length) (context ++ [address]) [] calleeInputs callee.raw
      | .repeat spec _ =>
        node := { node with tag := "repeat", roleMap := spec.roles }
        let callbackScopes ← match
            (Availability.repeatInputs roster.length spec (arguments.map (·.scopes))).run {} with
          | .ok (scopes, _) => pure scopes
          | .error error => throw error
        let _ ← visitCallbacks program summaries fuel definition roster selectedRole spec.roles
          context path 0 callbackScopes bodies
      if visible then recordNode node
      visitRegion program summaries fuel definition roster selectedRole active context
        (path ++ [1]) (outgoing ++ environment) next

  partial def visitCallbacks (program : Program) (summaries : List DependencySummary)
      (fuel : Nat) (definition : String) (roster : List String) (selectedRole : Nat)
      (active : List Nat) (context : List Address) (path : List Nat) (index : Nat)
      (scopes : List (List Nat)) (bodies : RawRegions Ty ProtocolOp) : Query Unit := do
    match bodies with
    | .nil => pure ()
    | .cons inputs _ body tail =>
      let callbackPath := path ++ [2, index]
      let values := (inputs.zipIdx).map fun (ty, i) =>
        let origin := addressAt program.snapshot.source definition callbackPath (.input i)
        (⟨origin, ty, scopes[i]?.getD [], [origin], false⟩ : Value)
      let _ ← visitRegion program summaries fuel definition roster selectedRole active context
        callbackPath values body
      visitCallbacks program summaries fuel definition roster selectedRole active context path
        (index + 1) scopes tail
end

/-- The only Program-consuming entry point. Search itself consumes the returned
View. Relations and target clauses are copied, never inferred from a candidate. -/
def buildView (program : Program) (arm : Arm) (role : Nat) (steps : Nat := 20000) :
    Except String View := do
  let summaries ← summarizeHelpers program.payload.definitions
  let root := program.payload.entry
  if role >= root.roles.length then throw "discovery-role"
  let inputs := (root.inputs.zipIdx).map fun (ty, i) =>
    let origin := addressAt program.snapshot.source root.name [] (.input i)
    (⟨origin, ty, root.inputScopes[i]?.getD [], [origin], false⟩ : Value)
  let initial : Work := { remaining := steps, view :=     { snapshot := program.snapshot.source, entry := root.name, arm, role,       inputs := inputs.filter fun value => allowed arm role value.scopes,       relations := program.snapshot.relations, contracts := program.snapshot.contracts } }
  let computation : Query Unit := do
    for relation in program.snapshot.relations do
      if let some helper := relation.formula then addHelper program 32 helper
    let _ ← visitRegion program summaries 32 root.name root.roles role
      (List.range root.roles.length) [] [] inputs root.raw
  let (_, state) ← computation.run initial
  return { state.view with nodes := state.view.nodes.reverse, cuts := state.view.cuts.reverse,     helperBodies := state.view.helperBodies.reverse }

end ZkcTools.StructuredSource.Discovery
