import Zkc.Source.Mathematical.BlsAdmission
import Zkc.Source.Mathematical.PlacementView

/-! Independent role demand over a certified, closed mathematical body.

Vertex IDs are local checker indices. Source addresses are retained only for
checking witness correspondence. Each receive creates a new vertex: only its
sender component depends on the sent operand. Query occurrences remain distinct.
-/

set_option autoImplicit false
namespace Tools.Mathematical.PlacementGraph
open Zkc.Source.Mathematical BlsInstallation

structure Address where
  regions : List Nat
  binding : Nat
  deriving BEq, DecidableEq, Hashable, Repr

structure Port where
  roles : List Nat
  type : LogicalType
  deriving Repr

structure Vertex where
  address : Address
  port : Port
  dependencies : List Nat
  dependencyRole : Option Nat := none
  deriving Repr

structure Node where
  declaration : Nat
  operation : Operation
  arguments : List Nat
  output : Nat
  deriving Repr

inductive Step where
  | pure (sourceStep : Nat) (captures : List Nat) (nodes : List Node) (outputs : List Nat)
  | query (site owner root output : Nat)
  | guard (site owner condition : Nat)
  | message (site wire sender receiver input output : Nat)
  deriving Repr

inductive Terminal where
  | ret (values : List Nat)
  | stop (site owner : Nat) (reason : PIR.Stop)

structure Body where
  key : ClosedInstances.Key
  parties : List Nat
  arguments : List Nat
  results : List Port
  vertices : Array Vertex
  steps : List Step
  terminal : Terminal

structure Work where
  vertices : Array Vertex := #[]
  remaining : Nat := 10000000

abbrev Check := StateT Work (Except String)

def ensure (ok : Bool) (code : String) : Check Unit :=
  if ok then pure () else throw code

def consume (amount : Nat := 1) : Check Unit := do
  let state ← get
  ensure (amount ≤ state.remaining) "math-placement-resource"
  set {state with remaining := state.remaining - amount}

def select {α : Type} (values : List α) (index : Nat) : Check α := do
  consume (1 + values.length)
  match values[index]? with
  | some value => return value
  | none => throw "math-placement-scope"

def vertex (index : Nat) : Check Vertex := do
  consume
  match (← get).vertices[index]? with
  | some value => return value
  | none => throw "math-placement-scope"

def add (address : Address) (port : Port) (dependencies : List Nat := [])
    (dependencyRole : Option Nat := none) : Check Nat := do
  consume (1 + dependencies.length + port.roles.length)
  let state ← get
  -- The downstream common carrier has finite structural limits as well.
  ensure (state.vertices.size < 32768) "math-placement-resource"
  set {state with vertices := state.vertices.push ⟨address, port, dependencies, dependencyRole⟩}
  return state.vertices.size

def classify (source : Raw.Subject) (shape : TypeExpansion.Shape source.manifest.domains.length 0) :
    Check LogicalType := do
  consume
  match BlsInstallation.classify source.manifest shape with
  | some type => return type
  | none => throw "math-placement-type-subset"

variable {source : Raw.Subject}
  (header : DeclarationAdmission.Header BlsAdmission.installed source)

private def port (value : Zkc.Source.Mathematical.Port Nat (RegisteredVocabulary.vocabulary header 0).Ty) :
    Check Port := do return ⟨value.roles, ← classify source value.ty⟩

private def graph (parties : List Nat) (step : Nat) :
    Graph.Raw (RegisteredVocabulary.vocabulary header 0).Op (RegisteredVocabulary.vocabulary header 0).Count →
    Nat → List Nat → List Node → Check (List Node × List Nat)
  | .outputs outputs, _, context, nodes => do
      return (nodes.reverse, ← outputs.mapM (select context))
  | .operation operation inputs next, ordinal, context, nodes => do
      consume
      ensure (operation.val.val.signature.statics.isEmpty && operation.val.val.attributes == .object [])
        "math-placement-operation-subset"
      let arguments ← inputs.mapM (select context)
      let argumentsPorts ← arguments.mapM vertex
      consume (parties.length * (1 + argumentsPorts.foldl (fun n v => n + v.port.roles.length) 0))
      let roles := parties.filter fun role => argumentsPorts.all (fun value => value.port.roles.contains role)
      let type ← classify source operation.val.val.signature.result
      let output ← add ⟨[step, 0], ordinal⟩ ⟨roles, type⟩ arguments
      graph parties step next (ordinal + 1) (output :: context)
        (⟨operation.val.val.declaration, BlsMeaning.payload header operation.val, arguments, output⟩ :: nodes)
  | _, _, _, _ => throw "math-placement-node-subset"

private def body (view : PlacementView.Body header) :
    Protocol.Raw Nat (RegisteredVocabulary.vocabulary header 0) → Nat → Nat → List Nat → List Step →
      Check (List Step × Terminal)
  | .ret values, _, _, context, steps => do return (steps.reverse, .ret (← values.mapM (select context)))
  | .stop site owner reason, _, _, _, steps => return (steps.reverse, .stop site owner reason)
  | .pure captures region next, step, ordinal, context, steps => do
      consume
      let selected ← captures.mapM (select context)
      let mut parameters := []
      for (value, index) in selected.zipIdx do
        consume parameters.length
        parameters := parameters ++ [← add ⟨[step, 0], index⟩ (← vertex value).port [value]]
      let (nodes, yielded) ← graph header view.parties step region parameters.length parameters []
      let mut outputs := []
      for (value, index) in yielded.zipIdx do
        consume outputs.length
        outputs := outputs ++ [← add ⟨[], ordinal + index⟩ (← vertex value).port [value]]
      body view next (step + 1) (ordinal + outputs.length) (outputs ++ context)
        (.pure step parameters nodes outputs :: steps)
  | .query site owner capability arguments next, step, ordinal, context, steps => do
      consume
      ensure arguments.isEmpty "math-placement-query-subset"
      let selected ← select view.capabilities capability
      let output ← add ⟨[], ordinal⟩ ⟨[owner], ← classify source selected.service.val.result⟩
      body view next (step + 1) (ordinal + 1) (output :: context)
        (.query site owner selected.root output :: steps)
  | .guard site owner condition next, step, ordinal, context, steps => do
      consume
      let condition ← select context condition
      body view next (step + 1) ordinal context (.guard site owner condition :: steps)
  | .message site wire sender receiver input next, step, ordinal, context, steps => do
      consume
      let type ← classify source wire.1
      -- This installed profile realizes exactly these four payload packages
      -- with the common carrier's canonical default codec.
      ensure (wire.2.val.val.identity == type.wireIdentity && wire.2.val.val.statics.isEmpty)
        "math-placement-wire-realization"
      let input ← select context input
      let output ← add ⟨[], ordinal⟩
        ⟨view.parties.filter (fun role => role == sender || role == receiver), type⟩
        [input] (some sender)
      body view next (step + 1) (ordinal + 1) (output :: context)
        (.message site wire.2.val.val.declaration sender receiver input output :: steps)
  | _, _, _, _, _ => throw "math-placement-step-subset"

def build (view : PlacementView.Body header) : Check Body := do
  ensure (source.module.definitions.length == 1) "math-placement-definition-subset"
  ensure (source.module.relations.isEmpty && source.module.definitions.all (·.relations.isEmpty))
    "math-placement-relation-subset"
  ensure (view.parties == List.range source.module.roles.length) "math-placement-role-subset"
  let mut arguments := []
  for (value, index) in view.arguments.zipIdx do
    consume arguments.length
    arguments := arguments ++ [← add ⟨[], index⟩ (← port header value)]
  let results ← view.results.mapM (port header)
  let (steps, terminal) ← body header view view.program 0 arguments.length arguments []
  return ⟨view.key, view.parties, arguments, results, (← get).vertices, steps, terminal⟩

abbrev Component := Nat × Nat

private def seeds (body : Body) : Check (List Component) := do
  let mut seeds := []
  for input in body.arguments do
    seeds := seeds ++ (← vertex input).port.roles.map (input, ·)
  for step in body.steps do
    consume
    match step with
    | .pure .. => pure ()
    | .query _ owner _ output => seeds := (output, owner) :: seeds
    | .guard _ owner condition => seeds := (condition, owner) :: seeds
    | .message _ _ sender receiver input output =>
        seeds := (input, sender) :: (output, sender) :: (output, receiver) :: seeds
  if let .ret values := body.terminal then
    ensure (values.length == body.results.length) "math-placement-result-arity"
    for (value, result) in values.zip body.results do
      seeds := seeds ++ result.roles.map (value, ·)
  return seeds

/-- A fresh receive has no sender dependency at the receiver. This is a local
property of the actual dependency rule, independent of honest transport. -/
def dependencies (value : Vertex) (role : Nat) : List Component :=
  if value.dependencyRole.all (· == role) then value.dependencies.map (·, role) else []

theorem fresh_receive (address : Address) (port : Port) (input sender receiver : Nat)
    (different : sender ≠ receiver) :
    dependencies ⟨address, port, [input], some sender⟩ receiver = [] := by
  simp [dependencies, different]

private def close : Nat → List Component → List Component → Check (List Component)
  | 0, [], live => return live
  | 0, _ :: _, _ => throw "math-placement-resource"
  | fuel + 1, pending, live => do
      match pending with
      | [] => return live
      | first :: rest =>
          consume (1 + live.length)
          if live.contains first then close fuel rest live
          else
            let value ← vertex first.1
            consume (value.port.roles.length + value.dependencies.length)
            ensure (value.port.roles.contains first.2) "math-placement-unavailable-component"
            close fuel (dependencies value first.2 ++ rest) (first :: live)

def demand (body : Body) : Check (List Component) := do
  close (← get).remaining (← seeds body) []

end Tools.Mathematical.PlacementGraph
