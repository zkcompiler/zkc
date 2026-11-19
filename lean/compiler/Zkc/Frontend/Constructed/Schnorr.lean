module

public import Zkc.Frontend.Constructed.Correspondence
public import Zkc.Frontend.Written.Root
public import Zkc.Frontend.Written.Contract

@[expose] public section

namespace Zkc.Frontend.Constructed
open Core

abbrev V := (Emit.Bindings.mk [] (by decide)).vocabulary
abbrev point : V.Ty := .nominal (.inl (.group .g1))
abbrev scalar : V.Ty := .nominal (.inl (.field .bls12381Fr))
abbrev uniformScalar : V.LawKey := .uniform (.nominal (.field .bls12381Fr))
def merlinSuite := "suite.merlin3.bls12-381.fr64be/0"

def hasConstructedStage (goal : Lowered.Goal) : Bool :=
  let stages : Array Lowered.GoalValue := goal.args.filterMap fun
    | .named _ key value => if key.text == "stage" then some value else none
    | _ => none
  match stages with
  | #[.path _ (.reference (.reference _ #[.segment (.word "constructed") none none])) none] => true
  | _ => false

def goalDeclaration (goal : Lowered.Goal) : Option DeclarationId :=
  match goal.scheme with
  | .reference ref => ref.declaration?
  | _ => none

inductive ExecutionRequest where
  | scheme (name : String)
  | goal (name : String)

/-- A named goal contributes its complete lowered declaration, checked at the constructed stage. -/
def ExecutionRequest.Subject (request : ExecutionRequest) (scheme : SchemeEntry) : Type :=
  match request with
  | .scheme _ => Unit
  | .goal _ => { g : Lowered.Goal // hasConstructedStage g = true ∧
      goalDeclaration g = some scheme.declaration }

private def resolveScheme (state : Compile.State) (request : ExecutionRequest) :
    Except String ((scheme : SchemeEntry) × request.Subject scheme × Compile.State) :=
  match request with
  | .scheme name => do
    let (selection, state) ← Written.select state (.scheme name)
    return ⟨selection.scheme, (), state⟩
  | .goal name => do
    let (id, _) ← Written.selectDeclaration state .goal name "FS-GOAL"
    let some {content := .goal goal, ..} := state.env.modules.lowered? id | throw "FS-GOAL: missing goal"
    if stage : hasConstructedStage goal then
      let (scheme, state) ← Written.goalScheme state goal
      if bound : goalDeclaration goal = some scheme.declaration then
        return ⟨scheme, ⟨goal, stage, bound⟩, state⟩
      throw "FS-GOAL: requested scheme differs from the constructed verifier"
    throw "FS-STAGE: expected an explicit constructed-stage goal"

/-- Keep the emission and successful admission of this particular source instance.
The equality specializes its linked vocabulary without rebuilding its program. -/
structure SourceEntry (request : ExecutionRequest) where
  private mk ::
  scheme : SchemeEntry
  subject : request.Subject scheme
  root : Written.AdmittedRoot
  selected : root.id = scheme.protocol
  suite : scheme.suite = .ok merlinSuite
  standard : root.emission.bindings = (⟨[], by decide⟩ : Emit.Bindings)
  declaredProver : Option Role

/-- Select and admit from a single assembly, including the state obtained when closing an imported scheme. -/
@[no_expose] def resolveEntry (assembly : Assembly) (request : ExecutionRequest) : Except String (SourceEntry request) := do
  let state ← Written.sourceState assembly
  let ⟨scheme, subject, state⟩ ← resolveScheme state request
  if let some why := scheme.waits then throw s!"FS-SCHEME: {why}"
  let hSuite ← (show Except String (PLift (scheme.suite = .ok merlinSuite)) from
    match scheme.suite with
    | .error why => .error s!"FS-SUITE: {why}"
    | .ok suite => if h : suite = merlinSuite then .ok ⟨congrArg Except.ok h⟩
      else .error s!"FS-SUITE: unsupported catalogue binding {suite}")
  unless (scheme.lines.filter (fun | .construction _ (.derived ..) => true | _ => false)).size == 1 &&
      (scheme.lines.filter (fun | .layout .. => true | _ => false)).size ≤ 1 &&
      scheme.lines.all (fun | .construction _ (.derived ..) | .prover .. | .layout _ _ none => true | _ => false) do
    throw "FS-SCHEME: expected one derived construction and the canonical layout"
  let root ← Written.admitInstance state scheme.protocol scheme.span
  let some (.protocol code) := root.state.results.body? root.id | throw "FS-ENTRY: missing protocol"
  let some key := root.state.results.key? root.id | throw "FS-ENTRY: missing closed instance"
  let some source := root.state.program.declarations[key.declaration]? | throw "FS-ENTRY: missing declaration"
  let .protocol proto := source.node | throw "FS-ENTRY: expected protocol"
  unless !code.specificationOnly && code.roles.size == 2 && proto.head.ports.size == 3 &&
      proto.head.ports.all (fun | .port _ _ _ _ false => true | _ => false) do
    throw "FS-ENTRY: expected two public points and a prover scalar"
  unless root.emission.named.definitions.length == 1 do throw "FS-ENTRY: expected a single deployed definition"
  let selected ← if h : root.id = scheme.protocol then pure (PLift.up h) else throw "FS-ENTRY: wrong emitted instance"
  let roles ← Written.writtenParties scheme code.roles
  if standard : root.emission.bindings.rows = [] then
    have same : root.emission.bindings = (⟨[], by decide⟩ : Emit.Bindings) := by
      cases eq : root.emission.bindings with
      | mk rows nodup => rw [eq] at standard; cases standard; rfl
    return ⟨scheme, subject, root, selected.down, hSuite.down, same, roles.declaredProver⟩
  else throw "FS-ENTRY: unsupported project primitive bindings"

/-- The same successful lookup fixes the subject, scheme, admitted program and role designation. -/
structure Entry (assembly : Assembly) (request : ExecutionRequest) extends SourceEntry request where
  issued : resolveEntry assembly request = .ok toSourceEntry

variable {assembly : Assembly} {request : ExecutionRequest}

def Entry.declaration (e : Entry assembly request) : Core.Declaration where
  key := ⟨e.scheme.declaration⟩
  entry := ⟨e.root.id⟩
  kinds := [.online,.online]
  construction := .catalogue merlinSuite
  prover := e.declaredProver
  layout := none
  retry := none
  samples := none
  context := []
  grinds := []
  commits := []
  pins := []

def Entry.admitted (e : Entry assembly request) : Core.Admitted V :=
  cast (congrArg (fun b : Emit.Bindings => Core.Admitted b.vocabulary) e.standard) e.root.evidence.admitted

def Entry.header (e : Entry assembly request) := e.admitted.program.findProtocol e.declaration.entry

def Entry.firstUnused (e : Entry assembly request) (found : e.header.isSome) : Nat :=
  let body := e.admitted.program.defs.protocolEntry e.admitted.program.distinct (e.header.get found).2
  1 + (body.body.addresses []).foldl (fun n (_,k) => max n k.number) 0

/-- Written event numbers bound to emitted instruction keys before constructing the layer. -/
structure Labels where
  commitment : Nat
  challenge : Nat
  response : Nat
  deriving DecidableEq, Repr

def siteNumber (code : Typing.ProtocolCode) (key : Key) : Except String Nat := do
  let #[site] := code.sites.filter (·.instruction == some key.number)
    | throw "FS-SITES: missing or ambiguous source event"
  unless site.part == "value" && site.iteration.isEmpty && site.event < 2^64 do
    throw "FS-SITES: expected a top-level event with a 64-bit label"
  return site.event

def sitesOf (header : ProtocolHeader V) (p v : Role) (fresh : Nat) : Option Sites := do
  let .event _ (.given (.coin nonceLaw) nonceOwner []) nonce
      (.event c (.flow .message sender [receiver]) first
      (.event d (.given (.coin drawLaw) owner [peer]) draw
      (.event z (.flow .message lastSender [lastReceiver]) last
      (.guard _ [judge] .reject .nil)))) := header.shape | none
  guard (nonceOwner == p && nonceLaw == uniformScalar && nonce == scalar &&
    sender == p && receiver == v && first == point &&
    owner == v && peer == p && drawLaw == uniformScalar && draw == scalar &&
    lastSender == p && lastReceiver == v && last == scalar && judge == v)
  return ⟨header.key,c,d,z,fresh⟩

def labelsOf (root : Written.AdmittedRoot) (sites : Sites) : Except String Labels := do
  let some (.protocol code) := root.state.results.body? root.id | throw "FS-ENTRY: missing protocol"
  return ⟨← siteNumber code sites.commitment, ← siteNumber code sites.challenge,
    ← siteNumber code sites.response⟩

structure Verifier (assembly : Assembly) (request : ExecutionRequest) where
  entry : Entry assembly request
  found : entry.header.isSome
  prover : Role
  verifier : Role
  parties : proverAndVerifier (entry.header.get found).1 entry.declaration = some (prover,verifier)
  inputs : held verifier (entry.header.get found).1.ins = [point,point]
  sites : Sites
  labels : Labels
  located : sitesOf (entry.header.get found).1 prover verifier (entry.firstUnused found) = some sites
  numbered : labelsOf entry.root sites = .ok labels

def Verifier.deployment (v : Verifier assembly request) : Deployed V where
  admitted := v.entry.admitted
  declaration := v.entry.declaration
  found := v.found
  stack r := if r = v.verifier then
    [verifierLayer v.sites v.prover r point scalar uniformScalar _] else []

/-- Exactly the typed verifier stack used by the run, including every clause operand,
the start, and the state returned on success. -/
theorem Verifier.stack_eq (v : Verifier assembly request) :
    v.deployment.stack v.verifier =
      [verifierLayer v.sites v.prover v.verifier point scalar uniformScalar _] := by
  simp [deployment]

/-- Interpret the catalogue binding and role designation on the actual entry shape.
An unknown binding or a different shape cannot prescribe these clauses. -/
def declaredHandlers (d : Core.Declaration) (hdr : ProtocolHeader V) (fresh : Nat) :
    Option (List (LayerCode V)) := do
  let .catalogue suite := d.construction | none
  guard (suite == merlinSuite)
  let (p,v) ← proverAndVerifier hdr d
  let sites ← sitesOf hdr p v fresh
  return [declaredCode sites p v point scalar uniformScalar]

theorem Verifier.handler_correspondence (v : Verifier assembly request) :
    declaredHandlers v.entry.declaration (v.entry.header.get v.found).1 (v.entry.firstUnused v.found) =
      some ((v.deployment.stack v.verifier).map readLayer) := by
  have binding : v.entry.declaration.construction = .catalogue merlinSuite := rfl
  simp [declaredHandlers, binding, v.parties, v.located, v.stack_eq, verifierLayer_readback, guard]

def construct (assembly : Assembly) (request : ExecutionRequest) : Except String (Verifier assembly request) := do
  let e ← (show Except String (Entry assembly request) from
    match issued : resolveEntry assembly request with
    | .error why => .error why
    | .ok source => .ok ⟨source, issued⟩)
  if found : e.header.isSome then
    let hdr := (e.header.get found).1
    match parties : proverAndVerifier hdr e.declaration with
    | none => throw "SC3: the designated online roles disagree with the entry"
    | some (p,v) =>
      unless hdr.roles == 2 && hdr.outs.isEmpty && hdr.ins.map LTy.ty == [point,point,scalar] &&
          statementOf hdr p v == [point,point] && witnessOf hdr p v == [scalar] do
        throw "FS-ENTRY: incompatible public or witness ports"
      match located : sitesOf hdr p v (e.firstUnused found) with
      | none => throw "FS-SITES: unsupported verifier shape or draw law"
      | some sites =>
        match numbered : labelsOf e.root sites with
        | .error why => throw why
        | .ok labels =>
          if inputs : held v hdr.ins = [point,point] then
            return ⟨e,found,p,v,parties,inputs,sites,labels,located,numbered⟩
          else throw "FS-ENTRY: incompatible verifier inputs"
  else throw "FS-ENTRY: admitted protocol missing"

/-- Select by the resolved scheme declaration, including qualified names. -/
def selectScheme (assembly : Assembly) (name : String) := construct assembly (.scheme name)

/-- Execution subject only. The complete lowered goal retains its property, clause,
model and ceiling. Any theorem about them needs a separate interpretation. -/
structure GoalExecution (assembly : Assembly) (name : String) where
  verifier : Verifier assembly (.goal name)

variable {name : String}

def GoalExecution.goal (execution : GoalExecution assembly name) := execution.verifier.entry.subject.val

theorem GoalExecution.constructed (execution : GoalExecution assembly name) :
    hasConstructedStage execution.goal = true := execution.verifier.entry.subject.property.1

theorem GoalExecution.bound (execution : GoalExecution assembly name) :
    goalDeclaration execution.goal = some execution.verifier.entry.scheme.declaration :=
  execution.verifier.entry.subject.property.2

def selectGoalExecution (assembly : Assembly) (name : String) : Except String (GoalExecution assembly name) :=
  GoalExecution.mk <$> construct assembly (.goal name)

end Zkc.Frontend.Constructed
