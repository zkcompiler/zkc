import M0.Core

/-!
# `PCClass`, `Join`, `Publish`, the Kahn order, and the class fold

`docs-next/pir/interactive-core.md` Section 11 fixes the four-element lattice
`PCClass = StaticPublic | PublicHistory | VerifierPrivate | Invalid`, the
functions `Join` and `Publish`, the deterministic topological order ("Kahn's
algorithm, selecting at each step the available node with the least
`M(PCNodeBody(node))`"), and the per-node transfer rules. Appendix A of the
same page fixes `PCNodeBody`.

This file transcribes the lattice, order, transfers, and M1 construction of
`PCGraph(core)` from the fourteen decoded Core tables and used authenticated
semantic-module declarations. D1 node and edge tables are comparison outputs,
not construction inputs.
-/

namespace M0

/-- `PCClass` (Section 11), in the order the page lists the cases. -/
inductive PCClass where
  | staticPublic
  | publicHistory
  | verifierPrivate
  | invalid
  deriving DecidableEq, Repr, Inhabited

/-- `Join(xs)`, written exactly as Section 11 writes it. -/
def Join (xs : List PCClass) : PCClass :=
  if xs.contains .invalid then .invalid
  else if xs.contains .verifierPrivate then .verifierPrivate
  else if xs.contains .publicHistory then .publicHistory
  else .staticPublic

/-- `Publish(x)` (Section 11). -/
def Publish : PCClass → PCClass
  | .staticPublic => .publicHistory
  | .publicHistory => .publicHistory
  | .verifierPrivate => .verifierPrivate
  | .invalid => .invalid

/-- The binary join induced by `Join`. -/
def PCClass.join (a b : PCClass) : PCClass := Join [a, b]

/-! ## `PCNodeBody` (Appendix A) -/

/-- `PCNodeBody` for a node given by its tag and reference arguments. Tags
`8`, `12`, and `13` carry two ordinals in a two-field record; the other eleven
tags carry one ordinal. -/
def pcNodeBody (tag : Nat) (args : List Nat) : Option Datum :=
  match args with
  | [a] =>
    if tag ≤ 7 || (9 ≤ tag && tag ≤ 11) then some (.variant tag (.nat a)) else none
  | [a, b] =>
    if tag = 8 || tag = 12 || tag = 13 then
      some (.variant tag (.record [(0, .nat a), (1, .nat b)]))
    else none
  | _ => none

/-- Lexicographic comparison of two octet strings, as byte strings compare. -/
def lexLt : List Octet → List Octet → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else lexLt as bs

/-! ## The deterministic Kahn order -/

/-- The least-key element of a nonempty list of node indices. -/
def leastByKey (key : Nat → List Octet) : List Nat → Option Nat
  | [] => none
  | v :: vs =>
    match leastByKey key vs with
    | none => some v
    | some w => if lexLt (key w) (key v) then some w else some v

/-- Nodes whose predecessors have all been emitted and which are not yet
emitted themselves. -/
def available (n : Nat) (preds : Nat → List Nat) (emitted : List Nat) : List Nat :=
  (List.range n).filter fun v =>
    !emitted.contains v && (preds v).all fun p => emitted.contains p

/-- Kahn's algorithm with the Section 11 tie-break: at each step, emit the
available node with the least canonical body. Refuses when the nodes cannot
be exhausted (a cycle). -/
def kahnOrder (n : Nat) (key : Nat → List Octet) (preds : Nat → List Nat) :
    Option (List Nat) :=
  go n []
where
  go : Nat → List Nat → Option (List Nat)
    | 0, emitted => if emitted.length = n then some emitted.reverse else none
    | steps + 1, emitted =>
      match leastByKey key (available n preds emitted) with
      | none => none
      | some v => go steps (v :: emitted)

/-! ## Transfer kinds and the class fold -/

/-- The per-node transfer rules of Section 11, as the D1 typed model applies
them. A `constant` node has a fixed class (public inputs and constants are
`StaticPublic`; Verifier-private inputs are `VerifierPrivate`; a Verifier-only
Query or Answer is `VerifierPrivate`; a nondeterministic module output is
`Invalid`). `joinIncoming` is `Join` of the exact incoming edges.
`publishJoinIncoming` is `Publish` of that join (a module Prover publication).
`publishOf` is `Publish(activity)` for a named activity node. `joinOf` joins a
named list of nodes that is not the incoming edge set (a public Query joins
its activity and index producer; a deterministic Verifier message joins its
activity and inputs). `challenge` is the specialised Challenge transfer. -/
inductive Transfer where
  | constant (c : PCClass)
  | joinIncoming
  | publishJoinIncoming
  | publishOf (node : Nat)
  | joinOf (nodes : List Nat)
  | challenge (activity : Nat) (conditions : List Nat) (priors : List Nat)
  deriving Repr

/-- The Challenge transfer as the D1 typed model reads Section 11: an
`Invalid` dependency anywhere wins, then a `VerifierPrivate` dependency
anywhere, then a non-static condition or non-history joint member makes the
Challenge `Invalid`, and otherwise a public activity yields `PublicHistory`. -/
def challengeClass (activity : PCClass) (conditions priors : List PCClass) : PCClass :=
  let dependencies := activity :: (conditions ++ priors)
  if dependencies.contains .invalid then .invalid
  else if dependencies.contains .verifierPrivate then .verifierPrivate
  else if conditions.any (· != .staticPublic) || priors.any (· != .publicHistory) then .invalid
  else if activity = .staticPublic || activity = .publicHistory then .publicHistory
  else .invalid

/-- The other reading of "by the first failed dependency": walk the
dependencies in declaration order (activity, then conditions, then joint
members) and let the first failing one decide. The two readings differ only
when an earlier dependency fails as `VerifierPrivate` while a later one is
`Invalid`; the runner reports whether the exported carriers exercise that
difference. -/
def challengeClassPositional (activity : PCClass) (conditions priors : List PCClass) :
    PCClass :=
  if activity = .verifierPrivate || activity = .invalid then activity
  else
    match conditions.find? (· != .staticPublic) with
    | some .verifierPrivate => .verifierPrivate
    | some _ => .invalid
    | none =>
      match priors.find? (· != .publicHistory) with
      | some .verifierPrivate => .verifierPrivate
      | some _ => .invalid
      | none => .publicHistory

/-- Class assignment in one topological order. Every lookup must hit an
already assigned node; otherwise the fold refuses. -/
def foldClasses (n : Nat) (order : List Nat) (preds : Nat → List Nat)
    (transfer : Nat → Transfer) : Option (Array PCClass) :=
  go order (Array.replicate n none)
where
  lookup (assigned : Array (Option PCClass)) (v : Nat) : Option PCClass :=
    match assigned[v]? with
    | some (some c) => some c
    | _ => none
  lookupAll (assigned : Array (Option PCClass)) : List Nat → Option (List PCClass)
    | [] => some []
    | v :: vs => do
      let c ← lookup assigned v
      let cs ← lookupAll assigned vs
      pure (c :: cs)
  step (assigned : Array (Option PCClass)) (v : Nat) : Option PCClass :=
    match transfer v with
    | .constant c => some c
    | .joinIncoming => (lookupAll assigned (preds v)).map Join
    | .publishJoinIncoming => (lookupAll assigned (preds v)).map (Publish ∘ Join)
    | .publishOf node => (lookup assigned node).map Publish
    | .joinOf nodes => (lookupAll assigned nodes).map Join
    | .challenge activity conditions priors => do
      let a ← lookup assigned activity
      let cs ← lookupAll assigned conditions
      let ps ← lookupAll assigned priors
      pure (challengeClass a cs ps)
  go : List Nat → Array (Option PCClass) → Option (Array PCClass)
    | [], assigned =>
      if assigned.all (·.isSome) then some (assigned.map fun c => c.getD .invalid) else none
    | v :: rest, assigned =>
      match step assigned v with
      | none => none
      | some c => if v < assigned.size then go rest (assigned.set! v (some c)) else none

/-- For every Challenge node, whether the two readings of "first failed
dependency" agree on the assigned classes. -/
def challengeReadingsAgree (n : Nat) (transfer : Nat → Transfer) (classes : Array PCClass) : Bool :=
  (List.range n).all fun v =>
    match transfer v with
    | .challenge activity conditions priors =>
      let cls := fun w => classes.getD w .invalid
      challengeClass (cls activity) (conditions.map cls) (priors.map cls)
        == challengeClassPositional (cls activity) (conditions.map cls) (priors.map cls)
    | _ => true

/-! ## Order-independent class equations -/

/-- Every class coordinate read by one Section 11 transfer. -/
def Transfer.dependencies (preds : Nat → List Nat) (node : Nat) : Transfer → List Nat
  | .constant _ => []
  | .joinIncoming | .publishJoinIncoming => preds node
  | .publishOf source => [source]
  | .joinOf sources => sources
  | .challenge activity conditions priors => activity :: conditions ++ priors

/-- The total class equation induced by a transfer once a complete class table
is available. A successful topological fold is a solution of these equations. -/
def evaluateClass (classes : Nat → PCClass) (preds : Nat → List Nat)
    (node : Nat) : Transfer → PCClass
  | .constant value => value
  | .joinIncoming => Join ((preds node).map classes)
  | .publishJoinIncoming => Publish (Join ((preds node).map classes))
  | .publishOf source => Publish (classes source)
  | .joinOf sources => Join (sources.map classes)
  | .challenge activity conditions priors =>
      challengeClass (classes activity) (conditions.map classes) (priors.map classes)

/-- A complete class table satisfies every transfer equation. -/
def ClassTableSolves (classes : Nat → PCClass) (preds : Nat → List Nat)
    (transfer : Nat → Transfer) : Prop :=
  ∀ node, classes node = evaluateClass classes preds node (transfer node)

/-- A rank is topological when every class dependency has smaller rank. The
rank may come from any topological node order; no canonical tie-break is
needed for the uniqueness statement. -/
def IsTopologicalRank (rank : Nat → Nat) (preds : Nat → List Nat)
    (transfer : Nat → Transfer) : Prop :=
  ∀ node dependency,
    dependency ∈ (transfer node).dependencies preds node → rank dependency < rank node

/-- A class fold indexed by any topological rank. `attach` carries list
membership to the termination checker; erasing those proofs yields exactly
the Section 11 transfer equations. -/
def classFoldByRank (preds : Nat → List Nat) (transfer : Nat → Transfer)
    (rank : Nat → Nat) (topological : IsTopologicalRank rank preds transfer)
    (node : Nat) : PCClass :=
  match _selected : transfer node with
  | .constant value => value
  | .joinIncoming => Join ((preds node).attach.map fun dependency =>
      classFoldByRank preds transfer rank topological dependency.1)
  | .publishJoinIncoming => Publish (Join ((preds node).attach.map fun dependency =>
      classFoldByRank preds transfer rank topological dependency.1))
  | .publishOf source => Publish (classFoldByRank preds transfer rank topological source)
  | .joinOf sources => Join (sources.attach.map fun dependency =>
      classFoldByRank preds transfer rank topological dependency.1)
  | .challenge activity conditions priors => challengeClass
      (classFoldByRank preds transfer rank topological activity)
      (conditions.attach.map fun dependency =>
        classFoldByRank preds transfer rank topological dependency.1)
      (priors.attach.map fun dependency =>
        classFoldByRank preds transfer rank topological dependency.1)
termination_by rank node
decreasing_by
  all_goals apply topological node <;> simp_all [Transfer.dependencies]
  all_goals simp [dependency.property]

/-! ## Construction from the admitted D1 Core fragment -/

/-- The closed Section 11 coordinate algebra. -/
inductive PCNode where
  | publicInput (reference : Nat)
  | verifierPrivateInput (reference : Nat)
  | constant (reference : Nat)
  | derivedValue (reference : Nat)
  | scopeOpening (reference : Nat)
  | bindingObservation (reference : Nat)
  | occurrenceActivity (reference : Nat)
  | occurrenceEffect (reference : Nat)
  | occurrenceOutput (occurrence output : Nat)
  | claimState (reference : Nat)
  | reductionState (reference : Nat)
  | terminalDecision (reference : Nat)
  | moduleControl (occurrence control : Nat)
  | moduleOutput (occurrence output : Nat)
  deriving DecidableEq, Repr

def PCNode.tagArgs : PCNode → Nat × List Nat
  | .publicInput r => (0, [r])
  | .verifierPrivateInput r => (1, [r])
  | .constant r => (2, [r])
  | .derivedValue r => (3, [r])
  | .scopeOpening r => (4, [r])
  | .bindingObservation r => (5, [r])
  | .occurrenceActivity r => (6, [r])
  | .occurrenceEffect r => (7, [r])
  | .occurrenceOutput r o => (8, [r, o])
  | .claimState r => (9, [r])
  | .reductionState r => (10, [r])
  | .terminalDecision r => (11, [r])
  | .moduleControl r o => (12, [r, o])
  | .moduleOutput r o => (13, [r, o])

def PCNode.ofTagArgs (tag : Nat) (args : List Nat) : Option PCNode :=
  match tag, args with
  | 0, [r] => some (.publicInput r)
  | 1, [r] => some (.verifierPrivateInput r)
  | 2, [r] => some (.constant r)
  | 3, [r] => some (.derivedValue r)
  | 4, [r] => some (.scopeOpening r)
  | 5, [r] => some (.bindingObservation r)
  | 6, [r] => some (.occurrenceActivity r)
  | 7, [r] => some (.occurrenceEffect r)
  | 8, [r, o] => some (.occurrenceOutput r o)
  | 9, [r] => some (.claimState r)
  | 10, [r] => some (.reductionState r)
  | 11, [r] => some (.terminalDecision r)
  | 12, [r, o] => some (.moduleControl r o)
  | 13, [r, o] => some (.moduleOutput r o)
  | _, _ => none

def PCNode.body (node : PCNode) : Datum :=
  let (tag, args) := node.tagArgs
  (pcNodeBody tag args).getD .unit

def PCNode.key (node : PCNode) : List Octet := encode node.body

def PCNode.lt (a b : PCNode) : Bool := lexLt a.key b.key

abbrev PCEdge := PCNode × PCNode

def edgeBody (edge : PCEdge) : Datum :=
  .record [(0, edge.1.body), (1, edge.2.body)]

def edgeLt (a b : PCEdge) : Bool := lexLt (encode (edgeBody a)) (encode (edgeBody b))

def insertUnique [BEq α] (x : α) (xs : List α) : List α :=
  if xs.contains x then xs else x :: xs

def unionUnique [BEq α] (left right : List α) : List α :=
  left.foldl (fun result x => insertUnique x result) right

def insertSorted (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertSorted lt x ys

def sortBy (lt : α → α → Bool) (xs : List α) : List α :=
  xs.foldr (insertSorted lt) []

structure GraphBuilder where
  nodes : List PCNode := []
  edges : List PCEdge := []
  deriving Repr

def GraphBuilder.node (g : GraphBuilder) (node : PCNode) : GraphBuilder :=
  { g with nodes := insertUnique node g.nodes }

def GraphBuilder.edge (g : GraphBuilder) (source target : PCNode) : GraphBuilder :=
  let g := (g.node source).node target
  { g with edges := insertUnique (source, target) g.edges }

def producerNode : ValueRef → PCNode
  | .publicInput r => .publicInput r
  | .verifierPrivateInput r => .verifierPrivateInput r
  | .constant r => .constant r
  | .derived r => .derivedValue r
  | .occurrenceOutput r o => .occurrenceOutput r o

def addProducerEdges (g : GraphBuilder) (sources : List ValueRef) (target : PCNode) : GraphBuilder :=
  sources.foldl (fun result source => result.edge (producerNode source) target) g

def findIndexFrom (predicate : α → Bool) : Nat → List α → Option Nat
  | _, [] => none
  | index, x :: xs => if predicate x then some index else findIndexFrom predicate (index + 1) xs

def findIndex? (predicate : α → Bool) (xs : List α) : Option Nat :=
  findIndexFrom predicate 0 xs

def challengeOccurrence (core : Core) (reference : Nat) : Option Nat :=
  findIndex? (fun occurrence => match occurrence.effect with
    | .challenge r => r == reference
    | _ => false) core.occurrences

def checkOccurrence (core : Core) (reference : Nat) : Option Nat :=
  findIndex? (fun occurrence => match occurrence.effect with
    | .check r => r == reference
    | _ => false) core.occurrences

def publicationOccurrence (core : Core) (reference : Nat) : Option Nat :=
  findIndex? (fun occurrence => match occurrence.effect with
    | .oraclePublish r => r == reference
    | _ => false) core.occurrences

def moduleDecl? (modules : List ModuleDecl) (moduleRef : List Octet) (ordinal : Nat) : Option ModuleDecl :=
  modules.find? fun declaration => declaration.moduleRef == moduleRef && declaration.ordinal == ordinal

def moduleForOccurrence (modules : List ModuleDecl) (occurrence : OccurrenceDecl) : Option ModuleDecl :=
  match occurrence.effect with
  | .module moduleRef ordinal _ => moduleDecl? modules moduleRef ordinal
  | _ => none

def moduleDependencyNode (occurrence : Nat) (payloadInputs : List ValueRef) :
    ModuleDependency → Option PCNode
  | .activity => some (.occurrenceActivity occurrence)
  | .effect => some (.occurrenceEffect occurrence)
  | .payloadInput ordinal => (payloadInputs[ordinal]?).map producerNode
  | .priorOutput ordinal => some (.moduleOutput occurrence ordinal)

def foldIndexedOption (f : Nat → σ → α → Option σ) : Nat → σ → List α → Option σ
  | _, state, [] => some state
  | index, state, x :: xs => do
      foldIndexedOption f (index + 1) (← f index state x) xs

def addModuleDependencies (occurrence : Nat) (payloadInputs : List ValueRef)
    (dependencies : List ModuleDependency) (target : PCNode) (g : GraphBuilder) : Option GraphBuilder :=
  dependencies.foldlM (fun result dependency => do
    pure (result.edge (← moduleDependencyNode occurrence payloadInputs dependency) target)) g

def occurrenceOutputCount (core : Core) (modules : List ModuleDecl) (effect : Effect) : Option Nat :=
  match effect with
  | .proverMessage | .verifierMessage _ | .challenge _ | .check _ | .oracleAnswer _ => some 1
  | .reduction _ | .terminal _ | .oracleQuery .. => some 0
  | .oraclePublish oracle => do
      match (← core.oracles[oracle]?).mode with
      | .logicalAccess => pure 0
      | _ => pure 1
  | .module moduleRef ordinal _ => do
      pure (← moduleDecl? modules moduleRef ordinal).outputs.length

def earlierTerminalNodes (core : Core) (occurrence : Nat) : List PCNode :=
  (List.range occurrence).filterMap fun index => do
    match (← core.occurrences[index]?).effect with
    | .terminal reference => some (.terminalDecision reference)
    | _ => none

def addOccurrence (core : Core) (modules : List ModuleDecl) (occurrenceRef : Nat)
    (g : GraphBuilder) (occurrence : OccurrenceDecl) : Option GraphBuilder := do
  let activity := PCNode.occurrenceActivity occurrenceRef
  let effectNode := PCNode.occurrenceEffect occurrenceRef
  let mut result := (g.node activity).node effectNode
  result := result.edge (.scopeOpening occurrence.scope) activity
  match occurrence.guard with
  | .always => pure ()
  | .evaluate inputs => result := addProducerEdges result inputs activity
  for terminal in earlierTerminalNodes core occurrenceRef do
    result := result.edge terminal activity
  result := result.edge activity effectNode
  match occurrence.effect with
  | .proverMessage => pure ()
  | .verifierMessage inputs => result := addProducerEdges result inputs effectNode
  | .challenge reference =>
      let challenge ← core.challenges[reference]?
      result := addProducerEdges result challenge.conditions effectNode
      for prior in challenge.priors do
        let priorOccurrence ← challengeOccurrence core prior
        result := result.edge (.occurrenceOutput priorOccurrence 0) effectNode
  | .check reference =>
      let check ← core.checks[reference]?
      result := addProducerEdges result check.inputs effectNode
  | .reduction reference =>
      let reduction ← core.reductions[reference]?
      for claim in reduction.claims do result := result.edge (.claimState claim) effectNode
      result := addProducerEdges result reduction.sideInputs effectNode
      for challenge in reduction.challenges do
        let challengeOccurrence ← challengeOccurrence core challenge
        result := result.edge (.occurrenceOutput challengeOccurrence 0) effectNode
      for publication in reduction.publications do
        result := result.edge (.occurrenceEffect publication) effectNode
      result := result.edge effectNode (.reductionState reference)
  | .terminal reference =>
      let terminal ← core.terminals[reference]?
      result := addProducerEdges result terminal.publicOutputs effectNode
      for check in terminal.checks do
        let checkOccurrence ← checkOccurrence core check
        result := result.edge (.occurrenceOutput checkOccurrence 0) effectNode
      for reduction in terminal.reductions do
        result := result.edge (.reductionState reduction) effectNode
      for claim in terminal.claims do result := result.edge (.claimState claim) effectNode
      result := result.edge effectNode (.terminalDecision reference)
  | .oraclePublish _ => pure ()
  | .oracleQuery oracle index _ =>
      let publication ← publicationOccurrence core oracle
      result := result.edge (.occurrenceEffect publication) effectNode
      result := result.edge (producerNode index) effectNode
  | .oracleAnswer query =>
      let queryOccurrence ← core.occurrences[query]?
      let oracle ← match queryOccurrence.effect with
        | .oracleQuery oracle _ _ => some oracle
        | _ => none
      let publication ← publicationOccurrence core oracle
      result := result.edge (.occurrenceEffect query) effectNode
      result := result.edge (.occurrenceEffect publication) effectNode
  | .module moduleRef ordinal payloadInputs =>
      let declaration ← moduleDecl? modules moduleRef ordinal
      result ← foldIndexedOption (fun control result spec => do
          let target := PCNode.moduleControl occurrenceRef control
          addModuleDependencies occurrenceRef payloadInputs spec.dependencies target (result.node target))
        0 result declaration.controls
      result ← foldIndexedOption (fun output result spec => do
          let target := PCNode.moduleOutput occurrenceRef output
          let result ← addModuleDependencies occurrenceRef payloadInputs spec.dependencies target (result.node target)
          pure (result.edge target (.occurrenceOutput occurrenceRef output)))
        0 result declaration.outputs
  let outputCount ← occurrenceOutputCount core modules occurrence.effect
  for output in List.range outputCount do
    result := result.edge effectNode (.occurrenceOutput occurrenceRef output)
  pure result

def constructGraph (core : Core) (modules : List ModuleDecl) : Option GraphBuilder := do
  let mut graph : GraphBuilder := {}
  for ordinal in List.range core.publicInputCount do graph := graph.node (.publicInput ordinal)
  for ordinal in List.range core.verifierPrivateInputCount do
    graph := graph.node (.verifierPrivateInput ordinal)
  for ordinal in List.range core.constantCount do graph := graph.node (.constant ordinal)
  graph ← foldIndexedOption (fun ordinal result declaration =>
      pure (addProducerEdges (result.node (.derivedValue ordinal)) declaration.inputs (.derivedValue ordinal)))
    0 graph core.derived
  graph ← foldIndexedOption (fun ordinal result declaration =>
      let target := PCNode.scopeOpening ordinal
      pure (match declaration.parent with
        | none => result.node target
        | some parent => (result.node target).edge (.scopeOpening parent) target))
    0 graph core.scopes
  graph ← foldIndexedOption (fun ordinal result declaration =>
      let target := PCNode.bindingObservation ordinal
      pure ((result.edge (.scopeOpening declaration.scope) target).edge
        (producerNode declaration.value) target))
    0 graph core.bindings
  graph ← foldIndexedOption (addOccurrence core modules) 0 graph core.occurrences
  graph ← foldIndexedOption (fun reference result declaration =>
      let target := PCNode.claimState reference
      pure (match declaration.source with
        | .initialBinding binding => result.edge (.bindingObservation binding) target
        | .reductionOutput reduction _ => result.edge (.reductionState reduction) target))
    0 graph core.claims
  pure {
    nodes := sortBy PCNode.lt graph.nodes
    edges := sortBy edgeLt graph.edges
  }

def nodeIndex? (nodes : List PCNode) (node : PCNode) : Option Nat :=
  findIndex? (· == node) nodes

def predecessorIndices (nodes : List PCNode) (edges : List PCEdge) (node : Nat) : List Nat :=
  edges.filterMap fun edge => do
    let target ← nodeIndex? nodes edge.2
    if target = node then nodeIndex? nodes edge.1 else none

def nodeKeyAt (nodes : List PCNode) (index : Nat) : List Octet :=
  (nodes[index]?).map PCNode.key |>.getD []

def kahnNodeOrder (nodes : List PCNode) (edges : List PCEdge) : Option (List PCNode) := do
  let indices ← kahnOrder nodes.length (nodeKeyAt nodes) (predecessorIndices nodes edges)
  mapOption (fun index => nodes[index]?) indices

def moduleOutputSpec? (core : Core) (modules : List ModuleDecl)
    (occurrence output : Nat) : Option ModuleOutput := do
  let occurrence ← core.occurrences[occurrence]?
  let declaration ← moduleForOccurrence modules occurrence
  declaration.outputs[output]?

def transferForNode (core : Core) (modules : List ModuleDecl) (graph : GraphBuilder)
    (node : PCNode) : Option Transfer := do
  match node with
  | .publicInput _ | .constant _ => pure (.constant .staticPublic)
  | .verifierPrivateInput _ => pure (.constant .verifierPrivate)
  | .moduleOutput occurrence output =>
      match (← moduleOutputSpec? core modules occurrence output).transfer with
      | .deterministic => pure .joinIncoming
      | .proverPublication => pure .publishJoinIncoming
      | .proverInternal => pure (.constant .invalid)
  | .occurrenceEffect occurrence =>
      match (← core.occurrences[occurrence]?).effect with
      | .oraclePublish oracle =>
          match (← core.oracles[oracle]?).mode with
          | .logicalAccess =>
              let activity ← nodeIndex? graph.nodes (.occurrenceActivity occurrence)
              pure (.publishOf activity)
          | _ => pure .joinIncoming
      | .oracleQuery _ _index .verifierOnlyView => pure (.constant .verifierPrivate)
      | .oracleQuery _ index .publicView =>
          let activity ← nodeIndex? graph.nodes (.occurrenceActivity occurrence)
          let producer ← nodeIndex? graph.nodes (producerNode index)
          pure (.joinOf [activity, producer])
      | .oracleAnswer query =>
          match (← core.occurrences[query]?).effect with
          | .oracleQuery _ _ .verifierOnlyView => pure (.constant .verifierPrivate)
          | .oracleQuery _ _ .publicView => pure .joinIncoming
          | _ => none
      | _ => pure .joinIncoming
  | .occurrenceOutput occurrence _ =>
      match (← core.occurrences[occurrence]?).effect with
      | .proverMessage =>
          let activity ← nodeIndex? graph.nodes (.occurrenceActivity occurrence)
          pure (.publishOf activity)
      | .verifierMessage inputs =>
          let activity ← nodeIndex? graph.nodes (.occurrenceActivity occurrence)
          let inputs ← mapOption (fun input => nodeIndex? graph.nodes (producerNode input)) inputs
          pure (.joinOf (activity :: inputs))
      | .challenge reference =>
          let declaration ← core.challenges[reference]?
          let activity ← nodeIndex? graph.nodes (.occurrenceActivity occurrence)
          let conditions ← mapOption
            (fun condition => nodeIndex? graph.nodes (producerNode condition)) declaration.conditions
          let priors ← mapOption (fun prior => do
            nodeIndex? graph.nodes (.occurrenceOutput (← challengeOccurrence core prior) 0))
            declaration.priors
          pure (.challenge activity conditions priors)
      | .oraclePublish _ =>
          let activity ← nodeIndex? graph.nodes (.occurrenceActivity occurrence)
          pure (.publishOf activity)
      | .oracleAnswer query =>
          match (← core.occurrences[query]?).effect with
          | .oracleQuery _ _ .verifierOnlyView => pure (.constant .verifierPrivate)
          | .oracleQuery _ _ .publicView =>
              let activity ← nodeIndex? graph.nodes (.occurrenceActivity occurrence)
              pure (.publishOf activity)
          | _ => none
      | _ => pure .joinIncoming
  | _ => pure .joinIncoming

def classTable (core : Core) (modules : List ModuleDecl) (graph : GraphBuilder) :
    Option (List (PCNode × PCClass)) := do
  let order ← kahnNodeOrder graph.nodes graph.edges
  let orderIndices ← mapOption (nodeIndex? graph.nodes) order
  let transfers ← mapOption (transferForNode core modules graph) graph.nodes
  let classes ← foldClasses graph.nodes.length orderIndices
    (predecessorIndices graph.nodes graph.edges) fun index =>
      (transfers[index]?).getD (.constant .invalid)
  pure (List.zip graph.nodes classes.toList)

def nodesWithClass (classes : List (PCNode × PCClass)) (klass : PCClass) : List PCNode :=
  classes.filterMap fun (node, value) => if value = klass then some node else none

def descendants (source : PCNode) (edges : List PCEdge) : List PCNode :=
  go [source] [source] edges.length
where
  go (pending seen : List PCNode) : Nat → List PCNode
    | 0 => seen
    | fuel + 1 =>
      match pending with
      | [] => seen
      | current :: rest =>
          let children := edges.filterMap fun edge =>
            if edge.1 = current && !seen.contains edge.2 then some edge.2 else none
          go (children ++ rest) (unionUnique children seen) fuel

structure GraphProducts where
  graph : GraphBuilder
  order : List PCNode
  classes : List (PCNode × PCClass)
  sinks : List PCNode
  acceptanceSinks : List PCNode
  privatePredecessors : List PCNode
  logicalCones : List (Nat × List PCNode)
  logicalIntersections : List (Nat × List PCNode)
  deriving Repr

def moduleAcceptanceNodes (core : Core) (modules : List ModuleDecl) : List PCNode :=
  (List.range core.occurrences.length).foldl (fun result occurrence =>
    match core.occurrences[occurrence]? with
    | none => result
    | some row => match moduleForOccurrence modules row with
      | none => result
      | some declaration =>
          let outputs := (List.range declaration.outputs.length).filterMap fun output =>
            if (declaration.outputs[output]?).any (·.acceptanceRelevant) then
              some (.moduleOutput occurrence output) else none
          let controls := (List.range declaration.controls.length).filterMap fun control =>
            if (declaration.controls[control]?).any (·.acceptanceRelevant) then
              some (.moduleControl occurrence control) else none
          unionUnique outputs (unionUnique controls result)) []

def observationNodes (core : Core) (modules : List ModuleDecl) : Option (List PCNode × List PCNode × List PCNode) := do
  let bindings := (List.range core.bindings.length).map PCNode.bindingObservation
  let mut observations := bindings
  let mut activities : List PCNode := []
  let mut challengeConditions : List PCNode := []
  let mut checks : List PCNode := []
  for occurrence in List.range core.occurrences.length do
    let row ← core.occurrences[occurrence]?
    let mut observed : List PCNode := []
    match row.effect with
    | .proverMessage | .verifierMessage _ =>
        let count ← occurrenceOutputCount core modules row.effect
        observed := (List.range count).map (.occurrenceOutput occurrence)
    | .challenge reference =>
        observed := [.occurrenceOutput occurrence 0]
        let declaration ← core.challenges[reference]?
        challengeConditions := unionUnique (declaration.conditions.map producerNode) challengeConditions
    | .check _ => checks := insertUnique (.occurrenceEffect occurrence) checks
    | .oraclePublish oracle =>
        match (← core.oracles[oracle]?).mode with
        | .logicalAccess => observed := [.occurrenceEffect occurrence]
        | _ =>
            let count ← occurrenceOutputCount core modules row.effect
            observed := (List.range count).map (.occurrenceOutput occurrence)
    | .oracleQuery _ index .publicView =>
        observed := [.occurrenceEffect occurrence]
        observations := insertUnique (producerNode index) observations
    | .oracleQuery _ _ .verifierOnlyView => pure ()
    | .oracleAnswer query =>
        match (← core.occurrences[query]?).effect with
        | .oracleQuery _ _ .publicView => observed := [.occurrenceOutput occurrence 0]
        | .oracleQuery _ _ .verifierOnlyView => pure ()
        | _ => none
    | .module .. =>
        let declaration ← moduleForOccurrence modules row
        for output in List.range declaration.outputs.length do
          if (declaration.outputs[output]?).any fun spec => spec.visibility = .publicView then
            observed := insertUnique (.moduleOutput occurrence output)
              (insertUnique (.occurrenceOutput occurrence output) observed)
    | _ => pure ()
    if !observed.isEmpty then activities := insertUnique (.occurrenceActivity occurrence) activities
    observations := unionUnique observed observations
  pure (observations, activities, unionUnique challengeConditions checks)

def deriveProducts (core : Core) (modules : List ModuleDecl) : Option GraphProducts := do
  let graph ← constructGraph core modules
  let order ← kahnNodeOrder graph.nodes graph.edges
  let classes ← classTable core modules graph
  let (observations, activities, conditionChecks) ← observationNodes core modules
  let reductions := (List.range core.reductions.length).map PCNode.reductionState
  let terminals := (List.range core.terminals.length).map PCNode.terminalDecision
  let terminalOutputs := core.terminals.foldl (fun result terminal =>
    unionUnique (terminal.publicOutputs.map producerNode) result) []
  let moduleAcceptance := moduleAcceptanceNodes core modules
  let challengeOutputs := (List.range core.occurrences.length).filterMap fun occurrence => do
    match (← core.occurrences[occurrence]?).effect with
    | .challenge _ => some (.occurrenceOutput occurrence 0)
    | _ => none
  let sinks := sortBy PCNode.lt (unionUnique observations (unionUnique activities
    (unionUnique conditionChecks (unionUnique challengeOutputs (unionUnique reductions
      (unionUnique terminals (unionUnique terminalOutputs moduleAcceptance)))))))
  let acceptingTerminals := (List.range core.terminals.length).filterMap fun reference => do
    if (← core.terminals[reference]?).verdict = .accept then some (.terminalDecision reference) else none
  let acceptingOutputs := (List.range core.terminals.length).foldl (fun result reference =>
    match core.terminals[reference]? with
    | some terminal => if terminal.verdict = .accept then
        unionUnique (terminal.publicOutputs.map producerNode) result else result
    | none => result) []
  let checks := (List.range core.occurrences.length).filterMap fun occurrence => do
    match (← core.occurrences[occurrence]?).effect with
    | .check _ => some (.occurrenceEffect occurrence)
    | _ => none
  let acceptance := sortBy PCNode.lt (unionUnique checks (unionUnique reductions
    (unionUnique acceptingTerminals (unionUnique acceptingOutputs moduleAcceptance))))
  let privatePredecessors := sortBy PCNode.lt ((List.range core.verifierPrivateInputCount).filterMap
    fun reference =>
      let source := PCNode.verifierPrivateInput reference
      if (descendants source graph.edges).any sinks.contains then some source else none)
  let logicalOracleRefs := (List.range core.oracles.length).filter fun reference =>
    (core.oracles[reference]?).any fun declaration => declaration.mode = .logicalAccess
  let logicalCones ← mapOption (fun reference => do
    let publication ← publicationOccurrence core reference
    pure (reference, sortBy PCNode.lt
      (descendants (.occurrenceEffect publication) graph.edges))) logicalOracleRefs
  let logicalIntersections := logicalCones.map fun (reference, cone) =>
    (reference, sortBy PCNode.lt (cone.filter acceptance.contains))
  pure {
    graph := graph
    order := order
    classes := classes
    sinks := sinks
    acceptanceSinks := acceptance
    privatePredecessors := privatePredecessors
    logicalCones := logicalCones
    logicalIntersections := logicalIntersections
  }

end M0
