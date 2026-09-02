import M0

/-!
# `lake exe m0 <input.json>`

Reads the runner's assembled input, exercises the Lean definitions against
every vector, and prints one JSON report on standard output. Exit status `0`
means the report was produced; the runner, not the exit status, decides the
findings.
-/

open Lean M0 M0.Transport

structure EncodeResult where
  name : String
  source : String
  wellFormed : Bool
  withinLimits : Bool
  encodeMatches : Bool
  decodeRoundTrips : Bool
  decodedEqualsValue : Bool
  transportError : Option String := none

def EncodeResult.toJson (r : EncodeResult) : Json :=
  Json.mkObj [
    ("name", r.name), ("source", r.source),
    ("well_formed", r.wellFormed), ("within_limits", r.withinLimits),
    ("encode_matches", r.encodeMatches), ("decode_roundtrips", r.decodeRoundTrips),
    ("decoded_equals_value", r.decodedEqualsValue),
    ("transport_error", match r.transportError with | some e => Json.str e | none => Json.null)
  ]

def runEncodeVector (j : Json) : Except String EncodeResult := do
  let name ← readString j "name"
  let source ← readString j "source"
  let hex ← readString j "hex"
  let golden ← octetsOfHex hex
  match datumOfJson (← readField j "value") with
  | .error e =>
    pure { name, source, wellFormed := false, withinLimits := false, encodeMatches := false,
           decodeRoundTrips := false, decodedEqualsValue := false, transportError := some e }
  | .ok value =>
    let wf := M0.wellFormed value
    let limits := M0.withinLimits value
    let encodeMatches := encodeChecked value == some golden
    let decoded := decode golden
    let decodeRoundTrips := match decoded with
      | some d => encodeChecked d == some golden
      | none => false
    let decodedEqualsValue := match decoded with
      | some d => beq d value
      | none => false
    pure { name, source, wellFormed := wf, withinLimits := limits, encodeMatches,
           decodeRoundTrips, decodedEqualsValue }

structure RejectResult where
  name : String
  rejected : Bool

def RejectResult.toJson (r : RejectResult) : Json :=
  Json.mkObj [("name", r.name), ("rejected", r.rejected)]

def runRejectVector (j : Json) : Except String RejectResult := do
  let name ← readString j "name"
  let octets ← octetsOfHex (← readString j "hex")
  pure { name, rejected := (decode octets).isNone }

structure CarrierResult where
  carrier : String
  nodeCount : Nat
  edgeCount : Nat
  keysMatchAppendixA : Bool
  orderComputed : Bool
  orderMatches : Bool
  classesComputed : Bool
  classesMatch : Bool
  challengeCount : Nat
  challengeReadingsAgree : Bool
  classCounts : List (String × Nat)

def CarrierResult.toJson (r : CarrierResult) : Json :=
  Json.mkObj [
    ("carrier", r.carrier), ("node_count", r.nodeCount), ("edge_count", r.edgeCount),
    ("keys_match_appendix_a", r.keysMatchAppendixA),
    ("order_computed", r.orderComputed), ("order_matches", r.orderMatches),
    ("classes_computed", r.classesComputed), ("classes_match", r.classesMatch),
    ("challenge_count", r.challengeCount),
    ("challenge_readings_agree", r.challengeReadingsAgree),
    ("class_counts", Json.mkObj (r.classCounts.map fun (k, v) => (k, Json.num v)))
  ]

def runCarrier (j : Json) : Except String CarrierResult := do
  let table ← carrierOfJson j
  let n := table.nodes.size
  let key := fun v => (table.nodes[v]?).map (·.key) |>.getD []
  let preds := fun v => table.edges.filterMap fun (s, t) => if t = v then some s else none
  let transfer := fun v => (table.transfers[v]?).getD (.constant .invalid)
  let keysMatch := table.nodes.all fun row =>
    match pcNodeBody row.tag row.args with
    | some body => encodeChecked body == some row.key
    | none => false
  let order := kahnOrder n key preds
  let orderMatches := order == some table.expectedOrder
  let classes := order.bind fun o => foldClasses n o preds transfer
  let classesMatch := match classes with
    | some cs => cs.toList == table.expectedClasses
    | none => false
  let challengeCount := (List.range n).countP fun v =>
    match transfer v with | .challenge .. => true | _ => false
  let readingsAgree := match classes with
    | some cs => challengeReadingsAgree n transfer cs
    | none => false
  let counts := match classes with
    | some cs => [PCClass.staticPublic, .publicHistory, .verifierPrivate, .invalid].map fun c =>
        (nameOfClass c, cs.toList.count c)
    | none => []
  pure { carrier := table.carrier, nodeCount := n, edgeCount := table.edges.length,
         keysMatchAppendixA := keysMatch, orderComputed := order.isSome, orderMatches,
         classesComputed := classes.isSome, classesMatch, challengeCount,
         challengeReadingsAgree := readingsAgree, classCounts := counts }

structure ConstructionResult where
  carrier : String
  coreTablesDecoded : Nat
  moduleDeclarationsDecoded : Nat
  nodeCount : Nat
  edgeCount : Nat
  nodesMatch : Bool
  edgesMatch : Bool
  orderMatches : Bool
  classesMatch : Bool
  sinksMatch : Bool
  acceptanceSinksMatch : Bool
  privatePredecessorsMatch : Bool
  logicalConesMatch : Bool
  logicalIntersectionsMatch : Bool
  terminalPreemptionEdges : Nat
  oracleQueryAnswerEdges : Nat
  moduleEdges : Nat
  challengeCount : Nat
  challengeReadingsAgree : Bool

def ConstructionResult.toJson (r : ConstructionResult) : Json :=
  Json.mkObj [
    ("carrier", r.carrier),
    ("core_tables_decoded", r.coreTablesDecoded),
    ("module_declarations_decoded", r.moduleDeclarationsDecoded),
    ("node_count", r.nodeCount), ("edge_count", r.edgeCount),
    ("nodes_match", r.nodesMatch), ("edges_match", r.edgesMatch),
    ("order_matches", r.orderMatches), ("classes_match", r.classesMatch),
    ("sinks_match", r.sinksMatch),
    ("acceptance_sinks_match", r.acceptanceSinksMatch),
    ("private_predecessors_match", r.privatePredecessorsMatch),
    ("logical_cones_match", r.logicalConesMatch),
    ("logical_intersections_match", r.logicalIntersectionsMatch),
    ("terminal_preemption_edges", r.terminalPreemptionEdges),
    ("oracle_query_answer_edges", r.oracleQueryAnswerEdges),
    ("module_edges", r.moduleEdges),
    ("challenge_count", r.challengeCount),
    ("challenge_readings_agree", r.challengeReadingsAgree)
  ]

def isTerminalPreemptionEdge : PCEdge → Bool
  | (.terminalDecision _, .occurrenceActivity _) => true
  | _ => false

def occurrenceHasQueryOrAnswer (core : Core) (reference : Nat) : Bool :=
  match core.occurrences[reference]? with
  | some occurrence => match occurrence.effect with
    | .oracleQuery .. | .oracleAnswer _ => true
    | _ => false
  | none => false

def isOracleQueryAnswerEdge (core : Core) : PCEdge → Bool
  | (_, .occurrenceEffect reference) => occurrenceHasQueryOrAnswer core reference
  | _ => false

def isModuleNode : PCNode → Bool
  | .moduleControl .. | .moduleOutput .. => true
  | _ => false

def isModuleEdge : PCEdge → Bool
  | (source, target) => isModuleNode source || isModuleNode target

def runConstruction (j : Json) : Except String ConstructionResult := do
  let carrier ← constructionCarrierOfJson j
  let products ← match deriveProducts carrier.core carrier.modules with
    | some products => pure products
    | none => throw "Section 11 graph construction or product derivation refused"
  let edges := products.graph.edges
  let transfers ← match mapOption
      (transferForNode carrier.core carrier.modules products.graph) products.graph.nodes with
    | some transfers => pure transfers
    | none => throw "Section 11 transfer derivation refused"
  let classArray := products.classes.map Prod.snd |>.toArray
  let challengeCount := transfers.countP fun transfer => match transfer with
    | .challenge .. => true
    | _ => false
  pure {
    carrier := carrier.carrier
    coreTablesDecoded := 14
    moduleDeclarationsDecoded := carrier.modules.length
    nodeCount := products.graph.nodes.length
    edgeCount := edges.length
    nodesMatch := products.graph.nodes == carrier.expected.nodes
    edgesMatch := edges == carrier.expected.edges
    orderMatches := products.order == carrier.expected.order
    classesMatch := products.classes == carrier.expected.classes
    sinksMatch := products.sinks == carrier.expected.sinks
    acceptanceSinksMatch := products.acceptanceSinks == carrier.expected.acceptanceSinks
    privatePredecessorsMatch := products.privatePredecessors == carrier.expected.privatePredecessors
    logicalConesMatch := products.logicalCones == carrier.expected.logicalCones
    logicalIntersectionsMatch :=
      products.logicalIntersections == carrier.expected.logicalIntersections
    terminalPreemptionEdges := edges.countP isTerminalPreemptionEdge
    oracleQueryAnswerEdges := edges.countP (isOracleQueryAnswerEdge carrier.core)
    moduleEdges := edges.countP isModuleEdge
    challengeCount := challengeCount
    challengeReadingsAgree := challengeReadingsAgree products.graph.nodes.length
      (fun index => (transfers[index]?).getD (.constant .invalid)) classArray
  }

def boundaryNaturalMagnitudeOctets : Nat := maxCanonicalBytes - 9

def boundaryNatural : Nat := 256 ^ (boundaryNaturalMagnitudeOctets - 1)

/-- Executed by the compiled Lean runner, not discharged by reduction in a
theorem: the natural's complete encoding reaches exactly the byte bound. -/
def naturalBoundaryReport : Json :=
  let datum := Datum.nat boundaryNatural
  let body := encode datum
  Json.mkObj [
    ("magnitude_octets", boundaryNaturalMagnitudeOctets),
    ("encoded_octets", body.length),
    ("reaches_bound", body.length == maxCanonicalBytes),
    ("checked_encoder_accepts", (encodeChecked datum).isSome)
  ]

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | do
    IO.eprintln "usage: m0 <input.json>"
    return 2
  let text ← IO.FS.readFile path
  let input ← match Json.parse text with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"input is not JSON: {e}")
  let run {α : Type} (name : String) (f : Json → Except String α) (toJson : α → Json) :
      IO (Array Json) := do
    let rows ← match readArray input name with
      | .ok rows => pure rows
      | .error e => throw (IO.userError e)
    rows.mapM fun row =>
      match f row with
      | .ok r => pure (toJson r)
      | .error e => throw (IO.userError s!"{name}: {e}")
  let encodeRows ← run "encode" runEncodeVector EncodeResult.toJson
  let rejectRows ← run "reject" runRejectVector RejectResult.toJson
  let constructionRows ← run "pcgraph_construction" runConstruction ConstructionResult.toJson
  let report := Json.mkObj [
    ("lean_version", Json.str Lean.versionString),
    ("natural_boundary", naturalBoundaryReport),
    ("encode", Json.arr encodeRows),
    ("reject", Json.arr rejectRows),
    ("pcgraph_construction", Json.arr constructionRows)
  ]
  IO.println report.compress
  return 0
