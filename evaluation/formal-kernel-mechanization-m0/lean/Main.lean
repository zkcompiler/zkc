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

structure M2AlgorithmRow where
  algorithm : Algorithm
  preimage : List Octet
  maximumCompletionBytes : Nat

def m2AlgorithmOfJson (j : Json) : Except String M2AlgorithmRow := do
  let preimage ← octetsOfHex (← readString j "preimage_hex")
  let datum ← match decode preimage with
    | some datum => pure datum
    | none => throw "M2 algorithm preimage failed the M0 strict decoder"
  let algorithm ← match algorithmOfDatum datum with
    | some algorithm => pure algorithm
    | none => throw "M2 algorithm preimage did not elaborate as a K1 algorithm"
  let maximumCompletionBytes ← readNat j "maximum_completion_bytes"
  pure { algorithm, preimage, maximumCompletionBytes }

def m2ChargeOfJson (j : Json) : Except String Charge := do
  let steps ← readNat j "steps"
  let iterationItems ← readNat j "iteration_items"
  let primitiveWork ← readNat j "primitive_work"
  let resultBytes ← readNat j "result_bytes"
  pure { steps, iterationItems, primitiveWork, resultBytes }

def zipTypedValues : List ValueType → List Datum → Option (List TypedValue)
  | [], [] => some []
  | ty :: types, datum :: data => do
      pure (⟨ty, datum⟩ :: (← zipTypedValues types data))
  | _, _ => none

def m2CaseAgrees (algorithm : Algorithm) (primitive : PrimitiveDenotation)
    (maximumCompletionBytes : Nat) (j : Json) : Except String Bool := do
  let inputsJson ← readArray j "inputs"
  let inputData ← inputsJson.toList.mapM datumOfJson
  let inputs ← match zipTypedValues algorithm.inputs inputData with
    | some inputs => pure inputs
    | none => throw "M2 case input arity differs from the decoded algorithm"
  let expected ← datumOfJson (← readField j "expected_completion")
  let expectedHex ← octetsOfHex (← readString j "expected_completion_hex")
  let expectedCharge ← m2ChargeOfJson (← readField j "expected_charge")
  let limits : Limits := ⟨100000, 100000, 2 ^ 22, 2 ^ 20⟩
  pure <| match evaluate primitive noFailureOrdinal 64 algorithm.term inputs
      maximumCompletionBytes limits with
    | .completed completion charge =>
        beq completion expected && encode completion == expectedHex && charge == expectedCharge
    | _ => false

structure M2Report where
  checkPreimageDecodes : Bool
  guardPreimageDecodes : Bool
  checkPreimageRoundTrips : Bool
  guardPreimageRoundTrips : Bool
  checkTermElaboratesExactly : Bool
  guardTermElaboratesExactly : Bool
  checkCases : Nat
  checkCasesAgree : Bool
  guardCases : Nat
  guardCasesAgree : Bool

def M2Report.toJson (r : M2Report) : Json := Json.mkObj [
  ("check_preimage_decodes", r.checkPreimageDecodes),
  ("guard_preimage_decodes", r.guardPreimageDecodes),
  ("check_preimage_roundtrips", r.checkPreimageRoundTrips),
  ("guard_preimage_roundtrips", r.guardPreimageRoundTrips),
  ("check_term_elaborates_exactly", r.checkTermElaboratesExactly),
  ("guard_term_elaborates_exactly", r.guardTermElaboratesExactly),
  ("check_cases", r.checkCases), ("check_cases_agree", r.checkCasesAgree),
  ("guard_cases", r.guardCases), ("guard_cases_agree", r.guardCasesAgree)
]

def runM2 (j : Json) : Except String M2Report := do
  let algorithms ← readField j "algorithms"
  let check ← m2AlgorithmOfJson (← readField algorithms "check")
  let guard ← m2AlgorithmOfJson (← readField algorithms "guard")
  let primitiveReferences ← readArray (← readField algorithms "check") "primitive_references"
  let some primitiveJson := primitiveReferences[0]? | throw "R1B check has no nat.lt reference"
  let natLtReference ← datumOfJson (← readField primitiveJson "value")
  let some z3 := check.algorithm.inputs[0]? | throw "R1B check has no first input type"
  let some boolean := guard.algorithm.inputs[0]? | throw "R1B guard has no Boolean input type"
  let expectedCheck := finiteSchnorrTerm z3 boolean natLtReference
  let expectedGuard := Term.variable 0 boolean
  let primitive := natLtPrimitive natLtReference boolean
  let checkCases ← readArray j "check_cases"
  let guardCases ← readArray j "guard_cases"
  let checked ← checkCases.mapM fun row =>
    m2CaseAgrees check.algorithm primitive check.maximumCompletionBytes row
  let guarded ← guardCases.mapM fun row =>
    m2CaseAgrees guard.algorithm primitive guard.maximumCompletionBytes row
  pure {
    checkPreimageDecodes := true
    guardPreimageDecodes := true
    checkPreimageRoundTrips := encode (algorithmDatum check.algorithm) == check.preimage
    guardPreimageRoundTrips := encode (algorithmDatum guard.algorithm) == guard.preimage
    checkTermElaboratesExactly := beq (termDatum check.algorithm.term) (termDatum expectedCheck)
    guardTermElaboratesExactly := beq (termDatum guard.algorithm.term) (termDatum expectedGuard)
    checkCases := checked.size
    checkCasesAgree := checked.all id
    guardCases := guarded.size
    guardCasesAgree := guarded.all id
  }

/-! Terminal-contract transport.  JSON remains outside the kernel module; the
runner normalizes predecessor carriers into only the Section 10 coordinates. -/

def jsonBoolField (j : Json) (name : String) : Except String Bool := do
  match ← readField j name with
  | .bool value => pure value
  | _ => throw s!"field {name} is not a Boolean"

def jsonNatList (j : Json) : Except String (List Nat) := do
  match j with
  | .arr values => values.toList.mapM fun value =>
      value.getNat?.mapError toString
  | _ => throw "expected an array of naturals"

def jsonBoolList (j : Json) : Except String (List Bool) := do
  match j with
  | .arr values => values.toList.mapM fun value =>
      match value with
      | .bool boolean => pure boolean
      | _ => throw "expected an array of Booleans"
  | _ => throw "expected an array of Booleans"

def compactConjunction (boolean : ValueType) : List Nat → M0.Term
  | [] => boolLiteral boolean true
  | [input] => .variable input boolean
  | input :: rest =>
      .conditional (.variable input boolean) (compactConjunction boolean rest)
        (boolLiteral boolean false)

def compactContradiction (boolean : ValueType) (input : Nat) : M0.Term :=
  .conditional (.variable input boolean)
    (.conditional (.variable input boolean)
      (boolLiteral boolean false) (boolLiteral boolean true))
    (boolLiteral boolean false)

def compactTermOfJson (boolean : ValueType) (j : Json) : Except String (Option M0.Term) := do
  match j with
  | .null => pure none
  | _ =>
      match ← readString j "kind" with
      | "identity" => pure (some (.variable (← readNat j "input") boolean))
      | "conjunction" =>
          pure (some (compactConjunction boolean (← jsonNatList (← readField j "inputs"))))
      | "true" => pure (some (boolLiteral boolean true))
      | "false" => pure (some (boolLiteral boolean false))
      | "contradiction" =>
          pure (some (compactContradiction boolean (← readNat j "input")))
      | other => throw s!"unknown compact guard term {other}"

def guardInputOfJson (j : Json) : Except String GuardInput := do
  match ← readString j "kind" with
  | "occurrence-output" =>
      pure (.occurrenceOutput (← readNat j "occurrence") (← readNat j "output"))
  | "other" => pure (.other (← readNat j "coordinate"))
  | other => throw s!"unknown Guard input kind {other}"

structure RawTerminalEffect where
  kind : String
  reference : Nat

def rawTerminalEffectOfJson (j : Json) : Except String RawTerminalEffect := do
  pure { kind := ← readString j "kind", reference := ← readNat j "reference" }

def optionalGuardAtomOfJson (j : Json) : Except String AttemptGuard := do
  match ← readField j "guard_atom" with
  | .null => pure .always
  | value => pure (.evaluate (← value.getNat?.mapError toString))

def scheduledOccurrenceOfJson (j : Json) : Except String ScheduledOccurrence := do
  let effect ← rawTerminalEffectOfJson (← readField j "effect")
  pure {
    openingsBefore := ← jsonNatList (← readField j "openings_before")
    guard := ← optionalGuardAtomOfJson j
    isTerminal := effect.kind == "terminal"
  }

def positionsOfKind (effects : List RawTerminalEffect) (kind : String)
    (reference : Nat) : List Nat :=
  (List.range effects.length).filter fun index =>
    match effects[index]? with
    | some effect => effect.kind == kind && effect.reference == reference
    | none => false

def uniquePosition? (effects : List RawTerminalEffect) (kind : String)
    (reference : Nat) : Option Nat :=
  match positionsOfKind effects kind reference with
  | [position] => some position
  | _ => none

def resolvePositions (effects : List RawTerminalEffect) (kind : String)
    (references : List Nat) : List Nat :=
  references.map fun reference =>
    (uniquePosition? effects kind reference).getD (effects.length + reference + 1)

def scopeOpeningOfJson (j : Json) : Except String ScopeOpening := do
  match ← readString j "kind" with
  | "initially" => pure .initially
  | "before-occurrence" => pure (.beforeOccurrence (← readNat j "occurrence"))
  | other => throw s!"unknown scope opening kind {other}"

def claimSourceOfJson (j : Json) : Except String AbstractClaimSource := do
  match ← readString j "kind" with
  | "initial-claim" =>
      pure (.initialClaim (← readNat j "binding") (← readNat j "scope")
        (← scopeOpeningOfJson (← readField j "opening")))
  | "reduction-output" =>
      pure (.reductionOutput (← readNat j "reduction") (← readNat j "output")
        (← readNat j "occurrence"))
  | other => throw s!"unknown claim source kind {other}"

def abstractClaimOfJson (j : Json) : Except String AbstractClaim := do
  pure {
    reference := ← readNat j "reference"
    source := ← claimSourceOfJson (← readField j "source")
    linearConsumers := ← jsonNatList (← readField j "linear_consumers")
  }

def claimAvailableBefore (occurrence : Nat) (claim : AbstractClaim) : Bool :=
  match claim.source with
  | .initialClaim _binding _scope .initially => true
  | .initialClaim _binding _scope (.beforeOccurrence boundary) =>
      decide (boundary ≤ occurrence)
  | .reductionOutput _reduction _outputOrdinal source => decide (source < occurrence)

def availableClaims (claims : List AbstractClaim) (occurrence : Nat) :
    List AbstractClaim :=
  claims.filter (claimAvailableBefore occurrence)

def openingBeforeDecision (schedule : List ScheduledOccurrence)
    (boundary scope : Nat) : Bool :=
  match schedule[boundary]? with
  | some row => row.openingsBefore.contains scope
  | none => false

def claimWellFormedAtDecision (schedule : List ScheduledOccurrence)
    (claim : AbstractClaim) (occurrence : Nat) : Bool :=
  (match claim.source with
   | .initialClaim _binding scope .initially => scope == 0
   | .initialClaim _binding scope (.beforeOccurrence boundary) =>
       decide (boundary ≤ occurrence) && openingBeforeDecision schedule boundary scope
   | .reductionOutput _reduction _outputOrdinal source =>
       decide (source < occurrence) && schedule[source]?.isSome) &&
  (earlierLinearConsumers claim occurrence).all fun consumer =>
    schedule[consumer]?.isSome

def terminalViewOfJson (boolean : ValueType) (effects : List RawTerminalEffect)
    (j : Json) : Except String TerminalView := do
  let terminal ← readNat j "reference"
  let guardInputs ← (← readArray j "guard_inputs").toList.mapM guardInputOfJson
  pure {
    terminal
    occurrence := (uniquePosition? effects "terminal" terminal).getD
      (effects.length + terminal + 1)
    guardTerm := ← compactTermOfJson boolean (← readField j "guard_term")
    guardInputs
    guardInputIsBoolean := ← jsonBoolList (← readField j "guard_input_is_boolean")
    requiredChecks := resolvePositions effects "check"
      (← jsonNatList (← readField j "required_checks"))
    requiredReductions := resolvePositions effects "reduction"
      (← jsonNatList (← readField j "required_reductions"))
    terminalClaims := ← jsonNatList (← readField j "terminal_claims")
  }

def exactTerminalBacklinks (effects : List RawTerminalEffect)
    (terminalReferences : List Nat) : Bool :=
  let occurred := effects.filterMap fun effect =>
    if effect.kind == "terminal" then some effect.reference else none
  occurred.length == terminalReferences.length &&
    terminalReferences.all fun reference =>
      (positionsOfKind effects "terminal" reference).length == 1

def finalFallback (schedule : List ScheduledOccurrence)
    (effects : List RawTerminalEffect) : Bool :=
  match schedule.getLast?, effects.getLast? with
  | some occurrence, some effect =>
      effect.kind == "terminal" && occurrence.guard == .always
  | _, _ => false

def natListJson (row : List Nat) : Json :=
  Json.arr (row.toArray.map fun value => Json.num (JsonNumber.fromNat value))

def claimJudgmentName : ClaimJudgment → String
  | .live => "Live"
  | .dead => "Dead"
  | .unknown => "Unknown"

structure TerminalRowReport where
  reference : Nat
  decision : Bool
  regionImpossible : Bool
  claimBindingsWellFormed : Bool
  liveClaims : List Nat
  claimStatuses : List (Nat × ClaimJudgment × ClaimJudgment)

def TerminalRowReport.toJson (row : TerminalRowReport) : Json :=
  Json.mkObj [
    ("reference", row.reference),
    ("decision", row.decision),
    ("region_impossible", row.regionImpossible),
    ("claim_bindings_well_formed", row.claimBindingsWellFormed),
    ("live_claims", natListJson row.liveClaims),
    ("claim_statuses", Json.arr (row.claimStatuses.toArray.map fun status =>
      Json.mkObj [
        ("reference", status.1),
        ("status", claimJudgmentName status.2.1),
        ("occurrence_coercion_status", claimJudgmentName status.2.2)
      ]))
  ]

structure TerminalCarrierReport where
  name : String
  family : String
  predecessorOutcome : String
  representable : Bool
  admitted : Option Bool
  backlinkExact : Bool
  finalFallback : Bool
  claimBindingsWellFormed : Bool
  terminalRows : List TerminalRowReport

def TerminalCarrierReport.toJson (report : TerminalCarrierReport) : Json :=
  Json.mkObj [
    ("name", report.name), ("family", report.family),
    ("predecessor_outcome", report.predecessorOutcome),
    ("representable", report.representable),
    ("admitted", match report.admitted with
      | some value => Json.bool value
      | none => Json.null),
    ("backlink_exact", report.backlinkExact),
    ("final_fallback", report.finalFallback),
    ("claim_bindings_well_formed", report.claimBindingsWellFormed),
    ("terminals", Json.arr (report.terminalRows.toArray.map TerminalRowReport.toJson))
  ]

def runTerminalCarrier (j : Json) : Except String TerminalCarrierReport := do
  let name ← readString j "name"
  let family ← readString j "family"
  let predecessorOutcome ← readString j "predecessor_outcome"
  let representable ← jsonBoolField j "representable"
  if !representable then
    pure {
      name := name
      family := family
      predecessorOutcome := predecessorOutcome
      representable := false
      admitted := none
      backlinkExact := false
      finalFallback := false
      claimBindingsWellFormed := false
      terminalRows := []
    }
  else
    let occurrenceRows ← readArray j "schedule"
    let schedule ← occurrenceRows.toList.mapM scheduledOccurrenceOfJson
    let effects ← occurrenceRows.toList.mapM fun row => do
      rawTerminalEffectOfJson (← readField row "effect")
    let claimJson ← readArray j "claims"
    let claims ← claimJson.toList.mapM abstractClaimOfJson
    let terminalJson ← readArray j "terminals"
    let boolean : ValueType := .mk .unit .bool
    let terminals ← terminalJson.toList.mapM (terminalViewOfJson boolean effects)
    let terminalReferences := terminals.map (·.terminal)
    let backlinkExact := exactTerminalBacklinks effects terminalReferences
    let fallback := finalFallback schedule effects
    let terminalRows := terminals.map fun terminal =>
      let localClaims := availableClaims claims terminal.occurrence
      let wellFormed := localClaims.all fun claim =>
        claimWellFormedAtDecision schedule claim terminal.occurrence
      {
        reference := terminal.terminal
        decision := wellFormed && terminalAdmissionDecision schedule localClaims terminal
        regionImpossible := (Region schedule terminal.occurrence).impossible
        claimBindingsWellFormed := wellFormed
        liveClaims := LiveClaims schedule localClaims terminal.occurrence
        claimStatuses := localClaims.map fun claim =>
          (claim.reference, ClaimStatus schedule claim terminal.occurrence,
            OccurrenceCoercionClaimStatus schedule claim terminal.occurrence)
      }
    let claimBindingsWellFormed := terminalRows.all (·.claimBindingsWellFormed)
    let admitted := backlinkExact && fallback && claimBindingsWellFormed &&
      terminalRows.all (·.decision)
    pure {
      name := name
      family := family
      predecessorOutcome := predecessorOutcome
      representable := true
      admitted := some admitted
      backlinkExact := backlinkExact
      finalFallback := fallback
      claimBindingsWellFormed := claimBindingsWellFormed
      terminalRows := terminalRows
    }

def unnamedConstructorsUnknown : Bool :=
  let unit : ValueType := .mk .unit .unit
  let literal : M0.Term := .literal ⟨unit, .unit⟩
  let failure : FailureType := { declaration := .unit, payloadType := unit }
  let terms : List M0.Term := [
    .recordConstruct [],
    .project literal 0,
    .inject 0 literal (.mk .unit (.variant [(0, unit)])),
    .caseE literal [],
    .sequenceConstruct unit [] 0,
    .sequenceLength literal,
    .fail failure literal unit,
    .strictIndex literal literal failure,
    .boundedAppend literal literal failure,
    .boundedIterate (.range literal) literal literal
  ]
  terms.all fun term => Must term [] == MustResult.unknown

def terminalLawReport : Json :=
  let boolean : ValueType := .mk .unit .bool
  Json.mkObj [
    ("non_boolean_input_has_no_literal", InputMust 0 false == MustResult.unknown),
    ("contradictory_union_is_impossible",
      FactSet.union (.possible [.positive 0]) (.possible [.negative 0]) == .impossible),
    ("contradictory_guard_is_impossible",
      MustWhenTrue (compactContradiction boolean 0) [true] == .impossible),
    ("unnamed_constructors_have_no_literals", unnamedConstructorsUnknown)
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
  let m2 ← match runM2 (← match readField input "m2" with
      | .ok value => pure value
      | .error e => throw (IO.userError e)) with
    | .ok report => pure report
    | .error e => throw (IO.userError s!"m2: {e}")
  let terminalRows ← run "terminal" runTerminalCarrier TerminalCarrierReport.toJson
  let report := Json.mkObj [
    ("lean_version", Json.str Lean.versionString),
    ("natural_boundary", naturalBoundaryReport),
    ("encode", Json.arr encodeRows),
    ("reject", Json.arr rejectRows),
    ("pcgraph_construction", Json.arr constructionRows),
    ("m2", m2.toJson),
    ("terminal_laws", terminalLawReport),
    ("terminal", Json.arr terminalRows)
  ]
  IO.println report.compress
  return 0
