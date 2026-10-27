module

public import Zkc.Source.Structured.ContractCalls
public import Zkc.Source.Structured.Format

@[expose] public section

/-! Bounded structural component routes. This traversal uses retained declarations
and the admitted original syntax. Its result is association data, not a proof of
any relation, totality, terminal adequacy, or protocol security. -/
namespace Zkc.Source.Structured

inductive SeamRoute where
  | input (port : Nat) (role : String)
  | result (site : String) (port : Nat) (role : String)
  | repeatInput (site : String) (port : Nat) (role : String)
  | repeatResult (site : String) (port : Nat) (role : String)
  | pure (operation : Descriptor) (position : List Nat) (port : Nat) (role : String)
      (arguments : List SeamRoute)
  | terminal (operation : Descriptor) (position : List Nat) (port : Nat) (role : String)
      (arguments : List SeamRoute)
  | action (operation : Descriptor) (position : List Nat) (port : Nat) (role : String)
      (arguments : List SeamRoute)
  deriving Repr

/-! Route association is kernel checked. Nested derived Boolean equality is
opaque to reduction, so both equality interfaces use structural recursion. -/
mutual
  def SeamRoute.decEq (first second : SeamRoute) : Decidable (first = second) := by
    cases first <;> cases second
    all_goals try exact isFalse (SeamRoute.noConfusion ·)
    case input.input a b c d =>
      exact decidable_of_iff (a = c ∧ b = d) (by simp only [SeamRoute.input.injEq])
    case result.result a b c d e f =>
      exact decidable_of_iff (a = d ∧ b = e ∧ c = f) (by simp only [SeamRoute.result.injEq])
    case repeatInput.repeatInput a b c d e f =>
      exact decidable_of_iff (a = d ∧ b = e ∧ c = f) (by simp only [SeamRoute.repeatInput.injEq])
    case repeatResult.repeatResult a b c d e f =>
      exact decidable_of_iff (a = d ∧ b = e ∧ c = f) (by simp only [SeamRoute.repeatResult.injEq])
    case pure.pure a b c d arguments e f g h other =>
      letI : Decidable (arguments = other) := seamRoutesDecEq arguments other
      exact decidable_of_iff (a = e ∧ b = f ∧ c = g ∧ d = h ∧ arguments = other)
        (by simp only [SeamRoute.pure.injEq])
    case terminal.terminal a b c d arguments e f g h other =>
      letI : Decidable (arguments = other) := seamRoutesDecEq arguments other
      exact decidable_of_iff (a = e ∧ b = f ∧ c = g ∧ d = h ∧ arguments = other)
        (by simp only [SeamRoute.terminal.injEq])
    case action.action a b c d arguments e f g h other =>
      letI : Decidable (arguments = other) := seamRoutesDecEq arguments other
      exact decidable_of_iff (a = e ∧ b = f ∧ c = g ∧ d = h ∧ arguments = other)
        (by simp only [SeamRoute.action.injEq])

  def seamRoutesDecEq : (first second : List SeamRoute) → Decidable (first = second)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro same; cases same)
    | _ :: _, [] => isFalse (by intro same; cases same)
    | first :: rest, second :: others => by
      letI : Decidable (first = second) := SeamRoute.decEq first second
      letI : Decidable (rest = others) := seamRoutesDecEq rest others
      exact decidable_of_iff (first = second ∧ rest = others) (by simp only [List.cons.injEq])
end

instance : DecidableEq SeamRoute := SeamRoute.decEq
instance : BEq SeamRoute := ⟨fun first second => decide (first = second)⟩
instance : LawfulBEq SeamRoute where
  eq_of_beq := of_decide_eq_true
  rfl := by intro value; exact decide_eq_true rfl

inductive SeamEndpoint where
  | argument (site : String) (port : Nat)
  | residual (port : Nat)
  | output (port clause : Nat)
  | guard (site role : String)
  | repeatInit (site : String) (port : Nat) (role : String)
  | repeatInput (site : String) (port : Nat) (role : String)
  | yield (site : String) (port : Nat) (role : String)
  | repeatResult (site : String) (port : Nat) (role : String)
  deriving BEq, Repr

inductive SeamKind where
  | direct | pure | terminal | method
  deriving BEq, Repr

structure SeamRow where
  caller : String
  endpoint : SeamEndpoint
  kind : SeamKind
  routes : List SeamRoute
  deriving BEq, Repr

/-- Search choices remain distinct from runtime operands. In particular `open`
never supplies a default value, and `operand` never becomes a public parameter
without an explicit instantiation of the existing logical assignment. -/
inductive InstantiationSource where
  | open
  | operand (port : Nat) (role : String)
  | parameter (selector : ContractSelector)
  | witness (selector : ContractSelector)
  | result (site : String) (port : Nat) (role : String)
  | math (helper : String) (port : Nat) (arguments : List InstantiationSource)
  deriving Repr

/- Proposal equality must reduce in the kernel just like route equality. -/
mutual
  def InstantiationSource.decEq (first second : InstantiationSource) : Decidable (first = second) := by
    cases first <;> cases second
    all_goals try exact isFalse (InstantiationSource.noConfusion ·)
    case open.open => exact isTrue rfl
    case operand.operand a b c d =>
      exact decidable_of_iff (a = c ∧ b = d) (by simp only [InstantiationSource.operand.injEq])
    case parameter.parameter a b =>
      exact decidable_of_iff (a = b) (by simp only [InstantiationSource.parameter.injEq])
    case witness.witness a b =>
      exact decidable_of_iff (a = b) (by simp only [InstantiationSource.witness.injEq])
    case result.result a b c d e f =>
      exact decidable_of_iff (a = d ∧ b = e ∧ c = f) (by simp only [InstantiationSource.result.injEq])
    case math.math a b arguments c d other =>
      letI : Decidable (arguments = other) := instantiationSourcesDecEq arguments other
      exact decidable_of_iff (a = c ∧ b = d ∧ arguments = other)
        (by simp only [InstantiationSource.math.injEq])

  def instantiationSourcesDecEq : (first second : List InstantiationSource) → Decidable (first = second)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro same; cases same)
    | _ :: _, [] => isFalse (by intro same; cases same)
    | first :: rest, second :: others => by
      letI : Decidable (first = second) := InstantiationSource.decEq first second
      letI : Decidable (rest = others) := instantiationSourcesDecEq rest others
      exact decidable_of_iff (first = second ∧ rest = others) (by simp only [List.cons.injEq])
end

instance : DecidableEq InstantiationSource := InstantiationSource.decEq
instance : BEq InstantiationSource := ⟨fun first second => decide (first = second)⟩
instance : LawfulBEq InstantiationSource where
  eq_of_beq := of_decide_eq_true
  rfl := by intro value; exact decide_eq_true rfl

structure InstantiationSlot where
  purpose : String
  selector : ContractSelector
  source : InstantiationSource
  deriving BEq, Repr

structure CallProposal where
  caller : String
  site : String
  callee : String
  operands : List Nat
  roles : List String
  slots : List InstantiationSlot
  deriving BEq, Repr

namespace ComponentRoutes

structure Flow where
  route : SeamRoute
  pending : List SeamRoute := []
  effect : Option String := none
  decision : Bool := false
  nodes : Nat := 1
  height : Nat := 1
  deriving Repr

abbrev Family := List (String × Flow)
abbrev Environment := List Family

structure ActionResults where
  site : String
  types : List Ty
  scopes : List (List String)
  offset : Nat := 0
  deriving Repr

/-- A proposal is checked where it occurs, retaining dominance and source types. -/
structure ProposalContext where
  proposal : CallProposal
  caller : Function
  visible : List ActionResults
  types : List Ty
  deriving Repr

structure Result where
  seams : List SeamRow := []
  calls : List ProposalContext := []
  visits : Nat := 0
  deriving Repr

abbrev Derive := StateT Result (Except String)

def charge (work : Nat := 1) : Derive Unit := do
  let state ← get
  if state.visits + work > 100000 then throw "component-seam-limit"
  set { state with visits := state.visits + work }

def function (snapshot : Snapshot) (name : String) : Except String Function :=
  requireSome (snapshot.definitions.findSome? fun
    | .function value => if value.name == name then some value else none
    | _ => none) "component-seam-call"

def helper (snapshot : Snapshot) (name : String) : Except String Function := do
  match snapshot.definitions.find? (·.name == name) with
  | some (.function value) => return value
  | some (.realization value) => function snapshot value.helper
  | some (.map value) => function snapshot value.helper
  | _ => throw "component-seam-call"

def contract (snapshot : Snapshot) (name : String) : Except String ProtocolContract :=
  requireSome (snapshot.contracts.find? (·.owner == name)) "component-seam-call"

def sourcePorts (snapshot : Snapshot) (name : String) (output : Bool) : List SourcePort :=
  match snapshot.sourceDeclarations.protocols.find? (·.name == name) with
  | none => []
  | some source => if output then source.outputs else source.inputs

def pendingPort (snapshot : Snapshot) (port : SourcePort) : Bool :=
  snapshot.sourceDeclarations.isLinear port.type

def pendingAt (snapshot : Snapshot) (ports : List SourcePort) (index : Nat) : Bool :=
  ports.any fun port => port.offset ≤ index && index < port.offset + port.count && pendingPort snapshot port

def leaf (route : SeamRoute) (pending : Bool := false) : Flow :=
  ⟨route, if pending then [route] else [], none, false, 1, 1⟩

def read (environment : Environment) (index : Nat) (role : String) : Except String Flow := do
  let family ← requireSome environment[index]? "component-seam-reference"
  return (← requireSome (family.find? (·.1 == role)) "component-seam-role").2

def methodEffect (code : String) : Bool :=
  code == "component-seam-sampling" || code == "component-seam-message"

/-- Refusals dominate method effects. Otherwise the existing effect wins;
each boundary input changes at most twice when closing carried backedges. -/
def joinEffect (first second : Option String) : Option String :=
  (first.filter (!methodEffect ·)).orElse (fun _ => second.filter (!methodEffect ·)) |>.orElse
    (fun _ => first.orElse (fun _ => second))

def pureFlow (flow : Flow) (method : Bool := false) : Except String Unit :=
  match flow.effect with
  | none => .ok ()
  | some code => if method && methodEffect code then .ok () else .error code

def consume (flows : List Flow) (live : List SeamRoute) (method : Bool := false) : Except String (List SeamRoute) := do
  let mut used : List SeamRoute := []
  let mut projections : List SeamRoute := []
  for flow in flows do
    pureFlow flow method
    unless flow.pending.isEmpty do
      if projections.contains flow.route then throw "component-seam-coverage"
      projections := flow.route :: projections
    used := (used ++ flow.pending).eraseDups
  let mut live := live
  for value in used do
    unless live.contains value do throw "component-seam-coverage"
    live := live.filter (· != value)
  return live

def direct : SeamRoute → Bool
  | .input .. | .result .. | .repeatInput .. | .repeatResult .. => true
  | _ => false

def row (caller : String) (endpoint : SeamEndpoint) (flows : List Flow)
    (kind : Option SeamKind := none) : Derive Unit := do
  let routes := flows.map (·.route)
  let value : SeamRow := ⟨caller, endpoint,
    kind.getD (if flows.any (·.effect.isSome) then .method else
      if routes.all direct then .direct else .pure), routes⟩
  modify fun state => { state with seams := state.seams ++ [value] }

def inputs (snapshot : Snapshot) (owner : Function) : Except String Environment := do
  let interface ← requireSome owner.interface "component-seam-role"
  return (List.range owner.inputs.length).map fun index =>
    (interface.inputScopes[index]?.getD []).map fun role =>
      (role, leaf (.input index role) (pendingAt snapshot (sourcePorts snapshot owner.name false) index))

def liveOf (environment : Environment) : List SeamRoute :=
  (environment.flatMap fun family => family.flatMap (·.2.pending)).eraseDups

def slots (snapshot : Snapshot) (owner : String) : Except String (List InstantiationSlot) := do
  let mut result := []
  for clause in (← contract snapshot owner).clauses do
    for application in clause.subject :: clause.residual.toList do
      let relation ← requireSome (snapshot.relations.find? (·.name == application.relation))
        "component-instantiation"
      for (selector, purpose) in application.selectors.zip relation.purposes do
        if purpose != "statement" then
          let slot : InstantiationSlot := ⟨purpose, selector, .open⟩
          unless result.contains slot do
            if result.length == 512 then throw "component-instantiation-limit"
            result := result ++ [slot]
  return result

/-- Reuse the existing typed primitive admission, including its binding. -/
def purePrimitive (snapshot : Snapshot) : Descriptor → Bool
  | .exec operation binding parameters => (resolvePrimitive snapshot operation binding parameters).isOk
  | _ => false

/-- Resolve the actual admitted domain and every finite callback. The predicate
is inspected even if no element would reach the body at runtime. -/
def finiteHelpers (snapshot : Snapshot) (domain body predicate : String) :
    Except String (List Function) := do
  unless snapshot.domains.any (·.name == domain) do throw "component-seam-call"
  let body ← function snapshot body
  if predicate.isEmpty then return [body]
  return [body, ← function snapshot predicate]

/-- Apply descriptors name admitted computation declarations, not guessed
primitive names. Maps retain their actual helper and its possible stops. -/
def computationHelpers (snapshot : Snapshot) (name : String) :
    Except String (List Function) := do
  match snapshot.definitions.find? (·.name == name) with
  | some (.function value) => return [value]
  | some (.realization value) => return [← function snapshot value.helper]
  | some (.map value) => return [← function snapshot value.helper]
  | some (.finite value) => finiteHelpers snapshot value.domain value.step value.predicate
  | some (.collect value) => finiteHelpers snapshot value.domain value.body value.predicate
  | _ => throw "component-seam-call"

/-- Math relies on whole-unit admission; Local exposes its actual body. This
lookup consumes no work and makes no totality or successful-return claim. -/
def inventoryBody : Nat → Function → Except String (Option Block)
  | 0, _ => .error "component-seam-depth"
  | _ + 1, owner =>
    if owner.kind == .math then .ok none
    else if owner.kind == .local then .ok (some owner.body)
    else .error "component-seam-effect"

/-- Inventory every stored region and actual callback. Recursion is structural
on the same depth budget as native admission, so kernel reduction and ordinary
execution use the same scanner. -/
def deterministicBody (snapshot : Snapshot) : Nat → Block → Derive Unit
  | 0, _ => throw "component-seam-depth"
  | fuel + 1, .block instructions _ => do
    for instruction in instructions do
      charge
      let .instruction descriptor _ _ regions _ := instruction
      unless regions.isEmpty || descriptor == .branch || descriptor == .loop ||
          descriptor == .loopCondition do throw "component-seam-control"
      match descriptor with
      | .draw .. => throw "component-seam-sampling"
      | .exchange .. => throw "component-seam-message"
      | .exec operation _ _ =>
        unless purePrimitive snapshot descriptor do
          throw (if operation.startsWith "oracle." then "component-seam-oracle" else "component-seam-effect")
      | .protocolApply .. | .protocolRepeat .. => throw "component-seam-effect"
      | .call name | .localCall name _ =>
        if let some body ← inventoryBody fuel (← function snapshot name) then
          deterministicBody snapshot fuel body
      | .apply name =>
        for callback in (← computationHelpers snapshot name) do
          if let some body ← inventoryBody fuel callback then deterministicBody snapshot fuel body
      | .fold domain body predicate =>
        for callback in (← finiteHelpers snapshot domain body predicate) do
          if let some body ← inventoryBody fuel callback then deterministicBody snapshot fuel body
      | _ => pure ()
      for region in regions do
        let .region _ _ body := region
        deterministicBody snapshot fuel body

def deterministic (snapshot : Snapshot) (fuel : Nat) (owner : Function) : Derive Unit := do
  if let some body ← inventoryBody fuel owner then deterministicBody snapshot fuel body

def aggregate (flows : List Flow) : Flow :=
  ⟨.input 0 "", (flows.flatMap (·.pending)).eraseDups,
    flows.foldl (fun effect flow => joinEffect effect flow.effect) none, false,
    1 + (flows.map (·.nodes)).sum, 1 + (flows.map (·.height)).foldl max 0⟩

/-- A Local helper remains a pure map at handoffs, including Boolean Pending
repacking. At an acceptance sink only actual conjunction paths select terminal
helpers. This selection supplies no adequacy or successful-return theorem. -/
def acceptance : Nat → SeamRoute → SeamRoute
  | 0, route => route
  | _ + 1, .pure (.localCall name holder) position port role arguments =>
      .terminal (.localCall name holder) position port role arguments
  | _ + 1, .pure (.call name) position port role arguments =>
      .terminal (.call name) position port role arguments
  | fuel + 1, .pure .booleanAnd position port role arguments =>
      .pure .booleanAnd position port role (arguments.map (acceptance fuel))
  | _ + 1, route => route

/-- Body and callback traversal share the same finite capacity. A repeat has
separate initialization and yield routes, and retains both result alternatives. -/
def block (snapshot : Snapshot) (owner : Function) : Nat → Block → List Ty → Environment →
    List SeamRoute → List Nat → List ActionResults → Derive (List Family)
  | 0, _, _, _, _, _, _ => throw "component-seam-depth"
  | fuel + 1, .block instructions terminator, initialTypes, initial, initialLive, path, initialVisible => do
    let interface ← requireSome owner.interface "component-seam-role"
    let mut environment := initial
    let mut typesInScope := initialTypes
    let mut live := initialLive
    let mut guarded : List SeamRoute := []
    let mut visible := initialVisible
    for (instruction, ordinal) in instructions.zipIdx do
      charge
      let .instruction descriptor args types regions site := instruction
      let position := path ++ [ordinal]
      let mut results : Environment := List.replicate types.length []
      match descriptor with
      | .protocolApply name actualRoles =>
        let callee ← function snapshot name
        let child ← requireSome callee.interface "component-seam-role"
        let actual := fun role => (child.roles.zip actualRoles).lookup role |>.getD ""
        for (port, portIndex) in (sourcePorts snapshot name false).zipIdx do
          if pendingPort snapshot port then
            let flows ← (List.range port.count).mapM fun index => do
              let arg ← requireSome args[port.offset + index]? "component-seam-reference"
              read environment arg (actual (port.roles.headD ""))
            row owner.name (.argument site portIndex) flows
            live ← consume flows live true
        let clauses := (← contract snapshot name).clauses
        results ← (List.range types.length).mapM fun index => do
          return (child.outputScopes[index]?.getD []).map fun role =>
            let value := leaf (.result site index (actual role))
              (pendingAt snapshot (sourcePorts snapshot name true) index)
            let decision := clauses.any fun clause => clause.decision.any fun selected =>
              selected.port == index && selected.role == role
            (actual role, { value with decision })
        live := (live ++ liveOf results).eraseDups
        let proposal : CallProposal := ⟨owner.name, site, name, args, actualRoles, ← slots snapshot name⟩
        modify fun state => { state with calls := state.calls ++ [⟨proposal, owner, visible, typesInScope⟩] }
      | .protocolRepeat carried _ _ scopes =>
        let [.region innerTypes _ body] := regions | throw "component-seam-control"
        let mut inner : Environment := []
        let mut marked := List.replicate args.length false
        let mut initialFlows := []
        let countIndex ← requireSome args.head? "component-seam-reference"
        let countFamily ← requireSome environment[countIndex]? "component-seam-reference"
        let count := aggregate (countFamily.map Prod.snd)
        for (argument, index) in args.zipIdx do
          let family ← requireSome environment[argument]? "component-seam-reference"
          let mut values : Family := []
          for (role, flow) in family do
            let pending := index > 0 && index ≤ carried && !flow.pending.isEmpty
            if index > 0 && index ≤ carried then
              row owner.name (.repeatInit site (index - 1) role) [flow]
            if pending then
              initialFlows := initialFlows ++ [flow]
              marked := marked.set index true
            else unless flow.pending.isEmpty do throw "component-seam-control"
            let input := leaf (.repeatInput site index role) pending
            values := values ++ [(role, { input with effect :=
              if index == 0 then flow.effect else joinEffect flow.effect count.effect })]
          inner := inner ++ [values]
        live ← consume initialFlows live true
        let carriedFlows := ((inner.drop 1).take carried).map List.length |>.sum
        let mut stable := false
        let mut yielded := []
        -- Derive candidate rows using the same traversal. Only the stable
        -- candidate is retained, but every candidate's work is charged.
        for _ in List.range (2 * carriedFlows + 1) do
          unless stable do
            let state ← get
            let (candidate, derived) ← (block snapshot owner fuel body innerTypes inner
              (liveOf inner) (position ++ [0]) []).run state
            if candidate.length != carried then throw "component-seam-control"
            yielded := candidate
            stable := true
            for index in List.range carried do
              let family ← requireSome inner[index + 1]? "component-seam-reference"
              let mut updated := []
              for (role, input) in family do
                let output ← read yielded index role
                let effect := joinEffect input.effect output.effect
                if effect != input.effect then stable := false
                updated := updated ++ [(role, { input with effect })]
              inner := inner.set (index + 1) updated
            if stable then set derived else set { state with visits := derived.visits }
        unless stable do throw "component-seam-limit"
        -- Associate fresh boundary leaves with source, count control and
        -- carried backedges, including ordinary values and captures.
        for (argument, index) in args.zipIdx do
          let family ← requireSome environment[argument]? "component-seam-reference"
          for (role, flow) in family do
            let mut dependencies := [flow]
            if index > 0 then dependencies := dependencies ++ countFamily.map Prod.snd
            if index > 0 && index ≤ carried then
              dependencies := dependencies ++ [← read yielded (index - 1) role]
            row owner.name (.repeatInput site index role) dependencies
        results ← (List.range carried).mapM fun index => do
          (scopes[index]?.getD []).mapM fun role => do
            let flow ← read yielded index role
            let pending := marked[index + 1]?.getD false
            let argument ← requireSome args[index + 1]? "component-seam-reference"
            let initial ← read environment argument role
            let controlled := { flow with effect := joinEffect flow.effect count.effect }
            row owner.name (.yield site index role) [controlled]
            row owner.name (.repeatResult site index role) [initial, controlled]
            let result := leaf (.repeatResult site index role) pending
            return (role, { result with effect := joinEffect (joinEffect initial.effect count.effect) flow.effect })
        live := (live ++ liveOf results).eraseDups
      | .statement .. => pure ()
      | .guard role =>
        let argument ← requireSome args.head? "component-seam-reference"
        let flow ← read environment argument role
        unless flow.pending.isEmpty do
          row owner.name (.guard site role) [flow] (some .method)
          pureFlow flow true
          for pending in flow.pending do
            unless live.contains pending do throw "component-seam-coverage"
          guarded := (guarded ++ flow.pending).eraseDups
      | descriptor =>
        unless regions.isEmpty do throw "component-seam-control"
        for role in interface.roles do
          let allowed := match descriptor with
            | .restrict roles => roles.contains role
            | .localCall _ holder | .draw holder _ => holder == role
            | .exchange _ receiver => receiver == role
            | _ => true
          if allowed then
            let mut operands := []
            let mut available := true
            for argument in args do
              let family ← requireSome environment[argument]? "component-seam-reference"
              let sourceRole := match descriptor with | .exchange sender _ => sender | _ => role
              match family.lookup sourceRole with
              | none => available := false
              | some flow => operands := operands ++ [flow]
            if available then
              let mut base := aggregate operands
              if base.height > 64 then throw "component-seam-depth"
              charge (base.nodes * types.length)
              match descriptor with
              | .draw .. | .exchange .. =>
                if base.effect.all methodEffect then
                  base := { base with effect := some (match descriptor with
                    | .draw .. => "component-seam-sampling" | _ => "component-seam-message") }
              | .exec operation _ _ =>
                unless purePrimitive snapshot descriptor do
                  base := { base with effect := some (if operation.startsWith "oracle." then
                    "component-seam-oracle" else "component-seam-effect") }
              | .apply .. | .fold .. => base := { base with effect := some "component-seam-effect" }
              | .call name =>
                if (← function snapshot name).kind != .math then
                  base := { base with effect := some "component-seam-effect" }
              | .localCall name _ => deterministic snapshot 65 (← function snapshot name)
              | _ => pure ()
              for (type, index) in types.zipIdx do
                let route := match descriptor with
                  | .restrict _ => (operands.headD base).route
                  | .localCall .. => if base.pending.isEmpty && base.effect.isNone then .result site index role else
                    .pure descriptor position index role (operands.map (·.route))
                  | .draw .. | .exchange .. => .action descriptor position index role (operands.map (·.route))
                  | _ => .pure descriptor position index role (operands.map (·.route))
                let decision := match descriptor with
                  | .localCall .. | .call .. => type == .boolean
                  | .booleanAnd => operands.all fun operand => operand.decision || operand.pending.isEmpty
                  | _ => false
                let pending := match descriptor with
                  | .localCall .. => if base.pending.isEmpty then [] else (base.pending ++ [route]).eraseDups
                  | _ => base.pending
                if let .localCall .. := descriptor then
                  unless base.pending.isEmpty do live := (live ++ [route]).eraseDups
                results := results.set index (results[index]?.getD [] ++ [(role, { base with route, decision, pending })])
      environment := results ++ environment
      typesInScope := types ++ typesInScope
      visible := visible.map (fun action => { action with offset := action.offset + types.length }) ++
        [⟨site, types, results.map (List.map Prod.fst), 0⟩]
    match terminator with
    | .stop .. => return []
    | .condition .. => throw "component-seam-control"
    | .ret indices | .yield indices =>
      let returned ← indices.mapM fun index => requireSome environment[index]? "component-seam-reference"
      match terminator with
      | .yield _ =>
        live ← consume ((returned.flatMap (List.map Prod.snd)).filter (!·.pending.isEmpty)) live true
      | _ =>
        for (port, portIndex) in (sourcePorts snapshot owner.name true).zipIdx do
          if pendingPort snapshot port then
            let flows ← (List.range port.count).mapM fun index => read returned (port.offset + index) (port.roles.headD "")
            row owner.name (.residual portIndex) flows
            live ← consume flows live true
        let mut acceptedOutputs : List (Nat × String) := []
        for (clause, clauseIndex) in (← contract snapshot owner.name).clauses.zipIdx do
          if let some decision := clause.decision then
            let flow ← read returned decision.port decision.role
            unless flow.pending.isEmpty do
              unless flow.decision do throw "component-seam-acceptance"
              pureFlow flow
              unless acceptedOutputs.contains (decision.port, decision.role) do
                live ← consume [flow] live
                acceptedOutputs := (decision.port, decision.role) :: acceptedOutputs
              row owner.name (.output decision.port clauseIndex) [{ flow with route := acceptance 65 flow.route }] (some .terminal)
      unless (live.filter (!guarded.contains ·)).isEmpty do throw "component-seam-coverage"
      return returned

def derive (snapshot : Snapshot) : Except String Result := do
  if !(snapshot.sourceDeclarations.records.any (·.resource == "linear")) then return {}
  let owners := snapshot.protocolFunctions
  let (_, result) ← (do
    for owner in owners.mergeSort (fun left right => left.name ≤ right.name) do
      let environment ← inputs snapshot owner
      let _ ← block snapshot owner 65 owner.body owner.inputs environment (liveOf environment) [] []
    : Derive Unit).run {}
  return result

end ComponentRoutes
end Zkc.Source.Structured
