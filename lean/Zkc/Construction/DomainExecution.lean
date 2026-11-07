module

public import Zkc.Construction.DomainTranscript
public import Zkc.Construction.Rule
public import Zkc.Source.Structured.DomainEvaluation
public import Zkc.Semantics.MonadExecution

@[expose] public section

/-! One constructed-program evaluator over the admitted nominal carriers.
Arithmetic and helpers use the structured domain evaluator, including failures.
Owner-local services remain explicit effects interpreted by the selected handler;
the default runner refuses them. Source correspondence is separate. -/
set_option autoImplicit false

namespace Zkc.Construction.Domain
open Zkc.Source

inductive Value (carriers : Structured.Carriers) where
  | data (payload : Payload carriers)
  /-- Nominal local custody, excluded from message and transcript payloads. -/
  | custody (slot : String) (token : Structured.CustodyToken)
  | transcript (suite : String) (history : History carriers)
  | indices (coordinates : List Nat)

abbrev Environment (carriers : Structured.Carriers) := List (Value carriers)

namespace Value
variable {carriers : Structured.Carriers}
def sort : Value carriers → ValueSort
  | .data payload => .data payload.ty
  | .custody slot _ => .data (.resourceUnit slot)
  | .transcript suite _ => .transcript suite
  | .indices _ => .indices

/-- Local encoding preserves custody coordinates without turning them into payloads. -/
def encode : (ty : Structured.Ty) → carriers.Value ty → Option (Value carriers)
  | .resourceUnit slot, token => some (.custody slot token)
  | ty, value => (Payload.ofValue ty value).map .data

def decode (ty : Structured.Ty) : Value carriers → Option (carriers.Value ty)
  | .custody actual token => match ty with
    | .resourceUnit slot => if slot = actual then some token else none
    | _ => none
  | .data payload => payload.value ty
  | _ => none
end Value

variable {carriers : Structured.Carriers}
def decodeValues : (tys : List Structured.Ty) → Environment carriers →
    Option (Values carriers.Value tys)
  | [], [] => some .nil
  | ty :: tys, value :: values => do
      let head ← value.decode ty
      let tail ← decodeValues tys values
      pure (.cons head tail)
  | _, _ => none

def encodeValues : {tys : List Structured.Ty} → Values carriers.Value tys →
    Option (Environment carriers)
  | [], .nil => some []
  | ty :: _, .cons value rest => do
      let head ← Value.encode ty value
      let tail ← encodeValues rest
      pure (head :: tail)

def read (env : Environment carriers) (references : List Nat) : Option (Environment carriers) :=
  references.mapM (env[·]?)

def closedOutcome {A : Type} : PIR.Process Structured.closedInterface A → PIR.Outcome A
  | .done value => .returned value
  | .halt reason => .stopped reason
  | .call operation _ => (show Empty from operation).elim

/-- Calculations use the actual structured domain operation. -/
def calculate (model : Structured.DomainModel) (calculation : Calculation)
    (arguments : Environment model.toCarriers) : PIR.Outcome (Environment model.toCarriers) :=
  match decodeValues calculation.op.arguments arguments with
  | none => .stopped .refused
  | some values =>
      match closedOutcome (Structured.Evaluation.operationOn model
          Structured.SiteObservations.closed [] calculation.op values
          (by cases calculation <;> exact .nil)) with
      | .stopped reason => .stopped reason
      | .returned results =>
          match encodeValues results with
          | some encoded => .returned encoded
          | none => .stopped .refused

/-- Installed local primitives use their checked structured outcome, including
machine-index ingress and arithmetic overflow refusals. -/
def executePrimitive (model : Structured.DomainModel) (primitive : Structured.Primitive)
    (arguments : Environment model.toCarriers) : PIR.Outcome (Environment model.toCarriers) :=
  match decodeValues primitive.arguments arguments with
  | none => .stopped .refused
  | some values =>
      match primitive.evaluateOn model.toFieldModel values with
      | .stopped reason => .stopped reason
      | .returned results =>
          match encodeValues results with
          | some encoded => .returned encoded
          | none => .stopped .refused

/-- Helpers close over the exact admitted program's checked dependency prefix. -/
def helperTable (model : Structured.DomainModel) (program : Structured.Program) :
    Structured.MeaningsOn model.toCarriers :=
  program.payload.definitions.foldl
    (Structured.Evaluation.extendMeaningsOn model Structured.SiteObservations.closed) []

def callHelper (model : Structured.DomainModel) (program : Structured.Program)
    (name : String) (declared : List ValueSort) (arguments : Environment model.toCarriers) :
    PIR.Outcome (Environment model.toCarriers) :=
  match (helperTable model program).find? (fun entry => entry.helper.name == name) with
  | none => .stopped .refused
  | some entry =>
      if entry.helper.outputs.map ValueSort.data = declared then
        match decodeValues entry.helper.inputs arguments with
        | none => .stopped .refused
        | some values =>
            match closedOutcome (entry.invoke values) with
            | .stopped reason => .stopped reason
            | .returned results =>
                match encodeValues results with
                | some encoded => .returned encoded
                | none => .stopped .refused
      else .stopped .refused

/-- Checkpoints preserve the full runtime environment on later failure. -/
inductive Effect (carriers : Structured.Carriers) where
  | receive (ty : Structured.Ty) (site schema peer : String)
  | send (site schema peer : String) (payload : Payload carriers)
  | query (history : History carriers) (origin : Origin)
  | localService (port : ServicePort) (origin : Origin)
  | observe (event : Event carriers)
  | checkpoint (environment : Environment carriers)

abbrev effects (carriers : Structured.Carriers) : PIR.Signature where
  Op := Effect carriers
  Reply
    | .receive ty .. => carriers.Value ty
    | .send .. => Unit
    | .query _ origin => Raw (.challenge origin : Event carriers)
    | .localService _ origin => Raw (.challenge origin : Event carriers)
    | .observe _ => Unit
    | .checkpoint _ => Unit

/-- Dynamic repeat coordinates in an abstract key, not native origin bytes. -/
def atCoordinates (origin : Origin) (coordinates : List Nat) : Origin :=
  if coordinates.isEmpty then origin
  else { origin with event := origin.event ++ "indices" :: coordinates.map toString }

/-- Interpret the same qualified occurrence as the checked construction rule.
The template root belongs to the selected Entry; the event's entry and service
port are local to its innermost callee. Their association with the selected root
service is established by construction/projection admission, not by equating
local names with root names here. Dynamic coordinates are checked separately. -/
def templateOrigin (context : Context) (template : Template) (coordinates : List Nat) :
    Option Origin :=
  if template.entry = context.entry ∧ template.repeats = coordinates.length ∧
      template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") then
    (template.origin context).map (atCoordinates · coordinates)
  else none

def queryOrigin (context : Context) (suite field : String) (template : Template)
    (coordinates : List Nat) : Option Origin :=
  if suite = context.suite ∧ context.contract = "random." ++ field ++ "/0" ∧
      context.request = some (.draw field) then
    match templateOrigin context template coordinates with
    | some origin => if origin.request = some (.draw field) then some origin else none
    | none => none
  else none

/-- Local services keep their own root and owner. They are not the replaced
public challenge service, and their occurrence is not a transcript observation. -/
def localOrigin (context : Context) (port : ServicePort) (request : Request)
    (template : Template) (coordinates : List Nat) : Option Origin := do
  if template.entry ≠ context.entry ∨ template.repeats ≠ coordinates.length ∨
      !template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") then none
  else do
    let ["query", _, site, _, contract, method, owner] := template.event | none
    if contract ≠ port.contract ∨ method ≠ request.method ∨ owner ≠ port.owner then none
    else some (atCoordinates
      (Origin.query context.entry (template.qualify site) ("input_" ++ decimal port.root)
        port.contract port.owner request) coordinates)

/-- The full typed request, including its values, determines the finite reply
carrier. Invalid requests cannot issue effects. -/
def requestValue (origin : Origin) (request : Request)
    (effect : Effect carriers := .query [] origin) :
    PIR.Process (effects carriers) (carriers.Value request.sort) :=
  if request.valid then
    if same : origin.request = some request then
      match effect with
      | .query history _ =>
        .call (.query history origin) fun answer =>
          match request.decode (by simpa only [Raw, same, Request.Raw] using answer) with
          | some value => .done value
          | none => .halt .refused
      | .localService port _ =>
        .call (.localService port origin) fun answer =>
          match request.decode (by simpa only [Raw, same, Request.Raw] using answer) with
          | some value => .done value
          | none => .halt .refused
      | _ => .halt .refused
    else .halt .refused
  else .halt .refused

/-- Runtime references must evaluate to the exact request values. The values
are not interpreted as environment positions. -/
def requestOperands (env : Environment carriers) (references : List Nat) (request : Request) : Bool :=
  (references.mapM fun reference => match env[reference]? with
    | some (.data (.index value)) => some value | _ => none) == some request.operands

/-- A typed challenge retains one event and one reply, also for an entire block.
The scalar native operation has a dynamic bound operand. The block native
operation fixes bound/count in its static parameters and has no data operands. -/
def challengeRequest (context : Context) (suite : String) (request : Request)
    (template : Template) (state coordinates : Nat) (references : List Nat)
    (declared : List ValueSort) (env : Environment carriers) :
    PIR.Process (effects carriers) (Environment carriers) :=
  match env[state]?, env[coordinates]? with
  | some (.transcript actual history), some (.indices path) =>
    let dynamic := if request.method = "index" then requestOperands env references request
      else references.isEmpty
    if actual = suite ∧ suite = context.suite ∧ context.service.isSome ∧
        request.valid ∧ request.nativeSupported ∧ (request.operation context.contract).isSome ∧ dynamic ∧
        declared = [.data request.sort, .transcript suite] then
      match templateOrigin
          (context.mapReplacement fun replacement => { replacement with request := some request })
          template path with
      | some origin =>
        (requestValue origin request (.query history origin)).bind fun value =>
          match Value.encode request.sort value with
          | some encoded => .done (env ++ [encoded,
              .transcript suite (history ++ [.challenge origin])])
          | none => .halt .refused
      | none => .halt .refused
    else .halt .refused
  | _, _ => .halt .refused

/-- Coordinates are the actual reached loop indices, not a static call label. -/
def localCoordinates (env : Environment carriers) (references : List Nat) : Option (List Nat) :=
  references.mapM fun (index : Nat) => match (env[index]? : Option (Value carriers)) with
    | some (.data (.index value)) => some value
    | _ => none

/-- Local requests read ordinary operand references and never touch history. -/
def localRequest (context : Context) (port : ServicePort) (request : Request)
    (template : Template) (coordinates references : List Nat) (declared : List ValueSort)
    (env : Environment carriers) : PIR.Process (effects carriers) (Environment carriers) :=
  if request.valid ∧ (request.operation port.contract).isSome ∧
      requestOperands env references request ∧ declared = [.data request.sort] then
    match localCoordinates env coordinates with
    | some path =>
      match localOrigin context port request template path with
      | some origin =>
        (requestValue origin request (.localService port origin)).bind fun value =>
          match Value.encode request.sort value with
          | some encoded => .done (env ++ [encoded])
          | none => .halt .refused
      | none => .halt .refused
    | none => .halt .refused
  else .halt .refused

/-- Types allowed on the wire. Local custody never satisfies this predicate. -/
def dataType (ty : Structured.Ty) : Bool := !ty.isHandle

/-- Values a local frame can transport: ordinary data or one nominal custody coordinate.
Compound handles, services and logical oracles need separate execution rules. -/
def localType (ty : Structured.Ty) : Bool := ty.isCustody || dataType ty

theorem localType_of_data {ty : Structured.Ty} (data : dataType ty = true) :
    localType ty = true := by simp [localType, data]

theorem localTypes_of_data {types : List Structured.Ty} (data : types.all dataType = true) :
    types.all localType = true := by
  induction types with
  | nil => rfl
  | cons ty rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at data ⊢
    exact ⟨localType_of_data data.1, ih data.2⟩

def sortsMatch (declared : List ValueSort) (values : Environment carriers) : Bool :=
  values.map Value.sort == declared

/-- Build exactly the admitted profile's physical data ABI. Plain inputs are
unchanged; only the selected Fiat–Shamir profile supplies a transcript slot. -/
def inputFrame (context : Context) (data : Environment carriers) (history : History carriers) :
    Environment carriers :=
  match context.profile with
  | .plain => data
  | .fiatShamir replacement => data ++ [.transcript replacement.suite history]

/-- Captures remain in the immutable outer environment. Only explicit yields
become the next carried state. Zero iterations do not execute the body. -/
def iterate
    (body : Environment carriers → PIR.Process (effects carriers) (Environment carriers))
    (outer : Environment carriers) (yielded : List Nat) (declared : List ValueSort) :
    List Nat → Environment carriers → PIR.Process (effects carriers) (Environment carriers)
  | [], carried => .done carried
  | index :: rest, carried =>
      (body (outer ++ .data (.index index) :: carried)).bind fun final =>
        match read final yielded with
        | some next =>
            if sortsMatch declared next then iterate body outer yielded declared rest next
            else .halt .refused
        | none => .halt .refused

/-- A loop's region adds its induction and carried arguments to the outer
frame. Its signature is checked even when the iteration count is zero. -/
def executeLoop (inputs : List ValueSort) (maximum : Nat) (yielded : List Nat)
    (count : Nat) (initial : List Nat) (declared : List ValueSort)
    (body : Environment carriers → PIR.Process (effects carriers) (Environment carriers))
    (env : Environment carriers) : PIR.Process (effects carriers) (Environment carriers) :=
  match env[count]?, read env initial with
  | some (.data (.index bound)), some carried =>
      if inputs = .data .index :: declared ∧ bound ≤ maximum ∧ sortsMatch declared carried then
        (iterate body env yielded declared (List.range bound) carried).bind fun results =>
          if sortsMatch declared results then .done (env ++ results) else .halt .refused
      else .halt .refused
  | _, _ => .halt .refused

/-- A closed lexical frame has local operand numbering but retains its caller
in diagnostic checkpoints. Nested frames compose by prefixing their parents;
returns, stops and all non-checkpoint operations keep their original meaning. -/
def withCallerFrame (caller : Environment carriers) :
    PIR.OperationInterpretation (effects carriers) (effects carriers)
  | .checkpoint frame => .call (.checkpoint (caller ++ frame)) .done
  | operation => .call operation .done

theorem withCallerFrame_nil {A : Type} (process : PIR.Process (effects carriers) A) :
    process.interpret (withCallerFrame []) = process := by
  have same : withCallerFrame (carriers := carriers) [] =
      (fun operation => PIR.Process.call operation .done) := by
    funext operation
    cases operation <;> rfl
  rw [same, PIR.Process.interpret_identity]

/-- Entering two closed frames preserves their lexical order in every checkpoint. -/
theorem withCallerFrame_nested {A : Type} (outer inner : Environment carriers)
    (process : PIR.Process (effects carriers) A) :
    (process.interpret (withCallerFrame inner)).interpret (withCallerFrame outer) =
      process.interpret (withCallerFrame (outer ++ inner)) := by
  rw [PIR.Process.interpret_comp]
  congr 1
  funext operation
  cases operation <;> try rfl
  rename_i frame
  exact congrArg (fun frame => PIR.Process.call (I := effects carriers) (.checkpoint frame) PIR.Process.done)
    (List.append_assoc outer inner frame).symm

/-- A closed arm can call only an actual Math declaration with this full ABI. -/
def mathCallMatches (program : Structured.Program) (name : String)
    (inputs outputs : List ValueSort) : Bool :=
  program.payload.definitions.any fun definition =>
    definition.name == name && definition.kind == .math &&
    definition.inputs.map ValueSort.data == inputs &&
    definition.outputs.map ValueSort.data == outputs

/-- Nested Math keeps its original helper restriction inside a local frame. -/
def closedCallMatches (program : Structured.Program) (kind : Structured.HelperKind)
    (name : String) (inputs outputs : List ValueSort) : Bool :=
  match kind with
  | .math => mathCallMatches program name inputs outputs
  | .local => program.payload.definitions.any fun definition =>
      definition.name == name && definition.inputs.map ValueSort.data == inputs &&
        definition.outputs.map ValueSort.data == outputs

/-- Resolve the same finite-domain tree and callback premises as original
Math. No incoming bound facts or mutable-state invariants are invented here. -/
def resolveFiniteFold (program : Structured.Program) (domain step predicate : String)
    (inputs outputs : List ValueSort) : Except String Structured.FoldSpec := do
  let dataSort := fun sort => match sort with
    | .data ty => if dataType ty then some ty else none
    | _ => none
  let some arguments := inputs.mapM dataSort | throw "construction-math-fold-inputs"
  let some results := outputs.mapM dataSort | throw "construction-math-fold-results"
  let domains ← program.snapshot.domains.mapM Structured.Domain.resolve
  let spec ← Structured.resolveFold program.snapshot domains .math domain step predicate
    arguments results (List.range arguments.length) []
  let installed := fun helper => program.payload.definitions.any (fun definition => definition.helper == helper)
  if !installed spec.stepHelper || (!predicate.isEmpty && !installed spec.predicateHelper) then
    throw "construction-math-fold-helper"
  return spec

/-- Original helper signatures and fold specifications share one closed-code
admission boundary. Nested Math always keeps Math callback rights. -/
def closedOperationMatches (program : Structured.Program) (kind : Structured.HelperKind)
    (operation : Operation) (inputs outputs : List ValueSort) : Bool :=
  match operation with
  | .call name => closedCallMatches program kind name inputs outputs
  | .finiteFold domain step predicate => (resolveFiniteFold program domain step predicate inputs outputs).isOk
  | _ => false

/-- A fold invokes the structured evaluator over the actual admitted helper
prefix. Domain-admission failures and callback stops are preserved exactly. -/
def finiteFold (model : Structured.DomainModel) (program : Structured.Program)
    (domain step predicate : String) (declared : List ValueSort)
    (arguments : Environment model.toCarriers) : PIR.Outcome (Environment model.toCarriers) :=
  match resolveFiniteFold program domain step predicate (arguments.map Value.sort) declared with
  | .error _ => .stopped .refused
  | .ok spec =>
    match decodeValues spec.arguments arguments with
    | none => .stopped .refused
    | some values =>
      match closedOutcome (Structured.Evaluation.denoteFoldOn (helperTable model program) spec values) with
      | .stopped reason => .stopped reason
      | .returned values =>
        match encodeValues values with
        | some results => .returned results
        | none => .stopped .refused

/-- An embedded mathematical body forms against the original program before
execution. Its explicit input/result map retains all computations and stops. -/
def compute (program : Structured.Program) (references : List Nat) (declared : List ValueSort)
    (region : InstructionRegion)
    (body : Environment carriers → PIR.Process (effects carriers) (Environment carriers))
    (env : Environment carriers) : PIR.Process (effects carriers) (Environment carriers) :=
  match read env references with
  | none => .halt .refused
  | some arguments =>
    if sortsMatch region.inputs arguments ∧
        (checkClosedBodyResults .math declared region
          (checkClosedFrom .math (closedOperationMatches program) region.inputs region.instructions)).isOk then
      ((body arguments).interpret (withCallerFrame env)).bind fun final =>
        match read final region.yielded with
        | some results => if sortsMatch declared results then .done (env ++ results) else .halt .refused
        | none => .halt .refused
    else .halt .refused

/-- Closed selection validates both arms before executing the chosen one.
All nested helper signatures and frame kinds are checked against the original
program; only the selected arm receives the capture frame. -/
def selectClosed (kind : Structured.HelperKind) (program : Structured.Program)
    (selector : Nat) (captures : List Nat) (declared : List ValueSort) (yes no : InstructionRegion)
    (runYes runNo : Environment carriers → PIR.Process (effects carriers) (Environment carriers))
    (env : Environment carriers) : PIR.Process (effects carriers) (Environment carriers) :=
  match env[selector]?, read env captures with
  | some (.data (.boolean condition)), some arguments =>
      if yes.inputs = no.inputs ∧ sortsMatch yes.inputs arguments ∧
          (checkClosedArms kind (closedOperationMatches program) declared yes no).isOk then
        let run := if condition then runYes else runNo
        let yielded := if condition then yes.yielded else no.yielded
        ((run arguments).interpret (withCallerFrame env)).bind fun final =>
          match read final yielded with
          | some values =>
              if sortsMatch declared values then .done (env ++ values) else .halt .refused
          | none => .halt .refused
      else .halt .refused
  | _, _ => .halt .refused


/-- Decode the exact conditional or unconditional range yield. -/
def rangeResult (conditional : Bool) (declared : List ValueSort)
    (values : Environment carriers) : Option (Bool × Environment carriers) := do
  let (continuing, carried) ← if conditional then
      match values with
      | .data (.boolean continuing) :: carried => some (continuing, carried)
      | _ => none
    else some (true, values)
  if sortsMatch declared carried then some (continuing, carried) else none

/-- Local ranges use the same finite traversal as structured source loops.
Both empty intervals and an early false continuation keep their carried values.
The closed body forms before traversal, and its checkpoints retain the caller. -/
def executeRange (program : Structured.Program) (conditional : Bool) (lower upper : Nat)
    (values : List Nat) (declared : List ValueSort) (region : InstructionRegion)
    (body : Environment carriers → PIR.Process (effects carriers) (Environment carriers))
    (env : Environment carriers) : PIR.Process (effects carriers) (Environment carriers) :=
  match env[lower]?, env[upper]?, read env values with
  | some (.data (.index lo)), some (.data (.index hi)), some arguments =>
      let carried := arguments.take declared.length
      let captured := arguments.drop declared.length
      if sortsMatch declared carried ∧
          (checkClosedRangeResults conditional declared (captured.map Value.sort) region
            (checkClosedFrom .local (closedOperationMatches program)
              region.inputs region.instructions)).isOk then
        (Finite.execute (.elements (List.range' lo (hi - lo)))
          (fun (current : Bool × Environment carriers) index =>
            if current.1 then
              ((body (.data (.index index) :: (current.2 ++ captured))).interpret
                (withCallerFrame env)).bind fun final =>
                  match (read final region.yielded).bind (rangeResult conditional declared) with
                  | some next => .done next
                  | none => .halt .refused
            else .done current) (true, carried)).bind fun result =>
            if sortsMatch declared result.2 then .done (env ++ result.2) else .halt .refused
      else .halt .refused
  | _, _, _ => .halt .refused

mutual
/-- Structural evaluation of the retained constructed instruction tree. -/
def evaluate (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    List Instruction → Environment model.toCarriers →
      PIR.Process (effects model.toCarriers) (Environment model.toCarriers)
  | [], env => .done env
  | instruction :: rest, env =>
      .call (.checkpoint env) fun _ =>
        (step model program context instruction env).bind fun next =>
          .call (.checkpoint next) fun _ => evaluate model program context rest next

def step (model : Structured.DomainModel) (program : Structured.Program) (context : Context) :
    Instruction → Environment model.toCarriers →
      PIR.Process (effects model.toCarriers) (Environment model.toCarriers)
  | ⟨operation, operands, declared, regions⟩, env =>
    let append := fun results =>
      if sortsMatch declared results then .done (env ++ results) else .halt .refused
    match operation, operands, regions with
    | .receive site schema peer ty, [], [] =>
        if schema = site ∧ dataType ty = true ∧ declared = [.data ty] then
          .call (.receive ty site schema peer) fun value =>
            match Value.encode ty value with
            | some encoded => append [encoded]
            | none => .halt .refused
        else .halt .refused
    | .send site schema peer, [reference], [] =>
        match env[reference]? with
        | some (.data payload) =>
            if schema = site ∧ declared = [] then
              .call (.send site schema peer payload) fun _ => .done env
            else .halt .refused
        | _ => .halt .refused
    | .indicesEmpty, [], [] => append [.indices []]
    | .indicesAppend, [coordinates, index], [] =>
        match env[coordinates]?, env[index]? with
        | some (.indices path), some (.data (.index index)) => append [.indices (path ++ [index])]
        | _, _ => .halt .refused
    | .observe suite template, [state, value, coordinates], [] =>
        match env[state]?, env[value]?, env[coordinates]? with
        | some (.transcript actual history), some (.data payload), some (.indices path) =>
            if suite = actual ∧ suite = context.suite ∧ declared = [.transcript suite] then
              match templateOrigin context template path with
              | some origin =>
                  if origin.request = none then
                    let event := Event.message origin payload
                    .call (.observe event) fun _ => append [.transcript suite (history ++ [event])]
                  else .halt .refused
              | none => .halt .refused
            else .halt .refused
        | _, _, _ => .halt .refused
    | .challenge suite field template, [state, coordinates], [] =>
        match env[state]?, env[coordinates]? with
        | some (.transcript actual history), some (.indices path) =>
            if actual = suite ∧ declared = [.data (.field field), .transcript suite] then
              match queryOrigin context suite field template path with
              | some origin =>
                  if request : origin.request = some (.draw field) then
                    .call (.query history origin) fun answer =>
                      let value : model.Field field := by
                        simpa only [Raw, request, Request.draw] using answer
                      append [.data (.field field value),
                        .transcript suite (history ++ [.challenge origin])]
                  else .halt .refused
              | none => .halt .refused
            else .halt .refused
        | _, _ => .halt .refused
    | .indexChallenge suite bound template, [state, reference, coordinates], [] =>
        challengeRequest context suite (.sampleIndex bound) template state coordinates [reference] declared env
    | .blockChallenge suite bound count template, [state, coordinates], [] =>
        challengeRequest context suite (.sampleIndices bound count) template state coordinates [] declared env
    | .localService port request template coordinates, references, [] =>
        localRequest context port request template coordinates references declared env
    | .calculate calculation, references, [] =>
        match read env references with
        | some arguments =>
            match calculate model calculation arguments with
            | .returned results => append results
            | .stopped reason => .halt reason
        | none => .halt .refused
    | .execute primitive, references, [] =>
        match read env references with
        | some arguments =>
            match executePrimitive model primitive arguments with
            | .returned results => append results
            | .stopped reason => .halt reason
        | none => .halt .refused
    | .call name, references, [] =>
        match read env references with
        | some arguments =>
            match callHelper model program name declared arguments with
            | .returned results => append results
            | .stopped reason => .halt reason
        | none => .halt .refused
    | .finiteFold domain helper predicate, references, [] =>
        match read env references with
        | some arguments =>
            match finiteFold model program domain helper predicate declared arguments with
            | .returned results => append results
            | .stopped reason => .halt reason
        | none => .halt .refused
    | .mathCompute, references, [region@⟨_, body, _⟩] =>
        compute program references declared region (evaluate model program context body) env
    | .guard _, [condition], [] =>
        if declared = [] then
          match env[condition]? with
          | some (.data (.boolean true)) => .done env
          | some (.data (.boolean false)) => .halt .reject
          | _ => .halt .refused
        else .halt .refused
    | .require _, [condition], [] =>
        if declared = [] then
          match env[condition]? with
          | some (.data (.boolean true)) => .done env
          | _ => .halt .refused
        else .halt .refused
    | .mathBranch, selector :: captures,
        [yes@⟨_, yesBody, _⟩, no@⟨_, noBody, _⟩] =>
        selectClosed .math program selector captures declared yes no
          (evaluate model program context yesBody) (evaluate model program context noBody) env
    | .localBranch, selector :: captures,
        [yes@⟨_, yesBody, _⟩, no@⟨_, noBody, _⟩] =>
        selectClosed .local program selector captures declared yes no
          (evaluate model program context yesBody) (evaluate model program context noBody) env
    | .localRange conditional, lower :: upper :: values, [region@⟨_, body, _⟩] =>
        executeRange program conditional lower upper values declared region
          (evaluate model program context body) env
    | .loop _ maximum, count :: initial, [⟨inputs, body, yielded⟩] =>
        executeLoop inputs maximum yielded count initial declared
          (evaluate model program context body) env
    | _, _, _ => .halt .refused
end

structure Result (carriers : Structured.Carriers) where
  values : Environment carriers
  environment : Environment carriers

/-- All declared returns and the complete final environment are retained.
Artifact admission and authored-pair selection remain caller obligations. -/
def participant (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (constructed : Participant) (inputs : Environment model.toCarriers) :
    PIR.Process (effects model.toCarriers) (Result model.toCarriers) :=
  .call (.checkpoint inputs) fun _ =>
    if sortsMatch constructed.inputs inputs then
      (evaluate model program context constructed.instructions inputs).bind fun env =>
        match read env constructed.returned with
        | some returned =>
            if sortsMatch constructed.outputs returned then .done ⟨returned, env⟩
            else .halt .refused
        | none => .halt .refused
    else .halt .refused

end Zkc.Construction.Domain

-- Equation lemmas belong to their defining module. Materializing them here
-- prevents independent clients from storing different private proofs under
-- the same public equation name.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Domain.Value.decode
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Domain.decodeValues
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Domain.encodeValues
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Domain.dataType
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Domain.localType
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Domain.step
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Domain.evaluate
