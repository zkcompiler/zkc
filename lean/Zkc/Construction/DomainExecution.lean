module

public import Zkc.Construction.DomainTranscript
public import Zkc.Construction.Semantics
public import Zkc.Source.Structured.DomainEvaluation
public import Zkc.Semantics.MonadExecution

@[expose] public section

/-! One constructed-program evaluator over the admitted nominal carriers.
Arithmetic and helpers use the structured domain evaluator, including failures.
Private coins are unsupported and refuse. Source correspondence is separate. -/
set_option autoImplicit false

namespace Zkc.Construction.Domain
open Zkc.Source

inductive Value (carriers : Structured.Carriers) where
  | data (payload : Payload carriers)
  | transcript (suite : String) (history : History carriers)
  | indices (coordinates : List Nat)

abbrev Environment (carriers : Structured.Carriers) := List (Value carriers)

namespace Value
variable {carriers : Structured.Carriers}
def sort : Value carriers → ValueSort
  | .data payload => .data payload.ty
  | .transcript suite _ => .transcript suite
  | .indices _ => .indices

def encode (ty : Structured.Ty) (value : carriers.Value ty) : Option (Value carriers) :=
  (Payload.ofValue ty value).map .data

def decode (ty : Structured.Ty) : Value carriers → Option (carriers.Value ty)
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

/-- Coordinates are the actual reached loop indices, not a static call label. -/
def localCoordinates (env : Environment carriers) (references : List Nat) : Option (List Nat) :=
  references.mapM fun (index : Nat) => match (env[index]? : Option (Value carriers)) with
    | some (.data (.index value)) => some value
    | _ => none

def dataType : Structured.Ty → Bool
  | .service _ => false
  | _ => true

def sortsMatch (declared : List ValueSort) (values : Environment carriers) : Bool :=
  values.map Value.sort == declared

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
  | ⟨operation, operands, declared, body⟩, env =>
    let append := fun results =>
      if sortsMatch declared results then .done (env ++ results) else .halt .refused
    match operation, operands, body with
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
    | .localService port request template coordinates, references, [] =>
        match request, localCoordinates env coordinates with
        | ⟨"draw", [], .field field⟩, some path =>
            if references = [] ∧ declared = [.data (.field field)] ∧
                port.contract = "random." ++ field ++ "/0" then
              match localOrigin context port (.draw field) template path with
              | some origin =>
                  if request : origin.request = some (.draw field) then
                    .call (.localService port origin) fun answer =>
                      let value : model.Field field := by
                        simpa only [Raw, request, Request.draw] using answer
                      append [.data (.field field value)]
                  else .halt .refused
              | none => .halt .refused
            else .halt .refused
        | _, _ => .halt .refused
    | .calculate calculation, references, [] =>
        match read env references with
        | some arguments =>
            match calculate model calculation arguments with
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
    | .guard _, [condition], [] =>
        if declared = [] then
          match env[condition]? with
          | some (.data (.boolean true)) => .done env
          | some (.data (.boolean false)) => .halt .reject
          | _ => .halt .refused
        else .halt .refused
    | .loop _ maximum yielded, count :: initial, body =>
        match env[count]?, read env initial with
        | some (.data (.index bound)), some carried =>
            if bound ≤ maximum ∧ sortsMatch declared carried then
              (iterate (evaluate model program context body) env yielded declared
                (List.range bound) carried).bind append
            else .halt .refused
        | _, _ => .halt .refused
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
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Domain.step
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Domain.evaluate
