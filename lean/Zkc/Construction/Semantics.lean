module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Construction.FiatShamir
public import Zkc.Source.Structured.Evaluation
public import Zkc.Source.Structured.Participant

@[expose] public section

/-! Meanings of exported constructed programs.

Values are structured data (scalars, indices and field vectors), transcript
histories and occurrence coordinates. Calculations are evaluated with the
structured evaluator's meaning and helper calls with a closed table of checked
helpers, looked up by name and invoked at their checked signatures.

`ideal` interprets a program with the ideal transcript model: a transcript
capability holds its absorbed history, an observation appends the model
occurrence of its template with the observed payload, and a challenge applies
the challenge function to the history ending with its occurrence. `spec` reads
the same program back as the interactive validator it replaced: each challenge
becomes the selected query on the service handle, and observing a message the
validator sends is the delivery of that message to the producer. Both are
written in continuation style, so a loop's iterations, a body's continuation and
a program's suffix compose without returning intermediate environments.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source
open Zkc.Source.Common.Native (ScalarValue)

variable {F G : Type}

/-- Runtime values of exported programs: scalar data, indices, vectors,
transcript histories and occurrence coordinates. -/
inductive Value (F G : Type) where
  | data (payload : Payload F G)
  | index (value : Nat)
  | vector (domain : String) (values : List F)
  | transcript (history : History F G)
  | indices (coordinates : List Nat)

deriving instance DecidableEq for Value

/-- Types whose values exported programs carry: everything except services. -/
def dataType : Structured.Ty → Bool
  | .service _ => false
  | _ => true

namespace Value

/-- A structured value as an exported value. Services are never carried. -/
def encode : (ty : Structured.Ty) → Structured.assignment F G ty → Value F G
  | .boolean, value => .data (.boolean value)
  | .field domain, value => .data (.field domain value)
  | .group domain, value => .data (.group domain value)
  | .index, value => .index value
  | .vector domain, values => .vector domain values
  | .service _, handle => .index handle

/-- Read an exported value at a structured type; services never decode. -/
def decode : (ty : Structured.Ty) → Value F G → Option (Structured.assignment F G ty)
  | .boolean, .data (.boolean value) => some value
  | .field domain, .data (.field other value) => if domain = other then some value else none
  | .group domain, .data (.group other value) => if domain = other then some value else none
  | .index, .index value => some value
  | .vector domain, .vector other values => if domain = other then some values else none
  | _, _ => none

theorem decode_encode {ty : Structured.Ty} (data : dataType ty = true)
    (value : Structured.assignment F G ty) : decode ty (encode ty value) = some value := by
  cases ty <;> simp_all [encode, decode, dataType]

end Value

/-- Decode ordered values at declared types. -/
def decodeValues : (tys : List Structured.Ty) → List (Value F G) →
    Option (Values (Structured.assignment F G) tys)
  | [], [] => some .nil
  | ty :: tys, value :: values => do
      let head ← Value.decode ty value
      let tail ← decodeValues tys values
      pure (.cons head tail)
  | _, _ => none

def encodeValues : {tys : List Structured.Ty} → Values (Structured.assignment F G) tys →
    List (Value F G)
  | [], .nil => []
  | ty :: _, .cons value rest => Value.encode ty value :: encodeValues rest

/-- A finished outcome as a process. -/
def ofOutcome {I : PIR.Signature} {A : Type} : PIR.Outcome A → PIR.Process I A
  | .returned value => .done value
  | .stopped reason => .halt reason

/-- The outcome of a process that cannot call. -/
def closedOutcome {A : Type} : PIR.Process Structured.closedInterface A → PIR.Outcome A
  | .done value => .returned value
  | .halt reason => .stopped reason
  | .call operation _ => (show Empty from operation).elim

namespace Calculation
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The structured meaning of a carrier calculation. -/
def evaluate : (calculation : Calculation) → Values (Structured.assignment F G) calculation.op.arguments →
    PIR.Outcome (Values (Structured.assignment F G) calculation.op.results)
  | .indexConstant value, .nil => .returned (.cons value .nil)
  | .indexEqual, .cons a (.cons b .nil) => .returned (.cons (decide (a = b)) .nil)
  | .fieldConstant _ value, .nil => .returned (.cons (value : F) .nil)
  | .fieldAdd _, .cons a (.cons b .nil) => .returned (.cons (a + b) .nil)
  | .fieldSubtract _, .cons a (.cons b .nil) => .returned (.cons (a - b) .nil)
  | .fieldMultiply _, .cons a (.cons b .nil) => .returned (.cons (a * b) .nil)
  | .fieldEqual _, .cons a (.cons b .nil) => .returned (.cons (decide (a = b)) .nil)
  | .groupIdentity _, .nil => .returned (.cons 0 .nil)
  | .groupAdd _, .cons a (.cons b .nil) => .returned (.cons (a + b) .nil)
  | .groupScale _ _, .cons point (.cons scalar .nil) => .returned (.cons (scalar • point) .nil)
  | .groupEqual _, .cons a (.cons b .nil) => .returned (.cons (decide (a = b)) .nil)
  | .booleanConstant value, .nil => .returned (.cons value .nil)
  | .booleanAnd, .cons a (.cons b .nil) => .returned (.cons (a && b) .nil)
  | .booleanOr, .cons a (.cons b .nil) => .returned (.cons (a || b) .nil)
  | .booleanXor, .cons a (.cons b .nil) => .returned (.cons (xor a b) .nil)
  | .booleanEqual, .cons a (.cons b .nil) => .returned (.cons (a == b) .nil)
  | .booleanNotEqual, .cons a (.cons b .nil) => .returned (.cons (a != b) .nil)
  | .select _, .cons condition (.cons yes (.cons no .nil)) =>
      .returned (.cons (if condition then yes else no) .nil)
  | .boundedAt _, .cons container (.cons index .nil) =>
      match container[index]? with
      | some value => .returned (.cons value .nil)
      | none => .stopped .refused

/-- The structured evaluator agrees with the carrier meaning, under every
effect interface, site observation and helper table. -/
theorem operation_eq {I : PIR.Signature} (observations : Structured.SiteObservations I)
    (table : Structured.Evaluation.Meanings F G I) (calculation : Calculation)
    (arguments : Values (Structured.assignment F G) calculation.op.arguments)
    (bodies : Values (RegionFunction (Structured.assignment F G) I) calculation.op.regions) :
    Structured.Evaluation.operation observations table calculation.op arguments bodies =
      ofOutcome (calculation.evaluate arguments) := by
  cases calculation <;> cases bodies
  case boundedAt domain =>
    rcases arguments with _ | ⟨container, _ | ⟨index, _ | _⟩⟩
    change (match container[index]? with
      | some value => PIR.Process.done (Values.cons (Value := Structured.assignment F G)
          (ty := .field domain) value Values.nil)
      | none => PIR.Process.halt PIR.Stop.refused) =
        ofOutcome (match container[index]? with
          | some value => PIR.Outcome.returned (Values.cons (Value := Structured.assignment F G)
              (ty := .field domain) value Values.nil)
          | none => PIR.Outcome.stopped PIR.Stop.refused)
    cases container[index]? <;> rfl
  all_goals
    rcases arguments with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
    rfl

end Calculation

/-- Invoke a checked helper by name in a closed helper table. The arguments are
decoded at the found helper's input types and its results encoded. -/
def callHelper (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
    (name : String) (arguments : List (Value F G)) : PIR.Outcome (List (Value F G)) :=
  match table.find? (fun entry => entry.helper.name == name) with
  | none => .stopped .refused
  | some entry =>
      match decodeValues entry.helper.inputs arguments with
      | none => .stopped .refused
      | some values =>
          match closedOutcome (entry.invoke values) with
          | .returned results => .returned (encodeValues results)
          | .stopped reason => .stopped reason

/-- A calculation on exported values. -/
def calculate [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (calculation : Calculation) (arguments : List (Value F G)) : PIR.Outcome (List (Value F G)) :=
  match decodeValues calculation.op.arguments arguments with
  | none => .stopped .refused
  | some values =>
      match calculation.evaluate values with
      | .returned results => .returned (encodeValues results)
      | .stopped reason => .stopped reason

def dataAt (env : List (Value F G)) (index : Nat) : Option (Payload F G) :=
  match env[index]? with
  | some (.data payload) => some payload
  | _ => none

def transcriptAt (env : List (Value F G)) (index : Nat) : Option (History F G) :=
  match env[index]? with
  | some (.transcript history) => some history
  | _ => none

def indicesAt (env : List (Value F G)) (index : Nat) : List Nat :=
  match env[index]? with
  | some (.indices coordinates) => coordinates
  | _ => []

def indexAt (env : List (Value F G)) (index : Nat) : Option Nat :=
  match env[index]? with
  | some (.index value) => some value
  | _ => none

/-- Read references from an environment. -/
def read (env : List (Value F G)) (references : List Nat) : Option (List (Value F G)) :=
  references.mapM (env[·]?)

namespace Template

/-- The model occurrence of a template, as `transform` names it: a message by
its qualified site and its roles; a selected draw challenge by its qualified
query site under the context's replaced service, with that service's typed
request. -/
def origin (context : Context) (template : Template) : Option Origin :=
  match template.event with
  | ["message", _, site, schema, sender, receiver] =>
      if schema = site then some (Origin.message context.entry (template.qualify site) sender receiver)
      else none
  | ["query", _, site, _, _, "draw", _] => context.request.map (context.query (template.qualify site))
  | _ => none

end Template

/-- A scalar structured type as a common transcript type. -/
def scalarType : Structured.Ty → Option Zkc.Source.Common.Native.Ty
  | .boolean => some .boolean
  | .field domain => some (.field domain)
  | .group domain => some (.group domain)
  | _ => none

/-- Send a payload to `receiver` at `site`. -/
def sendPayload {A : Type} (site : String) (receiver : Nat) (payload : Payload F G)
    (next : PIR.Process (Actions F G) A) : PIR.Process (Actions F G) A :=
  match payload with
  | .boolean value => .call (.send (ty := .boolean) site receiver value) fun _ => next
  | .field domain value => .call (.send (ty := .field domain) site receiver value) fun _ => next
  | .group domain value => .call (.send (ty := .group domain) site receiver value) fun _ => next

section Interactive
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (context : Context) (handle : Nat)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)

/-- Iterate a loop body over the given induction values. -/
def iterate {I : PIR.Signature} {A : Type}
    (body : List (Value F G) → (List (Value F G) → PIR.Process I A) → PIR.Process I A)
    (env : List (Value F G)) (yielded : List Nat) :
    List Nat → List (Value F G) → (List (Value F G) → PIR.Process I A) → PIR.Process I A
  | [], carried, next => next carried
  | index :: rest, carried, next =>
      body (env ++ .index index :: carried) fun final =>
        match read final yielded with
        | some carried' => iterate body env yielded rest carried' next
        | none => .halt .refused

mutual
/-- The interactive validator an exported program replaced, in continuation
style. Receives come from the producer; each challenge becomes the selected
query on `handle`; an observed message sent by the validator is its delivery to
the producer. Transcript values are computed as inert histories. -/
def specK {A : Type} : List Instruction → List (Value F G) →
    (List (Value F G) → PIR.Process (Actions F G) A) → PIR.Process (Actions F G) A
  | [], env, next => next env
  | instruction :: rest, env, next =>
      specStep instruction env fun env' => specK rest env' next

def specStep {A : Type} : Instruction → List (Value F G) →
    (List (Value F G) → PIR.Process (Actions F G) A) → PIR.Process (Actions F G) A
  | ⟨.receive site _ _ ty, [], _, _⟩, env, next =>
      match scalarType ty with
      | some common =>
          .call (.receive common site context.producer) fun value =>
            match Zkc.Construction.Payload.ofValue common value with
            | some payload => next (env ++ [.data payload])
            | none => .halt .refused
      | none => .halt .refused
  | ⟨.indicesEmpty, [], _, _⟩, env, next => next (env ++ [.indices []])
  | ⟨.indicesAppend, [coordinates, index], _, _⟩, env, next =>
      next (env ++ [.indices (indicesAt env coordinates ++ (indexAt env index).toList)])
  | ⟨.observe _ template, [state, value, _], _, _⟩, env, next =>
      let history := (transcriptAt env state).getD []
      match template.origin context, dataAt env value with
      | some origin, some payload =>
          let env' := env ++ [.transcript (history ++ [.message origin payload])]
          if template.sentBy (context.role context.validator) then
            sendPayload ((template.messageSite?).getD "") context.producer payload (next env')
          else next env'
      | _, _ => next (env ++ [.transcript history])
  | ⟨.challenge _ field template, [state, _], _, _⟩, env, next =>
      let history := (transcriptAt env state).getD []
      match template.origin context, template.querySite? with
      | some origin, some site =>
          .call (.query site field (.cons handle .nil)) fun answer =>
            next (env ++ [.data (.field field answer), .transcript (history ++ [.challenge origin])])
      | _, _ => .halt .refused
  | ⟨.calculate calculation, operands, _, _⟩, env, next =>
      match read env operands with
      | some arguments =>
          match Zkc.Construction.calculate calculation arguments with
          | .returned results => next (env ++ results)
          | .stopped reason => .halt reason
      | none => .halt .refused
  | ⟨.call name, operands, declared, _⟩, env, next =>
      match read env operands with
      | some arguments =>
          match callHelper table name arguments with
          | .returned results =>
              if results.length = declared.length then next (env ++ results) else .halt .refused
          | .stopped reason => .halt reason
      | none => .halt .refused
  | ⟨.guard _, [condition], _, _⟩, env, next =>
      match env[condition]? with
      | some (.data (.boolean true)) => next env
      | some (.data (.boolean false)) => .halt .reject
      | _ => .halt .refused
  | ⟨.loop _ maximum yielded, count :: initial, _, body⟩, env, next =>
      match indexAt env count, read env initial with
      | some bound, some carried =>
          if bound ≤ maximum then
            iterate (fun start continuation => specK body start continuation) env yielded
              (List.range bound) carried fun final => next (env ++ final)
          else .halt .refused
      | _, _ => .halt .refused
  | _, _, _ => .halt .refused
end

end Interactive

section Ideal
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]
variable (context : Context) (challenge : History F G → m F)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)

/-- Iterate a loop body over the given induction values, threading the proof. -/
def iterateM {R : Type}
    (body : List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G))
    (env : List (Value F G)) (yielded : List Nat) :
    List Nat → List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G)
  | [], carried, proof, next => next carried proof
  | index :: rest, carried, proof, next =>
      body (env ++ .index index :: carried) proof fun final unread =>
        match read final yielded with
        | some carried' => iterateM body env yielded rest carried' unread next
        | none => pure (.stopped .refused, unread)

mutual
/-- The ideal meaning of an exported constructed program, in continuation
style: a transcript capability holds its absorbed history, observation appends
the model occurrence of its template with the observed payload, and a challenge
applies `challenge` to the history ending with its occurrence. Receives read the
proof in order. A stop returns the unread proof at that point. -/
def idealK {R : Type} : List Instruction → List (Value F G) → Proof F G →
    (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G)
  | [], env, proof, next => next env proof
  | instruction :: rest, env, proof, next =>
      idealStep instruction env proof fun env' unread => idealK rest env' unread next

def idealStep {R : Type} : Instruction → List (Value F G) → Proof F G →
    (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G)
  | ⟨.receive _ _ _ ty, [], _, _⟩, env, proof, next =>
      match scalarType ty, proof with
      | some common, payload :: rest =>
          if payload.ty = common then next (env ++ [.data payload]) rest
          else pure (.stopped .refused, proof)
      | _, _ => pure (.stopped .refused, proof)
  | ⟨.indicesEmpty, [], _, _⟩, env, proof, next => next (env ++ [.indices []]) proof
  | ⟨.indicesAppend, [coordinates, index], _, _⟩, env, proof, next =>
      next (env ++ [.indices (indicesAt env coordinates ++ (indexAt env index).toList)]) proof
  | ⟨.observe _ template, [state, value, _], _, _⟩, env, proof, next =>
      match transcriptAt env state, template.origin context, dataAt env value with
      | some history, some origin, some payload =>
          next (env ++ [.transcript (history ++ [.message origin payload])]) proof
      | _, _, _ => pure (.stopped .refused, proof)
  | ⟨.challenge _ field template, [state, _], _, _⟩, env, proof, next =>
      match transcriptAt env state, template.origin context with
      | some history, some origin => do
          let answer ← challenge (history ++ [.challenge origin])
          next (env ++ [.data (.field field answer), .transcript (history ++ [.challenge origin])]) proof
      | _, _ => pure (.stopped .refused, proof)
  | ⟨.calculate calculation, operands, _, _⟩, env, proof, next =>
      match read env operands with
      | some arguments =>
          match Zkc.Construction.calculate calculation arguments with
          | .returned results => next (env ++ results) proof
          | .stopped reason => pure (.stopped reason, proof)
      | none => pure (.stopped .refused, proof)
  | ⟨.call name, operands, declared, _⟩, env, proof, next =>
      match read env operands with
      | some arguments =>
          match callHelper table name arguments with
          | .returned results =>
              if results.length = declared.length then next (env ++ results) proof
              else pure (.stopped .refused, proof)
          | .stopped reason => pure (.stopped reason, proof)
      | none => pure (.stopped .refused, proof)
  | ⟨.guard _, [condition], _, _⟩, env, proof, next =>
      match env[condition]? with
      | some (.data (.boolean true)) => next env proof
      | some (.data (.boolean false)) => pure (.stopped .reject, proof)
      | _ => pure (.stopped .refused, proof)
  | ⟨.loop _ maximum yielded, count :: initial, _, body⟩, env, proof, next =>
      match indexAt env count, read env initial with
      | some bound, some carried =>
          if bound ≤ maximum then
            iterateM (fun start unread continuation => idealK body start unread continuation) env yielded
              (List.range bound) carried proof fun final unread => next (env ++ final) unread
          else pure (.stopped .refused, proof)
      | _, _ => pure (.stopped .refused, proof)
  | _, _, proof, _ => pure (.stopped .refused, proof)
end

end Ideal

/-- Returned references, read from the final environment. -/
def finish (returned : List Nat) (env : List (Value F G)) : PIR.Outcome (List (Value F G)) :=
  match read env returned with
  | some values => .returned values
  | none => .stopped .refused

section Programs
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]

def ideal (context : Context) (challenge : History F G → m F)
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (returned : List Nat)
    (instructions : List Instruction) (env : List (Value F G)) (proof : Proof F G) :
    m (PIR.Outcome (List (Value F G)) × Proof F G) :=
  idealK context challenge table instructions env proof fun final unread =>
    pure (finish returned final, unread)

def spec (context : Context) (handle : Nat)
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (returned : List Nat)
    (instructions : List Instruction) (env : List (Value F G)) :
    PIR.Process (Actions F G) (List (Value F G)) :=
  specK context handle table instructions env fun final =>
    match read final returned with
    | some values => .done values
    | none => .halt .refused

end Programs

end Zkc.Construction

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.decodeValues
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.scalarType
