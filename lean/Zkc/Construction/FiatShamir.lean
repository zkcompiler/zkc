module

public import Zkc.Construction.Participant
public import Zkc.Source.Participant

@[expose] public section

/-! Checked Fiat–Shamir transcript construction for role-local validators.

`transform` is the Fiat–Shamir transform of any validator process over the
common participant actions: received messages come from a proof list and are
absorbed, each `query` is answered by the transcript challenge function on the
absorbed history followed by its own occurrence, and each challenge delivery to
the producer is absorbed instead of sent. The transform is independent of any
compiled program.

`ideal` interprets an exported constructed validator with the same transcript
model: a transcript capability holds its absorbed history, observation appends
an event, and a challenge applies the challenge function to the history ending
with its occurrence. `spec` reads the same exported program back as the
interactive validator it replaced, with the selected services' queries and
deliveries restored.

`check` is the transcript-construction rule. `check_sound` proves that every
accepted program's ideal meaning is the Fiat–Shamir transform of its
interactive reading, for every challenge function in every lawful monad. A
consumer separately proves that the interactive reading is the original
protocol's validator process. Treating the native suite's challenge function as
a random oracle is a named assumption of such a consumer, not of this rule.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source Zkc.Source.Common.Native

variable {F G : Type}

/-- Data absorbed by observations and carried by proof messages. -/
inductive Payload (F G : Type) where
  | boolean (value : Bool)
  | field (domain : String) (value : F)
  | group (domain : String) (value : G)
  deriving DecidableEq, Repr

namespace Payload

def ty : Payload F G → Ty
  | .boolean _ => .boolean
  | .field domain _ => .field domain
  | .group domain _ => .group domain

def ofValue : (ty : Ty) → ScalarValue F G ty → Option (Payload F G)
  | .boolean, value => some (.boolean value)
  | .field domain, value => some (.field domain value)
  | .group domain, value => some (.group domain value)
  | .service _, _ => none

/-- Decoding at an expected type requires the same kind and nominal domain. -/
def value : (ty : Ty) → Payload F G → Option (ScalarValue F G ty)
  | .boolean, .boolean value => some value
  | .field domain, .field other value => if domain = other then some value else none
  | .group domain, .group other value => if domain = other then some value else none
  | _, _ => none

theorem value_some {ty : Ty} {payload : Payload F G} {decoded : ScalarValue F G ty}
    (decodes : payload.value ty = some decoded) : ofValue ty decoded = some payload := by
  cases ty <;> cases payload <;> simp_all [value, ofValue]

theorem value_isSome {ty : Ty} {payload : Payload F G} :
    (payload.value ty).isSome = decide (payload.ty = ty) := by
  cases ty <;> cases payload <;> simp [value, Payload.ty]
  all_goals (split <;> simp_all [eq_comm])

/-- Ordered arguments at their declared types. -/
def arguments : (tys : List Ty) → List (Payload F G) → Option (Values (ScalarValue F G) tys)
  | [], [] => some .nil
  | ty :: tys, payload :: payloads => do
      let head ← payload.value ty
      let tail ← arguments tys payloads
      pure (.cons head tail)
  | _, _ => none

end Payload

/-- The selected scalar interpretation of one exported calculation. -/
def calculate [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (op : Op) (arguments : List (Payload F G)) : Option (Payload F G) := do
  let values ← Payload.arguments (language.arguments op) arguments
  Payload.ofValue (language.result op) ((scalarMeaning F G).operation op values)

/-- Absorbed transcript events. `binding` is the host's initialization with the
authorized public context; it is not an operation of the participant program. -/
inductive Event (F G : Type) where
  | binding (context : String) (values : List (Payload F G))
  | message (origin : Origin) (value : Payload F G)
  | challenge (origin : Origin)
  deriving DecidableEq, Repr

abbrev History (F G : Type) := List (Event F G)

/-- Proof messages, in their delivered order and at their typed values. -/
abbrev Proof (F G : Type) := List (Payload F G)

/-- Runtime values of exported programs under the ideal transcript model. -/
inductive Value (F G : Type) where
  | data (payload : Payload F G)
  | transcript (history : History F G)
  | indices
  deriving DecidableEq, Repr

def dataAt (env : List (Value F G)) (index : Nat) : Option (Payload F G) :=
  match env[index]? with
  | some (.data payload) => some payload
  | _ => none

def transcriptAt (env : List (Value F G)) (index : Nat) : Option (History F G) :=
  match env[index]? with
  | some (.transcript history) => some history
  | _ => none

/-- Returned references, read from the final environment. -/
def finish (returned : List Nat) (env : List (Value F G)) : PIR.Outcome (List (Value F G)) :=
  match returned.mapM (env[·]?) with
  | some values => .returned values
  | none => .stopped .refused

/-- The common participant actions of a validator. -/
abbrev Actions (F G : Type) := Participant.interface Nat Ty services (ScalarValue F G)

/-- Deployment facts that fix occurrence identities: original entry, role
roster, producer and validator positions, the replaced service's original input
index and contract, and the ordered query/delivery sites. -/
structure Context where
  entry : String
  roles : List String
  producer : Nat
  validator : Nat
  service : Nat
  contract : String
  suite : String
  draws : List (String × String)
  deriving DecidableEq, Repr

/-- One decimal digit; larger arguments spell `9`. -/
def decimalDigit : Nat → String
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"

/-- The canonical decimal spelling of an index below `10000`, as used in native
service port names. It is built from literals so that kernel evaluation reduces
it. -/
def decimal (index : Nat) : String :=
  if index < 10 then decimalDigit index
  else if index < 100 then decimalDigit (index / 10) ++ decimalDigit (index % 10)
  else if index < 1000 then
    decimalDigit (index / 100) ++ decimalDigit (index / 10 % 10) ++ decimalDigit (index % 10)
  else
    decimalDigit (index / 1000 % 10) ++ decimalDigit (index / 100 % 10) ++
      decimalDigit (index / 10 % 10) ++ decimalDigit (index % 10)

namespace Context

def role (context : Context) (index : Nat) : String := context.roles.getD index ""

def message (context : Context) (site : String) (sender receiver : Nat) : Origin :=
  .message context.entry site (context.role sender) (context.role receiver)

/-- The selected query's occurrence names the replaced service's original port
and contract, which the original export fixes. -/
def query (context : Context) (site : String) : Origin :=
  .query context.entry site ("input_" ++ decimal context.service) context.contract
    (context.role context.validator)

end Context

section Transform
variable {m : Type → Type} [Monad m]

/-- The Fiat–Shamir transform of a validator process whose every query is a
selected challenge. Receives read the proof in order and absorb the decoded
message; a decoding failure refuses without consuming. Every query is answered
by `challenge` on the history ending with its occurrence, which is absorbed. A
send is absorbed with its message occurrence and produces no proof data. Returns
the outcome and the unread proof suffix. -/
def transform {A : Type} (context : Context) (challenge : History F G → m F) :
    PIR.Proc (Actions F G) A → History F G → Proof F G → m (PIR.Outcome A × Proof F G)
  | .done value, _, proof => pure (.returned value, proof)
  | .halt stop, _, proof => pure (.stopped stop, proof)
  | .call (.receive ty site sender) next, history, proof =>
      match proof with
      | [] => pure (.stopped .refused, [])
      | payload :: rest =>
          match payload.value ty with
          | some value => transform context challenge (next value)
              (history ++ [.message (context.message site sender context.validator) payload]) rest
          | none => pure (.stopped .refused, payload :: rest)
  | .call (.query site _ _) next, history, proof => do
      let event := Event.challenge (context.query site)
      let answer ← challenge (history ++ [event])
      transform context challenge (next answer) (history ++ [event]) proof
  | .call (.send (ty := ty) site receiver sent) next, history, proof =>
      match Payload.ofValue ty sent with
      | some payload => transform context challenge (next ())
          (history ++ [.message (context.message site context.validator receiver) payload]) proof
      | none => pure (.stopped .refused, proof)

end Transform

section Programs
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]

/-- One exported instruction under the ideal transcript model: the values it
appends and the unread proof, or a stop. -/
def idealStep (challenge : History F G → m F) (instruction : Instruction)
    (env : List (Value F G)) (proof : Proof F G) :
    m (Except PIR.Stop (List (Value F G) × Proof F G)) :=
  match instruction.operation, instruction.operands with
  | .receive _ _ _ ty, [] =>
      pure (match proof with
        | payload :: rest => if payload.ty = ty then .ok ([.data payload], rest) else .error .refused
        | [] => .error .refused)
  | .indicesEmpty, [] => pure (.ok ([.indices], proof))
  | .observe _ origin, [state, value, _] =>
      pure (match transcriptAt env state, dataAt env value with
        | some history, some payload =>
            .ok ([.transcript (history ++ [.message origin payload])], proof)
        | _, _ => .error .refused)
  | .challenge _ field origin, [state, _] =>
      match transcriptAt env state with
      | some history =>
          (fun answer => .ok ([.data (.field field answer),
            .transcript (history ++ [.challenge origin])], proof)) <$>
            challenge (history ++ [.challenge origin])
      | none => pure (.error .refused)
  | .calculate op, operands =>
      pure (match operands.mapM (dataAt env) >>= calculate op with
        | some payload => .ok ([.data payload], proof)
        | none => .error .refused)
  | _, _ => pure (.error .refused)

/-- The ideal meaning of an exported constructed program. -/
def ideal (challenge : History F G → m F) (returned : List Nat) :
    List Instruction → List (Value F G) → Proof F G →
      m (PIR.Outcome (List (Value F G)) × Proof F G)
  | [], env, proof => pure (finish returned env, proof)
  | instruction :: rest, env, proof => do
      match ← idealStep challenge instruction env proof with
      | .ok (values, unread) => ideal challenge returned rest (env ++ values) unread
      | .error stop => pure (.stopped stop, proof)

/-- The interactive validator an exported constructed program replaced: each
challenge becomes the selected query on `handle`, followed by its delivery to
the producer. Transcript values are computed as inert histories. -/
def spec (context : Context) (handle : Nat) (returned : List Nat) :
    List Instruction → List (Value F G) → Nat → PIR.Proc (Actions F G) (List (Value F G))
  | [], env, _ =>
      match returned.mapM (env[·]?) with
      | some values => .done values
      | none => .halt .refused
  | instruction :: rest, env, drawn =>
      match instruction.operation, instruction.operands with
      | .receive site _ _ ty, [] =>
          .call (.receive ty site context.producer) fun value =>
            match Payload.ofValue ty value with
            | some payload => spec context handle returned rest (env ++ [.data payload]) drawn
            | none => .halt .refused
      | .indicesEmpty, [] => spec context handle returned rest (env ++ [.indices]) drawn
      | .observe _ origin, [state, value, _] =>
          match transcriptAt env state, dataAt env value with
          | some history, some payload =>
              spec context handle returned rest
                (env ++ [.transcript (history ++ [.message origin payload])]) drawn
          | _, _ => .halt .refused
      | .challenge _ field origin, [state, _] =>
          match transcriptAt env state, context.draws[drawn]? with
          | some history, some (site, delivery) =>
              .call (.query site field (.cons handle .nil)) fun answer =>
                .call (.send (ty := .field field) delivery context.producer answer) fun _ =>
                  spec context handle returned rest
                    (env ++ [.data (.field field answer),
                      .transcript (history ++ [.challenge origin])]) (drawn + 1)
          | _, _ => .halt .refused
      | .calculate op, operands =>
          match operands.mapM (dataAt env) >>= calculate op with
          | some payload => spec context handle returned rest (env ++ [.data payload]) drawn
          | none => .halt .refused
      | _, _ => .halt .refused

end Programs

/-! ## The construction rule -/

/-- An observation the next transcript operation must perform. -/
inductive Pending where
  | none
  | observe (value : Nat) (origin : Origin)
  deriving DecidableEq, Repr

structure CheckState where
  sorts : List ValueSort
  current : Nat
  pending : Pending
  drawn : Nat
  deriving DecidableEq, Repr

def dataSort (ty : Ty) : Bool :=
  match ty with
  | .service _ => false
  | _ => true

/-- One step of the rule. A received message is observed next, with its message
occurrence and the current transcript state. A challenge needs no pending
observation, consumes the current state, carries the next selected query
occurrence, and its delivery is observed next. Calculations read data only.
Coordinates are flat. Every other operation refuses. -/
def checkStep (context : Context) (state : CheckState) (instruction : Instruction) :
    Option CheckState :=
  let fresh := state.sorts.length
  match instruction.operation, instruction.operands, state.pending with
  | .receive site schema peer ty, [], .none =>
      if schema = site ∧ peer = context.role context.producer ∧ dataSort ty = true ∧
          instruction.results = [.data ty] then
        some ⟨state.sorts ++ [.data ty], state.current,
          .observe fresh (context.message site context.producer context.validator), state.drawn⟩
      else none
  | .indicesEmpty, [], _ =>
      if instruction.results = [.indices] then
        some ⟨state.sorts ++ [.indices], state.current, state.pending, state.drawn⟩
      else none
  | .observe suite origin, [current, value, coordinates], .observe expected expectedOrigin =>
      if suite = context.suite ∧ current = state.current ∧ value = expected ∧
          origin = expectedOrigin ∧ state.sorts[coordinates]? = some .indices ∧
          instruction.results = [.transcript context.suite] then
        some ⟨state.sorts ++ [.transcript context.suite], fresh, .none, state.drawn⟩
      else none
  | .challenge suite field origin, [current, coordinates], .none =>
      match context.draws[state.drawn]? with
      | some (site, delivery) =>
          if suite = context.suite ∧ current = state.current ∧ origin = context.query site ∧
              "random." ++ field ++ "/0" = context.contract ∧
              state.sorts[coordinates]? = some .indices ∧
              instruction.results = [.data (.field field), .transcript context.suite] then
            some ⟨state.sorts ++ [.data (.field field), .transcript context.suite], fresh + 1,
              .observe fresh (context.message delivery context.validator context.producer),
              state.drawn + 1⟩
          else none
      | none => none
  | .calculate op, operands, .none =>
      if operands.map (state.sorts[·]?) = (language.arguments op).map (some ∘ .data) ∧
          instruction.results = [.data (language.result op)] then
        some ⟨state.sorts ++ [.data (language.result op)], state.current, .none, state.drawn⟩
      else none
  | _, _, _ => none

def checkFrom (context : Context) : CheckState → List Instruction → Option CheckState
  | state, [] => some state
  | state, instruction :: rest =>
      match checkStep context state instruction with
      | some successor => checkFrom context successor rest
      | none => none

/-- The complete rule for one exported validator. Inputs are data followed by
one host transcript of the selected suite; every selected draw occurs, nothing
remains pending, the last returned value is the final transcript state and the
other returned values are data matching the declared outputs. -/
def check (context : Context) (participant : Participant) : Bool :=
  match participant.inputs.getLast? with
  | some (.transcript suite) =>
      suite = context.suite && participant.inputs.dropLast.all (· matches .data _) &&
      match checkFrom context
          ⟨participant.inputs, participant.inputs.length - 1, .none, 0⟩
          participant.instructions with
      | some final =>
          final.pending == .none && final.drawn == context.draws.length &&
          participant.returned.getLast? == some final.current &&
          participant.returned.map (final.sorts[·]?) == participant.outputs.map some &&
          participant.returned.dropLast.all (fun index => final.sorts[index]? matches some (.data _))
      | none => false
  | _ => false

end Zkc.Construction
