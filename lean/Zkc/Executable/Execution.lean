module

public import Zkc.Executable.Program
public import Zkc.Construction.Semantics

@[expose] public section

/-! The meaning of an executable validator under a native proof host.

`execute` runs the validator's instructions as the native runner does. Each
local call becomes a frame entry, the body's operations and the frame's
return; every one of them, every receive and the final return is charged one
instruction against the host's budget, and the budget is checked before each
participant action is exposed. A receive reads the next length-framed message
of the proof and decodes it at the receive's physical type: a missing message
cancels the run, a decoding failure stops it after charging the receive. A stop
leaves every active frame, innermost first, and retires the live transcript;
a normal return hands the returned transcript to the host, which retires it.

Installed operations are interpreted through a `Vocabulary`: each row assigns
a meaning to an exact contract, static arguments and implementation. Values
and transcript histories are those of the ideal transcript model of
`Zkc.Construction`: an observation appends the model occurrence of its template
under the deployment `Context`, and a challenge applies the challenge function
to the history ending with its occurrence; a template without a model
occurrence stops the run. Calculations have the structured meaning of
`Zkc.Construction.calculate`. The transcript is an affine unit: an operation
must consume its live state.

`validate` adds the host's acceptance: the framing header names the expected
invocation binding, the run returns normally with the selected Boolean true,
and every proof byte is read.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

/-! ## Installed operations -/

/-- The meaning assumed for an installed operation. -/
inductive Kernel where
  | indicesEmpty
  | observe (suite : String) (leaf : Structured.Ty)
  | challenge (suite field : String)
  | calculate (calculation : Calculation)
  deriving DecidableEq, Repr

/-- One installed operation: a binding's contract, static arguments and
implementation, and the meaning assumed for it. -/
structure Installed where
  contract : String
  arguments : List String
  implementation : String
  kernel : Kernel
  deriving DecidableEq, Repr

/-- Installed operations and the representations admitted for value sorts. -/
structure Vocabulary where
  operations : List Installed
  representations : List (ValueSort × String)
  deriving DecidableEq, Repr

/-- An operation with its meaning and decoded occurrence template. -/
inductive Resolved where
  | indicesEmpty
  | observe (suite : String) (leaf : Structured.Ty) (template : Template)
  | challenge (suite field : String) (template : Template)
  | calculate (calculation : Calculation)
  deriving DecidableEq, Repr

def Vocabulary.installed? (vocabulary : Vocabulary) (binding : Binding) : Option Installed :=
  vocabulary.operations.find? fun row =>
    row.contract == binding.contract && row.arguments == binding.arguments &&
      row.implementation == binding.implementation

/-- Resolve a binding and its parameters: transcript operations carry exactly
one occurrence; other operations carry none. -/
def Vocabulary.resolve (vocabulary : Vocabulary) (binding : Binding)
    (parameters : List Parameter) : Option Resolved :=
  match vocabulary.installed? binding with
  | some row =>
      match row.kernel, parameters with
      | .indicesEmpty, [] => some .indicesEmpty
      | .observe suite leaf, [.template template] => some (.observe suite leaf template)
      | .challenge suite field, [.template template] => some (.challenge suite field template)
      | .calculate calculation, [] => some (.calculate calculation)
      | _, _ => none
  | none => none

def Validator.function? (validator : Validator) (symbol : String) : Option Function :=
  validator.functions.find? (·.symbol == symbol)

def Validator.binding? (validator : Validator) (symbol : String) : Option Binding :=
  validator.bindings.find? (·.symbol == symbol)

/-! ## Machine work -/

/-- Work of the machine after unfolding local calls: a frame entry, each body
operation and the frame's return are separate charged items. -/
inductive Item where
  | receive (site schema peer output : String) (type : PhysicalType)
  | enter (site function : String) (arguments formals : List String)
  | operation (call function site binding : String) (parameters : List Parameter)
      (inputs outputs : List String)
  | leave (call function : String) (values outputs : List String) (results : List PhysicalType)
  | finish (values : List String)
  | unsupported (name : String)
  deriving DecidableEq, Repr

/-- Unfold one straight-line local function body; it must end in its only
return. -/
def unfoldBody (call function : String) (outputs : List String) (results : List PhysicalType) :
    List Step → List Item
  | [] => [.unsupported "missing-return"]
  | .operation site binding parameters inputs produced :: rest =>
      .operation call function site binding parameters inputs produced ::
        unfoldBody call function outputs results rest
  | [.ret values] => [.leave call function values outputs results]
  | .ret _ :: _ :: _ => [.unsupported "return-not-final"]
  | .unsupported name :: _ => [.unsupported name]

/-- Unfold the participant body. The final return ends the work. -/
def Validator.unfold (validator : Validator) : List Action → List Item
  | [] => []
  | .receive site schema peer output type :: rest =>
      .receive site schema peer output type :: validator.unfold rest
  | .call site function inputs outputs :: rest =>
      match validator.function? function with
      | some callee =>
          .enter site function inputs (callee.inputs.map (·.1)) ::
            (unfoldBody site function outputs callee.results callee.body ++ validator.unfold rest)
      | none => [.unsupported function]
  | [.ret values] => [.finish values]
  | .ret _ :: _ :: _ => [.unsupported "return-not-final"]
  | .unsupported name :: _ => [.unsupported name]

/-! ## Proof framing -/

/-- Little-endian unsigned value of a byte list. -/
def littleEndian : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * littleEndian rest

/-- The host's ceiling on one proof, and therefore on one message. -/
def proofLimit : Nat := 16777216

/-- Read one message: an eight-byte little-endian length and that many bytes.
A short length, an oversized length or a short payload has no message. -/
def readFrame (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  if bytes.length < 8 ∨ proofLimit < littleEndian (bytes.take 8) then none
  else
    let rest := bytes.drop 8
    if rest.length < littleEndian (bytes.take 8) then none
    else some (rest.take (littleEndian (bytes.take 8)), rest.drop (littleEndian (bytes.take 8)))

/-- The framing magic `ZKCPRF00`. -/
def magic : List UInt8 := [0x5a, 0x4b, 0x43, 0x50, 0x52, 0x46, 0x30, 0x30]

/-! ## Machine state and results -/

inductive FrameId where
  | participant
  | call (site function : String)
  deriving DecidableEq, Repr

inductive Exit where
  | returned
  | stopped
  | cancelled
  deriving DecidableEq, Repr

inductive FrameEvent where
  | enter (frame : FrameId)
  | leave (frame : FrameId) (exit : Exit)
  deriving DecidableEq, Repr

/-- Why a run ended without returning. -/
inductive Cause where
  /-- The instruction budget was exhausted. -/
  | limit
  /-- A received message did not decode at its type. -/
  | decode
  /-- No complete message remained; the host cancels the runner. -/
  | truncated
  /-- An operand, binding, frame, type or custody check failed. -/
  | contract
  deriving DecidableEq, Repr

variable {F G : Type}

abbrev Env (F G : Type) := List (String × Value F G)

structure Frame (F G : Type) where
  id : FrameId
  env : Env F G

structure State (F G : Type) where
  used : Nat
  transitions : Nat
  messages : Nat
  proof : List UInt8
  live : History F G
  frames : List (Frame F G)
  events : List FrameEvent

inductive Result (F G : Type) where
  | returned (values : List (Value F G))
  | stopped (cause : Cause) (site : Option String) (call : Option (String × String))

/-- A complete run: its result, charged instructions, applied transcript
transitions, read messages, unread proof bytes, retired transcript histories
and frame events. -/
structure Run (F G : Type) where
  result : Result F G
  used : Nat
  transitions : Nat
  messages : Nat
  unread : List UInt8
  retired : List (History F G)
  events : List FrameEvent

/-- Stop: leave every active frame, innermost first, and retire the live
transcript. A truncated proof cancels the runner instead. -/
def State.stop (s : State F G) (cause : Cause) (site : Option String)
    (call : Option (String × String)) : Run F G :=
  ⟨.stopped cause site call, s.used, s.transitions, s.messages, s.proof, [s.live],
    s.events ++ s.frames.map fun frame =>
      .leave frame.id (if cause = .truncated then .cancelled else .stopped)⟩

/-- Return normally: leave the participant frame; the host retires the
returned transcript. -/
def State.done (s : State F G) (values : List (Value F G)) : Run F G :=
  ⟨.returned values, s.used, s.transitions, s.messages, s.proof, [s.live],
    s.events ++ [.leave .participant .returned]⟩

def lookupAll (env : Env F G) (names : List String) : Option (List (Value F G)) :=
  names.mapM fun name => List.lookup name env

/-- The structured type of a decoded payload. -/
def payloadType : Payload F G → Structured.Ty
  | .boolean _ => .boolean
  | .field domain _ => .field domain
  | .group domain _ => .group domain

/-- Whether returned values hand back only the live transcript. -/
def custodyKept [DecidableEq F] [DecidableEq G] (live : History F G) (values : List (Value F G)) : Bool :=
  values.all fun value =>
    match value with
    | .transcript history => history == live
    | _ => true

section Machine
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]

/-- Apply a resolved operation to its argument values and the live transcript:
the results, the transcript after the operation and the transitions applied.
Occurrence templates are named by their model occurrence under `context`. -/
def Resolved.apply (context : Context) (challenge : History F G → m F) (live : History F G) :
    Resolved → List (Value F G) → m (Option (List (Value F G) × History F G × Nat))
  | .indicesEmpty, [] => pure (some ([.indices []], live, 0))
  | .observe _ leaf template, [.transcript history, .data payload, .indices _] =>
      pure (match template.origin context with
        | some origin =>
            if history = live ∧ payloadType payload = leaf then
              some ([.transcript (history ++ [.message origin payload])],
                history ++ [.message origin payload], 1)
            else none
        | none => none)
  | .challenge _ field template, [.transcript history, .indices _] =>
      match template.origin context with
      | some origin =>
          if history = live then
            (fun answer => some ([.data (.field field answer),
                .transcript (history ++ [.challenge origin])],
              history ++ [.challenge origin], 1)) <$> challenge (history ++ [.challenge origin])
          else pure none
      | none => pure none
  | .calculate calculation, arguments =>
      pure (match Zkc.Construction.calculate calculation arguments with
        | .returned results => some (results, live, 0)
        | .stopped _ => none)
  | _, _ => pure none

variable (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
  (budget : Nat)

/-- Run machine work. -/
def run : List Item → State F G → m (Run F G)
  | [], s => pure (s.stop .contract none none)
  | .receive site _ _ output type :: rest, s =>
      if s.used < budget then
        match readFrame s.proof with
        | none => pure (s.stop .truncated none none)
        | some (payload, unread) =>
            match decode type payload, s.frames with
            | none, _ =>
                pure ({ s with
                        used := s.used + 1
                        proof := unread
                        messages := s.messages + 1 }.stop .decode (some site) none)
            | some value, frame :: below =>
                if type.sort = .data (payloadType value) then
                  run rest { s with
                             used := s.used + 1
                             proof := unread
                             messages := s.messages + 1
                             frames := ⟨frame.id, (output, .data value) :: frame.env⟩ :: below }
                else
                  pure ({ s with
                          proof := unread
                          messages := s.messages + 1 }.stop .contract (some site) none)
            | some _, [] => pure (s.stop .contract (some site) none)
      else pure (s.stop .limit none none)
  | .enter site function arguments formals :: rest, s =>
      if s.used < budget then
        match s.frames with
        | frame :: _ =>
            match lookupAll frame.env arguments with
            | some values =>
                if formals.length = values.length then
                  run rest { s with
                             used := s.used + 1
                             frames := ⟨.call site function, formals.zip values⟩ :: s.frames
                             events := s.events ++ [.enter (.call site function)] }
                else pure (s.stop .contract (some site) none)
            | none => pure (s.stop .contract (some site) none)
        | [] => pure (s.stop .contract (some site) none)
      else pure (s.stop .limit none none)
  | .operation call function _ binding parameters inputs outputs :: rest, s =>
      if s.used < budget then
        match s.frames, validator.binding? binding >>= (vocabulary.resolve · parameters) with
        | frame :: below, some resolved =>
            match lookupAll frame.env inputs with
            | some arguments => do
                match ← resolved.apply context challenge s.live arguments with
                | some (results, live, transitions) =>
                    if outputs.length = results.length then
                      run rest { s with
                                 used := s.used + 1
                                 live := live
                                 transitions := s.transitions + transitions
                                 frames := ⟨frame.id, outputs.zip results ++ frame.env⟩ :: below }
                    else pure ({ s with used := s.used + 1 }.stop .contract (some call) (some (call, function)))
                | none => pure ({ s with used := s.used + 1 }.stop .contract (some call) (some (call, function)))
            | none => pure ({ s with used := s.used + 1 }.stop .contract (some call) (some (call, function)))
        | _, _ => pure ({ s with used := s.used + 1 }.stop .contract (some call) (some (call, function)))
      else pure (s.stop .limit (some call) (some (call, function)))
  | .leave call function values outputs _ :: rest, s =>
      if s.used < budget then
        match s.frames with
        | frame :: caller :: below =>
            match lookupAll frame.env values with
            | some results =>
                if outputs.length = results.length then
                  run rest { s with
                             used := s.used + 1
                             frames := ⟨caller.id, outputs.zip results ++ caller.env⟩ :: below
                             events := s.events ++ [.leave frame.id .returned] }
                else pure ({ s with used := s.used + 1 }.stop .contract (some call) (some (call, function)))
            | none => pure ({ s with used := s.used + 1 }.stop .contract (some call) (some (call, function)))
        | _ => pure ({ s with used := s.used + 1 }.stop .contract (some call) (some (call, function)))
      else pure (s.stop .limit (some call) (some (call, function)))
  | .finish values :: _, s =>
      if s.used < budget then
        match s.frames with
        | [frame] =>
            match lookupAll frame.env values with
            | some results =>
                if custodyKept s.live results then pure ({ s with used := s.used + 1 }.done results)
                else pure ({ s with used := s.used + 1 }.stop .contract none none)
            | none => pure ({ s with used := s.used + 1 }.stop .contract none none)
        | _ => pure ({ s with used := s.used + 1 }.stop .contract none none)
      else pure (s.stop .limit none none)
  | .unsupported _ :: _, s => pure (s.stop .contract none none)

/-- Entry inputs: the data inputs, at their declared sorts, followed by the
host's transcript. -/
def Validator.admits (data : List (Payload F G)) : Bool :=
  (validator.inputs.map (·.2.sort)).dropLast ==
      data.map (fun payload => ValueSort.data (payloadType payload)) &&
  match validator.inputs.getLast? with
  | some (_, type) => (type.sort matches .transcript _)
  | none => false

/-- The initial machine state for data inputs, the host's initial transcript and
the proof's message bytes. -/
def initial (data : List (Payload F G)) (history : History F G) (bytes : List UInt8) : State F G :=
  ⟨0, 0, 0, bytes, history,
    [⟨.participant, (validator.inputs.map (·.1)).zip (data.map .data ++ [.transcript history])⟩],
    [.enter .participant]⟩

/-- The meaning of the validator on data inputs, the host's initial transcript
and the proof's message bytes (after the framing header). -/
def execute (data : List (Payload F G)) (history : History F G) (bytes : List UInt8) : m (Run F G) :=
  if validator.admits data then
    run vocabulary validator context challenge decode budget (validator.unfold validator.body)
      (initial validator data history bytes)
  else pure ((initial validator data history bytes).stop .contract none none)

/-- Whether the selected returned value is the Boolean true. -/
def selectedTrue (values : List (Value F G)) (acceptance : Nat) : Bool :=
  match values[acceptance]? with
  | some (.data (.boolean true)) => true
  | _ => false

/-- Host acceptance of a run: a normal return with the selected Boolean true
and no unread proof byte. -/
def Run.accepts (result : Run F G) (acceptance : Nat) : Bool :=
  match result.result with
  | .returned values => result.unread.isEmpty && selectedTrue values acceptance
  | .stopped _ _ _ => false

/-- The host's validation of complete proof bytes: the framing header must
carry the expected invocation binding, then the run must be accepted. -/
def validate (binding : List UInt8) (acceptance : Nat) (data : List (Payload F G))
    (history : History F G) (bytes : List UInt8) : m Bool :=
  if bytes.take 40 = magic ++ binding then
    (fun result => result.accepts acceptance) <$>
      execute vocabulary validator context challenge decode budget data history (bytes.drop 40)
  else pure false

end Machine

end Zkc.Executable
