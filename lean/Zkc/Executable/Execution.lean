module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Executable.Program
public import Zkc.Executable.Numerical
public import Zkc.Construction.Semantics

@[expose] public section

/-! The meaning of an executable validator under a native proof host.

`execute` runs the validator's instructions as the native runner does. A local
call enters a frame and runs the function's body, and every loop iteration runs
the loop body in a frame of its own. Every receive, local call, loop, yield and
return of the participant and every instruction of a local body is charged one
instruction against the host's budget; the budget is checked before each
charge, so a budget of `b` executes exactly the first `b` charged steps. A
receive reads the next length-framed message of the proof and decodes it at the
receive's physical type: a missing message cancels the run, a decoding failure
stops it after charging the receive. A stop leaves every active frame,
innermost first, and retires the live transcript; a normal return hands the
returned transcript to the host, which retires it. The runner's other resources
(loop iterations, retained values and bytes, logical work, a numerical call's
work and managed memory, and frame depth) are not modelled: their exhaustion
only stops a run.

Installed operations are interpreted through a `Vocabulary`: each row assigns
a meaning to an exact contract, static arguments and implementation. Values
and transcript histories are those of the ideal transcript model of
`Zkc.Construction`: an observation appends the model occurrence of its template
under the deployment `Context`, and a challenge applies the challenge function
to the history ending with its occurrence; a template without a model
occurrence stops the run. Calculations have the structured meaning of
`Zkc.Construction.calculate` and the structured primitives their meaning of
`Zkc.Source.Structured.Primitive.evaluate`. A numerical call evaluates the
expression its parameter carries (`Zkc.Executable.Numerical.decode`) at every
row of its domain. The transcript is an affine unit: an operation must consume
its live state.

`validate` adds the host's acceptance: the framing header names the expected
invocation binding, the run returns normally with the selected Boolean true,
and every proof byte is read.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

/-! ## Installed operations -/

/-- Operations of local bodies that are not structured calculations: the
structured index and vector primitives, pointwise vector arithmetic, the
requirement that a Boolean is true, and a numerical call: an expression over
the field `domain`, read at every row with one operand per mask position (a
scalar for `false`, a vector for `true`), combined by its reduction. -/
inductive Computation where
  | primitive (primitive : Structured.Primitive)
  | vectorAdd (domain : String)
  | vectorSubtract (domain : String)
  | vectorScale (domain : String)
  | require
  | numerical (reduction : Numerical.Reduction) (domain : String) (mask : List Bool)
      (expression : Zkc.Algebra.RingExpression.Expr Nat Nat)
  deriving DecidableEq, Repr

/-- The meaning assumed for an installed operation. Constants take their value
from the operation's single canonical decimal parameter. A numerical row takes
the operand mask as its last static argument and the expression as its single
parameter; `characteristic` is its field's. -/
inductive Kernel where
  | indicesEmpty
  | indicesAppend
  | observe (suite : String) (leaf : Structured.Ty)
  | challenge (suite field : String)
  | calculate (calculation : Calculation)
  | indexConstant
  | fieldConstant (domain : String)
  | compute (operation : Computation)
  | numerical (reduction : Numerical.Reduction) (domain : String) (characteristic : Nat)
  deriving DecidableEq, Repr

/-- One installed operation: a binding's contract, logical arguments,
implementation, exact physical specialization and the meaning assumed for it. -/
structure Installed where
  contract : String
  arguments : List String
  implementation : String
  kernel : Kernel
  physicalArguments : List PhysicalType
  deriving DecidableEq, Repr

/-- Installed operations and the representations admitted for value sorts. -/
structure Vocabulary where
  operations : List Installed
  representations : List (ValueSort × String)
  deriving DecidableEq, Repr

/-- An operation with its meaning, its decoded occurrence template and its
constant. -/
inductive Resolved where
  | indicesEmpty
  | indicesAppend
  | observe (suite : String) (leaf : Structured.Ty) (template : Template)
  | challenge (suite field : String) (template : Template)
  | calculate (calculation : Calculation)
  | compute (operation : Computation)
  deriving DecidableEq, Repr

/-- The value of a canonical decimal spelling: one or more digits, without a
leading zero. -/
def decimalValue? (text : String) : Option Nat :=
  let digits := text.toList
  if digits.isEmpty || (digits.length > 1 && digits.head? == some '0') ||
      !digits.all Char.isDigit then none
  else some (digits.foldl (fun value digit => 10 * value + (digit.toNat - '0'.toNat)) 0)

/-- Whether a row takes a binding's static arguments: exactly its own, or, for
a numerical row, its own followed by the operand mask. -/
def Installed.takes (row : Installed) (arguments : List String) : Bool :=
  match row.kernel with
  | .numerical _ _ _ => arguments.length == row.arguments.length + 1 && arguments.dropLast == row.arguments
  | _ => arguments == row.arguments

def Vocabulary.installed? (vocabulary : Vocabulary) (binding : Binding) : Option Installed :=
  vocabulary.operations.find? fun row =>
    row.contract == binding.contract && row.takes binding.arguments &&
      row.implementation == binding.implementation &&
      row.physicalArguments == binding.physicalArguments

/-- Resolve a binding and its parameters: transcript operations carry exactly
one occurrence, constants exactly one canonical decimal below `2 ^ 64`, a
numerical call exactly one expression that `Numerical.decode` admits for its
mask (`Numerical.mask?`), and other operations none. -/
def Vocabulary.resolve (vocabulary : Vocabulary) (binding : Binding)
    (parameters : List Parameter) : Option Resolved :=
  match vocabulary.installed? binding with
  | some row =>
      match row.kernel, parameters with
      | .indicesEmpty, [] => some .indicesEmpty
      | .indicesAppend, [] => some .indicesAppend
      | .observe suite leaf, [.template template] => some (.observe suite leaf template)
      | .challenge suite field, [.template template] => some (.challenge suite field template)
      | .calculate calculation, [] => some (.calculate calculation)
      | .indexConstant, [.text text] =>
          (decimalValue? text).bind fun value =>
            if value < Structured.indexLimit then some (.calculate (.indexConstant value)) else none
      | .fieldConstant domain, [.text text] =>
          (decimalValue? text).map fun value => .calculate (.fieldConstant domain value)
      | .compute operation, [] => some (.compute operation)
      | .numerical reduction domain characteristic, [.text body] =>
          (binding.arguments.getLast? >>= Numerical.mask?).bind fun mask =>
            (Numerical.decode domain characteristic mask.length body).toOption.map fun expression =>
              .compute (.numerical reduction domain mask expression)
      | _, _ => none
  | none => none

def Validator.function? (validator : Validator) (symbol : String) : Option Function :=
  validator.functions.find? (·.symbol == symbol)

def Validator.binding? (validator : Validator) (symbol : String) : Option Binding :=
  validator.bindings.find? (·.symbol == symbol)

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
  | loop (site : String) (iteration : Nat)
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
  /-- An operand, binding, frame, type, count or custody check failed. -/
  | contract
  /-- An installed operation stopped for this reason. -/
  | kernel (reason : PIR.Stop)
  /-- An explicit stop instruction with this reason. -/
  | explicit (reason : PIR.Stop)
  deriving DecidableEq, Repr

/-- The reason an explicit stop names. -/
def stopReason? : String → Option PIR.Stop
  | "reject" => some .reject
  | "abort" => some .abort
  | "exhausted" => some .exhausted
  | "incomplete" => some .incomplete
  | "refused" => some .refused
  | _ => none

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

/-- Charge one instruction. -/
def State.charge (s : State F G) : State F G := { s with used := s.used + 1 }

/-- Bind names in the innermost participant frame. -/
def State.bind (s : State F G) (names : List String) (values : List (Value F G)) : State F G :=
  match s.frames with
  | frame :: below => { s with frames := ⟨frame.id, names.zip values ++ frame.env⟩ :: below }
  | [] => s

def lookupAll (env : Env F G) (names : List String) : Option (List (Value F G)) :=
  names.mapM fun name => List.lookup name env

/-- The structured type of a decoded payload. -/
def payloadType : Payload F G → Structured.Ty
  | .boolean _ => .boolean
  | .field domain _ => .field domain
  | .group domain _ => .group domain

/-- The sort of a data value: a scalar, an index or a field vector. -/
def dataSort? : Value F G → Option ValueSort
  | .data payload => some (.data (payloadType payload))
  | .index _ => some (.data .index)
  | .vector domain _ => some (.data (.vector domain))
  | _ => none

/-- Whether returned values hand back only the live transcript. -/
def custodyKept [DecidableEq F] [DecidableEq G] (live : History F G) (values : List (Value F G)) : Bool :=
  values.all fun value =>
    match value with
    | .transcript history => history == live
    | _ => true

/-- One operand of a numerical call: a scalar for every row, or a column with
a value per row. -/
inductive Numerical.Slot (F : Type) where
  | scalar (value : F)
  | column (values : List F)

/-- The value a slot gives at a row. -/
def Numerical.Slot.read [Zero F] (row : Nat) : Numerical.Slot F → F
  | .scalar value => value
  | .column values => values.getD row 0

/-- The operands of a numerical call over `domain` with `rows` rows, as slots:
one scalar of the field for each `false` of the mask and one vector of exactly
`rows` values for each `true`, including slots the expression does not read. -/
def Numerical.slots (domain : String) (rows : Nat) :
    List Bool → List (Value F G) → Option (List (Numerical.Slot F))
  | [], [] => some []
  | false :: mask, .data (.field field value) :: rest =>
      if field = domain then (.scalar value :: ·) <$> Numerical.slots domain rows mask rest else none
  | true :: mask, .vector field values :: rest =>
      if field = domain ∧ values.length = rows then
        (.column values :: ·) <$> Numerical.slots domain rows mask rest
      else none
  | _, _ => none

/-- The expression's value at a row: each input reads its slot at the row, and
each literal is the natural number in the field. -/
def Numerical.row [CommRing F] (expression : Zkc.Algebra.RingExpression.Expr Nat Nat)
    (slots : List (Numerical.Slot F)) (row : Nat) : F :=
  (expression.map fun literal : Nat => (literal : F)).eval fun slot =>
    ((slots[slot]?).map (·.read row)).getD 0

section Machine
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]

/-- The meaning of a pure operation on its argument values. A numerical call
reads the row count, then its operands: an operand count other than the mask's,
an operand of another kind or field, or a vector of another length is refused.
A map returns the vector of the expression's values at the rows, a sum their
sum from zero and a product their product from one. The runtime's bound on a
call's rows (`Numerical.rowLimit`) is a native capacity limit, like the element
limit of every vector a kernel produces: neither stops this meaning. -/
def Computation.apply : Computation → List (Value F G) → PIR.Outcome (List (Value F G))
  | .primitive operation, arguments =>
      match decodeValues operation.arguments arguments with
      | some values =>
          match operation.evaluate values with
          | .returned results => .returned (encodeValues results)
          | .stopped reason => .stopped reason
      | none => .stopped .refused
  | .vectorAdd domain, [.vector first xs, .vector second ys] =>
      if first = domain ∧ second = domain ∧ xs.length = ys.length then
        .returned [.vector domain (List.zipWith (· + ·) xs ys)]
      else .stopped .refused
  | .vectorSubtract domain, [.vector first xs, .vector second ys] =>
      if first = domain ∧ second = domain ∧ xs.length = ys.length then
        .returned [.vector domain (List.zipWith (· - ·) xs ys)]
      else .stopped .refused
  | .vectorScale domain, [.vector first xs, .data (.field second scalar)] =>
      if first = domain ∧ second = domain then .returned [.vector domain (xs.map (· * scalar))]
      else .stopped .refused
  | .require, [.data (.boolean true)] => .returned []
  | .numerical reduction domain mask expression, .index rows :: operands =>
      match Numerical.slots domain rows mask operands with
      | some slots =>
          let values := (List.range rows).map (Numerical.row expression slots)
          match reduction with
          | .map => .returned [.vector domain values]
          | .sum => .returned [.data (.field domain (values.foldl (· + ·) 0))]
          | .product => .returned [.data (.field domain (values.foldl (· * ·) 1))]
      | none => .stopped .refused
  | _, _ => .stopped .refused

/-- Apply a resolved operation to its argument values and the live transcript:
the results, the transcript after the operation and the transitions applied,
or the reason the operation stops. Occurrence templates are named by their
model occurrence under `context`. -/
def Resolved.apply (context : Context) (challenge : History F G → m F) (live : History F G) :
    Resolved → List (Value F G) → m (PIR.Outcome (List (Value F G) × History F G × Nat))
  | .indicesEmpty, [] => pure (.returned ([.indices []], live, 0))
  | .indicesAppend, [.indices coordinates, .index index] =>
      pure (.returned ([.indices (coordinates ++ [index])], live, 0))
  | .observe _ leaf template, [.transcript history, .data payload, .indices _] =>
      pure (match template.origin context with
        | some origin =>
            if history = live ∧ payloadType payload = leaf then
              .returned ([.transcript (history ++ [.message origin payload])],
                history ++ [.message origin payload], 1)
            else .stopped .refused
        | none => .stopped .refused)
  | .challenge _ field template, [.transcript history, .indices _] =>
      match template.origin context with
      | some origin =>
          if history = live then
            (fun answer => .returned ([.data (.field field answer),
                .transcript (history ++ [.challenge origin])],
              history ++ [.challenge origin], 1)) <$> challenge (history ++ [.challenge origin])
          else pure (.stopped .refused)
      | none => pure (.stopped .refused)
  | .calculate calculation, arguments =>
      pure (match Zkc.Construction.calculate calculation arguments with
        | .returned results => .returned (results, live, 0)
        | .stopped reason => .stopped reason)
  | .compute operation, arguments =>
      pure (match operation.apply arguments with
        | .returned results => .returned (results, live, 0)
        | .stopped reason => .stopped reason)
  | _, _ => pure (.stopped .refused)

variable (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
  (budget : Nat)

/-! ## Local bodies -/

/-- Run a counted iteration's region for each index: the region sees the index,
the carried values and the captures, and what it yields is carried into the
next iteration. -/
def forK (run : Env F G → State F G →
      (List (Value F G) → State F G → m (Run F G)) → m (Run F G))
    (site induction : String) (carried : List String) (captured : Env F G)
    (call : String × String) :
    List Nat → List (Value F G) → State F G →
      (List (Value F G) → State F G → m (Run F G)) → m (Run F G)
  | [], values, s, done => done values s
  | index :: rest, values, s, done =>
      run ((induction, .index index) :: carried.zip values ++ captured) s fun yielded s' =>
        if yielded.length = carried.length then
          forK run site induction carried captured call rest yielded s' done
        else pure (s'.stop .contract (some site) (some call))

mutual
/-- Run a local body for the call `call`: `top` marks the function's own body,
as opposed to a region, and `region` is the site of the innermost enclosing
region. A stop is reported at the failing instruction's own site; an operation
of the function's own body, and a yield or return, report the call's site or
the region's. `exit` receives the values a yield or return hands back. -/
def localK (call : String × String) (top : Bool) (region : Option String) :
    List Step → Env F G → State F G →
      (List (Value F G) → State F G → m (Run F G)) → m (Run F G)
  | [], _, s, _ => pure (s.stop .contract (if top then some call.1 else region) (some call))
  | step :: rest, env, s, exit =>
      localStep call top region step env s (fun env' s' => localK call top region rest env' s' exit) exit

def localStep (call : String × String) (top : Bool) (region : Option String) :
    Step → Env F G → State F G → (Env F G → State F G → m (Run F G)) →
      (List (Value F G) → State F G → m (Run F G)) → m (Run F G)
  | .operation site binding parameters inputs outputs, env, s, next, _ =>
      let place := if top then some call.1 else some site
      if s.used < budget then
        match validator.binding? binding >>= (vocabulary.resolve · parameters),
            lookupAll env inputs with
        | some resolved, some arguments =>
            resolved.apply context challenge s.live arguments >>= fun applied =>
            match applied with
            | .returned (results, live, transitions) =>
                if outputs.length = results.length then
                  next (outputs.zip results ++ env)
                    { s.charge with live := live, transitions := s.transitions + transitions }
                else pure (s.charge.stop .contract place (some call))
            | .stopped reason => pure (s.charge.stop (.kernel reason) place (some call))
        | _, _ => pure (s.charge.stop .contract place (some call))
      else pure (s.stop .limit place (some call))
  | .constant site output value, env, s, next, _ =>
      if s.used < budget then next ((output, .data (.boolean value)) :: env) s.charge
      else pure (s.stop .limit (some site) (some call))
  | .cond site condition captures yes no outputs, env, s, next, _ =>
      if s.used < budget then
        match List.lookup condition env, lookupAll env captures with
        | some (.data (.boolean true)), some captured =>
            localK call false (some site) yes (captures.zip captured) s.charge fun results s' =>
              if outputs.length = results.length then next (outputs.zip results ++ env) s'
              else pure (s'.stop .contract (some site) (some call))
        | some (.data (.boolean false)), some captured =>
            localK call false (some site) no (captures.zip captured) s.charge fun results s' =>
              if outputs.length = results.length then next (outputs.zip results ++ env) s'
              else pure (s'.stop .contract (some site) (some call))
        | _, _ => pure (s.charge.stop .contract (some site) (some call))
      else pure (s.stop .limit (some site) (some call))
  | .iterate site induction lower upper carried captures body outputs, env, s, next, _ =>
      if s.used < budget then
        match List.lookup lower env, List.lookup upper env,
            lookupAll env (carried.map (·.2)), lookupAll env captures with
        | some (.index first), some (.index last), some initial, some captured =>
            if first ≤ 1048576 ∧ last ≤ 1048576 ∧ last - first ≤ 1048576 then
              forK (fun env' s' exit => localK call false (some site) body env' s' exit) site induction
                (carried.map (·.1)) (captures.zip captured) call (List.range' first (last - first))
                initial s.charge fun final s' =>
                  if outputs.length = final.length then next (outputs.zip final ++ env) s'
                  else pure (s'.stop .contract (some site) (some call))
            else pure (s.charge.stop (.kernel .exhausted) (some site) (some call))
        | _, _, _, _ => pure (s.charge.stop .contract (some site) (some call))
      else pure (s.stop .limit (some site) (some call))
  | .stop site reason, _, s, _, _ =>
      if s.used < budget then
        match stopReason? reason with
        | some stop => pure (s.charge.stop (.explicit stop) (some site) (some call))
        | none => pure (s.charge.stop .contract (some site) (some call))
      else pure (s.stop .limit (some site) (some call))
  | .yield values, env, s, _, exit =>
      let place := if top then some call.1 else region
      if s.used < budget then
        match lookupAll env values with
        | some results => exit results s.charge
        | none => pure (s.charge.stop .contract place (some call))
      else pure (s.stop .limit place (some call))
  | .ret values, env, s, _, exit =>
      let place := if top then some call.1 else region
      if s.used < budget then
        match lookupAll env values with
        | some results => exit results s.charge
        | none => pure (s.charge.stop .contract place (some call))
      else pure (s.stop .limit place (some call))
  | .unsupported _, _, s, _, _ => pure (s.stop .contract (if top then some call.1 else region) (some call))
end

/-! ## Local bodies without transcript operations

A local body that applies no transcript operation does not depend on the
challenge function or the live transcript. `evalSteps` gives its unbounded
meaning: what it hands back or why it stops, and how many instructions it
charges until then. `Zkc.Executable.Soundness` shows that `localK` on such a
body is this evaluation, cut off by the budget. -/

/-- What a local body or region hands back, or why it stops, with the
instructions it charges until then. -/
inductive Evaluated (F G : Type) where
  | values (results : List (Value F G)) (cost : Nat)
  | stopped (cause : Cause) (cost : Nat)

/-- The instructions an evaluation charges. -/
def Evaluated.cost : Evaluated F G → Nat
  | .values _ cost => cost
  | .stopped _ cost => cost

/-- Charge `extra` instructions before an evaluation. -/
def Evaluated.after (extra : Nat) : Evaluated F G → Evaluated F G
  | .values results cost => .values results (extra + cost)
  | .stopped cause cost => .stopped cause (extra + cost)

/-- One evaluated step: continue in an extended environment after charging, or
end. -/
inductive Stepped (F G : Type) where
  | next (env : Env F G) (cost : Nat)
  | done (result : Evaluated F G)

/-- Apply a resolved operation without a transcript: transcript operations
refuse. -/
def Resolved.evaluate : Resolved → List (Value F G) → PIR.Outcome (List (Value F G))
  | .indicesEmpty, [] => .returned [.indices []]
  | .indicesAppend, [.indices coordinates, .index index] => .returned [.indices (coordinates ++ [index])]
  | .calculate calculation, arguments => Zkc.Construction.calculate calculation arguments
  | .compute operation, arguments => operation.apply arguments
  | _, _ => .stopped .refused

/-- Iterate a region without a transcript. -/
def evalFor (run : Env F G → Evaluated F G) (induction : String) (carried : List String)
    (captured : Env F G) : List Nat → List (Value F G) → Evaluated F G
  | [], values => .values values 0
  | index :: rest, values =>
      match run ((induction, .index index) :: carried.zip values ++ captured) with
      | .values yielded cost =>
          if yielded.length = carried.length then
            (evalFor run induction carried captured rest yielded).after cost
          else .stopped .contract cost
      | .stopped cause cost => .stopped cause cost

mutual
/-- The unbounded meaning of a local body without transcript operations. -/
def evalSteps : List Step → Env F G → Evaluated F G
  | [], _ => .stopped .contract 0
  | step :: rest, env =>
      match evalStep step env with
      | .next env' cost => (evalSteps rest env').after cost
      | .done result => result

def evalStep : Step → Env F G → Stepped F G
  | .operation _ binding parameters inputs outputs, env =>
      match validator.binding? binding >>= (vocabulary.resolve · parameters), lookupAll env inputs with
      | some resolved, some arguments =>
          match resolved.evaluate arguments with
          | .returned results =>
              if outputs.length = results.length then .next (outputs.zip results ++ env) 1
              else .done (.stopped .contract 1)
          | .stopped reason => .done (.stopped (.kernel reason) 1)
      | _, _ => .done (.stopped .contract 1)
  | .constant _ output value, env => .next ((output, .data (.boolean value)) :: env) 1
  | .cond _ condition captures yes no outputs, env =>
      match List.lookup condition env, lookupAll env captures with
      | some (.data (.boolean true)), some captured =>
          match evalSteps yes (captures.zip captured) with
          | .values results cost =>
              if outputs.length = results.length then .next (outputs.zip results ++ env) (1 + cost)
              else .done (.stopped .contract (1 + cost))
          | .stopped cause cost => .done (.stopped cause (1 + cost))
      | some (.data (.boolean false)), some captured =>
          match evalSteps no (captures.zip captured) with
          | .values results cost =>
              if outputs.length = results.length then .next (outputs.zip results ++ env) (1 + cost)
              else .done (.stopped .contract (1 + cost))
          | .stopped cause cost => .done (.stopped cause (1 + cost))
      | _, _ => .done (.stopped .contract 1)
  | .iterate _ induction lower upper carried captures body outputs, env =>
      match List.lookup lower env, List.lookup upper env,
          lookupAll env (carried.map (·.2)), lookupAll env captures with
      | some (.index first), some (.index last), some initial, some captured =>
          if first ≤ 1048576 ∧ last ≤ 1048576 ∧ last - first ≤ 1048576 then
            match evalFor (fun env' => evalSteps body env') induction (carried.map (·.1))
                (captures.zip captured) (List.range' first (last - first)) initial with
            | .values final cost =>
                if outputs.length = final.length then .next (outputs.zip final ++ env) (1 + cost)
                else .done (.stopped .contract (1 + cost))
            | .stopped cause cost => .done (.stopped cause (1 + cost))
          else .done (.stopped (.kernel .exhausted) 1)
      | _, _, _, _ => .done (.stopped .contract 1)
  | .stop _ reason, _ =>
      match stopReason? reason with
      | some stop => .done (.stopped (.explicit stop) 1)
      | none => .done (.stopped .contract 1)
  | .yield values, env =>
      match lookupAll env values with
      | some results => .done (.values results 1)
      | none => .done (.stopped .contract 1)
  | .ret values, env =>
      match lookupAll env values with
      | some results => .done (.values results 1)
      | none => .done (.stopped .contract 1)
  | .unsupported _, _ => .done (.stopped .contract 0)
end

/-- What a call to a local function without transcript operations hands back
on the given arguments, and the instructions its body charges. -/
def Validator.evaluateCall (symbol : String) (arguments : List (Value F G)) : Evaluated F G :=
  match validator.function? symbol with
  | some callee =>
      if callee.inputs.length = arguments.length then
        evalSteps vocabulary validator callee.body ((callee.inputs.map (·.1)).zip arguments)
      else .stopped .contract 0
  | none => .stopped .contract 0

/-! ## Participant bodies -/

/-- Run a loop's body for each index, in a frame of its own that holds the
index, the carried values and the captures; what an iteration yields is carried
into the next one. -/
def loopK (run : State F G → (List (Value F G) → State F G → m (Run F G)) → m (Run F G))
    (site induction : String) (carried : List String) (captured : Env F G) :
    List Nat → List (Value F G) → State F G →
      (List (Value F G) → State F G → m (Run F G)) → m (Run F G)
  | [], values, s, done => done values s
  | index :: rest, values, s, done =>
      run { s with
            frames := ⟨.loop site index, (induction, .index index) :: carried.zip values ++ captured⟩ ::
              s.frames
            events := s.events ++ [.enter (.loop site index)] } fun yielded s' =>
        match s'.frames with
        | _ :: below =>
            if yielded.length = carried.length then
              loopK run site induction carried captured rest yielded
                { s' with frames := below, events := s'.events ++ [.leave (.loop site index) .returned] } done
            else pure (s'.stop .contract (some site) none)
        | [] => pure (s'.stop .contract (some site) none)

mutual
/-- Run participant instructions. `exit` receives the values a loop body
yields. -/
def runK : List Action → State F G →
    (List (Value F G) → State F G → m (Run F G)) → m (Run F G)
  | [], s, _ => pure (s.stop .contract none none)
  | action :: rest, s, exit => runStep action s (fun s' => runK rest s' exit) exit

def runStep : Action → State F G → (State F G → m (Run F G)) →
    (List (Value F G) → State F G → m (Run F G)) → m (Run F G)
  | .receive site _ _ output type, s, next, _ =>
      if s.used < budget then
        match readFrame s.proof with
        | none => pure (s.stop .truncated none none)
        | some (payload, unread) =>
            match decode type payload with
            | none =>
                pure ({ s with
                        used := s.used + 1
                        proof := unread
                        messages := s.messages + 1 }.stop .decode (some site) none)
            | some value =>
                if type.sort = .data (payloadType value) then
                  next ({ s with
                          used := s.used + 1
                          proof := unread
                          messages := s.messages + 1 }.bind [output] [.data value])
                else
                  pure ({ s with
                          proof := unread
                          messages := s.messages + 1 }.stop .contract (some site) none)
      else pure (s.stop .limit none none)
  | .call site function inputs outputs, s, next, _ =>
      if s.used < budget then
        match s.frames, validator.function? function with
        | frame :: _, some callee =>
            match lookupAll frame.env inputs with
            | some values =>
                if callee.inputs.length = values.length then
                  localK vocabulary validator context challenge budget (site, function) true none callee.body
                    ((callee.inputs.map (·.1)).zip values)
                    { s with
                      used := s.used + 1
                      frames := ⟨.call site function, (callee.inputs.map (·.1)).zip values⟩ :: s.frames
                      events := s.events ++ [.enter (.call site function)] }
                    fun results s' =>
                      match s'.frames with
                      | _ :: caller :: below =>
                          if outputs.length = results.length then
                            next { s' with
                                   frames := ⟨caller.id, outputs.zip results ++ caller.env⟩ :: below
                                   events := s'.events ++ [.leave (.call site function) .returned] }
                          else pure (s'.stop .contract (some site) (some (site, function)))
                      | _ => pure (s'.stop .contract (some site) (some (site, function)))
                else pure (s.stop .contract (some site) none)
            | none => pure (s.stop .contract (some site) none)
        | _, _ => pure (s.stop .contract (some site) none)
      else pure (s.stop .limit none none)
  | .loop site count maximum induction carried captures body outputs, s, next, _ =>
      match s.frames with
      | frame :: _ =>
          match List.lookup count frame.env, lookupAll frame.env (carried.map (·.2)),
              lookupAll frame.env captures with
          | some (.index bound), some initial, some captured =>
              if bound ≤ maximum then
                if s.used < budget then
                  loopK (fun s' exit => runK body s' exit) site induction (carried.map (·.1))
                    (captures.zip captured) (List.range bound) initial s.charge
                    fun final s' => next (s'.bind outputs final)
                else pure (s.stop .limit (some site) none)
              else pure (s.stop .contract (some site) none)
          | _, _, _ => pure (s.stop .contract (some site) none)
      | [] => pure (s.stop .contract (some site) none)
  | .yield values, s, _, exit =>
      if s.used < budget then
        match s.frames with
        | frame :: _ =>
            match lookupAll frame.env values with
            | some results => exit results s.charge
            | none => pure (s.charge.stop .contract none none)
        | [] => pure (s.charge.stop .contract none none)
      else pure (s.stop .limit none none)
  | .ret values, s, _, _ =>
      if s.used < budget then
        match s.frames with
        | [frame] =>
            match lookupAll frame.env values with
            | some results =>
                if custodyKept s.live results then pure (s.charge.done results)
                else pure (s.charge.stop .contract none none)
            | none => pure (s.charge.stop .contract none none)
        | _ => pure (s.charge.stop .contract none none)
      else pure (s.stop .limit none none)
  | .unsupported _, s, _, _ => pure (s.stop .contract none none)
end

/-- Entry inputs: the data inputs, at their declared sorts, followed by the
host's transcript. -/
def Validator.admits (data : List (Value F G)) : Bool :=
  (validator.inputs.map (·.2.sort)).dropLast.map some == data.map dataSort? &&
  match validator.inputs.getLast? with
  | some (_, type) => (type.sort matches .transcript _)
  | none => false

/-- The initial machine state for data inputs, the host's initial transcript and
the proof's message bytes. -/
def initial (data : List (Value F G)) (history : History F G) (bytes : List UInt8) : State F G :=
  ⟨0, 0, 0, bytes, history,
    [⟨.participant, (validator.inputs.map (·.1)).zip (data ++ [.transcript history])⟩],
    [.enter .participant]⟩

/-- The meaning of the validator on data inputs, the host's initial transcript
and the proof's message bytes (after the framing header). -/
def execute (data : List (Value F G)) (history : History F G) (bytes : List UInt8) : m (Run F G) :=
  if validator.admits data then
    runK vocabulary validator context challenge decode budget validator.body
      (initial validator data history bytes) fun _ s => pure (s.stop .contract none none)
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
def validate (binding : List UInt8) (acceptance : Nat) (data : List (Value F G))
    (history : History F G) (bytes : List UInt8) : m Bool :=
  if bytes.take 40 = magic ++ binding then
    (fun result => result.accepts acceptance) <$>
      execute vocabulary validator context challenge decode budget data history (bytes.drop 40)
  else pure false

end Machine

end Zkc.Executable

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Executable.forK
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Executable.localK
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Executable.localStep
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Executable.loopK
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Executable.runK
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Executable.runStep
