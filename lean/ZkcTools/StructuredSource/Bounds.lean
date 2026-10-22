module

public import Zkc.Source.Structured.ClosedProfile
public import Zkc.Source.Structured.ProtocolContext
public import Std.Data.HashMap.Basic

@[expose] public section

/-! Executable capacity policy over the retained checked raw carrier. This is
abstract size analysis, not a second concrete evaluator or a soundness theorem.
Only the tools use these budgets; Source.Region and PIR.Process remain fuel-free. -/

namespace ZkcTools.StructuredSource
open Zkc.Source Zkc.Source.Structured

def workLimit : Nat := 1000000

namespace Bounds

def vectorLimit : Nat := 4096
def analysisLimit : Nat := 1000000

structure Interval where
  lower : Nat
  upper : Nat
  deriving BEq, Repr, Inhabited

def exact (n : Nat) : Interval := ⟨n, n⟩

def Interval.join (a b : Interval) : Interval :=
  ⟨min a.lower b.lower, max a.upper b.upper⟩

/-- Absence is not an unknown present value. Atoms omit scalar/group contents. -/
inductive Value where
  | absent
  | atom
  | boolean (known : Option Bool)
  | index (bounds : Interval)
  | vector (length : Interval)
  | optional (present : Value)
  deriving BEq, Repr, Inhabited

/-- Ordered arguments, results and carried state retain the list ABI. -/
abbrev Env := List Value
/-- Region SSA storage is reversed: de Bruijn zero is the last array element. -/
abbrev Context := Array Value
/-- `none` means no returning path, never analysis failure. -/
abbrev Result := Option Env

inductive Failure where
  | work | analysis | value | unknown
  deriving BEq, Repr

def Failure.code (openMode : Bool) : Failure → String
  | .work => if openMode then "structured-open-work-limit" else "structured-evaluation-work-limit"
  | .analysis => "structured-bounds-analysis-limit"
  | .value => if openMode then "structured-open-value-limit" else "structured-evaluation-value-limit"
  | .unknown => "structured-bounds-unknown"

structure Meter where
  analysis : Nat := 0
  work : Nat := 0
  deriving Repr

abbrev Analysis := StateT Meter (Except Failure)

def tick (amount : Nat := 1) : Analysis Unit := do
  let meter ← get
  if amount > analysisLimit - meter.analysis then throw .analysis
  set { meter with analysis := meter.analysis + amount }

def charge (amount : Nat := 1) : Analysis Unit := do
  let meter ← get
  if amount > workLimit - meter.work then throw .work
  set { meter with work := meter.work + amount }

/-- Aggregate work is not a vector length. Check before multiplying, without
raising either the work budget or the independent per-vector capacity. -/
def chargeRepeated (amount count : Nat) : Analysis Unit := do
  let meter ← get
  if count != 0 && amount > (workLimit - meter.work) / count then throw .work
  charge (amount * count)

def visit : Analysis Unit := do tick; charge

def Value.join : Value → Value → Analysis Value
  | a, b => do
    tick
    match a, b with
    | .absent, .absent => pure .absent
    | .absent, .optional b | .optional b, .absent => pure (.optional b)
    | .absent, b | b, .absent => pure (.optional b)
    | .optional a, .optional b | .optional a, b | a, .optional b =>
        return .optional (← a.join b)
    | .atom, .atom => pure .atom
    | .boolean a, .boolean b => pure (.boolean (if a == b then a else none))
    | .index a, .index b => pure (.index (a.join b))
    | .vector a, .vector b => pure (.vector (a.join b))
    | _, _ => throw .unknown

def join : Env → Env → Analysis Env
  | [], [] => pure []
  | a :: as, b :: bs => do
      tick
      return (← a.join b) :: (← join as bs)
  | _, _ => throw .unknown

def joinResult : Result → Result → Analysis Result
  | none, b | b, none => pure b
  | some a, some b => return some (← join a b)

def lookup (env : Context) (index : Nat) : Analysis Value := do
  visit
  -- Check before subtraction: an invalid index must not alias element zero.
  if index < env.size then return env[env.size - 1 - index]!
  throw .unknown

def operands (env : Context) (indices : List Nat) : Analysis Env :=
  indices.mapM (lookup env)

/-- Fold-domain arguments are a bounded list, not the growing SSA context. -/
def argument (args : Env) (index : Nat) : Analysis Value := do
  tick (index + 1)
  charge
  match args[index]? with
  | some value => pure value
  | none => throw .unknown

def prepend (values env : Env) : Analysis Env := do
  tick values.length
  charge values.length
  return values ++ env

def context (values : Env) : Analysis Context := do
  tick (3 * values.length) -- length, reverse and array construction
  return values.reverse.toArray

def extend (values : Env) (env : Context) : Analysis Context := do
  -- Consume the context at its last use. Reverse-push preserves result order;
  -- geometric array growth is amortized over the inserted values.
  tick (4 * values.length)
  charge values.length
  return values.reverse.foldl Array.push env

def regionIn {O : Type} (transfer : O → Env → RawRegions Ty O → Analysis Result) :
    RawRegion Ty O → Context → Analysis Result
  | .ret indices, env => do visit; return some (← operands env indices)
  | .stop _, _ => do visit; return none
  | .letOp op indices _ bodies next, env => do
      visit
      let some values ← transfer op (← operands env indices) bodies | return none
      regionIn transfer next (← extend values env)
  | .bind _ body next, env => do
      visit
      -- The caller retains this array across the body. Allow for its first
      -- copy-on-write extension; later body extensions consume their context.
      tick env.size
      let some values ← regionIn transfer body env | return none
      regionIn transfer next (← extend values env)

/-- One traversal handles both operation families. It only propagates abstract
values. Convert each entry's list ABI once; SSA lookup is independent of depth.
Work counts logical operand selections, not the concrete interpreter's context
steps or CPU instructions. Structural admission bounds remain separate. -/
def region {O : Type} (transfer : O → Env → RawRegions Ty O → Analysis Result)
    (body : RawRegion Ty O) (args : Env) : Analysis Result := do
  tick
  regionIn transfer body (← context args)

def value {F G : Type} : (type : Ty) → assignment F G type → Value
  | .boolean, b => .boolean (some b)
  | .index, n => .index (exact n)
  | .vector _, xs => .vector (exact xs.length)
  | _, _ => .atom

def values {F G : Type} {types : List Ty} : Values (assignment F G) types → Env
  | .nil => []
  | .cons (ty := type) x xs => value type x :: values xs

def length (n : Interval) : Analysis Value := do
  if n.upper > vectorLimit then throw .value
  return .vector n

def asLength : Value → Analysis Interval
  | .vector n => pure n
  | _ => throw .unknown

def vectorWork (n : Interval) : Analysis Unit := do
  if n.upper > vectorLimit then throw .value
  -- Split checks length repeatedly before take/drop; count those traversals as
  -- well as building results. Other vector primitives use this same envelope.
  charge (1 + 8 * n.upper)

/-- Output aliases still require separate serialization traversals. -/
def outputWork : Value → Analysis Unit
  | .optional v => outputWork v
  | .vector n => vectorWork n
  | _ => charge

def checkedRange (lo hi : Nat) : Analysis Result :=
  if lo ≥ indexLimit then pure none
  else pure (some [.index ⟨lo, min hi (indexLimit - 1)⟩])

def compareIndices (less : Bool) (a b : Interval) : Value :=
  .boolean (if less then
    if a.upper < b.lower then some true
    else if a.lower ≥ b.upper then some false else none
  else if a.upper < b.lower || b.upper < a.lower then some false
    else if a.lower == a.upper && b.lower == b.upper then some (a.lower == b.lower)
    else none)

/-- Bounds describe successful results. Proven arithmetic failure ends only
this abstract path; the admitted concrete program still produces its own stop. -/
def primitive (op : Primitive) (args : Env) : Analysis Result := do
  visit
  match op, args with
  | .indexConstant n, [] => checkedRange n n
  | .indexEqual, [.index a, .index b] => return some [compareIndices false a b]
  | .indexLess, [.index a, .index b] => return some [compareIndices true a b]
  | .indexAdd, [.index a, .index b] => checkedRange (a.lower + b.lower) (a.upper + b.upper)
  | .indexMul, [.index a, .index b] => checkedRange (a.lower * b.lower) (a.upper * b.upper)
  | .indexSub, [.index a, .index b] =>
      if a.upper < b.lower then return none
      checkedRange (a.lower - b.upper) (a.upper - b.lower)
  | .indexDiv, [.index a, .index b] =>
      if b.upper == 0 then return none
      checkedRange (a.lower / b.upper) (a.upper / max 1 b.lower)
  | .indexMod, [.index a, .index b] =>
      if b.upper == 0 then return none
      checkedRange 0 (min a.upper (b.upper - 1))
  | .vectorEmpty _, [] => return some [.vector (exact 0)]
  | .vectorLength _, [.vector n] => vectorWork n; return some [.index n]
  | .vectorSum _, [.vector n] => vectorWork n; return some [.atom]
  | .vectorSplit _, [.vector n] =>
      vectorWork n
      if n.upper == 0 || (n.lower == n.upper && n.upper % 2 != 0) then return none
      let half ← length ⟨n.lower / 2, n.upper / 2⟩
      return some [half, half]
  | .vectorAppend _, [.vector n, .atom] =>
      let result ← length ⟨n.lower + 1, n.upper + 1⟩
      vectorWork n
      return some [result]
  | .vectorEqual _, [.vector a, .vector b] =>
      vectorWork a; vectorWork b
      return some [.boolean none]
  | .fieldEqual _, [.atom, .atom] => return some [.boolean none]
  | _, _ => throw .unknown

def absent (args : Env) : Bool := args.any (· == .absent)

def Value.isOptional : Value → Bool
  | .optional _ => true
  | _ => false

def Value.present : Value → Value
  | .optional value => value.present
  | value => value

/-- Iteration does not allocate a range. Its count is charged before entry.
Joining each prefix accounts for zero iterations, predicates and early exits. -/
def iterate (step : Nat → Env → Analysis Result) : Nat → Nat → Env → Analysis Env
  | 0, _, state => pure state
  | remaining + 1, index, state => do
      visit
      let result ← step index state
      let next ← match result with
        | none => pure state
        | some result => join state result
      iterate step remaining (index + 1) next

/-- A private-to-preflight index of the existing checked definitions. Admission
already establishes unique names and acyclic exact-signature linkage. -/
abbrev Helpers := Std.HashMap String CheckedDefinition

def typeWork : Ty → Nat
  | .field name | .vector name | .group name | .service name => 1 + name.utf8ByteSize
  | _ => 1

def signatureWork (helper : Helper) : Nat :=
  1 + helper.name.utf8ByteSize +
    helper.inputs.foldl (fun cost type => cost + typeWork type) 0 +
    helper.outputs.foldl (fun cost type => cost + typeWork type) 0

/-- Build once, within the analysis meter. Even a worst-case hash bucket is
bounded by the admitted 128-definition maximum. Never replace duplicate names. -/
def prepareHelpers (definitions : List CheckedDefinition) : Analysis Helpers := do
  let mut table : Helpers := {}
  for definition in definitions do
    tick (1 + 3 * definition.name.utf8ByteSize + signatureWork definition.helper)
    if table.size ≥ 128 || table.contains definition.name then throw .unknown
    table := table.insert definition.name definition
  return table

def findHelper (definitions : Helpers) (helper : Helper) : Analysis CheckedDefinition := do
  -- Charge hashing/comparing this identity, not a scan of all declarations.
  -- Map lookup is a bounded analysis operation, not an exact CPU-step count.
  tick (1 + helper.name.utf8ByteSize + 2 * signatureWork helper)
  charge (1 + helper.inputs.length + helper.outputs.length)
  let some definition := definitions[helper.name]? | throw .unknown
  if definition.helper != helper then throw .unknown
  return definition

def booleanBinary (op : Bool → Bool → Bool) (a b : Option Bool) : Value :=
  .boolean (do return op (← a) (← b))

/-- The concrete map collects every row length before its ordered shape test.
Charge this traversal even for unused rows and eventual mismatches. Broadcasts
remain in the full argument tuple; they do not contribute a row length. -/
def mapLengths : List Bool → Env → Analysis (List Interval)
  | [], [] => pure []
  | true :: mask, .vector n :: args => do
      visit
      if n.lower > n.upper then throw .unknown
      vectorWork n
      return n :: (← mapLengths mask args)
  | false :: mask, .atom :: args => do
      visit
      mapLengths mask args
  | _, _ => throw .unknown

/-- Only successful shape paths contribute a common length. Each row checks
representability before equality; a disjoint interval ends that prefix before
later checks. Unknown lengths retain every possible equal, representable shape. -/
def mapShapeRemaining (common : Interval) : List Interval → Analysis (Option Interval)
  | [] => pure (some common)
  | n :: rest => do
      visit
      if n.lower > n.upper then throw .unknown
      if n.lower ≥ indexLimit then return none
      let next := Interval.mk (max common.lower n.lower)
        (min common.upper (min n.upper (indexLimit - 1)))
      if next.lower > next.upper then return none
      mapShapeRemaining next rest

def mapShape : List Interval → Analysis (Option Interval)
  | [] => throw .unknown -- admitted maps have at least one row
  | n :: rest => do
      visit
      if n.lower > n.upper then throw .unknown
      if n.lower ≥ indexLimit then return none
      mapShapeRemaining ⟨n.lower, min n.upper (indexLimit - 1)⟩ rest

/-- Calls specialize checked acyclic bodies to their arguments. The analysis
meter is checked at every recursive entry, independently of estimated work. -/
partial def operation (definitions : Helpers) (op : Op) (args : Env)
    (bodies : RawRegions Ty Op) : Analysis Result := do
  visit
  tick args.length
  -- Math calls must inspect their dependencies even with absent arguments.
  match op with
  | .invoke helper@⟨_, .math, _, _⟩ =>
      let definition ← findHelper definitions helper
      region (operation definitions) definition.raw args
  | _ =>
    if absent args then
      if let .exec _ := op then return none
      if let .map _ := op then return none
      return some (op.results.map fun _ => .absent)
    if args.any Value.isOptional then
      let result ← operation definitions op (args.map Value.present) bodies
      if let .exec _ := op then return result
      if let .map _ := op then return result
      return ← joinResult result (some (op.results.map fun _ => .absent))
    match op, args, bodies with
    | .invoke helper, _, .nil =>
        let definition ← findHelper definitions helper
        region (operation definitions) definition.raw args
    | .map spec, _, .nil =>
        let some n ← mapShape (← mapLengths spec.rowwise args) | return none
        let output ← length n
        if n.upper == 0 then return some [output]
        -- Range allocation/traversal, complete row tuple selection/construction,
        -- and output cons cells. Arity * rows may exceed vectorLimit.
        chargeRepeated (3 + 2 * args.length) n.upper
        tick args.length
        let rowArgs := args.map fun _ => Value.atom
        let before := (← get).work
        let result ← operation definitions (.invoke spec.helper) rowArgs .nil
        let rowWork := (← get).work - before
        -- All rows have exactly the same abstract scalar arguments. Analyze
        -- the retained body (including nested helpers) once, and reserve its
        -- entire logical work for every potential row. Analysis counts only
        -- the traversal performed here, with no helper result/global cache.
        chargeRepeated rowWork (n.upper - 1)
        match result with
        | some [.atom] => return some [output]
        | none => return if n.lower == 0 then some [.vector (exact 0)] else none
        | _ => throw .unknown
    | .exec p, _, .nil => primitive p args
    | .indexConstant n, [], .nil => return some [.index (exact n)]
    | .indexEqual, [.index a, .index b], .nil => return some [compareIndices false a b]
    | .booleanConstant b, [], .nil => return some [.boolean (some b)]
    | .booleanAnd, [.boolean a, .boolean b], .nil => return some [booleanBinary (· && ·) a b]
    | .booleanOr, [.boolean a, .boolean b], .nil => return some [booleanBinary (· || ·) a b]
    | .booleanXor, [.boolean a, .boolean b], .nil => return some [booleanBinary xor a b]
    | .booleanEqual, [.boolean a, .boolean b], .nil => return some [booleanBinary (· == ·) a b]
    | .booleanNotEqual, [.boolean a, .boolean b], .nil => return some [booleanBinary (· != ·) a b]
    | .select _, [.boolean (some condition), yes, no], .nil =>
        return some [if condition then yes else no]
    | .select _, [.boolean none, yes, no], .nil => return some [← yes.join no]
    | .guard, [.boolean (some false)], .nil => return none
    | .guard, [.boolean _], .nil | .mark _, [], .nil => return some []
    | .boundedAt _, [.vector n, .index i], .nil =>
        vectorWork n
        if i.lower ≥ n.upper then return none
        return some [.atom]
    | .branch .., .boolean condition :: captures, .cons _ _ yes (.cons _ _ no .nil) =>
        match condition with
        | some choice => region (operation definitions) (if choice then yes else no) captures
        | none =>
            let left ← region (operation definitions) yes captures
            let right ← region (operation definitions) no captures
            joinResult left right
    | .loop stateTypes _, .index lo :: .index hi :: rest, .cons _ _ body .nil
    | .loopCondition stateTypes _, .index lo :: .index hi :: rest, .cons _ _ body .nil =>
        let count := hi.upper - lo.lower
        charge (2 * count) -- allocation and traversal, even for empty/conditional bodies
        let state := rest.take stateTypes.length
        let captures := rest.drop stateTypes.length
        let conditional := match op with | .loopCondition .. => true | _ => false
        let result ← iterate (fun offset current => do
          let index := Value.index ⟨lo.lower + offset, min (hi.upper - 1) (lo.upper + offset)⟩
          let callbackArgs ← prepend current captures
          let returned ← region (operation definitions) body (index :: callbackArgs)
          match returned with
          | none => return none
          | some returned =>
            tick returned.length
            return some ((if conditional then returned.drop 1 else returned).take stateTypes.length))
          count 0 state
        return some result
    | .fold spec, _, .nil =>
        let domainArgs := args.take spec.domain.inputs.length
        let rest := args.drop spec.domain.inputs.length
        let initial := rest.take spec.state.length
        let captures := rest.drop spec.state.length
        let n ← asLength (← argument domainArgs spec.domain.container.index)
        vectorWork n
        charge (2 * n.upper)
        let result ← iterate (fun index current => do
          let item := if spec.domain.indices then Value.index (exact index) else .atom
          let callbackArgs := item :: (← prepend domainArgs captures)
          if !spec.predicate.isEmpty then
            let predicate ← operation definitions (.invoke spec.predicateHelper) callbackArgs .nil
            match predicate with
            | none | some [.boolean (some false)] => return none
            | some [.boolean _] => pure ()
            | _ => throw .unknown
          operation definitions (.invoke spec.stepHelper) (← prepend current callbackArgs) .nil)
          n.upper 0 initial
        return some result
    | .fieldConstant .., _, .nil | .fieldAdd .., _, .nil
    | .fieldSubtract .., _, .nil | .fieldMultiply .., _, .nil
    | .groupIdentity .., _, .nil | .groupAdd .., _, .nil | .groupScale .., _, .nil =>
        return some [.atom]
    | .fieldEqual .., _, .nil | .groupEqual .., _, .nil => return some [.boolean none]
    | _, _, _ => throw .unknown

def checkValue : Value → Analysis Unit
  | .optional v => checkValue v
  | .vector n => do
      tick (n.upper + 1)
      if n.lower > n.upper then throw .unknown
      if n.upper > vectorLimit then throw .value
  | .index n => do
      tick
      if n.lower > n.upper || n.upper ≥ indexLimit then throw .unknown
  | _ => tick

def closed (payload : Payload) (args : Env) : Except Failure (Result × Meter) :=
  (do
    let helpers ← prepareHelpers payload.definitions
    args.forM checkValue
    let result ← region (operation helpers) payload.entry.raw args
    if let some outputs := result then outputs.forM outputWork
    return result).run {}

/-- Abstract protocol closures capture only the preceding checked declarations.
The reply envelope and immutable root-coordinate context belong to each request. -/
abbrev ProtocolTransfer := ProtocolContext → Nat →
  (Ty → Analysis (Option Value)) → Env → Analysis Result

structure ProtocolBoundEntry where
  signature : ProtocolSignature
  transfer : ProtocolTransfer

abbrev ProtocolBounds := List ProtocolBoundEntry

def protocolSignatureWork (signature : ProtocolSignature) : Nat :=
  1 + signature.name.utf8ByteSize +
    signature.roles.foldl (fun cost role => cost + 1 + role.utf8ByteSize) 0 +
    signature.inputs.foldl (fun cost type => cost + typeWork type) 0 +
    signature.outputs.foldl (fun cost type => cost + typeWork type) 0 +
    signature.inputScopes.foldl (fun cost scope => cost + 1 + scope.length) 0 +
    signature.outputScopes.foldl (fun cost scope => cost + 1 + scope.length) 0

/-- Compare the first matching name at its complete ABI, roster and scopes.
Neither lookup nor a transfer can silently truncate an argument/result tuple. -/
def invokeProtocolBound (protocols : ProtocolBounds) (signature : ProtocolSignature)
    (context : ProtocolContext) (self : Nat)
    (received : Ty → Analysis (Option Value)) (args : Env) : Analysis Result := do
  tick
  tick (protocolSignatureWork signature + args.length)
  charge (1 + signature.inputs.length + signature.outputs.length)
  if args.length != signature.inputs.length then throw .unknown
  for entry in protocols do
    tick (1 + entry.signature.name.utf8ByteSize + signature.name.utf8ByteSize)
    if entry.signature.name == signature.name then
      tick (protocolSignatureWork entry.signature + protocolSignatureWork signature)
      if entry.signature != signature then throw .unknown
      let result ← entry.transfer context self received args
      if let some outputs := result then
        tick outputs.length
        if outputs.length != signature.outputs.length then throw .unknown
      return result
  throw .unknown

/-- Mask actual optional components without sequencing them. Scope lookup uses
root coordinates; the same mask serves direct roots and retained applications. -/
def maskProtocolValues (context : ProtocolContext) (self : Nat) :
    List (List Nat) → Env → Analysis Env
  | scopes, values => do
    tick
    match scopes, values with
    | [], [] => pure []
    | scope :: scopes, value :: values =>
      tick (1 + scope.length)
      let visible := scope.any (fun role => context.roles role == self)
      return (if visible then value else .absent) ::
        (← maskProtocolValues context self scopes values)
    | _, _ => throw .unknown

/-- Receives use independent reply bounds. All owner/scope tests map into root
coordinates while self stays unchanged. Protocol callbacks retain their own
optional carrier; they are never reinterpreted as closed helper callbacks. -/
partial def protocolOperation (definitions : Helpers) (protocols : ProtocolBounds)
    (context : ProtocolContext) (self : Nat)
    (received : Ty → Analysis (Option Value)) (op : ProtocolOp) (args : Env)
    (bodies : RawRegions Ty ProtocolOp) : Analysis Result := do
  visit
  tick (args.length + op.arguments.length + op.results.length)
  if args.length != op.arguments.length then throw .unknown
  match op, args, bodies with
  | .calculate op _, _, .nil => operation definitions op args .nil
  | .localCall helper _ owner _, _, .nil =>
      if self != context.roles owner then return some (helper.outputs.map fun _ => .absent)
      if absent args then return none
      operation definitions (.invoke helper) (args.map Value.present) .nil
  | .guard owner _, [condition], .nil =>
      if self == context.roles owner then
        if condition == .absent || condition.present == .boolean (some false) then return none
      return some []
  | .exchange type sender receiver _, [input], .nil =>
      if self == context.roles sender then
        if input == .absent then return none
        outputWork input
        return some [input.present]
      if self == context.roles receiver then
        let some value ← received type | return none
        outputWork value
        return some [value]
      return some [.absent]
  | .restrict _ roles, [input], .nil =>
      tick roles.length
      return some [if roles.any (fun role => context.roles role == self) then input else .absent]
  | .draw owner .., _, .nil =>
      if self != context.roles owner then return some [.absent]
      if absent args then return none
      return some [.atom]
  | .protocolApply signature roles site, _, .nil =>
      tick (1 + roles.length + signature.roles.length + site.utf8ByteSize +
        (context.applicationPrefix.map String.utf8ByteSize).getD 0)
      let child := context.enter site roles
      if !child.contains signature self then return some (signature.outputs.map fun _ => .absent)
      invokeProtocolBound protocols signature child self received args
  | .repeat spec _, count :: rest, .cons inputs outputs body .nil =>
      tick (inputs.foldl (fun cost type => cost + typeWork type) 0 +
        outputs.foldl (fun cost type => cost + typeWork type) 0 + spec.roles.length)
      if inputs != op.arguments || outputs != spec.state then throw .unknown
      if !spec.roles.any (fun role => context.roles role == self) then
        return some (spec.state.map fun _ => .absent)
      -- Only the present count branch can return. Missing captures remain
      -- optional; a reached strict operation decides whether they are needed.
      if count.present == .absent then return none
      let .index bounds := count.present | throw .unknown
      if bounds.lower > bounds.upper then throw .unknown
      if bounds.lower > spec.maximum then return none
      -- This cap limits abstract exploration only. Concrete excessive counts
      -- are refused by the process, never truncated to this many iterations.
      let count := min bounds.upper spec.maximum
      let initial ← maskProtocolValues context self spec.stateScopes
        (rest.take spec.state.length)
      let captures := rest.drop spec.state.length
      charge (2 * count) -- reserve range allocation/traversal before callback entry
      let result ← iterate (fun index current => do
        let masked ← maskProtocolValues context self spec.stateScopes current
        let callbackArgs ← prepend masked captures
        let returned ← region (protocolOperation definitions protocols context self received)
          body (.index (exact index) :: callbackArgs)
        match returned with
        | none => return none
        | some values =>
          return some (← maskProtocolValues context self spec.stateScopes values)) count 0 initial
      return some result
  | .statement .., _, .nil | .mark _, [], .nil => return some []
  | _, _, _ => throw .unknown

/-- The checked dependency order determines each captured strict prefix. This
fold stores abstract transfers over retained bodies, with no expansion or
recursive symbol resolver. Preparation and each body entry share one meter. -/
def prepareProtocols (helpers : Helpers) (definitions : List CheckedProtocol) :
    Analysis ProtocolBounds := do
  tick
  let mut table : ProtocolBounds := []
  for definition in definitions do
    tick
    tick (1 + protocolSignatureWork definition.signature + table.length)
    if table.length ≥ 128 then throw .unknown
    for entry in table do
      tick (1 + entry.signature.name.utf8ByteSize + definition.name.utf8ByteSize)
      if entry.signature.name == definition.name then throw .unknown
    if definition.inputScopes.length != definition.inputs.length ||
        definition.outputScopes.length != definition.outputs.length then throw .unknown
    let captured := table
    let transfer : ProtocolTransfer := fun context self received args => do
      tick
      let masked ← maskProtocolValues context self definition.inputScopes args
      let result ← region (protocolOperation helpers captured context self received) definition.raw masked
      match result with
      | none => return none
      | some outputs => return some (← maskProtocolValues context self definition.outputScopes outputs)
    table := ⟨definition.signature, transfer⟩ :: table
  return table

end Bounds
end ZkcTools.StructuredSource
