module

public import Zkc.Frontend.Passes.Stops
public import Zkc.Frontend.Emit.Tables

@[expose] public section

set_option autoImplicit false

/-!
# The emission of local code to the named program

The typed tree of a body is emitted as instructions of the named program of the core
(`Zkc.Core.Named`): every value is a name, a number unique in its definition, and a nested
region reads the names around it. The core's lowering makes positions and captures, and the
core's admission decides what a fact must justify. So the emitter holds no fact, no range and
no key of a term: it emits every use of a term anew, and the core shares what is one value.

Each form of the tree has one rule (§7.4 of the reference), and each instruction carries the
number of the node it is made for, which a refusal of the core names.

- A `mut` name stands for the name of its last value. A region returns the names that its
  suites update, and they are bound to its results after it.
- `a and b` and `a or b` are the boolean operation of the core unless the right operand can
  fail (`Typed.isChoice`); otherwise a local `if` on the left operand whose other region
  returns the literal.
- A condition with such an `and` or `or` is taken one operand at a time (TY9): an `if` on
  `a and b` is the `if` on `a` whose region of `true` is the `if` on `b`, so that each arm is
  under both operands. A guard on a conjunction is a guard per conjunct in the tree already.
- An operation on naturals reads an `index<s>` operand through `fin.to_nat`, after every
  operand is evaluated.
- A loop in sequence is a block per iteration: a block is a boundary at which a proof states
  what holds, and it does nothing.
- A range that starts at the static `0` counts to its end, and its index is the iteration
  number; any other range counts the difference of its bounds, and its index is the start plus
  the iteration number.
-/

namespace Zkc.Frontend.Emit.Named

open Syntax
open Static
open Zkc.Core.Named (ValueName Tag Instruction LocalOp Exit Count)
open Typing (EmitM EmitFailure toTy recordNumber variantNumber rowNumberOf)

/-- What a local name stands for at the point reached. -/
inductive Bound where
  /-- A value. `static` is its number when it is an operand bound to keep the order written
  whose value is a static natural. -/
  | value (name : ValueName) (static : Option Nat := none)
  /-- A static natural without a value: a static name, or the index of an iteration emitted on
  its own. A read of it is a literal. -/
  | static (value : Nat)
  deriving Inhabited

/-- What the emission of a body asks of the package it is emitted into. -/
structure Context where
  callees : Typed.Callees
  /-- The operation that applies a function instance, at the types of its arguments and of its
  result, to operands: a call of its number in the package, or the row that the instance is
  bound to. -/
  apply : InstanceId → Array ClosedType → ClosedType → List ValueName → EmitM LocalOp
  /-- The emission is for the check of a definition (`Emit.Check`): an operation of
  specifications and an error node are rows of their own, so that the body around them can be
  checked. -/
  checking : Bool := false

structure State where
  /-- The next name that no value has. -/
  next : ValueName := 0
  names : Std.HashMap LocalId Bound := {}
  /-- The instructions of the regions being built, innermost last. -/
  frames : Array (Array Instruction) := #[#[]]
  /-- The type that each `mut` name has at the point reached (TY10): the type of its last
  value. A block of an iteration states the types of the names it updates. -/
  types : Std.HashMap LocalId ClosedType := {}
  /-- The instructions of the regions of a protocol body being built, innermost last. -/
  steps : Array (Array Zkc.Core.Named.ProtocolInstruction) := #[#[]]
  deriving Inhabited

abbrev NamedM := ReaderT Context (StateT State EmitM)

def defect {α : Type} (message : String) : NamedM α := throw (EmitFailure.defect message)

def fresh : NamedM ValueName :=
  modifyGet fun state => (state.next, { state with next := state.next + 1 })

def bind (binder : LocalId) (bound : Bound) : NamedM Unit :=
  modify fun state => { state with names := state.names.insert binder bound }

/-- Emits an operation with `count` results for a node. -/
def emit (tag : Tag) (step : LocalOp) (count : Nat) : NamedM (List ValueName) := do
  let results ← (List.range count).mapM fun _ => fresh
  modify fun state =>
    { state with frames := state.frames.modify (state.frames.size - 1) (·.push (.mk tag results step)) }
  return results

def emit1 (tag : Tag) (step : LocalOp) : NamedM ValueName := do
  match ← emit tag step 1 with
  | [result] => return result
  | _ => defect "an operation of one result gives another number of results"

def builtin (tag : Tag) (operation : Zkc.Core.Raw.Builtin) (operands : List ValueName) :
    NamedM ValueName :=
  emit1 tag (.builtin operation operands)

def literal (tag : Tag) (value : Zkc.Core.Raw.Literal) : NamedM ValueName := emit1 tag (.literal value)

def ty (type : ClosedType) : NamedM Zkc.Core.Ty := liftM (toTy type : EmitM Zkc.Core.Ty)

def tys (types : Array ClosedType) : NamedM (List Zkc.Core.Ty) := types.toList.mapM ty

/-- In the check of a definition: what has no operation of the core (an operation of
specifications, an error node) stands as a pure row of its name at its types, of which the core
knows nothing. -/
def placeholder (tag : Tag) (name : String) (inputs : Array ClosedType) (output : ClosedType)
    (operands : List ValueName) : NamedM ValueName := do
  -- a catalogue name has letters, digits and `. _ - /`
  let name := String.ofList (name.toList.map fun character =>
    if character.isAlphanum || character == '.' || character == '_' then character else '_')
  let row : Typing.Row :=
    { key := { name, statics := (inputs.push output).map Typing.RowStatic.type }
      kind := .pure, inputs, outputs := #[output] }
  emit1 tag (.op (← (rowNumberOf row : EmitM Nat)) operands)

/-- Applies a row of the vocabulary, on operands of the given types. A row that the vocabulary
does not have at its static arguments waits in a package; in the check of a definition it
stands as a row of which the core knows nothing, so that the rest of the body is checked. -/
def applyRow (tag : Tag) (request : Typing.RowRequest) (inputs : Array ClosedType)
    (output : ClosedType) (operands : List ValueName) : NamedM ValueName := do
  match Typing.rowOf? request with
  | some row => emit1 tag (.op (← (rowNumberOf row : EmitM Nat)) operands)
  | none =>
    unless (← read).checking do
      throw (EmitFailure.waiting s!"the row `{request.name}` at these static arguments, which the vocabulary does not have")
    placeholder tag request.name inputs output operands

/-- Builds a nested region with its own inputs: `action` emits its instructions and gives the
names it returns. A name bound in the region does not leave it. -/
def inRegion {α : Type} (inputs : List ValueName) (action : NamedM (α × List ValueName)) :
    NamedM (α × Zkc.Core.Named.Region) := do
  let saved := (← get).names
  modify fun state => { state with frames := state.frames.push #[] }
  let (result, returned) ← action
  let state ← get
  let instructions := state.frames.back!
  set { state with frames := state.frames.pop, names := saved }
  return (result, .mk inputs instructions.toList (.ret returned))

/-- The name of the value that a local name has now. -/
def currentOf (binder : LocalId) : NamedM ValueName := do
  match (← get).names[binder]? with
  | some (.value name _) => return name
  | _ => defect s!"the carried name {binder} is not bound to a value"

/-- Binds the names that the suites of a statement update to its results, at the types they
have after it. -/
def rebind (control : Typed.Control) (results : List ValueName) : NamedM Unit := do
  for (binder, name) in control.updates.toList.zip results do bind binder (.value name)
  modify fun state => { state with
    types := (control.updates.zip control.carried).foldl (init := state.types) fun types (binder, type) =>
      types.insert binder type }

/-- The literal of the core for a literal of the tree at its type. -/
def literalOf (type : ClosedType) : Typed.Literal → NamedM Zkc.Core.Raw.Literal
  | .nat value => return .nat value
  | .bool value => return .bool value
  | .index value => match type with
    | .index bound => return .fin bound value
    | _ => return .nat value
  | .bytes data => return .bytes data
  | .nominal data => do
    match ← ty type with
    | .nominal row => return .nominal row data
    | _ => defect "a literal of a type that is no nominal row"

/-- The value of a natural as a `nat`: an `index<s>` is read through `fin.to_nat`. -/
def naturalOf (tag : Tag) (value : ValueName) (type : ClosedType) : NamedM ValueName :=
  match type with
  | .index bound => builtin tag (.finToNat bound) [value]
  | _ => pure value

/-- The value of a block whose statements only bind operands to keep the order written. -/
def operandBlock? : Typed.Expr → Option Typed.Expr
  | .block _ statements result =>
    if statements.all fun
      | .bind _ binder _ _ => binder.origin == .operand
      | _ => false
    then some result else none
  | _ => none

/-- The number an expression stands for when it is static: a static natural, a number, the
index of an iteration emitted on its own, and the arithmetic of sizes over them (TY2). -/
partial def staticOf? (expr : Typed.Expr) : NamedM (Option Nat) := do
  if let some result := operandBlock? expr then return ← staticOf? result
  match expr with
  | .staticValue _ value _ => return some value
  | .literal _ (.index value) => return some value
  | .local _ binder =>
    match (← get).names[binder]? with
    | some (.static value) => return some value
    | some (.value _ static) => return static
    | none => return none
  | .convert _ .indexToNat inner _ => staticOf? inner
  | .apply _ (.operation operation) #[x, y] =>
    let some a ← staticOf? x | return none
    let some b ← staticOf? y | return none
    match operation with
    | .natAdd => return some (a + b)
    | .natSub => return if b ≤ a then some (a - b) else none
    | .natMul => return some (a * b)
    | .natDiv => return if b == 0 then none else some (a / b)
    | .natRem => return if b == 0 then none else some (a % b)
    | .natPow => return some (a ^ b)
    | _ => return none
  | _ => return none

/-- The domain of a loop as emitted: its count, the static start of a range or its start as a
natural, and the collection. -/
structure Prepared where
  count : Count
  start : Option Nat := none
  lower : ValueName := 0
  source : ValueName := 0
  deriving Inhabited

mutual
  /-- The value of `value`, of the type `source`, at the type `target`, by the conversion the
  tree gives it (TY5). The refining operations are applied where the node stands; the core
  checks that the role that computes them has the fact. -/
  partial def convert (tag : Tag) (value : ValueName) (source : ClosedType)
      (conversion : Typed.Conversion) (target : ClosedType) : NamedM ValueName := do
    match conversion, source, target with
    | .empty, _, .seq element (some 0) => builtin tag (.seqMake (← ty element) 0) []
    | .empty, _, .seq element none =>
      let element ← ty element
      let empty ← builtin tag (.seqMake element 0) []
      builtin tag (.seqUnsized element 0) [empty]
    | .indexToNat, _, _ => naturalOf tag value source
    | .widenIndex, .index bound, .index wider => builtin tag (.finWiden bound wider) [value]
    | .bounded, _, .index bound =>
      let natural ← naturalOf tag value source
      builtin tag (.natBelow bound) [natural]
    | .unsized, .seq element (some size), _ => builtin tag (.seqUnsized (← ty element) size) [value]
    | .sized, .seq element none, .seq _ (some size) =>
      builtin tag (.seqSized (← ty element) size) [value]
    | .elements inner, .seq element size, .seq other _ =>
      -- a loop that collects each element converted
      let elementTy ← ty element
      let count ← match size with
        | some n => pure (Count.static n)
        | none => do pure (Count.runtime (← builtin tag (.seqLength elementTy none) [value]))
      let iteration ← fresh
      let (_, body) ← inRegion [iteration] do
        let item ← builtin tag (.seqAt elementTy size) [value, iteration]
        let converted ← convert tag item element inner other
        return ((), [converted])
      emit1 tag (.loop count none [] [← ty other] body)
    | .components inner, .tuple components _, .tuple targets _ =>
      let componentTys ← tys components
      let mut values := #[]
      for index in [0:components.size] do
        let component ← builtin tag (.tupleGet componentTys index) [value]
        let converted ← match inner[index]?.getD none with
          | some conversion => convert tag component components[index]! conversion targets[index]!
          | none => pure component
        values := values.push converted
      builtin tag (.tupleMake (← tys targets)) values.toList
    | .fromNonzero, .nonzero field, _ =>
      applyRow tag (Typing.Rows.fieldFromNonzero field) #[source] target [value]
    | .nonzero, _, .nonzero field =>
      applyRow tag (Typing.Rows.fieldNonzero field) #[source] target [value]
    | .andThen first middle second, _, _ =>
      let converted ← convert tag value source first middle
      convert tag converted middle second target
    | _, _, _ => defect "a conversion that does not fit the types it converts"

  /-- Emits an expression: its instructions, and the name of its value. -/
  partial def emitExpr (expr : Typed.Expr) : NamedM ValueName := do
    match expr with
    | .literal info value =>
      -- a literal of a type without a form in the core, in the check of a definition
      if (← read).checking && !(info.type matches .bool | .nat | .index _ | .nominal .. | .seq ..) then
        return ← placeholder info.id "literal" #[] info.type []
      literal info.id (← literalOf info.type value)
    | .staticValue info value _ => literal info.id (.nat value)
    | .local info binder =>
      match (← get).names[binder]? with
      | some (.value name _) => return name
      | some (.static value) => literal info.id (.nat value)
      | none => defect s!"the local name {binder} is read where it is not bound"
    | .construct info .tuple parts =>
      let values ← parts.toList.mapM emitExpr
      builtin info.id (.tupleMake (← tys (parts.map (·.type)))) values
    | .construct info (.record inst) parts =>
      let values ← parts.toList.mapM emitExpr
      builtin info.id (.recordMake (← (recordNumber inst : EmitM Nat))) values
    | .construct info .sequence parts =>
      let .seq element _ := info.type | defect "a collection whose type is no collection"
      let values ← parts.toList.mapM emitExpr
      builtin info.id (.seqMake (← ty element) parts.size) values
    | .construct info (.alternative inst index) parts =>
      let values ← parts.toList.mapM emitExpr
      let payload ← match values with
        | [value] => pure value
        | _ => builtin info.id (.tupleMake (← tys (parts.map (·.type)))) values
      builtin info.id (.variantMake (← (variantNumber inst : EmitM Nat)) index) [payload]
    | .project info target position _ =>
      let whole ← emitExpr target
      match target.type with
      | .record inst => builtin info.id (.recordGet (← (recordNumber inst : EmitM Nat)) position) [whole]
      | .tuple components _ => builtin info.id (.tupleGet (← tys components) position) [whole]
      | _ => defect "a part of a value that is no tuple and no record"
    | .convert info conversion value _ =>
      let operand ← emitExpr value
      convert info.id operand value.type conversion info.type
    | .block _ statements result =>
      emitStmts statements
      emitExpr result
    | .conditional info .and a b _ => emitLogic info true a b
    | .conditional info .or a _ b => emitLogic info false a b
    | .conditional info .ifThenElse condition onTrue onFalse => emitIf info condition onTrue onFalse
    | .apply info (.operation .seqSlice) arguments => emitSlice info arguments
    | .apply info (.operation operation) arguments =>
      let operands ← arguments.toList.mapM emitExpr
      emitOperation info operation (operands.zip (arguments.toList.map (·.type)))
    | .apply info (.instance inst) arguments =>
      let operands ← arguments.toList.mapM emitExpr
      emit1 info.id (← ((← read).apply inst (arguments.map (·.type)) info.type operands : EmitM LocalOp))
    | .apply info (.row row) arguments =>
      let operands ← arguments.toList.mapM emitExpr
      applyRow info.id row.request (arguments.map (·.type)) info.type operands
    | .apply info (.boundRow row) arguments =>
      let operands ← arguments.toList.mapM emitExpr
      emit1 info.id (.op (← (rowNumberOf row : EmitM Nat)) operands)
    | .apply info (.specification what) arguments =>
      unless (← read).checking do throw (EmitFailure.noCoreForm what)
      let operands ← arguments.toList.mapM emitExpr
      placeholder info.id s!"specification.{what}" (arguments.map (·.type)) info.type operands
    | .apply info (.member _ name _) arguments =>
      unless (← read).checking do
        throw (EmitFailure.waiting "a member of a module parameter in an opaque elaboration (SP12)")
      let operands ← arguments.toList.mapM emitExpr
      placeholder info.id s!"member.{name}" (arguments.map (·.type)) info.type operands
    | .error info evaluated =>
      unless (← read).checking do defect "a body with an error node is emitted"
      let operands ← evaluated.toList.mapM emitExpr
      placeholder info.id "error" (evaluated.map (·.type)) info.type operands

  /-- An operation of the core on emitted operands, each with its type. -/
  partial def emitOperation (info : Typed.Info) (operation : Typed.CoreOperation)
      (operands : List (ValueName × ClosedType)) : NamedM ValueName := do
    let tag := info.id
    -- the operands of an operation on naturals, as naturals
    let naturals : NamedM (List ValueName) := operands.mapM fun (value, type) => naturalOf tag value type
    match operation, operands with
    | .natAdd, [_, _] => builtin tag .natAdd (← naturals)
    | .natSub, [_, _] => builtin tag .natSub (← naturals)
    | .natMul, [_, _] => builtin tag .natMul (← naturals)
    | .natDiv, [_, _] => builtin tag .natDiv (← naturals)
    | .natRem, [_, _] => builtin tag .natRem (← naturals)
    | .natPow, [_, _] => builtin tag .natPow (← naturals)
    | .natLess, [_, _] => builtin tag .natLess (← naturals)
    | .natEqual, [_, _] => builtin tag .natEqual (← naturals)
    | .boolNot, [(x, _)] => builtin tag .boolNot [x]
    | .boolEqual, [(x, _), (y, _)] => builtin tag .boolEqual [x, y]
    | .boolAnd, [(x, _), (y, _)] => builtin tag .boolAnd [x, y]
    | .boolOr, [(x, _), (y, _)] => builtin tag .boolOr [x, y]
    | .seqLength, [(xs, .seq element size)] => builtin tag (.seqLength (← ty element) size) [xs]
    | .seqAt, [(xs, .seq element size), (i, type)] =>
      let position ← naturalOf tag i type
      builtin tag (.seqAt (← ty element) size) [xs, position]
    | .seqConcat, [(x, .seq _ m), (y, .seq _ n)] =>
      let .seq element _ := info.type | defect "a concatenation whose type is no collection"
      builtin tag (.seqConcat (← ty element) m n) [x, y]
    | .seqFill, [(element, _)] =>
      let .seq type (some count) := info.type | defect "a fill without a static count"
      builtin tag (.seqFill (← ty type) count) [element]
    | _, _ => defect s!"the operation {operation.name} on operands that do not fit it"

  /-- `xs[a..b]` (TY7): the collection, the lower bound, the length where the upper bound is
  not written, the upper bound. -/
  partial def emitSlice (info : Typed.Info) (arguments : Array Typed.Expr) : NamedM ValueName := do
    let tag := info.id
    let (xsExpr, aExpr, bExpr?) ← match arguments with
      | #[xsExpr, aExpr] => pure (xsExpr, aExpr, none)
      | #[xsExpr, aExpr, bExpr] => pure (xsExpr, aExpr, some bExpr)
      | _ => defect "a slice without its operands"
    let xs ← emitExpr xsExpr
    let .seq element size := xsExpr.type | defect "a slice of a value that is no collection"
    let .seq _ resultSize := info.type | defect "a slice whose type is no collection"
    let element ← ty element
    let a ← emitExpr aExpr
    let (b, bType) ← match bExpr? with
      | some bExpr => pure (← emitExpr bExpr, bExpr.type)
      | none => pure (← builtin tag (.seqLength element size) [xs], ClosedType.nat)
    let start ← naturalOf tag a aExpr.type
    let stop ← naturalOf tag b bType
    builtin tag (.seqSlice element size resultSize) [xs, start, stop]

  /-- `a and b` (`conjunction`) or `a or b` (§4.2, TY9). -/
  partial def emitLogic (info : Typed.Info) (conjunction : Bool) (a b : Typed.Expr) :
      NamedM ValueName := do
    let callees := (← read).callees
    -- a left operand that is such a local `if` is grouped to the right, so that the right
    -- operand has the facts of both
    if let some (inner, x, y) := Typed.operands? a conjunction then
      if Typed.isChoice callees (Typed.logic inner conjunction x y) then
        return ← emitLogic info conjunction x (Typed.logic info conjunction y b)
    let left ← emitExpr a
    unless b.canFail callees do
      let right ← emitExpr b
      return ← builtin info.id (if conjunction then .boolAnd else .boolOr) [left, right]
    let (_, region) ← inRegion [] do return ((), [← emitExpr b])
    let (_, constant) ← inRegion [] do return ((), [← literal info.id (.bool (!conjunction))])
    let (onTrue, onFalse) := if conjunction then (region, constant) else (constant, region)
    emit1 info.id (.conditional left [.bool] onTrue onFalse)

  /-- `if c then a else b`: a local `if`, the region of `true` first. -/
  partial def emitIf (info : Typed.Info) (condition onTrue onFalse : Typed.Expr) :
      NamedM ValueName := do
    if Typed.hasChoice (← read).callees condition then
      if let some split := Typed.split? condition then
        let inner (test : Typed.Expr) : Typed.Expr :=
          .conditional { test.info with type := info.type } .ifThenElse test onTrue onFalse
        match split with
        | .conjunction a b => return ← emitIf info a (inner b) onFalse
        | .disjunction a b => return ← emitIf info a onTrue (inner b)
        | .condition other => return ← emitIf info other onTrue onFalse
    let test ← emitExpr condition
    let arm (branch : Typed.Expr) : NamedM Zkc.Core.Named.Region := do
      let (_, region) ← inRegion [] do return ((), [← emitExpr branch])
      return region
    let whenTrue ← arm onTrue
    let whenFalse ← arm onFalse
    emit1 info.id (.conditional test [← ty info.type] whenTrue whenFalse)

  partial def emitStmts (statements : Array Typed.Stmt) : NamedM Unit := do
    for statement in statements do emitStmt statement

  /-- The parts of a value that a pattern takes apart, bound to its binders: the components of a
  tuple, the fields of a record, or the payload of a variant of one alternative, which a `match`
  of one region takes out. -/
  partial def emitUnpack (tag : Tag) (binders : Array (Option Typed.Binder)) (whole : ValueName)
      (type : ClosedType) : NamedM Unit := do
    let (whole, payload?) ← match type with
      | .«variant» inst =>
        let alternatives ← match (← readThe Compile.State).table.content? inst with
          | some (.«variant» alternatives) => pure alternatives
          | _ => defect "a variant whose alternatives are not evaluated"
        let payload := (alternatives[0]?.map (·.2)).getD #[]
        let input ← fresh
        let (_, arm) ← inRegion [input] do return ((), [input])
        let value ← emit1 tag (.«match» (← (variantNumber inst : EmitM Nat)) whole
          [← ty (payloadType payload)] [arm])
        pure (value, some payload)
      | _ => pure (whole, none)
    for index in [0:binders.size] do
      let some binder := binders[index]! | continue
      let part ← match type, payload? with
        | _, some payload =>
          -- a payload of one type is the payload itself
          if payload.size == 1 then pure whole
          else builtin tag (.tupleGet (← tys payload) index) [whole]
        | .tuple components _, none => builtin tag (.tupleGet (← tys components) index) [whole]
        | .record inst, none => builtin tag (.recordGet (← (recordNumber inst : EmitM Nat)) index) [whole]
        | _, _ => defect "a pattern of a value that is no tuple, record or variant"
      bind binder.id (.value part)

  partial def emitStmt : Typed.Stmt → NamedM Unit
    | .bind _ binder value _ => do
      let static ← if binder.origin == .operand then staticOf? value else pure none
      let name ← emitExpr value
      bind binder.id (.value name static)
      if binder.mutable then
        modify fun state => { state with types := state.types.insert binder.id value.type }
    | .unpack mark binders value _ => do
      let whole ← emitExpr value
      emitUnpack mark.id binders whole value.type
    | .update _ binder value _ => do
      let name ← emitExpr value
      bind binder (.value name)
      modify fun state => { state with types := state.types.insert binder value.type }
    | .guard mark condition reason _ => do
      -- elaboration makes a guard on a conjunction a guard on each conjunct
      let test ← emitExpr condition
      discard <| emit mark.id (.guard reason test) 0
    | .scope _ body => emitStmts body
    | .«if» mark condition onTrue onFalse control => emitIfStmt mark condition onTrue onFalse control
    | .«for» mark loop control => emitFor mark.id loop control
    | .«match» mark scrutinee binder inst cases control => do
      -- the matched value is bound where the `match` stands, and read by its binder
      let value ← emitExpr scrutinee
      if let some binder := binder then bind binder.id (.value value)
      let alternatives ← match (← readThe Compile.State).table.content? inst with
        | some (.«variant» alternatives) => pure alternatives
        | _ => defect "a match on a variant whose alternatives are not evaluated"
      let mut regions := #[]
      for index in [0:alternatives.size] do
        let some (.«case» _ _ payload body) := cases.find? fun (.«case» _ covered _ _) => covered.contains index
          | defect "an alternative that no case covers"
        let payloadTypes := alternatives[index]!.2
        let input ← fresh
        let (_, region) ← inRegion [input] do
          for position in [0:payload.size] do
            let some binder := payload[position]! | continue
            let item ← if payloadTypes.size == 1 then pure input
              else builtin mark.id (.tupleGet (← tys payloadTypes) position) [input]
            bind binder.id (.value item)
          emitStmts body
          return ((), ← control.updates.toList.mapM currentOf)
        regions := regions.push region
      let results ← emit mark.id (.«match» (← (variantNumber inst : EmitM Nat)) value
        (← tys control.carried) regions.toList) control.updates.size
      rebind control results
    | .event .. => defect "an event in local code"
    | .error mark binders => do
      unless (← read).checking do defect "a body with an error node is emitted"
      for binder in binders do
        bind binder.id (.value (← placeholder mark.id "error" #[] binder.type []))

  /-- `if c: A else: B`: a local `if` whose regions return the `mut` names that the suites
  update. -/
  partial def emitIfStmt (mark : Typed.Mark) (condition : Typed.Expr)
      (onTrue onFalse : Array Typed.Stmt) (control : Typed.Control) : NamedM Unit := do
    if Typed.hasChoice (← read).callees condition then
      if let some split := Typed.split? condition then
        match split with
        | .conjunction a b =>
          return ← emitIfStmt mark a #[.«if» mark b onTrue onFalse control] onFalse control
        | .disjunction a b =>
          return ← emitIfStmt mark a onTrue #[.«if» mark b onTrue onFalse control] control
        | .condition other => return ← emitIfStmt mark other onTrue onFalse control
    let test ← emitExpr condition
    let arm (statements : Array Typed.Stmt) : NamedM Zkc.Core.Named.Region := do
      let (_, region) ← inRegion [] do
        emitStmts statements
        return ((), ← control.updates.toList.mapM currentOf)
      return region
    let whenTrue ← arm onTrue
    let whenFalse ← arm onFalse
    let results ← emit mark.id (.conditional test (← tys control.carried) whenTrue whenFalse)
      control.updates.size
    rebind control results

  /-- The domain of a loop: a static range emits nothing; a range with a run-time bound emits
  its bounds and its count; a collection is evaluated once, with its length when it has no
  static size. -/
  partial def emitDomain (tag : Tag) (domain : Typed.Domain) : NamedM Prepared := do
    match domain with
    | .range start _ (some count) =>
      return { count := .static count, start := some ((← staticOf? start).getD 0) }
    | .range start stop none =>
      let static ← staticOf? start
      -- a start of `0` is read by nothing: the count is the end, the index the iteration number
      if static == some 0 then
        let b ← emitExpr stop
        return { count := .runtime (← naturalOf tag b stop.type), start := static }
      let a ← emitExpr start
      let b ← emitExpr stop
      let upper ← naturalOf tag b stop.type
      let lower ← naturalOf tag a start.type
      return { count := .runtime (← builtin tag .natSub [upper, lower]), start := static, lower }
    | .collection source _ size =>
      let xs ← emitExpr source
      match size, source.type with
      | some n, _ => return { count := .static n, source := xs }
      | none, .seq element _ =>
        return { count := .runtime (← builtin tag (.seqLength (← ty element) none) [xs]), source := xs }
      | none, _ => defect "a loop over a value that is no collection"

  /-- Binds the item of an iteration: the index of a range (static when `fixed` gives the
  number of the iteration), or the element of a collection. -/
  partial def bindLoopItem (tag : Tag) (prepared : Prepared) (domain : Typed.Domain)
      (index : Typed.Binder) (iteration : ValueName) (fixed : Option Nat) : NamedM Unit := do
    match domain with
    | .range .. =>
      -- `_` as the index of a range binds nothing
      if index.origin == .patternValue then return
      match fixed with
      | some k => bind index.id (.static ((prepared.start.getD 0) + k))
      | none =>
        let value ← match prepared.start with
          | some 0 => pure iteration
          | some start => do builtin tag .natAdd [← literal tag (.nat start), iteration]
          | none => builtin tag .natAdd [prepared.lower, iteration]
        bind index.id (.value value)
    | .collection _ item size =>
      match fixed with
      | some k => bind index.id (.static k)
      | none => bind index.id (.value iteration)
      let value ← builtin tag (.seqAt (← ty item.type) size) [prepared.source, iteration]
      bind item.id (.value value)

  /-- `for` (TY10, TY16): one loop for a uniform body, a block per iteration for a loop in
  sequence, nothing for a loop of no iteration. -/
  partial def emitFor (tag : Tag) (loop : Typed.Loop) (control : Typed.Control) : NamedM Unit := do
    let .loop index domain collected body := loop
    let prepared ← emitDomain tag domain
    let iterations ← match body with
      | .uniform statements values =>
        let carried := control.updates
        let starts ← carried.toList.mapM currentOf
        let iteration ← fresh
        let inputs ← carried.toList.mapM fun _ => fresh
        let (_, region) ← inRegion (iteration :: inputs) do
          rebind control inputs
          bindLoopItem tag prepared domain index iteration none
          emitStmts statements
          let gathered ← values.toList.mapM emitExpr
          return ((), gathered ++ (← carried.toList.mapM currentOf))
        let results ← emit tag (.loop prepared.count none starts (← tys (values.map (·.type))) region)
          (values.size + carried.size)
        for (binder, value) in collected.toList.zip results do bind binder.id (.value value)
        rebind control (results.drop values.size)
        return
      | .stepped iterations => pure iterations
      -- of a loop of no iteration nothing is emitted: its body typed apart is no code
      | .empty .. => pure #[]
    if iterations.isEmpty then
      -- each collected name is the collection of no elements
      for binder in collected do
        let .seq element _ := binder.type | defect "a collected name that is no collection"
        bind binder.id (.value (← builtin tag (.seqMake (← ty element) 0) []))
      return
    -- a loop in sequence: a block per iteration, which returns the `mut` names from outside
    -- that the iteration updates and the values it collects
    let mut gathered : Array (Array (ValueName × ClosedType)) := collected.map fun _ => #[]
    for (.iteration k statements values) in iterations do
      let inner := Typed.updatedIn statements
      let updated := control.updates.filter inner.contains
      let saved := (← get).names
      let before := (← get).types
      modify fun state => { state with frames := state.frames.push #[] }
      let number ← match domain with
        | .collection .. => literal tag (.nat k)
        | .range .. => pure 0
      bindLoopItem tag prepared domain index number (some k)
      emitStmts statements
      let mut emitted := #[]
      for value in values do emitted := emitted.push (← emitExpr value, value.type)
      let finals ← updated.toList.mapM currentOf
      let state ← get
      let types := updated.map fun binder => (state.types[binder]?).getD ClosedType.nat
      let instructions := state.frames.back!
      set { state with frames := state.frames.pop, names := saved, types := before }
      let outputs := (← tys types) ++ (← tys (emitted.map (·.2)))
      let results ← emit tag
        (.block outputs (.mk [] instructions.toList (.ret (finals ++ emitted.toList.map (·.1)))))
        outputs.length
      rebind { updates := updated, carried := types } (results.take updated.size)
      gathered := (gathered.zip ((results.drop updated.size).toArray.zip (emitted.map (·.2)))).map
        fun (all, value) => all.push value
    for (binder, values) in collected.zip gathered do
      let names := values.toList.map (·.1)
      let value ← match binder.type with
        | .seq element (some count) => builtin tag (.seqMake (← ty element) count) names
        | _ => builtin tag (.tupleMake (← tys (values.map (·.2)))) names
      bind binder.id (.value value)
end

/-- The body of a function instance as a region of the named program: its inputs are the
parameters, and it returns its value. -/
def emitFunction (context : Context) (body : Typed.FunctionBody) : EmitM Zkc.Core.Named.Region := do
  let action : NamedM Zkc.Core.Named.Region := do
    let inputs ← body.parameters.toList.mapM fun binder => do
      let name ← fresh
      bind binder.id (.value name)
      return name
    emitStmts body.statements
    let value ← emitExpr body.result
    let instructions := ((← get).frames[0]?).getD #[]
    return .mk inputs instructions.toList (.ret [value])
  (action.run context).run' {}

end Zkc.Frontend.Emit.Named
