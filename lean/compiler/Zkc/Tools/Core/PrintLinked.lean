import Zkc.Core.Unelaborate

/-! Printing a typed package as Lean source that links it to its raw package.

The compiled tool elaborates a raw package and prints, for every definition, one
declaration that holds the typed definition, its raw syntax and the two facts of
`Core/Link.lean`, and then the declarations that assemble the package. Nothing printed
here is trusted: the kernel type-checks every typed term and decides every fact.

Form of what is printed.

- A typed term is written with constructors. The implicit context of a region is left
  to unification from the type of the declaration, so no context is ever written.
- A reference is its position and a proof. The proof is `kernel_rfl%`
  (`Checks/Reflexivity.lean`): `Eq.refl` of the expected type, which the kernel checks
  by evaluating the lookup. Every other erased proof and every fact is closed the same
  way.
- Types, located types, signatures, rows and headers that repeat are auxiliary
  definitions of a prelude.
- A body with more instructions than the piece size is printed in pieces, each a
  function of the region that follows, with its facts stated for every such region.
  The context at the start of a piece is a definition. A reference to a value bound
  before the previous piece is proved through skips over whole pieces, so the kernel
  does not walk the context to it.
- A nested closed region with more instructions than the piece size is printed as a
  link of its own, in pieces, and named where it is used.
- The headers of the functions and of the protocols before a definition are a chain of
  definitions, one list per definition. A callee further back than a few positions is
  proved through skips over the chain.
-/

set_option autoImplicit false

namespace Zkc.Core.PrintLinked

open Zkc.Source

/-- What the printer may vary; each field is one lever of the measurements. -/
structure Options where
  /-- Instructions per piece of a long body. Zero prints every body whole. -/
  piece : Nat := 64
  /-- Repeated types, signatures, rows and headers are auxiliary definitions. -/
  share : Bool := true
  /-- Numbers are raw literals (`nat_lit n`), not numerals that need an instance. -/
  literals : Bool := true
  /-- Proofs are `kernel_rfl%`; otherwise `rfl`, which the elaborator also evaluates. -/
  kernelProofs : Bool := true
  /-- Old values are reached through skips over whole pieces. -/
  skips : Bool := true
  /-- The program is as written: its sites are numbered without gaps. -/
  written : Bool := true
  /-- Definitions are added as elaborated (`linked_def`); otherwise by `def`, which moves
  every proof inside a value into an auxiliary theorem. -/
  linkedDefinitions : Bool := true
  /-- The number of files the definitions are divided over. -/
  parts : Nat := 1

/-- The key of a protocol header: the data its raw syntax states. -/
abbrev ProtocolKey := Bool × Nat × List Located × List Located × List Raw.Agreement

/-- The pieces of the body being printed, for references to old values. -/
structure Far where
  /-- The prefix of the names of the body's declarations. -/
  name : String
  /-- The context at the start of the body. -/
  context : String
  /-- The values bound by each finished piece. -/
  blocks : Array Nat := #[]
  /-- `starts[j]` is the number of values bound before piece `j`. -/
  starts : Array Nat := #[0]
  /-- The values bound so far in the current piece. -/
  bound : Nat := 0
  /-- The instructions so far in the current piece. -/
  items : Nat := 0
  /-- Some reference used a skip. -/
  used : Bool := false

structure State where
  options : Options
  types : Array Ty := #[]
  located : Array Located := #[]
  functionHeaders : Array FunctionHeader := #[]
  protocolHeaders : Array ProtocolKey := #[]
  /-- The header constant of each function and of each protocol, in program order. -/
  functionHeaderOf : Array String := #[]
  protocolHeaderOf : Array String := #[]
  /-- Declarations of the prelude. -/
  shared : Array String := #[]
  /-- Declarations of the unit being printed. A unit needs the prelude and nothing else,
  so units can be checked in any order and at the same time. -/
  output : Array String := #[]
  /-- The finished units of the definition being printed. -/
  units : Array (Array String) := #[]
  /-- Declarations that join the units of the definition being printed. -/
  closing : Array String := #[]
  /-- Nested declarations go to the prelude: several units will name them. -/
  nestedShared : Bool := false
  fresh : Nat := 0
  far : Option Far := none
  /-- The skips over the chains of header lists that are declared: one flag per chain,
  list and level. -/
  tableSkips : Array Bool := #[]

abbrev M := StateM State

def declareShared (text : String) : M Unit :=
  modify fun state => { state with shared := state.shared.push text }

/-- A declaration of the current unit. -/
def declareUnit (text : String) : M Unit :=
  modify fun state => { state with output := state.output.push text }

/-- A declaration that a nested region needs: in the current unit, or in the prelude when
the body around it is printed as several units. -/
def declare (text : String) : M Unit := do
  if (← get).nestedShared then declareShared text else declareUnit text

def declareClosing (text : String) : M Unit :=
  modify fun state => { state with closing := state.closing.push text }

/-- End the current unit. -/
def closeUnit : M Unit :=
  modify fun state =>
    if state.output.isEmpty then state
    else { state with units := state.units.push state.output, output := #[] }

/-! ## Numbers, lists and proofs -/

/-- A number inside a list or after a comma. -/
def number (value : Nat) : M String := do
  if (← get).options.literals then pure s!"nat_lit {value}" else pure (toString value)

/-- A number as an argument. -/
def numberArgument (value : Nat) : M String := do
  if (← get).options.literals then pure s!"(nat_lit {value})" else pure (toString value)

/-- A term as an argument. -/
def argument (text : String) : String := if text.contains ' ' then s!"({text})" else text

def list (items : List String) : String := "[" ++ ", ".intercalate items ++ "]"

def numbers (values : List Nat) : M String := do pure (list (← values.mapM number))

def proof : M String := do
  if (← get).options.kernelProofs then pure "kernel_rfl%" else pure "rfl"

def boolean (value : Bool) : String := if value then "true" else "false"

/-- What is printed where a typed term and its raw syntax do not have the same shape,
which elaboration excludes. It is not a Lean term, so a file that contains it is refused. -/
def mismatch : String := "(typed term and raw syntax differ in shape)"

/-! ## Types -/

def useValue : Use → String
  | .free => "Use.free"
  | .atMostOnce => "Use.atMostOnce"
  | .exactlyOnce => "Use.exactlyOnce"

mutual
  /-- A type as an argument: a constructor without arguments, the name of its auxiliary
  definition, or its literal in parentheses. -/
  partial def type (ty : Ty) : M String := do
    match ty with
    | .tuple [] => pure "Ty.unit"
    | .bool => pure "Ty.bool"
    | .nat => pure "Ty.nat"
    | _ =>
        if !(← get).options.share then return s!"({← typeLiteral ty})"
        match (← get).types.findIdx? (decide <| · = ty) with
        | some index => pure s!"ty{index}"
        | none =>
            let literal ← typeLiteral ty
            let index := (← get).types.size
            modify fun state => { state with types := state.types.push ty }
            declareShared s!"linked_def ty{index} : Ty := {literal}"
            pure s!"ty{index}"

  partial def typeLiteral : Ty → M String
    | .tuple [] => pure "Ty.unit"
    | .bool => pure "Ty.bool"
    | .nat => pure "Ty.nat"
    | .fin bound => do pure s!"Ty.fin {← numberArgument bound}"
    | .nominal row => do pure s!"Ty.nominal {← numberArgument row}"
    | .seq element none => do pure s!"Ty.seq {← type element} none"
    | .seq element (some size) => do pure s!"Ty.seq {← type element} (some {← numberArgument size})"
    | .tuple components => do pure s!"Ty.tuple {list (← components.mapM type)}"
    | .record declaration use fields => do
        pure s!"Ty.record {← numberArgument declaration} {useValue use} {list (← fields.mapM type)}"
    | .variant declaration alternatives => do
        pure s!"Ty.variant {← numberArgument declaration} {list (← alternatives.mapM type)}"
end

def types (values : List Ty) : M String := do pure (list (← values.mapM type))

/-- A located type inside a list. -/
def locatedItem (located : Located) : M String := do
  if !(← get).options.share then
    return s!"⟨{← type located.type}, {← number located.holder}⟩"
  match (← get).located.findIdx? (decide <| · = located) with
  | some index => pure s!"loc{index}"
  | none =>
      let literal := s!"⟨{← type located.type}, {← number located.holder}⟩"
      let index := (← get).located.size
      modify fun state => { state with located := state.located.push located }
      declareShared s!"linked_def loc{index} : Located := {literal}"
      pure s!"loc{index}"

def locateds (values : List Located) : M String := do pure (list (← values.mapM locatedItem))

def reason : Reason → String
  | .reject => "Reason.reject"
  | .abort => "Reason.abort"
  | .exhausted => "Reason.exhausted"
  | .refused => "Reason.refused"

def stop : PIR.Stop → String
  | .reject => "PIR.Stop.reject"
  | .abort => "PIR.Stop.abort"
  | .exhausted => "PIR.Stop.exhausted"
  | .incomplete => "PIR.Stop.incomplete"
  | .refused => "PIR.Stop.refused"
  | .undefined => "PIR.Stop.undefined"

def kind : OperationKind → String
  | .pure => "OperationKind.pure"
  | .restricted none => "(OperationKind.restricted none)"
  | .restricted (some domain) => s!"(OperationKind.restricted (some {domain}))"
  | .sampling => "OperationKind.sampling"

def choiceTag : ChoiceTag → M String
  | .condition => pure "ChoiceTag.condition"
  | .arm count => do pure s!"(ChoiceTag.arm {← numberArgument count})"
  | .alternative declaration alternatives => do
      pure s!"(ChoiceTag.alternative {← numberArgument declaration} {← types alternatives})"

def signatureLiteral (signature : OperationSignature) : M String := do
  pure s!"⟨{← types signature.inputs}, {← types signature.outputs}, {kind signature.kind}⟩"

/-- A reference to a row of the operation table, with its signature. -/
def row (index : Nat) (signature : OperationSignature) : M String := do
  if (← get).options.share then pure s!"row{index}"
  else
    pure s!"(⟨{← number index}, {← proof}⟩ : Var signatures {← signatureLiteral signature})"

/-! ## References -/

/-- The largest `level` such that `2 ^ level` divides `piece` and `piece - 2 ^ level` is
not below `target`. -/
def skipLevel (piece target : Nat) : Nat := Id.run do
  let mut level := 0
  while piece % (2 ^ (level + 1)) == 0 && piece - 2 ^ (level + 1) ≥ target && 2 ^ (level + 1) ≤ piece do
    level := level + 1
  return level

/-- The context at the start of a piece. -/
def Far.contextOf (far : Far) (piece : Nat) : String :=
  if piece == 0 then far.context else s!"{far.name}_context{piece}"

/-- A reference by its position. In a long body a value bound before the previous piece
is found through the skips over the pieces between. -/
def reference (index : Nat) : M String := do
  let state ← get
  let plain := s!"⟨{← number index}, {← proof}⟩"
  let some far := state.far | return plain
  let piece := far.blocks.size
  if piece == 0 || !state.options.skips then return plain
  if index < far.bound + far.blocks[piece - 1]! then return plain
  -- The piece whose start has the value among its most recent block, and the position there.
  let mut target := piece
  let mut position := index - far.bound
  while target > 0 && position ≥ far.blocks[target - 1]! do
    position := position - far.blocks[target - 1]!
    target := target - 1
  let mut skips := s!"Skips.drop _ {far.contextOf piece} {← numberArgument far.bound} {← proof}"
  let mut total := far.bound
  let mut current := piece
  while current > target do
    let level := skipLevel current target
    total := total + (far.starts[current]! - far.starts[current - 2 ^ level]!)
    skips := s!"Skips.trans {← numberArgument total} ({skips}) {far.name}_skip{current}_{level} {← proof}"
    current := current - 2 ^ level
  set { state with far := some { far with used := true } }
  pure s!"⟨{← number index}, Skips.lookup ({skips}) {← numberArgument position} {← numberArgument index} _ {← proof} {← proof}⟩"

/-- The most levels of skips over a chain of header lists. -/
def skipLevels : Nat := 32

/-- Declare the skip from the list of the first `count` headers over the `2 ^ level`
most recent ones, and the skips it is composed of. `functions` selects the chain. -/
partial def declareTableSkip (functions : Bool) (count level : Nat) : M Unit := do
  let key := (count * skipLevels + level) * 2 + (if functions then 0 else 1)
  if (← get).tableSkips.getD key false then return
  let chain := if functions then "functionHeaders" else "protocolHeaders"
  let skip := if functions then "functionSkip" else "protocolSkip"
  let span := 2 ^ level
  if level == 0 then
    declareShared s!"theorem {skip}{count}_0 : Skips {chain}{count} {chain}{count - 1} {← numberArgument 1} :=\n  Skips.drop _ _ _ {← proof}"
  else
    declareTableSkip functions count (level - 1)
    declareTableSkip functions (count - span / 2) (level - 1)
    declareShared s!"theorem {skip}{count}_{level} : Skips {chain}{count} {chain}{count - span} {← numberArgument span} :=\n  Skips.trans {← numberArgument span} {skip}{count}_{level - 1} {skip}{count - span / 2}_{level - 1} {← proof}"
  modify fun state =>
    let flags := if key < state.tableSkips.size then state.tableSkips
      else state.tableSkips ++ Array.replicate (key + 1 - state.tableSkips.size) false
    { state with tableSkips := flags.set! key true }

/-- The positions of a table that a reference reaches by walking. Below this distance the
walk costs the kernel less than the proof through skips costs the term elaborator. -/
def nearTable : Nat := 64

/-- A reference into the list of the first `count` headers, by its position. A header
further back than a few positions is found through skips over the chain of header lists,
so the kernel does not walk the list to it. -/
def tableReference (functions : Bool) (count index : Nat) : M String := do
  if !(← get).options.skips || index < nearTable then
    return s!"⟨{← number index}, {← proof}⟩"
  let skip := if functions then "functionSkip" else "protocolSkip"
  -- The list of the first `target` headers has the named header first.
  let target := count - index
  let mut skips := ""
  let mut total := 0
  let mut current := count
  while current > target do
    let level := skipLevel current target
    declareTableSkip functions current level
    total := total + 2 ^ level
    let step := s!"{skip}{current}_{level}"
    let joined := s!"Skips.trans {← numberArgument total} ({skips}) {step} {← proof}"
    skips := if skips.isEmpty then step else joined
    current := current - 2 ^ level
  pure s!"⟨{← number index}, Skips.lookup ({skips}) {← numberArgument 0} {← numberArgument index} _ {← proof} {← proof}⟩"

def operandIndexes {α : Type} {Γ : List α} : {entries : List α} → Operands Γ entries → List Nat
  | _, .nil => []
  | _, .cons value rest => value.index :: operandIndexes rest

def operands {α : Type} {Γ entries : List α} (values : Operands Γ entries) : M String := do
  let references ← (operandIndexes values).mapM reference
  pure (references.foldr (fun value rest => s!"Values.cons {value} {argument rest}") "Values.nil")

/-! ## Regions -/

/-- One instruction of a region, without the region that follows it. -/
structure Item where
  typed : String
  raw : String
  /-- The types of the results, as a list. -/
  results : String
  count : Nat
  sites : List Nat := []

/-- The number of instructions before the end of a region. -/
partial def spineLength {dialect : Dialect} {Γ out : List dialect.Ty} :
    Region dialect Γ out → Nat → Nat
  | .letOp _ _ _ next, length => spineLength next (length + 1)
  | .bind _ next, length => spineLength next (length + 1)
  | _, length => length

/-- The instructions followed by the end, as one term. -/
def nest (items : Array Item) (endTyped endRaw : String) : String × String :=
  items.foldr (fun item (typed, raw) => (s!"{item.typed} ({typed})", s!"{item.raw} ({raw})"))
    (endTyped, endRaw)

/-- The instructions of a piece as a function of the region that follows. -/
def pieceFunctions (items : Array Item) : String × String :=
  let (typed, raw) := nest items "rest" "rest"
  (s!"fun rest => {typed}", s!"fun rest => {raw}")

/-- The context after the instructions of a piece, in the form the kernel meets it: one
`bindAll` per instruction. -/
def contextAfter (context : String) (items : Array Item) : String :=
  items.foldl (fun text item => s!"{text} {item.results}") s!"bindings% {context}"

/-- The sites of the instructions, the most recent first, before the earlier ones. -/
def sitesFunction (items : Array Item) : M String := do
  let sites := items.foldl (fun sites item => item.sites ++ sites) []
  let cells ← sites.mapM number
  pure s!"fun before => {" :: ".intercalate (cells ++ ["before"])}"

/-- After an instruction of the body being printed in pieces. -/
def advance (count : Nat) : M Unit := do
  let state ← get
  let some far := state.far | return
  let far := { far with bound := far.bound + count, items := far.items + 1 }
  if state.options.piece != 0 && far.items == state.options.piece then
    set { state with far := some { far with
      blocks := far.blocks.push far.bound, starts := far.starts.push (far.starts.back! + far.bound),
      bound := 0, items := 0 } }
  else
    set { state with far := some far }

/-- Run a printer of a region that is not the body in pieces. -/
def withoutFar {α : Type} (action : M α) : M α := do
  let saved := (← get).far
  modify fun state => { state with far := none }
  let result ← action
  modify fun state => { state with far := saved }
  pure result

def freshName (stem : String) : M String := do
  let index := (← get).fresh
  modify fun state => { state with fresh := index + 1 }
  pure s!"{stem}_n{index}"

/-- The skips of a body in pieces: one over each piece, and one over each aligned run of
`2 ^ level` pieces. -/
def declareSkips (far : Far) : M Unit := do
  for piece in [1 : far.blocks.size + 1] do
    declare s!"theorem {far.name}_skip{piece}_0 : Skips {far.contextOf piece} {far.contextOf (piece - 1)} {← numberArgument far.blocks[piece - 1]!} :=\n  Skips.drop _ _ _ {← proof}"
    let mut level := 1
    while piece % (2 ^ level) == 0 do
      let half := 2 ^ (level - 1)
      let total := far.starts[piece]! - far.starts[piece - 2 ^ level]!
      declare s!"theorem {far.name}_skip{piece}_{level} : Skips {far.contextOf piece} {far.contextOf (piece - 2 ^ level)} {← numberArgument total} :=\n  Skips.trans {← numberArgument total} {far.name}_skip{piece}_{level - 1} {far.name}_skip{piece - half}_{level - 1} {← proof}"
      level := level + 1

/-! ### Local regions -/

/-- What a local region is typed over, as text, and the names of its declarations. -/
structure LocalEnvironment where
  /-- The headers of the functions it may call. -/
  functions : String
  deployed : String
  functionCount : Nat
  /-- The prefix of the names of nested declarations. -/
  stem : String

def LocalEnvironment.dialect (environment : LocalEnvironment) : String :=
  s!"(LocalDialect signatures {environment.functions} {environment.deployed})"

def LocalEnvironment.link (environment : LocalEnvironment) (context out : String) (depth : Nat) :
    M String := do
  pure s!"LocalRegionLink typeTable signatures {environment.functions} {environment.deployed} {← numberArgument environment.functionCount} {context} {out} {← numberArgument depth}"

def LocalEnvironment.pieceLink (environment : LocalEnvironment) (context after out : String)
    (depth depthAfter : Nat) : M String := do
  pure s!"LocalPrefixLink typeTable signatures {environment.functions} {environment.deployed} {← numberArgument environment.functionCount} {context} {after} {out} {← numberArgument depth} {← numberArgument depthAfter}"

/-- A literal of the typed program. A `fin` literal and a byte are in range by a proof that
the kernel decides. The name is qualified: the printed file opens `Zkc.Core.Raw`, which has
its own `Literal`. -/
def literalValue : Literal → M String
  | .nat value => do pure s!"(Zkc.Core.Literal.nat {← numberArgument value})"
  | .bool value => pure s!"(Zkc.Core.Literal.bool {boolean value})"
  | .fin bound value => do
      pure s!"(Zkc.Core.Literal.fin {← numberArgument bound} ⟨{← number value.val}, by decide⟩)"
  | .nominal row data => do
      pure s!"(Zkc.Core.Literal.nominal {← numberArgument row} {← numbers data})"
  | .bytes data => do
      let bytes ← data.mapM fun byte => do pure s!"⟨{← number byte.val}, by decide⟩"
      pure s!"(Zkc.Core.Literal.bytes {list bytes})"

/-- A literal of the raw program. -/
def rawLiteralValue : Raw.Literal → M String
  | .nat value => do pure s!"(Raw.Literal.nat {← numberArgument value})"
  | .bool value => pure s!"(Raw.Literal.bool {boolean value})"
  | .fin bound value => do
      pure s!"(Raw.Literal.fin {← numberArgument bound} {← numberArgument value})"
  | .nominal row data => do pure s!"(Raw.Literal.nominal {← numberArgument row} {← numbers data})"
  | .bytes data => do pure s!"(Raw.Literal.bytes {← numbers data})"

/-- A size of a sequence type as an argument. -/
def sizeArgument : Option Nat → M String
  | none => pure "none"
  | some size => do pure s!"(some {← numberArgument size})"

/-- An operation the core owns, typed: a position is a variable with its proof and a
widening carries the proof that its bound grows. -/
def builtinValue : Builtin → M String
  | .natAdd => pure "Builtin.natAdd" | .natMul => pure "Builtin.natMul"
  | .natPow => pure "Builtin.natPow" | .natEqual => pure "Builtin.natEqual"
  | .natLess => pure "Builtin.natLess" | .natSub => pure "Builtin.natSub"
  | .natDiv => pure "Builtin.natDiv" | .natRem => pure "Builtin.natRem"
  | .boolAnd => pure "Builtin.boolAnd" | .boolOr => pure "Builtin.boolOr"
  | .boolNot => pure "Builtin.boolNot" | .boolEqual => pure "Builtin.boolEqual"
  | .seqLength element size => do pure s!"(Builtin.seqLength {← type element} {← sizeArgument size})"
  | .seqAt element size => do pure s!"(Builtin.seqAt {← type element} {← sizeArgument size})"
  | .seqSlice element size result => do
      pure s!"(Builtin.seqSlice {← type element} {← sizeArgument size} {← sizeArgument result})"
  | .seqConcat element left right => do
      pure s!"(Builtin.seqConcat {← type element} {← sizeArgument left} {← sizeArgument right})"
  | .seqFill element count => do pure s!"(Builtin.seqFill {← type element} {← numberArgument count})"
  | .seqMake element count => do pure s!"(Builtin.seqMake {← type element} {← numberArgument count})"
  | .seqSized element size => do pure s!"(Builtin.seqSized {← type element} {← numberArgument size})"
  | .seqUnsized element size => do
      pure s!"(Builtin.seqUnsized {← type element} {← numberArgument size})"
  | .natBelow bound => do pure s!"(Builtin.natBelow {← numberArgument bound})"
  | .finToNat bound => do pure s!"(Builtin.finToNat {← numberArgument bound})"
  | .finWiden bound wider _ => do
      pure s!"(Builtin.finWiden {← numberArgument bound} {← numberArgument wider} {← proof})"
  | .tupleMake components => do pure s!"(Builtin.tupleMake {← types components})"
  | .tupleGet components component position => do
      pure s!"(Builtin.tupleGet {← types components} {← type component} ⟨{← number position.index}, {← proof}⟩)"
  | .recordMake declaration use fields => do
      pure s!"(Builtin.recordMake {← numberArgument declaration} {useValue use} {← types fields})"
  | .recordGet declaration use fields field position => do
      pure s!"(Builtin.recordGet {← numberArgument declaration} {useValue use} {← types fields} {← type field} ⟨{← number position.index}, {← proof}⟩)"
  | .variantMake declaration alternatives payload position => do
      pure s!"(Builtin.variantMake {← numberArgument declaration} {← types alternatives} {← type payload} ⟨{← number position.index}, {← proof}⟩)"

/-- An operation the core owns, as written. -/
def rawBuiltinValue : Raw.Builtin → M String
  | .natAdd => pure "Raw.Builtin.natAdd" | .natMul => pure "Raw.Builtin.natMul"
  | .natPow => pure "Raw.Builtin.natPow" | .natEqual => pure "Raw.Builtin.natEqual"
  | .natLess => pure "Raw.Builtin.natLess" | .natSub => pure "Raw.Builtin.natSub"
  | .natDiv => pure "Raw.Builtin.natDiv" | .natRem => pure "Raw.Builtin.natRem"
  | .boolAnd => pure "Raw.Builtin.boolAnd" | .boolOr => pure "Raw.Builtin.boolOr"
  | .boolNot => pure "Raw.Builtin.boolNot" | .boolEqual => pure "Raw.Builtin.boolEqual"
  | .seqLength element size => do
      pure s!"(Raw.Builtin.seqLength {← type element} {← sizeArgument size})"
  | .seqAt element size => do pure s!"(Raw.Builtin.seqAt {← type element} {← sizeArgument size})"
  | .seqSlice element size result => do
      pure s!"(Raw.Builtin.seqSlice {← type element} {← sizeArgument size} {← sizeArgument result})"
  | .seqConcat element left right => do
      pure s!"(Raw.Builtin.seqConcat {← type element} {← sizeArgument left} {← sizeArgument right})"
  | .seqFill element count => do
      pure s!"(Raw.Builtin.seqFill {← type element} {← numberArgument count})"
  | .seqMake element count => do
      pure s!"(Raw.Builtin.seqMake {← type element} {← numberArgument count})"
  | .seqSized element size => do
      pure s!"(Raw.Builtin.seqSized {← type element} {← numberArgument size})"
  | .seqUnsized element size => do
      pure s!"(Raw.Builtin.seqUnsized {← type element} {← numberArgument size})"
  | .natBelow bound => do pure s!"(Raw.Builtin.natBelow {← numberArgument bound})"
  | .finToNat bound => do pure s!"(Raw.Builtin.finToNat {← numberArgument bound})"
  | .finWiden bound wider => do
      pure s!"(Raw.Builtin.finWiden {← numberArgument bound} {← numberArgument wider})"
  | .tupleMake components => do pure s!"(Raw.Builtin.tupleMake {← types components})"
  | .tupleGet components position => do
      pure s!"(Raw.Builtin.tupleGet {← types components} {← numberArgument position})"
  | .recordMake declaration => do
      pure s!"(Raw.Builtin.recordMake {← numberArgument declaration})"
  | .recordGet declaration position => do
      pure s!"(Raw.Builtin.recordGet {← numberArgument declaration} {← numberArgument position})"
  | .variantMake declaration position => do
      pure s!"(Raw.Builtin.variantMake {← numberArgument declaration} {← numberArgument position})"

/-- The count of a typed loop, as an argument. -/
def loopCount : LoopCount → M String
  | .static count => do pure s!"(LoopCount.static {← numberArgument count})"
  | .runtime none => pure "(LoopCount.runtime none)"
  | .runtime (some maximum) => do
      pure s!"(LoopCount.runtime (some {← numberArgument maximum}))"

/-- The count of a typed `repeat`, as an argument. -/
def repeatCount : RepeatCount → M String
  | .static count => do pure s!"(RepeatCount.static {← numberArgument count})"
  | .runtime maximum => do pure s!"(RepeatCount.runtime {← numberArgument maximum})"

/-- The count of a raw `repeat`, as an argument. -/
def rawRepeatCount : Raw.RepeatCount → M String
  | .static count => do pure s!"(Raw.RepeatCount.static {← numberArgument count})"
  | .runtime maximum counts => do
      pure s!"(Raw.RepeatCount.runtime {← numberArgument maximum} {← numbers counts})"

/-- The count of a raw loop, as an argument. -/
def rawLoopCount : Raw.LoopCount → M String
  | .static count => do pure s!"(Raw.LoopCount.static {← numberArgument count})"
  | .runtime none value => do pure s!"(Raw.LoopCount.runtime none {← numberArgument value})"
  | .runtime (some maximum) value => do
      pure s!"(Raw.LoopCount.runtime (some {← numberArgument maximum}) {← numberArgument value})"

/-- The typed operation of a local instruction. -/
def localOperation {operations : List OperationSignature} {functions : List FunctionHeader}
    {deployed : Bool} (environment : LocalEnvironment) :
    LocalOp operations functions deployed → M String
  | .op (inputs := inputs) (outputs := outputs) (kind := kind) reference _ => do
      pure s!"LocalOp.op {← row reference.index ⟨inputs, outputs, kind⟩} {← proof}"
  | .call callee _ => do
      let header := (← get).functionHeaderOf[environment.functionCount - 1 - callee.index]!
      pure s!"LocalOp.call (header := {header}) {← tableReference true environment.functionCount callee.index} {← proof}"
  | .conditional captures outputs => do
      pure s!"LocalOp.conditional {← types captures} {← types outputs}"
  | .match declaration alternatives captures outputs => do
      pure s!"LocalOp.match {← numberArgument declaration} {← types alternatives} {← types captures} {← types outputs}"
  | .loop count carried collected captures => do
      pure s!"LocalOp.loop {← loopCount count} {← types carried} {← types collected} {← types captures}"
  | .guard why => pure s!"LocalOp.guard {reason why}"
  | .literal value => do pure s!"LocalOp.literal {← literalValue value}"
  | .builtin operation => do pure s!"LocalOp.builtin {← builtinValue operation}"

/-- The raw syntax of a local instruction, given the raw syntax of its nested regions. -/
def localStep (instruction : Raw.LocalStep) (nested : List String) : M String := do
  match instruction, nested with
  | .op index values, _ => pure s!"LocalStep.op {← numberArgument index} {← numbers values}"
  | .call callee values, _ => pure s!"LocalStep.call {← numberArgument callee} {← numbers values}"
  | .conditional condition captures outputs _ _, [onTrue, onFalse] =>
      pure s!"LocalStep.conditional {← numberArgument condition} {← numbers captures} {← types outputs} ({onTrue}) ({onFalse})"
  | .match declaration value captures outputs _, arms =>
      let armsText := arms.foldr (fun arm rest => s!"LocalArms.arm ({arm}) ({rest})") "LocalArms.none"
      pure s!"LocalStep.match {← numberArgument declaration} {← numberArgument value} {← numbers captures} {← types outputs} ({armsText})"
  | .loop count carried captures collected _, [body] =>
      pure s!"LocalStep.loop {← rawLoopCount count} {← numbers carried} {← numbers captures} {← types collected} ({body})"
  | .guard why condition, _ => pure s!"LocalStep.guard {reason why} {← numberArgument condition}"
  | .literal value, _ => do pure s!"LocalStep.literal {← rawLiteralValue value}"
  | .builtin operation values, _ => do
      pure s!"LocalStep.builtin {← rawBuiltinValue operation} {← numbers values}"
  | _, _ => pure mismatch

/-- The raw regions nested in a local instruction. -/
def nestedLocal : Raw.LocalStep → List Raw.LocalRegion
  | .conditional _ _ _ onTrue onFalse => [onTrue, onFalse]
  | .match _ _ _ _ arms => arms.toList
  | .loop _ _ _ _ body => [body]
  | _ => []

mutual
  /-- The instructions of a local region and its end. -/
  partial def localItems {operations : List OperationSignature} {functions : List FunctionHeader}
      {deployed : Bool} (environment : LocalEnvironment) {Γ out : List Ty}
      (region : Region (LocalDialect operations functions deployed) Γ out) (raw : Raw.LocalRegion)
      (items : Array Item) : M (Array Item × String × String) := do
    match region, raw with
    | .ret values, .ret numbered =>
        pure (items, s!"Region.ret ({← operands values})", s!"LocalRegion.ret {← numbers numbered}")
    | .stop why, _ => pure (items, s!"Region.stop {stop why}", s!"LocalRegion.stop {stop why}")
    | .letOp op arguments bodies next, .step instruction rest =>
        let typedOp ← localOperation environment op
        let typedArguments ← operands arguments
        let (typedBodies, rawBodies) ← localRegions environment bodies (nestedLocal instruction)
        let item : Item := {
          typed := s!"Region.letOp ({typedOp}) {argument typedArguments} {argument typedBodies}"
          raw := s!"LocalRegion.step ({← localStep instruction rawBodies})"
          results := ← types (LocalOp.results op)
          count := (LocalOp.results op).length }
        advance item.count
        localItems environment next rest (items.push item)
    | .bind (mid := mid) body next, .block _ rawBody rest =>
        let (bodyItems, bodyTyped, bodyRaw) ← withoutFar (localItems environment body rawBody #[])
        let (typedBody, rawBodyText) := nest bodyItems bodyTyped bodyRaw
        let item : Item := {
          typed := s!"Region.bind (mid := {← types mid}) ({typedBody})"
          raw := s!"LocalRegion.block {← types mid} ({rawBodyText})"
          results := ← types mid
          count := mid.length }
        advance item.count
        localItems environment next rest (items.push item)
    | _, _ => pure (items, mismatch, mismatch)

  /-- Closed local regions: the typed regions as one term, and the raw syntax of each. -/
  partial def localRegions {operations : List OperationSignature} {functions : List FunctionHeader}
      {deployed : Bool} (environment : LocalEnvironment) {signatures : List (List Ty × List Ty)}
      (bodies : Regions (LocalDialect operations functions deployed) signatures)
      (raws : List Raw.LocalRegion) : M (String × List String) := do
    match signatures, bodies, raws with
    | _, .nil, _ => pure ("Regions.nil", [])
    | _, .cons (inputs := inputs) (outputs := outputs) body tail, raw :: rest =>
        let (typed, rawText) ← localClosed environment inputs outputs body raw
        let (typedTail, rawTail) ← localRegions environment tail rest
        pure (s!"Regions.cons ({typed}) {argument typedTail}", rawText :: rawTail)
    | _, _, _ => pure (mismatch, [])

  /-- A closed local region: written in place, or a link of its own when it is long. -/
  partial def localClosed {operations : List OperationSignature} {functions : List FunctionHeader}
      {deployed : Bool} (environment : LocalEnvironment) (inputs outputs : List Ty)
      (body : Region (LocalDialect operations functions deployed) (bindAll [] inputs) outputs)
      (raw : Raw.LocalRegion) : M (String × String) := do
    let piece := (← get).options.piece
    if piece == 0 || spineLength body 0 ≤ piece then
      let (items, typed, rawText) ← withoutFar (localItems environment body raw #[])
      pure (nest items typed rawText)
    else
      let name ← freshName environment.stem
      let link ← withoutFar <| localPieces false environment name
        s!"(bindAll [] {← types inputs})" (← types outputs) inputs.length body raw
      pure (s!"{link}.typed", s!"{link}.raw")

  /-- A local region in pieces: declares the pieces and the links that join them, and
  returns the name of the link of the whole region. -/
  partial def localPieces {operations : List OperationSignature} {functions : List FunctionHeader}
      {deployed : Bool} (top : Bool) (environment : LocalEnvironment) (name context out : String)
      (depth : Nat) {Γ outputs : List Ty}
      (region : Region (LocalDialect operations functions deployed) Γ outputs)
      (raw : Raw.LocalRegion) : M String := do
    let size := (← get).options.piece
    let outer := (← get).nestedShared
    modify fun state => { state with far := some { name, context }, nestedShared := outer || top }
    let (items, endTyped, endRaw) ← localItems environment region raw #[]
    let some far := (← get).far | pure mismatch
    modify fun state => { state with far := none }
    let pieces := far.blocks.size
    let mut contexts := #[context]
    for piece in [0 : pieces] do
      let after := contextAfter (far.contextOf piece) (items.extract (piece * size) ((piece + 1) * size))
      declare s!"linked_def {far.name}_context{piece + 1} : List Ty :=\n  {after}"
      contexts := contexts.push (far.contextOf (piece + 1))
    if far.used then declareSkips far
    modify fun state => { state with nestedShared := outer }
    for piece in [0 : pieces] do
      let (typed, rawText) := pieceFunctions (items.extract (piece * size) ((piece + 1) * size))
      let type ← environment.pieceLink contexts[piece]! contexts[piece + 1]! out
        (depth + far.starts[piece]!) (depth + far.starts[piece + 1]!)
      declare s!"linked_def {name}_piece{piece} : {type} :=\n  ⟨{typed},\n   {rawText},\n   fun _ => {← proof}, fun _ => {← proof}⟩"
      if top then closeUnit
    let (typed, rawText) := nest (items.extract (pieces * size) items.size) endTyped endRaw
    let type ← environment.link contexts[pieces]! out (depth + far.starts[pieces]!)
    declare s!"linked_def {name}_rest{pieces} : {type} :=\n  ⟨{typed},\n   {rawText},\n   {← proof}, {← proof}⟩"
    if top then closeUnit
    for step in [0 : pieces] do
      let piece := pieces - 1 - step
      let type ← environment.link contexts[piece]! out (depth + far.starts[piece]!)
      let join := s!"linked_def {name}_rest{piece} : {type} :=\n  {name}_piece{piece}.followedBy {name}_rest{piece + 1}"
      if top then declareClosing join else declare join
    pure s!"{name}_rest0"
end

/-- The link of the body of a function, as a term, and whether it is in pieces: a short
body is written in place. -/
def localBody {operations : List OperationSignature} {functions : List FunctionHeader}
    {deployed : Bool} (environment : LocalEnvironment) (name context out : String) (depth : Nat)
    {Γ outputs : List Ty} (region : Region (LocalDialect operations functions deployed) Γ outputs)
    (raw : Raw.LocalRegion) : M (String × Bool) := do
  let piece := (← get).options.piece
  if piece == 0 || spineLength region 0 ≤ piece then
    let (items, typed, rawText) ← withoutFar (localItems environment region raw #[])
    let (typed, rawText) := nest items typed rawText
    pure (s!"⟨{typed},\n   {rawText},\n   {← proof}, {← proof}⟩", false)
  else
    pure (← localPieces true environment name context out depth region raw, true)

/-! ### Protocol regions -/

structure ProtocolEnvironment extends LocalEnvironment where
  /-- The headers of the protocols it may apply. -/
  protocols : String
  protocolCount : Nat
  rolesText : String
  typeTable : TypeTable
  roles : Nat

def ProtocolEnvironment.participants (enclosing : Option (List Nat)) : M String := do
  match enclosing with
  | none => pure "none"
  | some participants => pure s!"(some {← numbers participants})"

def ProtocolEnvironment.link (environment : ProtocolEnvironment) (enclosing : Option (List Nat))
    (context out : String) (depth : Nat) : M String := do
  pure s!"ProtocolRegionLink typeTable signatures {environment.functions} {environment.protocols} {environment.deployed} {← numberArgument environment.functionCount} {← numberArgument environment.protocolCount} {environment.rolesText} {← ProtocolEnvironment.participants enclosing} {context} {out} {← numberArgument depth}"

def ProtocolEnvironment.pieceLink (environment : ProtocolEnvironment)
    (enclosing : Option (List Nat)) (context after out : String) (depth depthAfter : Nat) :
    M String := do
  pure s!"ProtocolPrefixLink typeTable signatures {environment.functions} {environment.protocols} {environment.deployed} {← numberArgument environment.functionCount} {← numberArgument environment.protocolCount} {environment.rolesText} {← ProtocolEnvironment.participants enclosing} {context} {after} {out} {← numberArgument depth} {← numberArgument depthAfter}"

/-- The raw regions nested in a protocol instruction. -/
def nestedProtocol : Raw.ProtocolStep → List Raw.ProtocolRegion
  | .repeat _ _ _ _ _ body => [body]
  | .choose _ _ _ _ _ arms => arms.toList
  | _ => []

/-- The raw syntax of a protocol instruction, given the raw syntax of its nested
regions (protocol regions, or the local regions of an `at`). -/
def protocolStep (instruction : Raw.ProtocolStep) (nested : List String) : M String := do
  match instruction, nested with
  | .at role step, nested => pure s!"ProtocolStep.at {← numberArgument role} ({← localStep step nested})"
  | .exchange sender receiver site value, _ =>
      pure s!"ProtocolStep.exchange {← numberArgument sender} {← numberArgument receiver} {← numberArgument site} {← numberArgument value}"
  | .draw owner receivers site law values, _ =>
      pure s!"ProtocolStep.draw {← numberArgument owner} {← numbers receivers} {← numberArgument site} {← numberArgument law} {← numbers values}"
  | .sample owner site law values, _ =>
      pure s!"ProtocolStep.sample {← numberArgument owner} {← numberArgument site} {← numberArgument law} {← numbers values}"
  | .repeat participants count carried captures collected _, [body] =>
      pure s!"ProtocolStep.repeat {← numbers participants} {← rawRepeatCount count} {← numbers carried} {← numbers captures} {← locateds collected} ({body})"
  | .choose participants tags tag captures outputs _, arms =>
      let armsText := arms.foldr (fun arm rest => s!"ProtocolArms.arm ({arm}) ({rest})") "ProtocolArms.none"
      pure s!"ProtocolStep.choose {← numbers participants} {← numbers tags} {← choiceTag tag} {← numbers captures} {← locateds outputs} ({armsText})"
  | .apply callee roleMap site values, _ =>
      pure s!"ProtocolStep.apply {← numberArgument callee} {← numbers roleMap} {← numberArgument site} {← numbers values}"
  | _, _ => pure mismatch

/-- The sites that one instruction adds: its own and those of its nested regions. -/
def instructionSites {operations : List OperationSignature} {functions : List FunctionHeader}
    {protocols : List ProtocolHeader} {deployed : Bool} (environment : ProtocolEnvironment)
    (enclosing : Option (List Nat)) (op : ProtocolOp operations functions protocols deployed)
    (bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions) :
    List Nat :=
  match protocolRegionsSites environment.typeTable environment.roles (ProtocolOp.enclosing enclosing op)
      bodies (ProtocolOp.sites op) with
  | .ok sites => sites
  | .error _ => []

mutual
  /-- The typed operation of a protocol instruction, its nested regions as one term, and
  the raw syntax of the nested regions. -/
  partial def protocolOperation {operations : List OperationSignature}
      {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
      (environment : ProtocolEnvironment)
      (op : ProtocolOp operations functions protocols deployed)
      (bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions)
      (instruction : Raw.ProtocolStep) : M (String × String × List String) := do
    match op, bodies, instruction with
    | .at role inner localBodies, _, .at _ step =>
        let typedLocal ← localOperation environment.toLocalEnvironment inner
        let (typedBodies, rawBodies) ← localRegions environment.toLocalEnvironment localBodies
          (nestedLocal step)
        pure (s!"ProtocolOp.at {← numberArgument role} ({typedLocal}) {argument typedBodies}", "Regions.nil",
          rawBodies)
    | .exchange sender receiver site ty, _, _ =>
        pure (s!"ProtocolOp.exchange {← numberArgument sender} {← numberArgument receiver} {← numberArgument site} {← type ty}",
          "Regions.nil", [])
    | .draw owner receivers site (inputs := inputs) (output := output) law _, _, _ =>
        pure (s!"ProtocolOp.draw {← numberArgument owner} {← numbers receivers} {← numberArgument site} {← row law.index ⟨inputs, [output], .sampling⟩} {← proof}",
          "Regions.nil", [])
    | .sample owner site (inputs := inputs) (output := output) law _, _, _ =>
        pure (s!"ProtocolOp.sample {← numberArgument owner} {← numberArgument site} {← row law.index ⟨inputs, [output], .sampling⟩} {← proof}",
          "Regions.nil", [])
    | .repeat participants count carried collected captures _, bodies, instruction =>
        let (typedBodies, rawBodies) ← protocolRegions environment (some participants) bodies
          (nestedProtocol instruction)
        pure (s!"ProtocolOp.repeat {← numbers participants} {← repeatCount count} {← locateds carried} {← locateds collected} {← locateds captures} {← proof}",
          typedBodies, rawBodies)
    | .choose participants tag captures outputs _, bodies, instruction =>
        let (typedBodies, rawBodies) ← protocolRegions environment (some participants) bodies
          (nestedProtocol instruction)
        pure (s!"ProtocolOp.choose {← numbers participants} {← choiceTag tag} {← locateds captures} {← locateds outputs} {← proof}",
          typedBodies, rawBodies)
    | .apply callee roleMap site _, _, _ =>
        let header := (← get).protocolHeaderOf[environment.protocolCount - 1 - callee.index]!
        pure (s!"ProtocolOp.apply (header := {header}) {← tableReference false environment.protocolCount callee.index} {← numbers roleMap} {← numberArgument site} {← proof}",
          "Regions.nil", [])
    | _, _, _ => pure (mismatch, mismatch, [])

  partial def protocolItems {operations : List OperationSignature} {functions : List FunctionHeader}
      {protocols : List ProtocolHeader} {deployed : Bool} (environment : ProtocolEnvironment)
      (enclosing : Option (List Nat)) {Γ out : List Located}
      (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
      (raw : Raw.ProtocolRegion) (items : Array Item) : M (Array Item × String × String) := do
    match region, raw with
    | .ret values, .ret numbered =>
        pure (items, s!"Region.ret ({← operands values})", s!"ProtocolRegion.ret {← numbers numbered}")
    | .stop why, _ => pure (items, s!"Region.stop {stop why}", s!"ProtocolRegion.stop {stop why}")
    | .letOp op arguments bodies next, .step instruction rest =>
        let typedArguments ← operands arguments
        let (typedOp, typedBodies, rawBodies) ← protocolOperation environment op bodies instruction
        let item : Item := {
          typed := s!"Region.letOp ({typedOp}) {argument typedArguments} {argument typedBodies}"
          raw := s!"ProtocolRegion.step ({← protocolStep instruction rawBodies})"
          results := ← locateds (ProtocolOp.results op)
          count := (ProtocolOp.results op).length
          sites := instructionSites environment enclosing op bodies }
        advance item.count
        protocolItems environment enclosing next rest (items.push item)
    | .bind (mid := mid) body next, .block _ rawBody rest =>
        let (bodyItems, bodyTyped, bodyRaw) ←
          withoutFar (protocolItems environment enclosing body rawBody #[])
        let (typedBody, rawBodyText) := nest bodyItems bodyTyped bodyRaw
        let item : Item := {
          typed := s!"Region.bind (mid := {← locateds mid}) ({typedBody})"
          raw := s!"ProtocolRegion.block {← locateds mid} ({rawBodyText})"
          results := ← locateds mid
          count := mid.length
          sites := bodyItems.foldl (fun sites item => item.sites ++ sites) [] }
        advance item.count
        protocolItems environment enclosing next rest (items.push item)
    | _, _ => pure (items, mismatch, mismatch)

  partial def protocolRegions {operations : List OperationSignature}
      {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
      (environment : ProtocolEnvironment) (enclosing : Option (List Nat))
      {signatures : List (List Located × List Located)}
      (bodies : Regions (ProtocolDialect operations functions protocols deployed) signatures)
      (raws : List Raw.ProtocolRegion) : M (String × List String) := do
    match signatures, bodies, raws with
    | _, .nil, _ => pure ("Regions.nil", [])
    | _, .cons (inputs := inputs) (outputs := outputs) body tail, raw :: rest =>
        let (typed, rawText) ← protocolClosed environment enclosing inputs outputs body raw
        let (typedTail, rawTail) ← protocolRegions environment enclosing tail rest
        pure (s!"Regions.cons ({typed}) {argument typedTail}", rawText :: rawTail)
    | _, _, _ => pure (mismatch, [])

  partial def protocolClosed {operations : List OperationSignature}
      {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
      (environment : ProtocolEnvironment) (enclosing : Option (List Nat))
      (inputs outputs : List Located)
      (body : Region (ProtocolDialect operations functions protocols deployed) (bindAll [] inputs)
        outputs)
      (raw : Raw.ProtocolRegion) : M (String × String) := do
    let piece := (← get).options.piece
    if piece == 0 || spineLength body 0 ≤ piece then
      let (items, typed, rawText) ← withoutFar (protocolItems environment enclosing body raw #[])
      pure (nest items typed rawText)
    else
      let name ← freshName environment.stem
      let link ← withoutFar <| protocolPieces false environment enclosing name
        s!"(bindAll [] {← locateds inputs})" (← locateds outputs) inputs.length body raw
      pure (s!"{link}.typed", s!"{link}.raw")

  partial def protocolPieces {operations : List OperationSignature}
      {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
      (top : Bool) (environment : ProtocolEnvironment) (enclosing : Option (List Nat))
      (name context out : String) (depth : Nat) {Γ outputs : List Located}
      (region : Region (ProtocolDialect operations functions protocols deployed) Γ outputs)
      (raw : Raw.ProtocolRegion) : M String := do
    let size := (← get).options.piece
    let outer := (← get).nestedShared
    modify fun state => { state with far := some { name, context }, nestedShared := outer || top }
    let (items, endTyped, endRaw) ← protocolItems environment enclosing region raw #[]
    let some far := (← get).far | pure mismatch
    modify fun state => { state with far := none }
    let pieces := far.blocks.size
    let mut contexts := #[context]
    for piece in [0 : pieces] do
      let after := contextAfter (far.contextOf piece) (items.extract (piece * size) ((piece + 1) * size))
      declare s!"linked_def {far.name}_context{piece + 1} : List Located :=\n  {after}"
      contexts := contexts.push (far.contextOf (piece + 1))
    if far.used then declareSkips far
    modify fun state => { state with nestedShared := outer }
    for piece in [0 : pieces] do
      let pieceItems := items.extract (piece * size) ((piece + 1) * size)
      let (typed, rawText) := pieceFunctions pieceItems
      let type ← environment.pieceLink enclosing contexts[piece]! contexts[piece + 1]! out
        (depth + far.starts[piece]!) (depth + far.starts[piece + 1]!)
      declare s!"linked_def {name}_piece{piece} : {type} :=\n  ⟨{typed},\n   {rawText},\n   {← sitesFunction pieceItems},\n   fun _ => {← proof}, fun _ _ => {← proof}⟩"
      if top then closeUnit
    let restItems := items.extract (pieces * size) items.size
    let (typed, rawText) := nest restItems endTyped endRaw
    let type ← environment.link enclosing contexts[pieces]! out (depth + far.starts[pieces]!)
    declare s!"linked_def {name}_rest{pieces} : {type} :=\n  ⟨{typed},\n   {rawText},\n   {← sitesFunction restItems},\n   {← proof}, fun _ => {← proof}⟩"
    if top then closeUnit
    for step in [0 : pieces] do
      let piece := pieces - 1 - step
      let type ← environment.link enclosing contexts[piece]! out (depth + far.starts[piece]!)
      let join := s!"linked_def {name}_rest{piece} : {type} :=\n  {name}_piece{piece}.followedBy {name}_rest{piece + 1}"
      if top then declareClosing join else declare join
    pure s!"{name}_rest0"
end

/-- The link of the body of a protocol, as a term, and whether it is in pieces: a short
body is written in place. -/
def protocolBody {operations : List OperationSignature} {functions : List FunctionHeader}
    {protocols : List ProtocolHeader} {deployed : Bool} (environment : ProtocolEnvironment)
    (name context out : String) (depth : Nat) {Γ outputs : List Located}
    (region : Region (ProtocolDialect operations functions protocols deployed) Γ outputs)
    (raw : Raw.ProtocolRegion) : M (String × Bool) := do
  let piece := (← get).options.piece
  if piece == 0 || spineLength region 0 ≤ piece then
    let (items, typed, rawText) ← withoutFar (protocolItems environment none region raw #[])
    let (typed, rawText) := nest items typed rawText
    pure (s!"⟨{typed},\n   {rawText},\n   {← sitesFunction items},\n   {← proof}, fun _ => {← proof}⟩",
      false)
  else
    pure (← protocolPieces true environment none name context out depth region raw, true)

/-! ## Headers -/

/-- The header constant of a function. -/
def functionHeader (header : FunctionHeader) : M String := do
  let state ← get
  let known := if state.options.share then
    state.functionHeaders.findIdx? (decide <| · = header) else none
  match known with
  | some index => pure s!"fh{index}"
  | none =>
      let index := (← get).functionHeaders.size
      modify fun state => { state with functionHeaders := state.functionHeaders.push header }
      declareShared s!"linked_def fh{index} : FunctionHeader :=\n  ⟨{← types header.inputs}, {← types header.outputs}, {boolean header.specificationOnly}⟩"
      pure s!"fh{index}"

def copy {ports : List Located} {ty : Ty} (value : Copy ports ty) : M String := do
  pure s!"⟨{← number value.holder}, ⟨{← number value.port.index}, {← proof}⟩⟩"

def agreement {ports : List Located} (value : Agreement ports) : M String := do
  pure s!"⟨{← type value.type}, {← copy value.first}, {list (← value.others.mapM copy)}⟩"

def rawAgreement (value : Raw.Agreement) : M String := do
  pure s!"⟨{boolean value.overOutputs}, {← numbers value.ports}⟩"

/-- The header constant of a protocol. -/
def protocolHeader (header : ProtocolHeader) (raw : Raw.Protocol) : M String := do
  let key : ProtocolKey :=
    (raw.specificationOnly, raw.roles, raw.inputs, raw.outputs, raw.agreements)
  let state ← get
  let known := if state.options.share then
    state.protocolHeaders.findIdx? (decide <| · = key) else none
  match known with
  | some index => pure s!"ph{index}"
  | none =>
      let index := (← get).protocolHeaders.size
      modify fun state => { state with protocolHeaders := state.protocolHeaders.push key }
      let overInputs ← header.agreements.inputs.mapM agreement
      let overOutputs ← header.agreements.outputs.mapM agreement
      declareShared s!"linked_def ph{index} : ProtocolHeader :=\n  ⟨{← number header.roles}, {← locateds header.inputs}, {← locateds header.outputs},\n   ⟨{list overInputs}, {list overOutputs}⟩, {boolean header.specificationOnly}⟩"
      pure s!"ph{index}"

/-! ## Definitions -/

/-- The declarations of one definition, apart from those in the prelude: units that
need only the prelude, and the declarations that join them. -/
structure Printed where
  units : Array (Array String)
  closing : Array String

def takePrinted : M Printed := do
  closeUnit
  let state ← get
  set { state with units := #[], closing := #[], fresh := 0 }
  pure ⟨state.units, state.closing⟩

/-- The functions of a program, oldest first: their declarations, and the chain of
header lists in the prelude. -/
def printFunctions {typeTable : TypeTable} {operations : List OperationSignature} :
    {headers : List FunctionHeader} → Functions typeTable operations headers →
      Array Raw.Function → M (Array Printed)
  | _, .nil, _ => do
      declareShared "linked_def functionHeaders0 : List FunctionHeader := []"
      pure #[]
  | _, .snoc (functions := earlierHeaders) (header := header) earlier definition _, raws => do
      let count := earlierHeaders.length
      let printed ← printFunctions earlier raws
      let some raw := raws[count]? | pure printed
      let headerName ← functionHeader header
      modify fun state => { state with functionHeaderOf := state.functionHeaderOf.push headerName }
      declareShared s!"linked_def functionHeaders{count + 1} : List FunctionHeader := {headerName} :: functionHeaders{count}"
      let environment : LocalEnvironment := {
        functions := s!"functionHeaders{count}", deployed := s!"(!{headerName}.specificationOnly)",
        functionCount := count, stem := s!"f{count}" }
      let some rawBody := raw.body | pure printed
      let (body, inPieces) ← localBody environment s!"f{count}_body"
        s!"(bindAll [] {headerName}.inputs)" s!"{headerName}.outputs" header.inputs.length
        definition.body rawBody
      let link := s!"linked_def f{count} : FunctionLink typeTable signatures functionHeaders{count} {← numberArgument count} {headerName} :=\n  FunctionLink.ofBody {headerName} {← numberArgument header.inputs.length} {← proof} {← proof}\n   {body}"
      if inPieces then declareClosing link else declareUnit link
      pure (printed.push (← takePrinted))

  | _, .opaque (functions := earlierHeaders) earlier header _, raws => do
      let count := earlierHeaders.length
      let printed ← printFunctions earlier raws
      let headerName ← functionHeader header
      modify fun state => { state with functionHeaderOf := state.functionHeaderOf.push headerName }
      declareShared s!"linked_def functionHeaders{count + 1} : List FunctionHeader := {headerName} :: functionHeaders{count}"
      declareUnit s!"linked_def f{count} : OpaqueLink typeTable {headerName} := ⟨{← proof}⟩"
      pure (printed.push (← takePrinted))

/-- Whether each function of a program, oldest first, is known by its header only. -/
def headerOnly {typeTable : TypeTable} {operations : List OperationSignature} :
    {headers : List FunctionHeader} → Functions typeTable operations headers → List Bool → List Bool
  | _, .nil, later => later
  | _, .snoc earlier _ _, later => headerOnly earlier (false :: later)
  | _, .opaque earlier _ _, later => headerOnly earlier (true :: later)

def printProtocols {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} (functionCount : Nat) :
    {headers : List ProtocolHeader} → Protocols typeTable operations functions headers →
      Array Raw.Protocol → M (Array Printed)
  | _, .nil, _ => do
      declareShared "linked_def protocolHeaders0 : List ProtocolHeader := []"
      pure #[]
  | _, .snoc (protocols := earlierHeaders) (header := header) earlier definition _, raws => do
      let count := earlierHeaders.length
      let printed ← printProtocols functionCount earlier raws
      let some raw := raws[count]? | pure printed
      let headerName ← protocolHeader header raw
      modify fun state => { state with protocolHeaderOf := state.protocolHeaderOf.push headerName }
      declareShared s!"linked_def protocolHeaders{count + 1} : List ProtocolHeader := {headerName} :: protocolHeaders{count}"
      let written := (← get).options.written
      let environment : ProtocolEnvironment := {
        functions := s!"functionHeaders{functionCount}",
        deployed := s!"(!{headerName}.specificationOnly)", functionCount, stem := s!"p{count}",
        protocols := s!"protocolHeaders{count}", protocolCount := count,
        rolesText := s!"{headerName}.roles", typeTable, roles := header.roles }
      let (body, inPieces) ← protocolBody environment s!"p{count}_body"
        s!"(bindAll [] {headerName}.inputs)" s!"{headerName}.outputs" header.inputs.length
        definition.body raw.body
      let dense ← if written then pure s!"(fun _ => {← proof})"
        else pure "(fun impossible => nomatch impossible)"
      let link := s!"linked_def p{count} : ProtocolLink {boolean written} typeTable signatures functionHeaders{functionCount} protocolHeaders{count} {← numberArgument functionCount} {← numberArgument count} {headerName} :=\n  ProtocolLink.ofBody {headerName} {← numberArgument header.inputs.length} {list (← raw.agreements.mapM rawAgreement)}\n   ({body})\n   {← proof} {← proof} {← proof} {← proof} {dense}"
      if inPieces then declareClosing link else declareUnit link
      pure (printed.push (← takePrinted))

/-! ## Tables and the package -/

def name (value : Name) : M String := numbers value

def static : Static → M String
  | .domain value => do pure s!"Static.domain {← name value}"
  | .nat value => do pure s!"Static.nat {← numberArgument value}"
  | .type value => do pure s!"Static.type {← type value}"

def catalogueRow (value : CatalogueRow) : M String := do
  pure s!"⟨{← name value.name}, {list (← value.statics.mapM static)}⟩"

def quoted (text : String) : String := "\"" ++ text ++ "\""

def strings (values : List String) : String := list (values.map quoted)

def names : Option Raw.Names → String
  | none => "none"
  | some value =>
      s!"(some ⟨{strings value.functions}, {strings value.protocols}, {list (value.roles.map strings)}, {list (value.sites.map strings)}⟩)"

/-- The tables of a package, in the prelude. -/
def printTables (typed : Typed) : M Unit := do
  declareShared s!"linked_def types : List CatalogueRow :=\n  {list (← typed.types.mapM catalogueRow)}"
  let records ← typed.records.mapM fun record => do
    pure s!"⟨{useValue record.use}, {← types record.fields}⟩"
  declareShared s!"linked_def records : List RecordDeclaration :=\n  {list records}"
  let variants ← typed.variants.mapM fun variant => do pure s!"⟨{← types variant.alternatives}⟩"
  declareShared s!"linked_def variants : List VariantDeclaration :=\n  {list variants}"
  declareShared "linked_def typeTable : TypeTable := typeTableOf types records variants"
  let share := (← get).options.share
  let mut signatures := #[]
  let mut rows := #[]
  let mut index := 0
  for operation in typed.table do
    let literal ← signatureLiteral operation.signature
    if share then
      declareShared s!"linked_def sig{index} : OperationSignature := {literal}"
      signatures := signatures.push s!"sig{index}"
    else
      signatures := signatures.push literal
    rows := rows.push s!"⟨{← catalogueRow operation.identity}, {signatures[index]!}⟩"
    index := index + 1
  declareShared s!"linked_def table : List Operation :=\n  {list rows.toList}"
  declareShared s!"linked_def signatures : List OperationSignature :=\n  {list signatures.toList}"
  if share then
    for row in [0 : index] do
      declareShared s!"linked_def row{row} : Var signatures sig{row} := ⟨{← number row}, {← proof}⟩"

/-- The source of a printed package: the prelude, the declarations of each definition
with its number of instructions, and the assembly. -/
structure Source where
  prelude : Array String
  functions : Array Printed
  protocols : Array Printed
  assembly : Array String

/-- Print a typed package with its raw package. -/
def printPackage (options : Options) (typed : Typed) (raw : Raw.Package) : Source :=
  let action : M Source := do
    printTables typed
    let functions ← printFunctions typed.program.functions raw.functions.toArray
    let functionCount := typed.functions.length
    let protocols ← printProtocols functionCount typed.program.protocols raw.protocols.toArray
    let protocolCount := typed.protocols.length
    let written := boolean options.written
    declareUnit "linked_def functions0 : LinkedFunctions typeTable signatures (nat_lit 0) functionHeaders0 :=\n  LinkedFunctions.empty"
    let opaqueFunctions := (headerOnly typed.program.functions []).toArray
    for index in [0 : functionCount] do
      let step := if opaqueFunctions[index]! then "snocOpaque" else "snoc"
      declareUnit s!"linked_def functions{index + 1} : LinkedFunctions typeTable signatures (nat_lit {index + 1}) functionHeaders{index + 1} :=\n  functions{index}.{step} f{index}"
    declareUnit s!"linked_def protocols0 : LinkedProtocols {written} typeTable signatures functionHeaders{functionCount} (nat_lit {functionCount}) (nat_lit 0) protocolHeaders0 :=\n  LinkedProtocols.empty"
    for index in [0 : protocolCount] do
      declareUnit s!"linked_def protocols{index + 1} : LinkedProtocols {written} typeTable signatures functionHeaders{functionCount} (nat_lit {functionCount}) (nat_lit {index + 1}) protocolHeaders{index + 1} :=\n  protocols{index}.snoc p{index}"
    declareUnit s!"linked_def names : Option Raw.Names :=\n  {names typed.names}"
    declareUnit s!"linked_def package : LinkedPackage {written} :=\n  ⟨types, records, variants, table, names, nat_lit {functionCount}, nat_lit {protocolCount}, functionHeaders{functionCount}, protocolHeaders{protocolCount},\n   functions{functionCount}, protocols{protocolCount}, {← proof}, {← proof}⟩"
    declareUnit "linked_def typed : Typed := package.typed"
    let rawFunctions := (List.range functionCount).map fun index => s!"f{index}.raw"
    let rawProtocols := (List.range protocolCount).map fun index => s!"p{index}.raw"
    declareUnit s!"linked_def raw : Raw.Package :=\n  ⟨types.map CatalogueRow.strip, records, variants, table.map Operation.strip,\n   {list rawFunctions},\n   {list rawProtocols}, names⟩"
    declareUnit s!"theorem raw_eq : package.raw = raw := {← proof}"
    declareUnit "theorem unelaborates : unelaborate typed = raw := raw_eq ▸ package.unelaborates"
    declareUnit "theorem elaborates : elaborate raw = Except.ok typed := raw_eq ▸ package.elaborates"
    if options.written then
      declareUnit "theorem elaboratesWritten : elaborateWritten raw = Except.ok typed :=\n  raw_eq ▸ package.elaboratesWritten rfl"
    let assembly := (← get).output
    pure ⟨(← get).shared, functions, protocols, assembly⟩
  (action.run { options }).1

end Zkc.Core.PrintLinked
