module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.IR.Source.Structured.Operations
public import Zkc.IR.Source.Structured.ProtocolContext
public import Zkc.IR.Source.Structured.ServiceOperations
public import Init.Data.Nat.Power2.Bitwise

@[expose] public section

/-! Role-local participant programs after native construction, including plain
participants with no transcript capability.

The bridge decodes the compiler's `zkc.constructed-participant/0` export into
this carrier. Every exported operation keeps its operand references and result
sorts; transcript operations keep their decoded occurrence templates; every region keeps its inputs, body and yielded references. References are absolute positions in a scoped environment:
inputs first, then every result in execution order; a loop body extends the
environment at the loop with the induction index and the carried values, and
after the loop its results take the place of the body's values. Calculations use
the structured vocabulary and helper calls name checked helpers of the original
program. The carrier fixes no meaning for any operation; separate models select
one.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source

/-- A request identity: the method, the operands fixed before sampling
and the result sort. The strict typed operation decoder admits field draw,
scalar index and block indices. Values in this record are evaluated unsigned
constants; instruction operands separately retain the actual SSA references. -/
structure Request where
  method : String
  operands : List Nat
  sort : Structured.Ty
  deriving DecidableEq, Repr

namespace Request

/-- A field draw with no data operands, used by local and replaced services. -/
def draw (field : String) : Request := ⟨"draw", [], .field field⟩

/-- Request operands are evaluated unsigned values, never SSA references. -/
def sampleIndex (bound : Nat) : Request := ⟨"index", [bound], .index⟩

def sampleIndices (bound count : Nat) : Request := ⟨"indices", [bound, count], .indices⟩

/-- Positive source formation does not impose provider power-of-two/count caps. -/
def valid : Request → Bool
  | ⟨"draw", [], .field _⟩ => true
  | ⟨"index", [bound], .index⟩ => 0 < bound && bound < Structured.indexLimit
  | ⟨"indices", [bound, count], .indices⟩ =>
      0 < bound && bound < Structured.indexLimit && 0 < count && count < Structured.indexLimit
  | _ => false

/-- Native transcript providers have a narrower supported domain than source
and private services. This predicate is never used for source formation. -/
def nativeSupported : Request → Bool
  | ⟨"draw", [], .field _⟩ => true
  | ⟨"index", [bound], .index⟩ => decide bound.isPowerOfTwo && bound ≤ 2 ^ 63
  | ⟨"indices", [bound, count], .indices⟩ =>
      decide bound.isPowerOfTwo && bound ≤ 2 ^ 63 && 0 < count && count ≤ 1048576
  | _ => false

/-- Exact nominal contract plus typed operation; no unchecked method fallback. -/
def operation (contract : String) : Request → Option Structured.ServiceOp
  | ⟨"draw", [], .field field⟩ =>
      if contract = "random." ++ field ++ "/0" then some (.draw field) else none
  | ⟨"index", [_], .index⟩ => some (.sampleIndex contract)
  | ⟨"indices", [_, _], .indices⟩ => some (.sampleIndices contract)
  | _ => none

end Request

/-- A model occurrence: the original entry, the ordered event fields that the
Fiat–Shamir transform absorbs, and, for a challenge, its typed request. -/
structure Origin where
  entry : String
  event : List String
  request : Option Request
  deriving DecidableEq, Repr

namespace Origin

/-- A message occurrence; its schema is the original source site. -/
def message (entry site sender receiver : String) : Origin :=
  ⟨entry, ["message", entry, site, site, sender, receiver], none⟩

/-- A challenge occurrence at a query site of the replaced service, with its
typed request: the key spells the kind, the occurrence (entry, site, port and
contract), the owner, and the request's method, operands and result sort. -/
def query (entry site port contract owner : String) (request : Request) : Origin :=
  ⟨entry, ["query", entry, site, port, contract, owner], some request⟩

end Origin

/-- One step of a native occurrence path: an application of a protocol at a
site, a repeat, or the selected arm of a branch, which keeps the arm's exact
declared alternative. A branch step precedes only events in that arm and adds
no dynamic coordinate. -/
inductive Step where
  | apply (protocol site : String)
  | «repeat» (protocol site : String)
  | branch (protocol site alternative : String)
  deriving DecidableEq, Repr

namespace Step

/-- The step's tag in the canonical encoding: `apply`, `repeat` or `branch`. -/
def kind : Step → String
  | .apply .. => "apply"
  | .repeat .. => "repeat"
  | .branch .. => "branch"

/-- The original protocol the step occurs in. -/
def protocol : Step → String
  | .apply protocol _ | .repeat protocol _ | .branch protocol _ _ => protocol

/-- The original site of the application, repeat or branch. -/
def site : Step → String
  | .apply _ site | .repeat _ site | .branch _ site _ => site

end Step

/-- A native occurrence template, decoded from its canonical bytes
`["zkc.native-origin-template/0", entry, steps, [], event]`. -/
structure Template where
  entry : String
  steps : List Step
  event : List String
  deriving DecidableEq, Repr

namespace Template

/-- The application prefix of the template's path, rendered as the structured
semantics renders nested application sites. -/
def applicationPrefix (template : Template) : Option String :=
  template.steps.foldl (fun outer step =>
    if step.kind = "apply" then some (Structured.qualifyProtocolSite outer step.site) else outer) none

/-- A local site of the template's innermost protocol, qualified by its path. -/
def qualify (template : Template) (site : String) : String :=
  Structured.qualifyProtocolSite template.applicationPrefix site

/-- The number of enclosing repeats, which is the number of dynamic coordinates. -/
def repeats (template : Template) : Nat :=
  (template.steps.filter (·.kind = "repeat")).length

/-- The qualified site of a query template. -/
def querySite? (template : Template) : Option String :=
  match template.event with
  | ["query", _, site, _, _, _, _] => some (template.qualify site)
  | _ => none

/-- The qualified site of a message template. -/
def messageSite? (template : Template) : Option String :=
  match template.event with
  | ["message", _, site, _, _, _] => some (template.qualify site)
  | _ => none

/-- Whether a message template's sender is the given role name. -/
def sentBy (template : Template) (role : String) : Bool :=
  match template.event with
  | ["message", _, _, _, sender, _] => sender == role
  | _ => false

end Template

/-- Pure calculations of the structured vocabulary that exported programs
execute directly. Helper invocations are separate `call` operations. -/
inductive Calculation where
  | indexConstant (value : Nat)
  | indexEqual
  | indexWrappingAdd | indexWrappingSubtract | indexBitAnd | indexLogicalShiftRight
  | fieldConstant (domain : String) (value : Nat)
  | fieldAdd (domain : String)
  | fieldSubtract (domain : String)
  | fieldMultiply (domain : String)
  | fieldEmbed (extension base : String)
  | fieldEqual (domain : String)
  | groupIdentity (domain : String)
  | groupAdd (domain : String)
  | groupScale (group field : String)
  | groupEqual (domain : String)
  | booleanConstant (value : Bool)
  | booleanAnd | booleanOr | booleanXor | booleanEqual | booleanNotEqual
  | select (type : Structured.Ty)
  | boundedAt (domain : String)
  deriving DecidableEq, Repr

namespace Calculation

/-- The structured operation a calculation denotes. -/
def op : Calculation → Structured.Op
  | .indexConstant value => .indexConstant value
  | .indexEqual => .indexEqual
  | .indexWrappingAdd => .indexWrappingAdd
  | .indexWrappingSubtract => .indexWrappingSubtract
  | .indexBitAnd => .indexBitAnd
  | .indexLogicalShiftRight => .indexLogicalShiftRight
  | .fieldConstant domain value => .fieldConstant domain value
  | .fieldAdd domain => .fieldAdd domain
  | .fieldSubtract domain => .fieldSubtract domain
  | .fieldMultiply domain => .fieldMultiply domain
  | .fieldEmbed extension base => .fieldEmbed extension base
  | .fieldEqual domain => .fieldEqual domain
  | .groupIdentity domain => .groupIdentity domain
  | .groupAdd domain => .groupAdd domain
  | .groupScale group field => .groupScale group field
  | .groupEqual domain => .groupEqual domain
  | .booleanConstant value => .booleanConstant value
  | .booleanAnd => .booleanAnd
  | .booleanOr => .booleanOr
  | .booleanXor => .booleanXor
  | .booleanEqual => .booleanEqual
  | .booleanNotEqual => .booleanNotEqual
  | .select type => .select type
  | .boundedAt domain => .boundedAt domain

/-- The calculation a structured operation is, if it is one. -/
def ofOp? : Structured.Op → Option Calculation
  | .indexConstant value => some (.indexConstant value)
  | .indexEqual => some .indexEqual
  | .indexWrappingAdd => some .indexWrappingAdd
  | .indexWrappingSubtract => some .indexWrappingSubtract
  | .indexBitAnd => some .indexBitAnd
  | .indexLogicalShiftRight => some .indexLogicalShiftRight
  | .fieldConstant domain value => some (.fieldConstant domain value)
  | .fieldAdd domain => some (.fieldAdd domain)
  | .fieldSubtract domain => some (.fieldSubtract domain)
  | .fieldMultiply domain => some (.fieldMultiply domain)
  | .fieldEmbed extension base => some (.fieldEmbed extension base)
  | .fieldEqual domain => some (.fieldEqual domain)
  | .groupIdentity domain => some (.groupIdentity domain)
  | .groupAdd domain => some (.groupAdd domain)
  | .groupScale group field => some (.groupScale group field)
  | .groupEqual domain => some (.groupEqual domain)
  | .booleanConstant value => some (.booleanConstant value)
  | .booleanAnd => some .booleanAnd
  | .booleanOr => some .booleanOr
  | .booleanXor => some .booleanXor
  | .booleanEqual => some .booleanEqual
  | .booleanNotEqual => some .booleanNotEqual
  | .select type => some (.select type)
  | .boundedAt domain => some (.boundedAt domain)
  | _ => none

theorem ofOp?_some {op : Structured.Op} {calculation : Calculation}
    (found : ofOp? op = some calculation) : calculation.op = op := by
  cases op <;> simp [ofOp?] at found <;> subst found <;> rfl

/-- Calculations that never stop; only an out-of-range `boundedAt` refuses. -/
def total : Calculation → Bool
  | .boundedAt _ => false
  | _ => true

end Calculation

/-- Sorts of exported values: structured data, the affine transcript capability
of one suite, and occurrence coordinates. -/
inductive ValueSort where
  | data (ty : Structured.Ty)
  | transcript (suite : String)
  | indices
  deriving DecidableEq, Repr

/-- A retained native service port, separate from ordinary SSA inputs. `root`
is its original entry input; `input` is its position in the role's complete
native interface. Aliases of one root share state, regardless of query site. -/
structure ServicePort where
  name : String
  owner : String
  root : Nat
  input : Nat
  contract : String
  deriving DecidableEq, Repr

/-- Exported operations, as decoded from operation names, operation bindings and
attributes. Anything outside this vocabulary is retained as `unsupported`. -/
inductive Operation where
  | receive (site schema peer : String) (ty : Structured.Ty)
  | send (site schema peer : String)
  | indicesEmpty
  | indicesAppend
  | observe (suite : String) (template : Template)
  | challenge (suite field : String) (template : Template)
  /-- Typed requests retain value identity; the instruction operands separately
  retain the corresponding SSA references after transcript and coordinates. -/
  | indexChallenge (suite : String) (bound : Nat) (template : Template)
  | blockChallenge (suite : String) (bound count : Nat) (template : Template)
  /-- An owner-local request. Coordinates are references to enclosing induction
  values, separate from the request's evaluated bound/count and service operands. -/
  | localService (port : ServicePort) (request : Request)
      (template : Template) (coordinates : List Nat)
  | calculate (calculation : Calculation)
  | call (helper : String)
  | guard (site : String)
  /-- A loop of at most `maximum` iterations. Its single region owns the
  induction/carried arguments, body and yielded references. -/
  | loop (site : String) (maximum : Nat)
  /-- Pure Boolean selection. Both closed arms are retained and checked; only
  the selected arm executes. It does not select protocol interactions. -/
  | mathBranch
  | unsupported (name : String)
  deriving DecidableEq, Repr

mutual
/-- An exported instruction with the ordered regions its operation owns. -/
structure Instruction where
  operation : Operation
  operands : List Nat
  results : List ValueSort
  regions : List InstructionRegion
  deriving Repr

/-- Region arguments and exact yields belong to the body. Math arms use closed
argument frames; loop bodies extend the surrounding frame. The operation fixes
that scoping rule, so a body cannot choose its own ambient environment. -/
structure InstructionRegion where
  inputs : List ValueSort
  instructions : List Instruction
  yielded : List Nat
  deriving Repr
end

mutual
/-- Equality decisions expose Boolean computation to kernel admission checks. -/
def Instruction.decide : (left right : Instruction) → Decidable (left = right)
  | ⟨operation, operands, results, regions⟩, ⟨operation', operands', results', regions'⟩ =>
      letI := InstructionRegion.decideList regions regions'
      decidable_of_iff (operation = operation' ∧ operands = operands' ∧
        results = results' ∧ regions = regions') (by simp only [Instruction.mk.injEq])

def Instruction.decideList : (left right : List Instruction) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | head :: tail, head' :: tail' =>
      letI := Instruction.decide head head'
      letI := Instruction.decideList tail tail'
      decidable_of_iff (head = head' ∧ tail = tail') (by simp only [List.cons.injEq])

def InstructionRegion.decide : (left right : InstructionRegion) → Decidable (left = right)
  | ⟨inputs, instructions, yielded⟩, ⟨inputs', instructions', yielded'⟩ =>
      letI := Instruction.decideList instructions instructions'
      decidable_of_iff (inputs = inputs' ∧ instructions = instructions' ∧ yielded = yielded')
        (by simp only [InstructionRegion.mk.injEq])

def InstructionRegion.decideList :
    (left right : List InstructionRegion) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | head :: tail, head' :: tail' =>
      letI := InstructionRegion.decide head head'
      letI := InstructionRegion.decideList tail tail'
      decidable_of_iff (head = head' ∧ tail = tail') (by simp only [List.cons.injEq])
end

instance : DecidableEq Instruction := Instruction.decide
instance : DecidableEq InstructionRegion := InstructionRegion.decide

mutual
/-- Helper calls in every stored region, including dormant Math arms. -/
def Instruction.callList : List Instruction → List (String × List ValueSort)
  | [] => []
  | instruction :: rest => Instruction.callsOf instruction ++ Instruction.callList rest

def Instruction.callsOf : Instruction → List (String × List ValueSort)
  | ⟨operation, _, results, regions⟩ =>
      (match operation with | .call name => [(name, results)] | _ => []) ++
        InstructionRegion.calls regions

def InstructionRegion.calls : List InstructionRegion → List (String × List ValueSort)
  | [] => []
  | ⟨_, body, _⟩ :: rest => Instruction.callList body ++ InstructionRegion.calls rest
end

/-- The supported projection of a native deployment policy: entry, producer and
validator roles, acceptance index, suite, replaced services, public inputs,
ordered query/delivery site pairs, framing and construction selector. The reader
requires the final wire gates array to be empty before omitting it here. -/
structure Policy where
  entry : String
  producer : String
  validator : String
  acceptance : Nat
  suite : String
  services : List Nat
  publicInputs : List Nat
  draws : List (String × String)
  format : String
  construction : String
  deriving DecidableEq, Repr

/-- One exported validator participant. `source` and `candidate` identify the
original MLIR bytes and the checked candidate print. -/
structure Participant where
  source : String
  candidate : String
  policy : Policy
  symbol : String
  inputs : List ValueSort
  outputs : List ValueSort
  instructions : List Instruction
  returned : List Nat
  servicePorts : List ServicePort := []
  deriving DecidableEq, Repr

mutual
/-- The first stored challenge field, including nested regions. -/
def Instruction.challengeField : Instruction → Option String
  | ⟨.challenge _ field _, _, _, _⟩ => some field
  | ⟨_, _, _, regions⟩ => InstructionRegion.challengeField regions

def Instruction.challengeFieldList : List Instruction → Option String
  | [] => none
  | instruction :: rest =>
      instruction.challengeField.orElse fun _ => Instruction.challengeFieldList rest

def InstructionRegion.challengeField : List InstructionRegion → Option String
  | [] => none
  | ⟨_, body, _⟩ :: rest =>
      (Instruction.challengeFieldList body).orElse fun _ => InstructionRegion.challengeField rest
end

end Zkc.Construction

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Calculation.total
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Request.valid
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Request.operation
