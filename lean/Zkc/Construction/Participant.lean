module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Source.Structured.Operations
public import Zkc.Source.Structured.ProtocolContext

@[expose] public section

/-! Role-local participant programs after native transcript construction.

The bridge decodes the compiler's `zkc.constructed-participant/0` export into
this carrier. Every exported operation keeps its operand references and result
sorts; transcript operations keep their decoded occurrence templates; a loop
keeps its body. References are absolute positions in a scoped environment:
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

/-- A typed request identity: the method, the operands fixed before sampling
and the result sort. `draw` is the only method the construction model carries:
it has no operands, and its result sort is the field its service contract
names. -/
structure Request where
  method : String
  operands : List Nat
  sort : Structured.Ty
  deriving DecidableEq, Repr

namespace Request

/-- A field draw with no data operands, used by local and replaced services. -/
def draw (field : String) : Request := ⟨"draw", [], .field field⟩

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
site, or a repeat. -/
structure Step where
  kind : String
  protocol : String
  site : String
  deriving DecidableEq, Repr

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
  /-- An owner-local request. Coordinates are references to enclosing induction
  values, not request operands or transcript state. Only field draw is admitted. -/
  | localService (port : ServicePort) (request : Request)
      (template : Template) (coordinates : List Nat)
  | calculate (calculation : Calculation)
  | call (helper : String)
  | guard (site : String)
  /-- A loop of at most `maximum` iterations; its operands are the count and the
  initial carried values, and `yielded` names the body's yielded references. -/
  | loop (site : String) (maximum : Nat) (yielded : List Nat)
  | unsupported (name : String)
  deriving DecidableEq, Repr

/-- An exported instruction. Only a loop has a nonempty body. -/
structure Instruction where
  operation : Operation
  operands : List Nat
  results : List ValueSort
  body : List Instruction
  deriving Repr

mutual
/-- Equality decisions expose Boolean computation to kernel admission checks. -/
def Instruction.decide : (left right : Instruction) → Decidable (left = right)
  | ⟨operation, operands, results, body⟩, ⟨operation', operands', results', body'⟩ =>
      letI : Decidable (body = body') := Instruction.decideList body body'
      decidable_of_iff (operation = operation' ∧ operands = operands' ∧
        results = results' ∧ body = body') (by simp only [Instruction.mk.injEq])

def Instruction.decideList : (left right : List Instruction) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | head :: tail, head' :: tail' =>
      letI := Instruction.decide head head'
      letI := Instruction.decideList tail tail'
      decidable_of_iff (head = head' ∧ tail = tail') (by simp only [List.cons.injEq])
end

instance : DecidableEq Instruction := Instruction.decide

/-- The native deployment policy exactly as exported: entry, producer and
validator roles, acceptance index, suite, replaced services, public inputs,
ordered query/delivery site pairs, framing and construction selector. -/
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
/-- The field of the first challenge operation of an instruction, searching loop
bodies. -/
def Instruction.challengeField : Instruction → Option String
  | ⟨.challenge _ field _, _, _, _⟩ => some field
  | ⟨_, _, _, body⟩ => Instruction.challengeFieldList body

/-- The field of the first challenge operation of an instruction list. -/
def Instruction.challengeFieldList : List Instruction → Option String
  | [] => none
  | instruction :: rest =>
      match Instruction.challengeField instruction with
      | some field => some field
      | none => Instruction.challengeFieldList rest
end

end Zkc.Construction

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Calculation.total
