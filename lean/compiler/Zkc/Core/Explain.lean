module

public import Zkc.Core.Admission

public section

/-! The explanation of a refusal of the check of facts.

Admission says whether a package is admitted, and names the first application of each
definition that is not justified. A producer that words a refusal for the author of a program
needs more: every application of a definition that is not justified, the condition of the
requirement that is not met, and what was known of the operands.

`explain` goes through the normal form of a definition as the check of facts does, with the
same functions for what is known, and does not stop at an application that is not justified:
it goes on with what the check would know after it. It returns, for each such application,
the path of the instruction as written, the role for which it is a copy in a protocol body,
the requirement, its condition, and the lower and the upper end and the known length of each
operand.

It decides nothing and no theorem reads it. What it reports of a definition is empty exactly
when the definition passes the check, since it finds the first application that the check
finds.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

namespace Explain

/-- What is known of an operand: the ends of its interval, and, for a sequence, its length
when it is known to be a number. -/
structure Known where
  lo : Nat
  hi : Option Nat
  length : Option Nat
  deriving Repr, Inhabited, DecidableEq

/-- The condition of a requirement that is not met. A slice has four. -/
inductive Condition where
  /-- The requirement has one condition. -/
  | whole
  /-- The bounds of a slice are not known to be in order. -/
  | order
  /-- The upper bound of a slice is not known to be within the static size. -/
  | upperSize
  /-- The upper bound of a slice is not known to be within the length. -/
  | upperLength
  /-- The bounds of a slice are not known to have the size of its result. -/
  | resultSize
  deriving Repr, Inhabited, DecidableEq

/-- An application that is not justified, explained. -/
structure Explained where
  /-- The path of the instruction in the body as written; empty when it is found at no
  instruction. -/
  path : List Nat
  /-- The role for which the instruction is a copy, in a protocol body. -/
  role : Option Nat
  requirement : Requirement
  condition : Condition
  /-- What is known of each operand, in the order of the operands. -/
  operands : List Known
  deriving Repr, Inhabited

/-- What the facts know of a value. -/
def known (facts : Facts) (level : Nat) : Known :=
  { lo := facts.lo level, hi := facts.hi level
    length := (facts.lengths level).findSome? fun length =>
      match facts.hi length with
      | some size => cond (facts.point length size) (some size) none
      | none => none }

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- The condition of the requirement of an application that is not met. -/
def conditionOf (facts : Facts) : LocalOp operations functions deployed → List Nat → Condition
  | .builtin (.seqSlice _ size _), [sequence, first, last] =>
      if !facts.knownLe first last then .order
      else match size with
        | some size => if !within (facts.hi last) size then .upperSize else .resultSize
        | none =>
            if !(facts.lengths sequence).any fun length => facts.knownLe last length then .upperLength
            else .resultSize
  | _, _ => .whole

mutual
  /-- What a local region returns, and every application of it that is not justified, in the
  order of the body. `role` is the role whose code the region is. -/
  def explainRegion (role : Option Nat) (path : List Nat) (index : Nat) (facts : Facts)
      {Γ out : List Ty} :
      Region (LocalDialect operations functions deployed) Γ out → Outcome × List Explained
    | .ret values => (some ((Scope.numbers facts.depth values).map facts.returned), [])
    | .stop reason =>
        (none, if reason = .undefined then [⟨path ++ [index], role, .reservedStop, .whole, []⟩] else [])
    | .letOp op arguments bodies next =>
        let levels := Scope.numbers facts.depth arguments
        let here := match cond facts.dead none (LocalOp.unjustified facts op levels) with
          | some requirement =>
              [⟨path ++ [index], role, requirement, conditionOf facts op levels, levels.map (known facts)⟩]
          | none => []
        let (outcomes, inner) := explainRegions role (path ++ [index])
          (LocalOp.regionFacts facts op levels) 0 bodies
        let (outcome, rest) := explainRegion role path (index + 1)
          ((LocalOp.factsAfter facts op levels outcomes).reshape facts.depth
            (LocalOp.branchShape op levels bodies)) next
        (outcome, here ++ inner ++ rest)
    | .bind (mid := mid) body next =>
        let (outcome, inner) := explainRegion role (path ++ [index]) 0 facts body
        let (after, rest) := explainRegion role path (index + 1)
          ((facts.after (mid.map fun _ => Shape.other)
            (boundsOf facts.depth mid outcome.intervals)).inScope mid) next
        (after, inner ++ rest)

  def explainRegions (role : Option Nat) (path : List Nat) (factsOf : Nat → Facts) (number : Nat)
      {signatures : List (List Ty × List Ty)} :
      Regions (LocalDialect operations functions deployed) signatures →
        List Outcome × List Explained
    | .nil => ([], [])
    | .cons body tail =>
        let (outcome, inner) := explainRegion role (path ++ [number]) 0 (factsOf number) body
        let (outcomes, rest) := explainRegions role path factsOf (number + 1) tail
        (outcome :: outcomes, inner ++ rest)
end

end Local

section Protocol

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- The first participant that does not know its copy of a count to be within a maximum, with
what it knows of it. -/
def unbounded (state : RoleFacts) (maximum : Nat) : List Nat → List Nat → Option (Nat × Known)
  | role :: participants, count :: counts =>
      if (state.view role).dead || within ((state.view role).hi count) maximum then
        unbounded state maximum participants counts
      else some (role, known (state.view role) count)
  | _, _ => none

mutual
  /-- What a region of a protocol body returns, and every application of it that is not
  justified, in the order of the body. -/
  def explainProtocol (path : List Nat) (index : Nat) (state : RoleFacts) {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out →
        Outcome × List Explained
    | .ret values => (some (state.returned state.depth values), [])
    | .stop reason =>
        (none, if reason = .undefined then [⟨path ++ [index], none, .reservedStop, .whole, []⟩] else [])
    | .letOp op arguments bodies next =>
        let levels := Scope.numbers state.depth arguments
        -- what the instruction itself does not meet, what its local regions do not, and what
        -- the roles know after it
        let (here, after) : List Explained × RoleFacts := match op, bodies with
          | .at role local_ regions, _ =>
              let unmet := match state.unjustifiedLocal role local_ levels with
                | some requirement =>
                    [⟨path ++ [index], some role, requirement,
                      conditionOf (state.view role) local_ levels,
                      levels.map (known (state.view role))⟩]
                | none => []
              let (outcomes, inner) := explainRegions (some role) (path ++ [index])
                (state.localRegionFacts role local_ levels) 0 regions
              (unmet ++ inner,
                state.afterLocal role local_ levels outcomes (LocalOp.branchShape local_ levels regions))
          | .repeat participants (.runtime maximum) _ _ _ _, _ =>
              (cond (state.dead || state.countsWithin maximum participants levels) []
                (match unbounded state maximum participants levels with
                  | some (role, count) => [⟨path ++ [index], some role, .maximum, .whole, [count]⟩]
                  | none => [⟨path ++ [index], none, .maximum, .whole, []⟩]),
                state.bind op.results.length)
          | _, _ => ([], state.bind op.results.length)
        let (outcomes, inner) := explainProtocols (path ++ [index])
          (ProtocolOp.regionState state op levels) 0 bodies
        let (outcome, rest) := explainProtocol path (index + 1)
          ((ProtocolOp.joined state.depth op outcomes after).inScope op.results) next
        (outcome, here ++ inner ++ rest)
    | .bind (mid := mid) body next =>
        let (outcome, inner) := explainProtocol (path ++ [index]) 0 state body
        let (after, rest) := explainProtocol path (index + 1)
          (((state.bind mid.length).withResults state.depth mid outcome.intervals).inScope mid) next
        (after, inner ++ rest)

  def explainProtocols (path : List Nat) (stateOf : Nat → RoleFacts) (number : Nat)
      {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures →
        List Outcome × List Explained
    | .nil => ([], [])
    | .cons body tail =>
        let (outcome, inner) := explainProtocol (path ++ [number]) 0 (stateOf number) body
        let (outcomes, rest) := explainProtocols path stateOf (number + 1) tail
        (outcome :: outcomes, inner ++ rest)
end

end Protocol

/-- An explanation at the path of the instruction as written. -/
def placed (origins : List Trace) (explained : Explained) : Explained :=
  { explained with path := (Trace.written origins explained.path).getD [] }

end Explain

section Definitions

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- Every application of a function's normal form that is not justified, at its path in the
body as written. -/
def FunctionDefinition.explain {header : FunctionHeader}
    (definition : FunctionDefinition operations functions header) : List Explain.Explained :=
  (Explain.explainRegion none [] 0 ((Facts.start header.inputs.length).inScope header.inputs)
    definition.normal.body).2.map
      (Explain.placed (definition.body.origins localNormalizer Tracer.none))

/-- Every application of a protocol's normal form that is not justified, at its path in the
body as written. -/
def ProtocolDefinition.explain {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) :
    List Explain.Explained :=
  (Explain.explainProtocol [] 0 ((RoleFacts.start header.inputs.length).inScope header.inputs)
    definition.normal.body).2.map
      (Explain.placed (definition.body.origins protocolNormalizer protocolTracer))

/-- The explanations of the functions of a program, by their numbers in program order. -/
def Functions.explain {typeTable : TypeTable} :
    {functions : List FunctionHeader} → Functions typeTable operations functions →
      List (Nat × Explain.Explained)
  | _, .nil => []
  | _, .snoc (functions := functions) earlier definition _ =>
      earlier.explain ++ definition.explain.map fun explained => (functions.length, explained)
  | _, .opaque earlier _ _ => earlier.explain

/-- The explanations of the protocols of a program, by their numbers in program order. -/
def Protocols.explain {typeTable : TypeTable} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      List (Nat × Explain.Explained)
  | _, .nil => []
  | _, .snoc (protocols := protocols) earlier definition _ =>
      earlier.explain ++ definition.explain.map fun explained => (protocols.length, explained)

end Definitions

/-- Every application of a typed package that is not justified, with the definition it is
in. -/
def Typed.explain (typed : Typed) : List (Zkc.Core.Refusal.Definition × Explain.Explained) :=
  typed.program.functions.explain.map (fun (number, explained) => (.function number, explained)) ++
    typed.program.protocols.explain.map fun (number, explained) => (.protocol number, explained)

end Zkc.Core
