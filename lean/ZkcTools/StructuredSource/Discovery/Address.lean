module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Search addresses in the admitted raw Region carrier. Paths use 0 for a bind
body, 1 for its continuation (also a let continuation), and 2,k for callback k.
These are static selections, never dynamic event or random-oracle keys. -/

namespace ZkcTools.StructuredSource.Discovery
open Zkc.Source Zkc.Source.Structured

inductive Coordinate where
  | instruction | input (index : Nat) | operand (index : Nat) | result (index : Nat)
  deriving DecidableEq, Repr

structure Address where
  snapshot : String
  definition : String
  region : List Nat := []
  coordinate : Coordinate := .instruction
  deriving DecidableEq, Repr

mutual
  def regionAt {Op : Type} (body : RawRegion Ty Op) : List Nat → Option (RawRegion Ty Op)
    | [] => some body
    | 0 :: path => match body with
      | .bind _ body _ => regionAt body path
      | _ => none
    | 1 :: path => match body with
      | .letOp _ _ _ _ next | .bind _ _ next => regionAt next path
      | _ => none
    | 2 :: index :: path => match body with
      | .letOp _ _ _ bodies _ => callbackAt bodies index path
      | _ => none
    | _ => none
  def callbackAt {Op : Type} (bodies : RawRegions Ty Op) (index : Nat)
      (path : List Nat) : Option (RawRegion Ty Op) :=
    match bodies, index with
    | .nil, _ => none
    | .cons _ _ body _, 0 => regionAt body path
    | .cons _ _ _ tail, index + 1 => callbackAt tail index path
end

def helperAt (program : Program) (address : Address) : Option CheckedDefinition :=
  if program.snapshot.source == address.snapshot then
    program.payload.definitions.find? (·.name == address.definition)
  else none

def protocolAt (program : Program) (address : Address) : Option CheckedProtocol :=
  if program.snapshot.source == address.snapshot then
    program.payload.protocols.find? (·.name == address.definition)
  else none

/-- A lookup key proposes a body; its checked equation and the actual law carry
all authority. In particular a digest match cannot construct this record.
The law parameter is the existing caller's equation, not a new semantics. -/
structure HelperAssociation (program : Program) (address : Address)
    (expected : CheckedDefinition) (law : Prop) : Prop where
  selected : helperAt program address = some expected
  checkedLaw : law

/-- Ordinary kernel equality suffices for association transport. -/
theorem HelperAssociation.transport {program : Program} {address : Address}
    {expected actual : CheckedDefinition} {law : Prop}
    (association : HelperAssociation program address expected law)
    (same : expected = actual) : HelperAssociation program address actual law := by
  cases same
  exact association

end ZkcTools.StructuredSource.Discovery
