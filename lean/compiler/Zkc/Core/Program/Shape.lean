module

public import Zkc.Core.Program.Record

@[expose] public section

/-!
The kinds of events and the shape of a protocol.

A value flows between roles, or the world gives one. The shape of a protocol is its events by
key, with its loops, choices, applications, blocks, guards and attempts kept; it is computed
once, from the term, and its events, through applications, are what deployment reads.
-/

namespace Zkc.Core

/-- A value flows between roles: one role gives it and others get it. -/
inductive FlowKind where
  /-- A message. -/
  | message
  /-- The rows of a query: the opener gives them and the reader gets them. -/
  | rows
  /-- An opening. -/
  | opening
deriving DecidableEq, Repr

/-- The world gives a value to one role, and to those that hear it. -/
inductive GivenKind (V : Vocabulary) where
  /-- A coin of a law: a draw when some role hears it, a sample when nobody does. -/
  | coin (law : V.LawKey) (statics : List Static)
  /-- A request to a service. -/
  | request (service : Key)
deriving DecidableEq


/-! ## The shape of a protocol -/

/-- Who takes part in an event, and how. -/
inductive EventClass (V : Vocabulary) where
  | flow (kind : FlowKind) (giver : Role) (getters : List Role)
  | given (kind : GivenKind V) (owner : Role) (hearers : List Role)

/-- A role's part of an event, naming its peers. -/
inductive Part (V : Vocabulary) where
  | give (kind : FlowKind) (getters : List Role)
  | get (kind : FlowKind) (giver : Role)
  | own (kind : GivenKind V) (hearers : List Role)
  | hear (kind : GivenKind V) (owner : Role)
deriving DecidableEq

mutual
  /-- The events of a protocol by key, with their kinds, roles and types; loops, choices,
  applications and blocks are kept. It is computed once, from the term. -/
  inductive Shape (V : Vocabulary) where
    | nil
    | event (key : Key) (cls : EventClass V) (τ : V.Ty) (rest : Shape V)
    | choice (key : Key) (participants : Holders) (arms : Shapes V) (rest : Shape V)
    | loop (key : Key) (participants : Holders) (body : Shape V) (rest : Shape V)
    | apply (key : Key) (callee : Key) (roles : List Role) (inner : Shape V) (rest : Shape V)
    | block (key : Key) (number : Nat) (body : Shape V) (rest : Shape V)
    | guard (key : Key) (who : Holders) (why : Reason) (rest : Shape V)
    | attempt (key : Key) (owner : Holders) (body : Shape V) (rest : Shape V)
  inductive Shapes (V : Vocabulary) where
    | nil
    | cons (arm : Shape V) (rest : Shapes V)
end

/-- Whether an event has a field in the record of a run: a coin that nobody hears has
none. -/
def EventClass.recorded {V : Vocabulary} : EventClass V → Bool
  | .flow .. => true
  | .given (.coin ..) _ [] => false
  | .given (.coin ..) _ (_ :: _) => true
  | .given (.request _) _ _ => true

mutual
  /-- The record of a run: a field per event, an option per field of an arm, a collection
  per field of a loop, the callee's record for an application, the body's record for a
  block. -/
  def Shape.fields {V : Vocabulary} : Shape V → Fields V
    | .nil => .nil
    | .event key cls τ rest =>
        if cls.recorded then .cons (.key key) (.val τ) rest.fields else rest.fields
    | .choice _ _ arms rest => arms.fields.append rest.fields
    | .loop _ _ body rest => (body.fields.map .many).append rest.fields
    | .apply key _ _ inner rest => .cons (.key key) (.record inner.fields) rest.fields
    | .block key number body rest => .cons (.step key number) (.record body.fields) rest.fields
    | .guard _ _ _ rest => rest.fields
    | .attempt _ _ body rest => body.fields.append rest.fields
  def Shapes.fields {V : Vocabulary} : Shapes V → Fields V
    | .nil => .nil
    | .cons arm rest => (arm.fields.map .opt).append rest.fields
end

/-- An event of a shape: its site, its class and its type. -/
structure ShapeEvent (V : Vocabulary) where
  site : Site
  cls : EventClass V
  τ : V.Ty

/-- The class of an event, with every role that takes part renamed. -/
def EventClass.rename {V : Vocabulary} (ρ : Role → Role) : EventClass V → EventClass V
  | .flow kind giver getters => .flow kind (ρ giver) (getters.map ρ)
  | .given kind owner hearers => .given kind (ρ owner) (hearers.map ρ)

mutual
  /-- The events of a shape in order, through its applications: each with its site (the keys
  of the applications that reach it, then its key), its class with the roles renamed by
  `rename` (the roles of a callee by the application's roles), and its type. Who proves, the
  heard coins, what deployment decides and the clauses that it makes read this list. -/
  def Shape.events {V : Vocabulary} (through : List Key) (rename : Role → Role) :
      Shape V → List (ShapeEvent V)
    | .nil => []
    | .event key cls τ rest =>
        ⟨⟨through, key⟩, cls.rename rename, τ⟩ :: Shape.events through rename rest
    | .choice _ _ arms rest => Shapes.events through rename arms ++ Shape.events through rename rest
    | .loop _ _ body rest => Shape.events through rename body ++ Shape.events through rename rest
    | .apply key _ roles inner rest =>
        Shape.events (through ++ [key]) (fun j => rename (roles.getD j j)) inner ++
          Shape.events through rename rest
    | .block _ _ body rest => Shape.events through rename body ++ Shape.events through rename rest
    | .guard _ _ _ rest => Shape.events through rename rest
    | .attempt _ _ body rest => Shape.events through rename body ++ Shape.events through rename rest
  def Shapes.events {V : Vocabulary} (through : List Key) (rename : Role → Role) :
      Shapes V → List (ShapeEvent V)
    | .nil => []
    | .cons arm rest => Shape.events through rename arm ++ Shapes.events through rename rest
end

end Zkc.Core
