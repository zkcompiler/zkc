module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Construction.RetainedTarget
public import VCVio.OracleComp.Constructions.SampleableType

@[expose] public section

/-! Structural response layouts fix recovery, private witness coordinates,
sampling and embedding into the actual retained target. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
namespace ZkcSecurity.Endpoint.Extraction
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- Scalar leaves or products, with explicit private-input coordinates. -/
inductive Layout where
  | scalar (input : Nat)
  | pair (left right : Layout)
  deriving DecidableEq, Repr

abbrev Layout.Carrier (F : Type) : Layout → Type
  | .scalar _ => F
  | .pair left right => left.Carrier F × right.Carrier F

instance Layout.sampleable (F : Type) [SampleableType F] : (layout : Layout) →
    SampleableType (layout.Carrier F)
  | .scalar _ => inferInstanceAs (SampleableType F)
  | .pair left right =>
    letI := left.sampleable F
    letI := right.sampleable F
    inferInstanceAs (SampleableType (left.Carrier F × right.Carrier F))

/-- Response difference, applied to every scalar component. -/
def Layout.recover {F : Type} [Field F] (layout : Layout) :
    F → layout.Carrier F → F → layout.Carrier F → layout.Carrier F :=
  match layout with
  | .scalar _ => fun first response₁ second response₂ => (response₁ - response₂) / (first - second)
  | .pair a b => fun first response₁ second response₂ =>
      (a.recover first response₁.1 second response₂.1, b.recover first response₁.2 second response₂.2)
termination_by structural layout

@[simp] theorem Layout.recover_scalar {F : Type} [Field F] (input : Nat) (c₁ z₁ c₂ z₂ : F) :
    (Layout.scalar input).recover c₁ z₁ c₂ z₂ = (z₁ - z₂) / (c₁ - c₂) := rfl

@[simp] theorem Layout.recover_pair {F : Type} [Field F] (a b : Layout) (c₁ c₂ : F)
    (z₁ z₂ : (a.pair b).Carrier F) :
    (a.pair b).recover c₁ z₁ c₂ z₂ = (a.recover c₁ z₁.1 c₂ z₂.1, b.recover c₁ z₁.2 c₂ z₂.2) := rfl

/-- Every independent response has one private-input coordinate. -/
def Layout.coordinates : Layout → List Nat
  | .scalar input => [input]
  | .pair left right => left.coordinates ++ right.coordinates

/-- Repeated uses of a coordinate share its assigned value. Admission rules
out assigning two independent response components to the same coordinate. -/
def Layout.read {F : Type} (layout : Layout) : layout.Carrier F → Nat → Option F :=
  match layout with
  | .scalar coordinate => fun witness input => if input = coordinate then some witness else none
  | .pair a b => fun witness input => a.read witness.1 input <|> b.read witness.2 input
termination_by structural layout

@[simp] theorem Layout.read_scalar {F : Type} (coordinate : Nat) (witness : F) (input : Nat) :
    (Layout.scalar coordinate).read witness input = (if input = coordinate then some witness else none) := rfl

@[simp] theorem Layout.read_pair {F : Type} (a b : Layout) (witness : (a.pair b).Carrier F) (input : Nat) :
    (a.pair b).read witness input = (a.read witness.1 input <|> b.read witness.2 input) := rfl

/-- Collect the retained relation's actual scalar witness inputs. Its support
proof separately enforces private producer roles and excludes output ports. -/
def witnessCoordinates {signature : ProtocolSignature} (domain : String) :
    List String → {types : List Ty} → Values (BoundarySelector signature) types → Option (List Nat)
  | [], _, .nil => some []
  | purpose :: purposes, _, .cons (ty := type) selector rest => do
      let tail ← witnessCoordinates domain purposes rest
      if purpose = "witness" then
        if type = .field domain then return selector.port.index :: tail else none
      else return tail
  | _, _, _ => none

def Layout.admitted {snapshot : Structured.Snapshot} {imported : Structured.Imported snapshot}
    {policy : Policy} {publics : List Ty} (layout : Layout)
    (target : RetainedTarget imported policy publics) (domain : String) : Bool :=
  match witnessCoordinates domain target.application.relation.declaration.purposes target.application.selectors with
  | none => false
  | some coordinates => decide layout.coordinates.Nodup &&
      coordinates.all layout.coordinates.contains && layout.coordinates.all coordinates.contains

def Layout.embed {F G : Type} {snapshot : Structured.Snapshot}
    {imported : Structured.Imported snapshot} {policy : Policy} {publics : List Ty}
    (layout : Layout) (target : RetainedTarget imported policy publics)
    (witness : layout.Carrier F) : target.Witness F G :=
  fun type selector => match type with
    | .field _ => layout.read witness selector.port.index
    | _ => none

-- Materialize these shared unfolding equations in their owning module. Lazy
-- client-local generation would give the same public equation distinct stored
-- proof providers, which the declaration-closure audit correctly rejects.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Layout.embed

end ZkcSecurity.Endpoint.Extraction
