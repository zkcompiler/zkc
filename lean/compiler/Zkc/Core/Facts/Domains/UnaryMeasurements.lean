module

public import Zkc.Core.Facts.Domains.Product
public import Zkc.Core.Facts.Body.ValueLaws

@[expose] public section
namespace Zkc.Core.BodyAnalysis.UnaryMeasurements

/-- Each role keeps its own subject identities. A measurement of a subject has one
numeric representative across the holder annotations on its different instructions. -/
structure State where
  subjects : NatMap Ident := .leaf
  measurements : NatMap Ident := .leaf
  numbers : NatMap Ident := .leaf

def representative (links : NatMap Ident) (id : Ident) : Ident :=
  (links.find id.key).getD id

def link (links : NatMap Ident) (id origin : Ident) : NatMap Ident :=
  if id == origin || (links.find id.key).isSome then links else links.insert id.key origin

def observe (s : State) (source result : Ident) : State :=
  { s with subjects := link s.subjects result (representative s.subjects source),
           numbers := link s.numbers result (representative s.numbers source) }

def record (s : State) (result subject : Ident) : State :=
  let origin := representative s.subjects subject
  match s.measurements.find origin.key with
  | none => { s with measurements := s.measurements.insert origin.key result }
  | some first => { s with numbers := link s.numbers result first }

def transfer {Raw : Type} (measures : Raw → Bool) (s : State) (e : Entry Raw) : State :=
  match e.form with
  | .app op [subject] =>
    if measures op && e.count > 0 then record s (.val e.lo) subject else s
  | _ => s

def domain {T Raw : Type} (measures : Raw → Bool) : Domain T Raw where
  State := State
  init := {}
  dead _ := false
  leaves s _ := s
  transfer _ _ s e := transfer measures s e
  observe _ _ := observe
  assume _ _ s _ _ := s
  truth _ _ _ _ := none
  after _ s _ _ := s
  enter _ _ s _ := s
  afterLoop _ _ _ s _ _ _ _ := s
  answers s := {Asks.nobody with numberSource := fun id => s.numbers.find id.key}

end Zkc.Core.BodyAnalysis.UnaryMeasurements
