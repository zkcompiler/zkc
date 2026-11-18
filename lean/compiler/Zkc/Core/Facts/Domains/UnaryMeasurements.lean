module

public import Zkc.Core.Facts.Domains.Product
public import Zkc.Core.Facts.Body.ValueLaws

@[expose] public section
namespace Zkc.Core.BodyAnalysis.UnaryMeasurements

/-- A numeric observation of one operand. Different written instructions may measure
the same operand, even when their result types carry different placement information. -/
structure State where
  samples : List (Ident × Ident) := []
  exacts : List (Ident × Nat) := []

def learn (asks : Asks) (s : State) : State :=
  let fresh := s.samples.filterMap fun (result, subject) => (asks.exact result).map (subject, ·)
  { s with exacts := (fresh.filter fun p => !s.exacts.contains p) ++ s.exacts }

def transfer {Raw : Type} (measures : Raw → Bool) (s : State) (e : Entry Raw) : State :=
  match e.form with
  | .app op [subject] =>
    if measures op && e.count > 0 then { s with samples := (.val e.lo, subject) :: s.samples } else s
  | _ => s

def exact (s : State) (id : Ident) : Option Nat := do
  let subject ← s.samples.lookup id
  s.exacts.lookup subject

def domain {T Raw : Type} (measures : Raw → Bool) : Domain T Raw where
  State := State
  init := {}
  dead _ := false
  leaves s _ := s
  transfer _ _ s e := transfer measures s e
  observe _ _ s _ _ := s
  assume asks _ s _ _ := learn asks s
  truth _ _ _ _ := none
  after _ s _ _ := s
  enter _ _ s _ := s
  afterLoop _ _ _ s _ _ _ _ := s
  answers s := { truth := fun _ => none, exact := exact s, upper := exact s }

end Zkc.Core.BodyAnalysis.UnaryMeasurements
