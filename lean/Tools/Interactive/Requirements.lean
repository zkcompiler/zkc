import Zkc.Source.Requirements
import Tools.Interactive.Syntax

/-! Bounded requirement search for portable source formation. Search is merely
a producer: every inserted fact passes the proof-producing kernel checker.
Failure to find a proof refuses formation; it does not refute the requirement. -/

set_option autoImplicit false

namespace Tools.Interactive.Requirements
open Zkc.Source.Requirements

def rules : List Implication :=
  [⟨"PairingField", "Field"⟩, ⟨"TwoAdicField", "Field"⟩, ⟨"PrimeField", "Field"⟩, ⟨"ExtensionField", "Field"⟩, ⟨"Field", "CommRing"⟩,
   ⟨"FieldTranscript", "Transcript"⟩]

structure Closure (assumptions : List Predicate) where
  facts : Array (Fact assumptions rules) := #[]
  index : Std.HashMap Predicate Nat := {}

def Closure.find? {assumptions : List Predicate} (closure : Closure assumptions)
    (predicate : Predicate) : Option Nat := do
  let index ← closure.index[predicate]?
  let fact ← closure.facts[index]?
  if fact.val == predicate then some index else none

def Closure.add {assumptions : List Predicate} (closure : Closure assumptions)
    (step : Step) : Result (Closure assumptions) := do
  if (closure.find? step.conclusion).isSome then return closure
  ensure (closure.facts.size < 32768) "requirement-fact-limit"
  let some fact := checkStep assumptions rules closure.facts step
    | throw "requirement-search-step"
  return ⟨closure.facts.push fact, closure.index.insert step.conclusion closure.facts.size⟩

private def termsOf : Predicate → List Term
  | .equal a b => [a, b]
  | .relation _ arguments => arguments

private def ancestors : Term → List Term
  | .root name => [.root name]
  | .project base member => .project base member :: ancestors base
  | .apply head arguments => .apply head arguments :: arguments.flatMap ancestors

/-- Finite congruence closure over source terms. Projections cannot introduce
unbounded new terms; each projection is present in a declaration or body need. -/
def close (assumptions : List Predicate) (needs : List Predicate) : Result (Closure assumptions) := do
  let terms := ((assumptions ++ needs).flatMap termsOf |>.flatMap ancestors).dedup
  ensure (terms.length ≤ 128 && assumptions.length ≤ 4096) "requirement-term-limit"
  let mut closure : Closure assumptions := {}
  for (p, index) in assumptions.zipIdx do
    closure ← closure.add ⟨p, .assumption index⟩
  for term in terms do
    closure ← closure.add ⟨.equal term term, .reflexivity⟩
  -- Each productive outer round merges an equivalence class or adds a unary
  -- implication. An explicit finite bound also makes hostile input terminate.
  for _ in [:terms.length + rules.length + 1] do
    let before := closure.facts.size
    for (fact, index) in closure.facts.toList.zipIdx do
      match fact.val with
      | .equal a b => closure ← closure.add ⟨.equal b a, .symmetry index⟩
      | .relation name [term] =>
          for (rule, declaration) in rules.zipIdx do
            if rule.premise == name then
              closure ← closure.add ⟨.relation rule.conclusion [term], .implication index declaration⟩
      | _ => pure ()
    for middle in terms do
      for left in terms do
        if let some first := closure.find? (.equal left middle) then
          for right in terms do
            if let some second := closure.find? (.equal middle right) then
              closure ← closure.add ⟨.equal left right, .transitivity first second⟩
    for left in terms do
      for right in terms do
        if let .project a member := left then
          if let .project b other := right then
            if member == other then
              if let some index := closure.find? (.equal a b) then
                closure ← closure.add ⟨.equal left right, .projection index⟩
        if let .apply head arguments := left then
          if let .apply other children := right then
            if head == other && arguments.length == children.length then
              let pairs := (arguments.zip children).map fun (a, b) => closure.find? (.equal a b)
              if pairs.all Option.isSome then
                closure ← closure.add ⟨.equal left right, .application (pairs.filterMap id)⟩
    if closure.facts.size == before then break
  return closure

/-- Query ordered relations by congruence. This never weakens a binary relation
to a unary capability and never assumes the converse of an installed rule. -/
def Closure.prove {assumptions : List Predicate} (closure : Closure assumptions)
    (predicate : Predicate) : Result (Closure assumptions) := do
  if (closure.find? predicate).isSome then return closure
  if let .relation name arguments := predicate then
    for (fact, index) in closure.facts.toList.zipIdx do
      if let .relation original sourceArguments := fact.val then
        if name == original && arguments.length == sourceArguments.length then
          let pairs := (sourceArguments.zip arguments).map fun (a, b) => closure.find? (.equal a b)
          if pairs.all Option.isSome then
            return ← closure.add ⟨predicate, .transport index (pairs.filterMap id)⟩
  throw "generic-requirement-not-provided"

def check (assumptions needs : List Predicate) : Result (Closure assumptions) := do
  let initial ← close assumptions needs
  needs.foldlM Closure.prove initial

end Tools.Interactive.Requirements
