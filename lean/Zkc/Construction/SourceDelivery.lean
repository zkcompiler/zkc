module

public import Zkc.Construction.SourceOccurrences

@[expose] public section

/-! Source-owned challenge delivery and occurrence discovery.

Discovery proposes finite paths through the admitted source. The existing
source-occurrence checker validates every emitted path independently. Delivery
admission follows SSA def-use in the original block: only an unchanged draw
result, possibly restricted in visibility, can be delivered. A same-typed or
equal-valued calculation is not that result. These are structural facts; the
source-to-construction theorem still has to relate actual execution.

This construction supports synchronous, single delivery. Markers survive only
visibility restrictions between a draw and its exchange. In particular another
message, draw, call or guard cannot move the producer's query past the original
draw. More general schedules require a construction that retains draw-time
history and caches the one sampled value across all its deliveries.
-/
set_option autoImplicit false
namespace Zkc.Construction.SourceDelivery
open Zkc.Source

/-- Candidate discovery is deliberately bounded. A missed candidate cannot
grant authority: clients refuse absent or ambiguous associations. -/
def candidates (snapshot : Structured.Snapshot) (context : Context) :
    Nat → List Step → SourceOccurrences.Frame → List Template
  | 0, _, _ => []
  | fuel + 1, steps, frame =>
      frame.body.topLevelInstructions.flatMap fun instruction =>
        match instruction with
        | .instruction descriptor _ _ _ site =>
            let leaf := match SourceOccurrences.event context frame site with
              | some event => [⟨context.entry, steps, event⟩]
              | none => []
            let kind := match descriptor with
              | .protocolApply .. => some "apply"
              | .protocolRepeat .. => some "repeat"
              | _ => none
            match kind with
            | none => leaf
            | some kind =>
                let step : Step := ⟨kind, frame.definition.name, site⟩
                match SourceOccurrences.descend snapshot frame step with
                | none => leaf
                | some child => leaf ++ candidates snapshot context fuel (steps ++ [step]) child

def discoveryFuel (snapshot : Structured.Snapshot) : Nat :=
  1 + snapshot.definitions.foldl (fun size definition =>
    match definition with
    | .function definition => size + 1 + definition.body.storedInstructions.length
    | _ => size) 0

/-- Exact source validation, not discovery, authorizes each candidate. -/
def templates (snapshot : Structured.Snapshot) (context : Context) : List Template :=
  match SourceOccurrences.root snapshot context with
  | none => []
  | some root =>
      (candidates snapshot context (discoveryFuel snapshot) [] root).filter
        (SourceOccurrences.valid snapshot context)

theorem templates_valid {snapshot : Structured.Snapshot} {context : Context} {template : Template}
    (member : template ∈ templates snapshot context) :
    SourceOccurrences.expected snapshot context template = some template.event := by
  unfold templates at member
  split at member
  · cases member
  · exact (SourceOccurrences.valid_iff _ _ _).mp (List.mem_filter.mp member).2

/-- Markers record identity of the draw result, not algebraic dependence. -/
abbrev Origins := List (Option String)

def resultOrigins (descriptor : Structured.Descriptor) (site : String)
    (arguments : Origins) (types : List Structured.Ty) : Origins :=
  match descriptor, arguments, types with
  | .draw _ field, _, [.field result] =>
      if field = result then [some site] else [none]
  | .restrict _, [origin], [_] => [origin]
  | _, _, _ => types.map fun _ => none

/-- Only a visibility restriction is transparent to this construction's
draw/delivery window. Refusal is conservative, including pure calculations. -/
def remainingOrigins (descriptor : Structured.Descriptor) (origins : Origins) : Origins :=
  match descriptor with
  | .restrict _ => origins
  | _ => origins.map fun _ => none

/-- The source export prepends every operation's results to its SSA context. -/
def atDelivery (site : String) : List Structured.Instruction → Origins → Option String
  | [], _ => none
  | .instruction descriptor operands types _ ownSite :: rest, origins => do
      let arguments ← operands.mapM (origins[·]?)
      if ownSite = site then
        match descriptor, arguments with
        | .exchange .., [origin] => origin
        | _, _ => none
      else atDelivery site rest (resultOrigins descriptor ownSite arguments types ++
        remainingOrigins descriptor origins)

/-- Current admission supports a synchronous draw and its first delivery in one original region.
Across-call/loop-carried delivery needs its own compositional def-use rule; it
does not fall back to site spelling, field equality or an artifact assertion. -/
def checked (snapshot : Structured.Snapshot) (context : Context)
    (query message : Template) : Bool := Id.run do
  if !SourceOccurrences.valid snapshot context query ||
      !SourceOccurrences.valid snapshot context message || query.steps != message.steps then return false
  let ["query", _, querySite, _, _, "draw", queryOwner] := query.event | return false
  let ["message", _, messageSite, _, sender, receiver] := message.event | return false
  if queryOwner != context.role context.validator || sender != queryOwner ||
      receiver != context.role context.producer then return false
  let some root := SourceOccurrences.root snapshot context | return false
  let some frame := SourceOccurrences.follow snapshot query.steps root | return false
  return atDelivery messageSite frame.body.topLevelInstructions
    (frame.ports.map fun _ => none) == some querySite

/-- A source policy edge is accepted only for a unique original draw/delivery
pair. Duplicate source associations do not resolve by list order. -/
def resolve (snapshot : Structured.Snapshot) (context : Context)
    (querySite messageSite : String) : Option (Template × Template) :=
  let all := templates snapshot context
  let pairs := all.flatMap fun query => all.filterMap fun message =>
    if query.querySite? == some querySite && message.messageSite? == some messageSite &&
        checked snapshot context query message then some (query, message) else none
  match pairs with
  | [pair] => some pair
  | _ => none

theorem resolved_checked {snapshot : Structured.Snapshot} {context : Context}
    {querySite messageSite : String} {query message : Template}
    (found : resolve snapshot context querySite messageSite = some (query, message)) :
    query ∈ templates snapshot context ∧ message ∈ templates snapshot context ∧
      query.querySite? = some querySite ∧ message.messageSite? = some messageSite ∧
      checked snapshot context query message = true := by
  unfold resolve at found
  dsimp only at found
  split at found
  · rename_i pair same
    have pairEq := Option.some.inj found
    subst pair
    have member : (query, message) ∈ (templates snapshot context).flatMap (fun query =>
        (templates snapshot context).filterMap fun message =>
          if query.querySite? == some querySite && message.messageSite? == some messageSite &&
              checked snapshot context query message then some (query, message) else none) := by
      rw [same]
      exact List.mem_singleton_self _
    obtain ⟨left, leftMember, pairMember⟩ := List.mem_flatMap.mp member
    obtain ⟨right, rightMember, selected⟩ := List.mem_filterMap.mp pairMember
    split at selected
    · rename_i accepted
      cases Option.some.inj selected
      simp only [Bool.and_eq_true, beq_iff_eq] at accepted
      exact ⟨leftMember, rightMember, accepted.1.1, accepted.1.2, accepted.2⟩
    · cases selected
  · cases found

end Zkc.Construction.SourceDelivery
