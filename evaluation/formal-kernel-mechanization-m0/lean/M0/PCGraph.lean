import M0.Encode

/-!
# `PCClass`, `Join`, `Publish`, the Kahn order, and the class fold

`docs-next/pir/interactive-core.md` Section 11 fixes the four-element lattice
`PCClass = StaticPublic | PublicHistory | VerifierPrivate | Invalid`, the
functions `Join` and `Publish`, the deterministic topological order ("Kahn's
algorithm, selecting at each step the available node with the least
`M(PCNodeBody(node))`"), and the per-node transfer rules. Appendix A of the
same page fixes `PCNodeBody`.

This file transcribes the lattice, the order, and the transfer rules as they
apply to an already constructed graph. It does not construct `PCGraph(core)`
from a Core: node and edge tables and the per-node transfer kinds come from
`evaluation/formal-source-integrated-graph-f0v2b2d1/model.py` through the
package's `export_vectors.py`. Porting the edge construction is the stated
next increment.
-/

namespace M0

/-- `PCClass` (Section 11), in the order the page lists the cases. -/
inductive PCClass where
  | staticPublic
  | publicHistory
  | verifierPrivate
  | invalid
  deriving DecidableEq, Repr, Inhabited

/-- `Join(xs)`, written exactly as Section 11 writes it. -/
def Join (xs : List PCClass) : PCClass :=
  if xs.contains .invalid then .invalid
  else if xs.contains .verifierPrivate then .verifierPrivate
  else if xs.contains .publicHistory then .publicHistory
  else .staticPublic

/-- `Publish(x)` (Section 11). -/
def Publish : PCClass → PCClass
  | .staticPublic => .publicHistory
  | .publicHistory => .publicHistory
  | .verifierPrivate => .verifierPrivate
  | .invalid => .invalid

/-- The binary join induced by `Join`. -/
def PCClass.join (a b : PCClass) : PCClass := Join [a, b]

/-! ## `PCNodeBody` (Appendix A) -/

/-- `PCNodeBody` for a node given by its tag and reference arguments. Tags
`8`, `12`, and `13` carry two ordinals in a two-field record; the other eleven
tags carry one ordinal. -/
def pcNodeBody (tag : Nat) (args : List Nat) : Option Datum :=
  match args with
  | [a] =>
    if tag ≤ 7 || (9 ≤ tag && tag ≤ 11) then some (.variant tag (.nat a)) else none
  | [a, b] =>
    if tag = 8 || tag = 12 || tag = 13 then
      some (.variant tag (.record [(0, .nat a), (1, .nat b)]))
    else none
  | _ => none

/-- Lexicographic comparison of two octet strings, as byte strings compare. -/
def lexLt : List Octet → List Octet → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else lexLt as bs

/-! ## The deterministic Kahn order -/

/-- The least-key element of a nonempty list of node indices. -/
def leastByKey (key : Nat → List Octet) : List Nat → Option Nat
  | [] => none
  | v :: vs =>
    match leastByKey key vs with
    | none => some v
    | some w => if lexLt (key w) (key v) then some w else some v

/-- Nodes whose predecessors have all been emitted and which are not yet
emitted themselves. -/
def available (n : Nat) (preds : Nat → List Nat) (emitted : List Nat) : List Nat :=
  (List.range n).filter fun v =>
    !emitted.contains v && (preds v).all fun p => emitted.contains p

/-- Kahn's algorithm with the Section 11 tie-break: at each step, emit the
available node with the least canonical body. Refuses when the nodes cannot
be exhausted (a cycle). -/
def kahnOrder (n : Nat) (key : Nat → List Octet) (preds : Nat → List Nat) :
    Option (List Nat) :=
  go n []
where
  go : Nat → List Nat → Option (List Nat)
    | 0, emitted => if emitted.length = n then some emitted.reverse else none
    | steps + 1, emitted =>
      match leastByKey key (available n preds emitted) with
      | none => none
      | some v => go steps (v :: emitted)

/-! ## Transfer kinds and the class fold -/

/-- The per-node transfer rules of Section 11, as the D1 typed model applies
them. A `constant` node has a fixed class (public inputs and constants are
`StaticPublic`; Verifier-private inputs are `VerifierPrivate`; a Verifier-only
Query or Answer is `VerifierPrivate`; a nondeterministic module output is
`Invalid`). `joinIncoming` is `Join` of the exact incoming edges.
`publishJoinIncoming` is `Publish` of that join (a module Prover publication).
`publishOf` is `Publish(activity)` for a named activity node. `joinOf` joins a
named list of nodes that is not the incoming edge set (a public Query joins
its activity and index producer; a deterministic Verifier message joins its
activity and inputs). `challenge` is the specialised Challenge transfer. -/
inductive Transfer where
  | constant (c : PCClass)
  | joinIncoming
  | publishJoinIncoming
  | publishOf (node : Nat)
  | joinOf (nodes : List Nat)
  | challenge (activity : Nat) (conditions : List Nat) (priors : List Nat)
  deriving Repr

/-- The Challenge transfer as the D1 typed model reads Section 11: an
`Invalid` dependency anywhere wins, then a `VerifierPrivate` dependency
anywhere, then a non-static condition or non-history joint member makes the
Challenge `Invalid`, and otherwise a public activity yields `PublicHistory`. -/
def challengeClass (activity : PCClass) (conditions priors : List PCClass) : PCClass :=
  let dependencies := activity :: (conditions ++ priors)
  if dependencies.contains .invalid then .invalid
  else if dependencies.contains .verifierPrivate then .verifierPrivate
  else if conditions.any (· != .staticPublic) || priors.any (· != .publicHistory) then .invalid
  else if activity = .staticPublic || activity = .publicHistory then .publicHistory
  else .invalid

/-- The other reading of "by the first failed dependency": walk the
dependencies in declaration order (activity, then conditions, then joint
members) and let the first failing one decide. The two readings differ only
when an earlier dependency fails as `VerifierPrivate` while a later one is
`Invalid`; the runner reports whether the exported carriers exercise that
difference. -/
def challengeClassPositional (activity : PCClass) (conditions priors : List PCClass) :
    PCClass :=
  if activity = .verifierPrivate || activity = .invalid then activity
  else
    match conditions.find? (· != .staticPublic) with
    | some .verifierPrivate => .verifierPrivate
    | some _ => .invalid
    | none =>
      match priors.find? (· != .publicHistory) with
      | some .verifierPrivate => .verifierPrivate
      | some _ => .invalid
      | none => .publicHistory

/-- Class assignment in one topological order. Every lookup must hit an
already assigned node; otherwise the fold refuses. -/
def foldClasses (n : Nat) (order : List Nat) (preds : Nat → List Nat)
    (transfer : Nat → Transfer) : Option (Array PCClass) :=
  go order (Array.replicate n none)
where
  lookup (assigned : Array (Option PCClass)) (v : Nat) : Option PCClass :=
    match assigned[v]? with
    | some (some c) => some c
    | _ => none
  lookupAll (assigned : Array (Option PCClass)) : List Nat → Option (List PCClass)
    | [] => some []
    | v :: vs => do
      let c ← lookup assigned v
      let cs ← lookupAll assigned vs
      pure (c :: cs)
  step (assigned : Array (Option PCClass)) (v : Nat) : Option PCClass :=
    match transfer v with
    | .constant c => some c
    | .joinIncoming => (lookupAll assigned (preds v)).map Join
    | .publishJoinIncoming => (lookupAll assigned (preds v)).map (Publish ∘ Join)
    | .publishOf node => (lookup assigned node).map Publish
    | .joinOf nodes => (lookupAll assigned nodes).map Join
    | .challenge activity conditions priors => do
      let a ← lookup assigned activity
      let cs ← lookupAll assigned conditions
      let ps ← lookupAll assigned priors
      pure (challengeClass a cs ps)
  go : List Nat → Array (Option PCClass) → Option (Array PCClass)
    | [], assigned =>
      if assigned.all (·.isSome) then some (assigned.map fun c => c.getD .invalid) else none
    | v :: rest, assigned =>
      match step assigned v with
      | none => none
      | some c => if v < assigned.size then go rest (assigned.set! v (some c)) else none

/-- For every Challenge node, whether the two readings of "first failed
dependency" agree on the assigned classes. -/
def challengeReadingsAgree (n : Nat) (transfer : Nat → Transfer) (classes : Array PCClass) : Bool :=
  (List.range n).all fun v =>
    match transfer v with
    | .challenge activity conditions priors =>
      let cls := fun w => classes.getD w .invalid
      challengeClass (cls activity) (conditions.map cls) (priors.map cls)
        == challengeClassPositional (cls activity) (conditions.map cls) (priors.map cls)
    | _ => true

end M0
