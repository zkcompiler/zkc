module

public import Zkc.Source.Structured.Operations
public import Zkc.Source.Structure

@[expose] public section

/-! Selection of actual local counted-loop callbacks. This is a traversal of
typed syntax, not an evaluator. Captures and all callback returns remain in the
selected Region. Conditional loops have a different contract and are not
silently treated as counted loops. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.HelperCallbacks
open Zkc.Source

inductive Edge where
  | next
  | bound
  | region (index : Nat)
  deriving DecidableEq, Repr

abbrev Path := List Edge

/-- The schema comes from the actual loop operation, including the boundary
between state and captures even when their types coincide. -/
structure Callback where
  state : List Ty
  captures : List Ty
  body : Region dialect (.index :: (state ++ captures)) (state ++ captures)

abbrev Callback.inputs (callback : Callback) := .index :: (callback.state ++ callback.captures)
abbrev Callback.outputs (callback : Callback) := callback.state ++ callback.captures

structure Located where
  path : Path
  callback : Callback

def atOperation : (op : Op) → Regions dialect op.regions → List Located
  | .loop state captures, .cons body .nil => [⟨[], ⟨state, captures, body⟩⟩]
  | _, _ => []

def beneath (edge : Edge) (callbacks : List Located) : List Located :=
  callbacks.map fun found => { found with path := edge :: found.path }

mutual
  /-- All occurrences, including dormant branches and nested loops. Neither
  identical bodies nor identical schemas collapse distinct occurrences. -/
  def loops {inputs outputs : List Ty} : Region dialect inputs outputs → List Located
    | .ret _ | .stop _ => []
    | .letOp op _ bodies next =>
      atOperation op bodies ++ regions 0 bodies ++ beneath .next (loops next)
    | .bind body next => beneath .bound (loops body) ++ beneath .next (loops next)

  def regions {signatures : List (List Ty × List Ty)} (index : Nat) :
      Regions dialect signatures → List Located
    | .nil => []
    | .cons body tail => beneath (.region index) (loops body) ++ regions (index + 1) tail
end

mutual
  /-- Follow only the checked occurrence path. Keeping extraction separate from
  uniqueness checking avoids re-enumerating the source when a consumer unfolds
  the selected callback. Both functions inspect the same typed Region. -/
  def atPath {inputs outputs : List Ty} :
      Region dialect inputs outputs → Path → Option Callback
    | .letOp op _ bodies next, path => match path with
      | [] => ((atOperation op bodies).head?).map (·.callback)
      | .next :: rest => atPath next rest
      | .region index :: rest => regionAtPath bodies index rest
      | _ => none
    | .bind body next, path => match path with
      | .next :: rest => atPath next rest
      | .bound :: rest => atPath body rest
      | _ => none
    | .ret _, _ | .stop _, _ => none

  def regionAtPath {signatures : List (List Ty × List Ty)} :
      Regions dialect signatures → Nat → Path → Option Callback
    | .cons body _, 0, path => atPath body path
    | .cons _ tail, index + 1, path => regionAtPath tail index path
    | .nil, _, _ => none
end

inductive Failure where
  | missing
  | ambiguous
  deriving DecidableEq, Repr

/-- No first-match fallback. An explicit path is checked against the same
complete traversal; names and ABI hints never assert source association. -/
def select {inputs outputs : List Ty} (source : Region dialect inputs outputs)
    (path : Option Path := none) : Except Failure Located :=
  let candidates := match path with
    | none => loops source
    | some path => (loops source).filter fun found => found.path == path
  match candidates with
  | [found] => .ok found
  | [] => .error .missing
  | _ => .error .ambiguous

/-- Ordinary kernel-checkable association to the complete actual source.
This does not assert reachability or that a callback returns successfully. -/
def Selected {inputs outputs : List Ty} (source : Region dialect inputs outputs)
    (path : Option Path) (found : Located) : Prop := select source path = .ok found

end Zkc.Source.Structured.HelperCallbacks
