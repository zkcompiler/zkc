import Zkc.Source.Decoding
import Zkc.Compiler.Lowering
import Zkc.Semantics.Interpretation
import Zkc.Semantics.Boundary

/-! A Merkle-opening verifier with a retained logical path operation.

The public height indexes challenge and opening types. Opening values are
otherwise arbitrary, including inconsistent paths. Interpreting verification
expands it into ordered node requests, after the commitment and query. This is
an expressiveness and algorithm-correspondence client, not a collision-resistance,
FRI-security or hostile-byte decoding theorem.
-/

set_option autoImplicit false

namespace Tests.ProtocolGenerality.Merkle

open PIR Zkc.Source Zkc.Compiler

structure Opening (D : Type) (height : Nat) where
  leaf : D
  siblings : List D
  length : siblings.length = height

inductive Ty where
  | digest | index | opening | boolean
  deriving DecidableEq

inductive Op where
  | commitment | challenge | opening | verify
  deriving DecidableEq

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .opening => [.index]
    | .verify => [.digest, .index, .opening]
    | _ => []
  result
    | .commitment => .digest
    | .challenge => .index
    | .opening => .opening
    | .verify => .boolean
  condition := .boolean

abbrev Value (D : Type) (height : Nat) : Ty → Type
  | .digest => D
  | .index => Fin (2 ^ height)
  | .opening => Opening D height
  | .boolean => Bool

inductive Call (D : Type) (height : Nat) where
  | commitment
  | challenge
  | opening (index : Fin (2 ^ height))
  | node (left right : D)

abbrev interface (D : Type) (height : Nat) : Signature := ⟨Call D height, fun
  | .commitment | .node _ _ => D
  | .challenge => Fin (2 ^ height)
  | .opening _ => Opening D height⟩

variable {D : Type} {height : Nat}

/-- Node order follows the current low bit of the query coordinate. -/
def ordered (index : Nat) (value sibling : D) : D × D :=
  if index % 2 = 0 then (value, sibling) else (sibling, value)

def walk (index : Nat) (value : D) : List D → Proc (interface D height) D
  | [] => .done value
  | sibling :: rest =>
      let pair := ordered index value sibling
      .call (.node pair.1 pair.2) fun next => walk (index / 2) next rest

/-- The mathematical path interpretation uses an ordinary list fold. -/
def root (hash : D → D → D) (index : Nat) (leaf : D) (siblings : List D) : D :=
  (siblings.foldl (fun (state : Nat × D) sibling =>
    let pair := ordered state.1 state.2 sibling
    (state.1 / 2, hash pair.1 pair.2)) (index, leaf)).2

def requests (hash : D → D → D) (index : Nat) (value : D) : List D → List (D × D)
  | [] => []
  | sibling :: rest =>
      let pair := ordered index value sibling
      pair :: requests hash (index / 2) (hash pair.1 pair.2) rest

theorem walk_exact {S : Type} (hash : D → D → D)
    (handler : Handler (interface D height) S (D × D))
    (node : ∀ left right state,
      handler (.node left right) state = ⟨.returned (hash left right), state, [(left, right)]⟩)
    (index : Nat) (leaf : D) (siblings : List D) (state : S) :
    (walk index leaf siblings).run handler state =
      ⟨.returned (root hash index leaf siblings), state, requests hash index leaf siblings⟩ := by
  induction siblings generalizing index leaf with
  | nil => rfl
  | cons sibling rest ih =>
      simp only [walk, Proc.run, node, Execution.follow, ih, root, List.foldl_cons,
        requests, List.singleton_append]

theorem walk_bounded (index : Nat) (leaf : D) (siblings : List D) :
    Within siblings.length (walk (height := height) index leaf siblings) := by
  induction siblings generalizing index leaf with
  | nil => trivial
  | cons sibling rest ih => exact fun next => ih (index / 2) next

variable [DecidableEq D]

abbrev meaning : Interpretation language (interface D height) where
  Value := Value D height
  condition := id
  operation
    | .commitment, .nil => .call .commitment .done
    | .challenge, .nil => .call .challenge .done
    | .opening, .cons index .nil => .call (.opening index) .done
    | .verify, .cons expected (.cons index (.cons proof .nil)) =>
        (walk index.val proof.leaf proof.siblings).bind fun actual =>
          .done (decide (actual = expected))

def raw : RawProgram Ty Op :=
  .letOp .commitment []
    (.letOp .challenge []
      (.letOp .opening [0] (.letOp .verify [2, 1, 0] (.ret 0))))

def program : Program language [] .boolean :=
  (raw.elaborate (language := language) [] .boolean).toOption.get (by decide)

def reference : Proc (interface D height) Bool :=
  .call .commitment fun expected =>
    .call .challenge fun index =>
      .call (.opening index) fun proof =>
        (walk index.val proof.leaf proof.siblings).bind fun actual =>
          .done (decide (actual = expected))

theorem denotes_verifier :
    program.denote (meaning (D := D) (height := height)) Values.nil.get = reference := by
  change reference.bind .done = reference
  exact Proc.bind_done _

theorem bounded : Within (3 + height) (reference (D := D) (height := height)) := by
  rw [Nat.add_comm 3 height]
  intro expected index proof
  have bounded := Boundary.within_bind (walk (height := height) index.val proof.leaf proof.siblings)
    (fun actual => .done (decide (actual = expected)))
    height 0 (by simpa only [proof.length] using
      walk_bounded (height := height) index.val proof.leaf proof.siblings) (fun _ => trivial)
  simpa using bounded

theorem plan_execution {S E : Type} (handler : Handler (interface D height) S E) (state : S) :
    (lower program).run meaning handler Values.nil.get state = reference.run handler state := by
  rw [lower_correct, denotes_verifier]

/-- Noncommutative encoding exposes swapped path directions; no field arithmetic is used. -/
example : root (fun a b : List Nat => a ++ b) 0 [1] [[2]] = [1, 2] := rfl
example : root (fun a b : List Nat => a ++ b) 1 [1] [[2]] = [2, 1] := rfl
example : root (fun a b : List Nat => a ++ b) 0 [1] [[2]] ≠
    root (fun a b : List Nat => a ++ b) 1 [1] [[2]] := by decide

/-- A query index cannot be replaced by the same-position digest input. -/
example : ((RawProgram.letOp Op.opening [0] (.ret 0)).elaborate
    (language := language) [.digest] .opening).isOk = false := by decide

def failingNodes : Handler (interface Nat 2) Nat (Nat × Nat)
  | .commitment, state => ⟨.returned 123, state, []⟩
  | .challenge, state => ⟨.returned 0, state, []⟩
  | .opening _, state => ⟨.returned ⟨1, [2, 3], rfl⟩, state, []⟩
  | .node left right, state =>
      ⟨if state = 0 then .returned (10 * left + right) else .stopped .abort,
        state + 1, [(left, right)]⟩

/-- Failure inside the expanded logical operation retains both node requests and state. -/
example : (lower program).run meaning failingNodes Values.nil.get 0 =
    ⟨.stopped .abort, 2, [(1, 2), (12, 3)]⟩ := rfl

/-- A concrete total node interpretation; commitment and query stay independently
supplied inputs so an inconsistent path cannot repair its own expected root. -/
def pathHandler (expected : Nat) (index : Fin 4) : Handler (interface Nat 2) Nat (Nat × Nat)
  | .commitment, state => ⟨.returned expected, state, []⟩
  | .challenge, state => ⟨.returned index, state, []⟩
  | .opening _, state => ⟨.returned ⟨1, [2, 3], rfl⟩, state, []⟩
  | .node left right, state =>
      ⟨.returned (10 * left + right), state + 1, [(left, right)]⟩

example : (lower program).run meaning (pathHandler 213 1) Values.nil.get 0 =
    ⟨.returned true, 2, [(2, 1), (21, 3)]⟩ := rfl

example : (lower program).run meaning (pathHandler 214 1) Values.nil.get 0 =
    ⟨.returned false, 2, [(2, 1), (21, 3)]⟩ := rfl

/-- Reusing the same root and siblings at another coordinate fails. -/
example : (lower program).run meaning (pathHandler 213 0) Values.nil.get 0 =
    ⟨.returned false, 2, [(1, 2), (12, 3)]⟩ := rfl

end Tests.ProtocolGenerality.Merkle
