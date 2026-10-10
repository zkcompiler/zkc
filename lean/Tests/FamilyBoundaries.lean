import Zkc.Semantics.Boundary
import Zkc.Semantics.Locality
import Zkc.Source.Family

/-! Negative controls for bounds, role knowledge, speculative publication and
construction guard order. These refute invalid generalizations of the adopted
contracts; they do not claim a native compiler currently makes those rewrites. -/

set_option autoImplicit false

namespace Tests.FamilyBoundaries

inductive Request where
  | readCount
  | tick

def reply : Request → Type
  | .readCount => Nat
  | .tick => Unit

abbrev signature : PIR.Signature := ⟨Request, reply⟩

def ticks : Nat → PIR.Proc signature Unit
  | 0 => .done ()
  | n + 1 => .call .tick (fun _ => ticks n)

theorem ticks_within (bound count : Nat) :
    PIR.Within bound (ticks count) ↔ count ≤ bound := by
  induction bound generalizing count with
  | zero => cases count <;> simp [ticks, PIR.Within]
  | succ bound ih =>
      cases count with
      | zero => simp [ticks, PIR.Within]
      | succ count => simp [ticks, PIR.Within, ih, reply]

/-- Every selected count terminates, but an unchecked received Nat has no
uniform public call bound. The initial read itself counts as one request. -/
theorem unchecked_count_unbounded (bound : Nat) :
    ¬ PIR.Within bound (PIR.Proc.call (I := signature) Request.readCount ticks) := by
  cases bound with
  | zero => exact id
  | succ bound =>
      intro allReplies
      have impossible := (ticks_within bound (bound + 1)).mp (allReplies (bound + 1))
      omega

def boundedCount (ceiling : Nat) : PIR.Proc signature Unit :=
  .call Request.readCount fun (count : Nat) =>
    if count ≤ ceiling then ticks count else .halt .reject

theorem bounded_count_within (ceiling : Nat) :
    PIR.Within (ceiling + 1) (boundedCount ceiling) := by
  change ∀ count : Nat, PIR.Within ceiling
    (if count ≤ ceiling then ticks count else .halt .reject)
  intro count
  change PIR.Within ceiling (if count ≤ ceiling then ticks count else .halt .reject)
  split
  next admitted => exact (ticks_within ceiling count).mpr admitted
  next _ => cases ceiling <;> trivial

/-- Selecting an old literal with pure administrative sequencing does not add
an observable receive or change that body's behavior. Not a grammar embedding. -/
theorem literal_selection_unchanged (count : Nat) :
    (PIR.Proc.done count).bind ticks = ticks count := rfl

/-- A role with no count information cannot select both required schedules. -/
theorem hidden_count_not_projectable :
    ¬ ∃ choose : Unit → Nat, ∀ count : Nat, choose () = count := by
  exact Zkc.Semantics.Locality.no_local_adapter (fun _ : Nat => ()) id
    0 1 rfl (by decide)

/-- Semantically inert repetition needs no count information. The required
behavior may be a denotation, rather than a distinct AST for every count. -/
def inert (count : Nat) : PIR.Proc signature Unit :=
  PIR.repeatN count PIR.Proc.done ()

theorem inert_same (count : Nat) : inert count = .done () := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [inert, PIR.repeatN, PIR.Proc.bind] using ih

def inertKnown : Zkc.Source.Family.Known (fun _ : Nat => True) (fun _ => ()) inert where
  select _ := .done ()
  realizes count _ := (inert_same count).symm

inductive AttemptEvent where
  | staged : Nat → AttemptEvent
  | commit
  | discard

/-- An append-preserving per-event observer cannot retroactively publish or
erase a previously emitted payload based on a later marker. An actual buffer
must emit the payload only when committed (or use a separately justified
stateful construction). Changing observeEvents silently is not such a proof. -/
theorem no_retroactive_projection :
    ¬ ∃ view : AttemptEvent → List Nat,
      PIR.observeEvents view [.staged 0, .discard] = [] ∧
      PIR.observeEvents view [.staged 1, .discard] = [] ∧
      PIR.observeEvents view [.staged 0, .commit] = [0] ∧
      PIR.observeEvents view [.staged 1, .commit] = [1] := by
  rintro ⟨view, zeroDiscard, oneDiscard, zeroCommit, oneCommit⟩
  have zeroEmpty : view (.staged 0) = [] := by
    simpa [PIR.observeEvents] using (List.append_eq_nil_iff.mp
      (show view (.staged 0) ++ view .discard = [] by
        simpa [PIR.observeEvents] using zeroDiscard)).1
  have oneEmpty : view (.staged 1) = [] := by
    exact (List.append_eq_nil_iff.mp
      (show view (.staged 1) ++ view .discard = [] by
        simpa [PIR.observeEvents] using oneDiscard)).1
  have left : view .commit = [0] := by
    simpa [PIR.observeEvents, zeroEmpty] using zeroCommit
  have right : view .commit = [1] := by
    simpa [PIR.observeEvents, oneEmpty] using oneCommit
  have impossible : ([0] : List Nat) = [1] := left.symm.trans right
  cases impossible

/-- Absorbing stops cannot acquire retry behavior by sequencing a suffix. -/
theorem stop_is_still_terminal {I : PIR.Signature} {A B : Type}
    (reason : PIR.Stop) (next : A → PIR.Proc I B) :
    (PIR.Proc.halt reason).bind next = .halt reason := rfl

namespace GuardOrder

abbrev effects : PIR.Signature := ⟨Unit, fun _ => Unit⟩

def emit : PIR.Handler effects Nat Nat :=
  fun _ state => ⟨.returned (), state + 1, [state]⟩

def late : PIR.Proc effects Unit := .call () (fun _ => .halt .reject)
def early : PIR.Proc effects Unit := .halt .reject

/-- Hoisting a rejecting guard can preserve the rejection answer while changing
the residual state and observation prefix. This is a model counterexample,
not a statement that the compiler currently performs this rewrite. -/
theorem same_rejection_different_execution :
    (late.run emit 0).outcome = (early.run emit 0).outcome ∧
    (late.run emit 0).state ≠ (early.run emit 0).state ∧
    (late.run emit 0).events ≠ (early.run emit 0).events := by
  decide

end GuardOrder

end Tests.FamilyBoundaries
