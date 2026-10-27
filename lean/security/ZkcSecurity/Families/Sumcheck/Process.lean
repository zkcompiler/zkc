module

public import ZkcSecurity.Families.Sumcheck.Round
public import Zkc.Semantics.Boundary
public import Zkc.Transcript.Interface

@[expose] public section

/-! A reusable remaining-round component over the existing open Process. The
receive stage can contain multiple typed receives and actual decoding. Context,
sites, private frames and prefixes belong to the caller's implementation state.
The reference is a separate mathematical interpretation, never an evaluator. -/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck

variable {F : Type} [Field F] {I : PIR.Signature} {Context : Type}
  {State : Nat → Type} {message : Message F}

structure Program (I : PIR.Signature) (Context : Type) (State : Nat → Type)
    (message : Message F) where
  claim : {n : Nat} → State n → F
  receive : {n : Nat} → Context → State (n + 1) → PIR.Process I (Option message.Carrier)
  query : {n : Nat} → Context → State (n + 1) → message.Carrier → I.Op
  challenge : {n : Nat} → (context : Context) → (state : State (n + 1)) →
    (m : message.Carrier) → I.Reply (query context state m) → F
  /-- Actual challenge delivery, including typed sends and their possible stops.
  Every returned reply continues to the same mathematical advance. -/
  deliver : {n : Nat} → Context → State (n + 1) → message.Carrier → F → PIR.Process I PUnit :=
    fun _ _ _ _ => .done ()
  advance : {n : Nat} → Context → State (n + 1) → message.Carrier → F → State n

namespace Program

variable (program : Program I Context State message)

/-- Zero rounds returns the entire state. A partial call retains its residual
dimension. Malformed messages refuse; failed boundaries reject before querying. -/
noncomputable def remaining [DecidableEq F] {n : Nat} :
    (count : Nat) → Context → State (n + count) → PIR.Process I (State n)
  | 0, _, state => .done state
  | count + 1, context, state =>
      (program.receive context state).bind fun decoded =>
        match decoded with
        | none => .halt .refused
        | some m =>
            if message.boundary m = program.claim state then
              .call (program.query context state m) fun reply =>
                (program.deliver context state m (program.challenge context state m reply)).bind fun _ =>
                  remaining count context
                    (program.advance context state m (program.challenge context state m reply))
            else .halt .reject

theorem remaining_zero [DecidableEq F] {n : Nat} (context : Context) (state : State n) :
    program.remaining 0 context state = .done state := rfl

/-- A caller invariant is preserved along every typed-reply path that returns.
No honest-message or sampling premise is needed for a private frame law. -/
theorem returns [DecidableEq F] (interaction : PIR.Interaction I)
    (invariant : {k : Nat} → State k → Prop)
    (preserved : ∀ {k} (context : Context) (s : State (k + 1)), invariant s →
      ∀ m r, invariant (program.advance context s m r))
    {n : Nat} (count : Nat) (context : Context) (s : State (n + count))
    (phase : interaction.Phase) (initial : invariant s) :
    PIR.Boundary.Returns interaction (fun result _ => invariant result)
      (program.remaining count context s) phase := by
  induction count generalizing phase with
  | zero => exact initial
  | succ count ih =>
      unfold remaining
      have receiveReturns : PIR.Boundary.Returns interaction (fun _ _ => True)
          (program.receive context s) phase := PIR.Boundary.returns_true interaction _ _
      apply PIR.Boundary.returns_bind interaction _ _ (fun _ _ => True) _ phase receiveReturns
      intro decoded reached _
      cases decoded with
      | none => trivial
      | some m =>
          dsimp only
          split
          · intro reply
            apply PIR.Boundary.returns_bind interaction _ _ (fun _ _ => True) _ _
            · exact PIR.Boundary.returns_true interaction _ _
            · intro _ _ _
              exact ih _ _ (preserved context s initial m _)
          · trivial

end Program

/-- Representation holds at every implementation state, including false scalar
claims. Admissibility is supplied separately by caller shape, never target truth. -/
structure Representation (program : Program I Context State message) (reference : Reference F) where
  state : {n : Nat} → State n → reference.State n
  advance : ∀ {n} (context : Context) (s : State (n + 1)) m r,
    state (program.advance context s m r) = reference.restrict (state s) r
  claim : ∀ {n} (context : Context) (s : State (n + 1)) m r,
    program.claim (program.advance context s m r) = message.evaluate m r

namespace Representation

variable {program : Program I Context State message} {reference : Reference F}
  (representation : Representation program reference)

def Allowed {n : Nat} (s : State n) : Prop := reference.admissible (representation.state s)
def Yes {n : Nat} (s : State n) : Prop :=
  representation.Allowed s ∧ program.claim s = reference.total (representation.state s)
def No {n : Nat} (s : State n) : Prop :=
  representation.Allowed s ∧ program.claim s ≠ reference.total (representation.state s)

theorem advance_allowed {degree n : Nat} (laws : ReferenceLaws reference degree)
    (context : Context) (s : State (n + 1)) (allowed : representation.Allowed s) m r :
    representation.Allowed (program.advance context s m r) := by
  unfold Allowed
  rw [representation.advance]
  exact laws.restriction_closed _ r allowed

end Representation
end ZkcSecurity.Families.Sumcheck
