module

public import ZkcSecurity.Realizations.Gkr.Circuit
public import ZkcSecurity.Families.Sumcheck.Contract
public import ZkcExamples.Structured.GkrVerifierProcess

public section
noncomputable section

/-! The actual common-action GKR rounds instantiate the existing Sumcheck
family. The reference is ghost state. The projection equation keeps every
receive, check, challenge, delivery and stop of the source presentation.
-/

namespace ZkcSecurity.Realizations.Gkr.Rounds
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Construction
open Zkc.Source.Structured
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Examples.Components
open ZkcExamples.Structured OracleComp OracleSpec

variable {F G : Type} [Field F] [DecidableEq F]

structure State (F : Type) (n : Nat) where
  reference : GkrRoundsReference.State F n
  point : List F
  claim : F

@[expose] def advance {n : Nat} (state : State F (n + 1)) (m : F × F × F) (r : F) : State F n :=
  ⟨GkrRoundsReference.restrict state.reference r, state.point ++ [r],
    (Message.coefficientTriples F).evaluate m r⟩

@[expose] def receive (ctx : ProtocolContext) : PIR.Process (Actions F G) (Option (F × F × F)) :=
  .call (.receive GkrVerifier.scalar (GkrVerifier.roundSite ctx "0") (ctx.roles 0)) fun a =>
  .call (.receive GkrVerifier.scalar (GkrVerifier.roundSite ctx "1") (ctx.roles 0)) fun b =>
  .call (.receive GkrVerifier.scalar (GkrVerifier.roundSite ctx "2") (ctx.roles 0)) fun c =>
  .done (some (a, b, c))

@[expose] noncomputable def program (ctx : ProtocolContext) (handle : Nat) :
    Program (Actions F G) Unit (State F) (Message.coefficientTriples F) where
  claim := State.claim
  receive _ _ := receive ctx
  query _ _ _ := .query (GkrVerifier.challengeSite ctx) "bls12-381.fr" (.cons handle .nil)
  challenge _ _ _ r := r
  deliver _ _ _ r :=
    .call (.send (ty := GkrVerifier.scalar) (GkrVerifier.deliverySite ctx) (ctx.roles 0) r)
      fun _ => .done ()
  advance _ state m r := advance state m r

@[expose] noncomputable def representation (ctx : ProtocolContext) (handle : Nat) :
    Representation (program (F := F) (G := G) ctx handle) (GkrRoundsReference.data F) where
  state := State.reference
  advance _ _ _ _ := rfl
  claim _ _ _ _ := rfl

@[expose] def project {n : Nat} (state : State F n) : List F × F := (state.point, state.claim)

/-- One equation for both the honest and arbitrary-message consumers. -/
theorem binding (handle count : Nat) (ctx : ProtocolContext) {n : Nat}
    (state : State F (n + count)) :
    ((program (G := G) ctx handle).remaining count () state).bind (fun final => .done (project final)) =
      PIR.repeatN count (GkrVerifier.round ctx handle) (project state) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Program.remaining, PIR.repeatN]
    simp only [program, receive, PIR.Process.bind]
    congr 1; funext a; congr 1; funext b; congr 1; funext c
    have boundary : (Message.ofTriple (a, b, c)).boundary = a + a + b + c := by
      simp only [Message.ofTriple, Zkc.Protocols.AlgebraicRounds.Message.boundary,
        Zkc.Protocols.AlgebraicRounds.Message.evaluate]; ring
    have evaluation (r : F) : (Message.ofTriple (a, b, c)).evaluate r =
        a + r * (b + r * c) := by
      simp only [Message.ofTriple,
        Zkc.Protocols.AlgebraicRounds.Message.evaluate]; ring
    by_cases checked : state.claim = a + a + b + c
    · simp only [boundary, GkrVerifier.roundCheck, project, checked,
        ite_true, PIR.Process.bind, GkrVerifier.roundChallenge]
      congr 1; funext r; congr 1; funext delivered
      simpa only [program, receive, advance, project, evaluation] using ih (advance state (a, b, c) r)
    · simp only [boundary, GkrVerifier.roundCheck, project, checked, Ne.symm checked,
        ite_false, PIR.Process.bind]

@[expose] def value {n : Nat} (reference : GkrRoundsReference.State F n) (point : Fin n → F) : F :=
  Zkc.Protocols.AlgebraicRounds.Gate.value
    (extension n reference.add point) (extension n reference.mul point)
    (extension n reference.left point) (extension n reference.right point)

omit [DecidableEq F] in
theorem value_restrict {n : Nat} (reference : GkrRoundsReference.State F (n + 1))
    (r : F) (tail : List F) :
    value (GkrRoundsReference.restrict reference r) (coordinates n tail) =
      value reference (coordinates (n + 1) (r :: tail)) := by
  have coordinatesEq : coordinates (n + 1) (r :: tail) = Fin.cons r (coordinates n tail) := by
    funext i; refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  simp only [value, GkrRoundsReference.restrict, extension_fixFirst, coordinatesEq]

/-- A trace invariant records observations after all future restrictions, not
just the initial sum. It is independent of the messages and claim truth. -/
@[expose] def Anchored {dimension n : Nat} (root : GkrRoundsReference.State F dimension)
    (state : State F n) : Prop :=
  state.point.length + n = dimension ∧
    ∀ tail : List F, value state.reference (coordinates n tail) =
      value root (coordinates dimension (state.point ++ tail))

omit [DecidableEq F] in
theorem anchored_initial {dimension : Nat} (root : GkrRoundsReference.State F dimension) (claim : F) :
    Anchored root (⟨root, [], claim⟩ : State F dimension) := by
  exact ⟨by simp, fun _ => rfl⟩

omit [DecidableEq F] in
theorem anchored_advance {dimension n : Nat} (root : GkrRoundsReference.State F dimension)
    (state : State F (n + 1)) (anchored : Anchored root state) (m : F × F × F) (r : F) :
    Anchored root (advance state m r) := by
  refine ⟨?_, fun tail => ?_⟩
  · have sized := anchored.1
    simp only [advance, List.length_append, List.length_singleton]; omega
  · rw [show (advance state m r).reference = GkrRoundsReference.restrict state.reference r from rfl,
      value_restrict, anchored.2]
    simp only [advance, List.append_assoc, List.singleton_append]

@[expose] def Residual {dimension n : Nat} (root : GkrRoundsReference.State F dimension)
    (result : List F × F) : Prop :=
  ∃ state : State F n, Anchored root state ∧
    GkrRoundsReference.admissible state.reference ∧
    state.claim ≠ GkrRoundsReference.total state.reference ∧ project state = result

/-- Honest execution of the same actual round loop and the same binding used
below for soundness. Delivery laws concern the actual handler's reached state;
the enclosing producer must establish them rather than assume acceptance. -/
theorem honest {H O : Type} (ctx : ProtocolContext) (handle : Nat)
    (handler : PIR.Handler (Actions F G) H O)
    (invariant : Nat → {k : Nat} → Unit → State F k → H → Prop)
    (ready : Nat → {k : Nat} → Unit → State F (k + 1) → (F × F × F) → H → Prop)
    (execution : HonestRunLaws (program ctx handle) handler invariant ready)
    (messages : HonestMessageLaw (representation (G := G) ctx handle) ready)
    (count : Nat) {n : Nat} (state : State F (n + count)) (h : H)
    (yes : (representation (G := G) ctx handle).Yes state)
    (initial : invariant count () state h) :
    ∃ result : State F n, ∃ final events,
      (PIR.repeatN count (GkrVerifier.round ctx handle) (project state)).run handler h =
        ⟨.returned (project result), final, events⟩ ∧
      (representation (G := G) ctx handle).Yes result ∧ invariant 0 () result final := by
  obtain ⟨result, final, events, ran, correct, finished⟩ := Contract.honest
    (representation ctx handle) Message.coefficientTriples_laws GkrRoundsReference.laws
    handler invariant ready execution messages n count
    (fun runtime => (program ctx handle).remaining count runtime.1 runtime.2)
    (fun _ => rfl) ((), state) h yes initial
  refine ⟨result, final, events, ?_, correct, finished⟩
  rw [← binding handle count ctx state, PIR.run_bind, ran]
  simp only [PIR.Execution.follow, PIR.Process.run, List.append_nil]

variable [Fintype F] [SampleableType F]
open Zkc.Obligations ZkcSecurity.Obligations OracleComp OracleSpec

@[expose] noncomputable def queries (ctx : ProtocolContext) (handle : Nat) (context : Context) :
    QueryInterface (program (F := F) (G := G) ctx handle) context.interface where
  event _ _ _ := .challenge (context.query (GkrVerifier.challengeSite ctx) (.draw "bls12-381.fr"))
  decode _ _ _ := some
  challenge _ _ _ := id
  absorbed _ _ _ := rfl
  decoded _ _ _ _ _ decoded := Option.some.inj decoded |>.symm

/-- The only probability step is the generic Sumcheck theorem at degree two. -/
noncomputable opaque residual (handle count : Nat) (ctx : ProtocolContext) (context : Context)
    {n : Nat} (root : GkrRoundsReference.State F (n + count)) (claim : F)
    (allowed : GkrRoundsReference.admissible root)
    (wrong : claim ≠ GkrRoundsReference.total root)
    (charge : History F G → Event F G → ENNReal)
    (covers : ∀ history, 2 / (Fintype.card F : ENNReal) ≤ charge history
      (.challenge (context.query (GkrVerifier.challengeSite ctx) (.draw "bls12-381.fr"))))
    (history : History F G) :
    Derivation context.interface (boundedEscape charge)
      (fun _ result => Residual (n := n) root result) history
      (GkrVerifier.rounds ctx handle count claim) := by
  let initial : State F (n + count) := ⟨root, [], claim⟩
  have uniform : (queries (F := F) (G := G) ctx handle context).ConditionalBound
      (representation ctx handle) 2 2 (fun _ _ => (max 2 2 : Nat) / (Fintype.card F : ENNReal)) :=
    (queries ctx handle context).conditional_of_uniform (representation ctx handle) 2 2 (by intros; rfl)
  have sampling : (queries (G := G) ctx handle context).ConditionalBound (representation ctx handle) 2 2 charge := by
    intro k inner state admissible m reached p q different pd qd
    exact (uniform inner state admissible m reached p q different pd qd).trans (by
      simpa only [queries, max_self, Nat.cast_ofNat] using covers reached)
  have contract := Contract.soundness (representation (G := G) ctx handle)
    Message.coefficientTriples_laws GkrRoundsReference.laws context.interface (queries ctx handle context)
    charge sampling n count (fun runtime => (program ctx handle).remaining count runtime.1 runtime.2)
    (fun _ => rfl)
  have derived := contract () ((), initial) history trivial (ReadbackHolds.some.mpr ⟨allowed, wrong⟩)
  let interaction : PIR.Interaction (Actions F G) :=
    ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
  have returns := Program.returns (program (G := G) ctx handle) interaction (Anchored root)
    (fun _ state anchored m r => anchored_advance root state anchored m r)
    count () initial () (anchored_initial root claim)
  have framed := derived.frameReturns interaction (Anchored root) () returns
  have projected : Derivation context.interface (boundedEscape charge)
      (fun _ result => Residual (n := n) root result) history
      (((program ctx handle).remaining count () initial).bind (fun state => .done (project state))) :=
    framed.bind (fun state => .done (project state)) (fun _ state holds =>
    Derivation.done ⟨state, holds.2, (ReadbackHolds.some.mp holds.1).1,
      (ReadbackHolds.some.mp holds.1).2, rfl⟩)
  exact projected.transport (binding handle count ctx initial).symm

omit [DecidableEq F] [Fintype F] [SampleableType F] in
theorem terminal {dimension : Nat} (root : GkrRoundsReference.State F dimension)
    (result : List F × F) (wrong : Residual (n := 0) root result) :
    result.1.length = dimension ∧ result.2 ≠ value root (coordinates dimension result.1) := by
  obtain ⟨state, anchored, _, wrong, rfl⟩ := wrong
  refine ⟨by simpa [project] using anchored.1, ?_⟩
  have observation := anchored.2 []
  simp only [List.append_nil] at observation
  have total : GkrRoundsReference.total state.reference = value state.reference (coordinates 0 []) := rfl
  exact fun same => wrong (same.trans (total.trans observation).symm)

end ZkcSecurity.Realizations.Gkr.Rounds
