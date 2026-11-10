module

public import Zkc.Tests.Protocol.Construction.Readings.Sumcheck

/-! Soundness for a statement the prover chooses and sends in the clear, through the same reading
and the same endpoint.

The prover first sends a table handle; the handle is the witness. The verifier runs the Sumcheck
rounds against the reference of that table, evaluating the reference at the handle itself, and
returns the handle with its decision. The property is no longer that a fixed false claim is
rejected but that an accepted run returns a handle whose table sums to the claim. The
postcondition has the shape of an extraction statement, with the identity on the received handle
as its extractor: no commitment is opened and no knowledge extractor is constructed. The
derivation is the charged derivation with the invariant "if the running claim agrees with the
reference, the statement of the handle holds"; the endpoint is the retained Fiat–Shamir theorem at
the acceptance predicate "accepted and the statement of the returned handle fails". No reading,
certificate type or endpoint theorem is added. -/

@[expose] public section
set_option experimental.vcgen true
open PIR Zkc.Source Zkc.Transcript Std.WP ProtocolProof
open OracleComp OracleSpec ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition
open ZkcSecurity.FiatShamir.Typed
open scoped ENNReal

namespace ProtocolProofExamples.ExtractionSumcheck
open ProtocolProofExamples.ChargedSumcheck (Laws escape_le)

variable {F : Type} [Field F] [DecidableEq F] {T : Type}

inductive Ev (T F : Type) where
  | table (handle : T)
  | msg (low high : F)
  | chal
  deriving DecidableEq

inductive VOp where
  | table | recv | draw

abbrev VSig (T F : Type) : Signature :=
  ⟨VOp, fun | .table => T | .recv => F × F | .draw => F⟩

/-- One proof message is either the table handle or a round pair. -/
def event : T ⊕ (F × F) → Ev T F
  | .inl handle => .table handle
  | .inr pair => .msg pair.1 pair.2

def absorb : Interface (VSig T F) (Ev T F) (T ⊕ (F × F)) (fun _ => F) := fun op =>
  match op with
  | .table => .receive event (fun e => match e with | .table handle => some handle | _ => none)
  | .recv => .receive event (fun e => match e with | .msg low high => some (low, high) | _ => none)
  | .draw => .query Ev.chal (fun raw => some raw)

inductive Ty where
  | table | state | msg | chal | out
  deriving DecidableEq

inductive Op where
  | table | init | recv | check | draw | fold | final

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .table | .recv | .draw => []
    | .init => [.table]
    | .check => [.state, .msg]
    | .fold => [.state, .msg, .chal]
    | .final => [.state]
  result
    | .table => .table
    | .init | .fold => .state
    | .recv | .check => .msg
    | .draw => .chal
    | .final => .out
  condition := .chal

abbrev meaning (S : T → List F → F) (claim : F) : Interpretation language (VSig T F) where
  Value
    | .table => T
    | .state => T × List F × F
    | .msg => F × F
    | .chal => F
    | .out => T × Bool
  condition := fun r => r = 0
  operation
    | .table, .nil => .call .table .done
    | .init, .cons handle .nil => .done (handle, [], claim)
    | .recv, .nil => .call .recv .done
    | .draw, .nil => .call .draw .done
    | .check, .cons st (.cons m .nil) => if m.1 + m.2 = st.2.2 then .done m else .halt .reject
    | .fold, .cons st (.cons m (.cons r .nil)) =>
        .done (st.1, st.2.1 ++ [r], (1 - r) * m.1 + r * m.2)
    | .final, .cons st .nil => .done (st.1, decide (st.2.2 = S st.1 st.2.1))

def round : Region (scalarDialect language) [.state] [.state] :=
  .letOp (.ordinary .recv) .nil .nil
    (.letOp (.ordinary .check) (.cons (.there .here) (.cons .here .nil)) .nil
      (.letOp (.ordinary .draw) .nil .nil
        (.letOp (.ordinary .fold)
          (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons .here .nil))) .nil
          (.ret (.cons .here .nil)))))

def rounds (count : Nat) {Γ : List Ty} : Region (scalarDialect language) (.state :: Γ) [.state] :=
  .letOp (.repeat count [] .state) (.cons .here .nil) (.cons round .nil) (.ret (.cons .here .nil))

/-- Receive the table, initialize, run the rounds, decide and return the handle. -/
def verifier (count : Nat) : Region (scalarDialect language) [] [.out] :=
  .letOp (.ordinary .table) .nil .nil
    (.letOp (.ordinary .init) (.cons .here .nil) .nil
      (.bind (rounds count)
        (.letOp (.ordinary .final) (.cons .here .nil) .nil (.ret (.cons .here .nil)))))

def game (S : T → List F → F) (claim : F) (count : Nat) : Process (VSig T F) (T × Bool) :=
  ((verifier count).denote (meaning S claim).regionMeaning Values.nil.get).bind
    fun out => .done (out.get .here)

section Rules
variable (S : T → List F → F) (claim : F)

@[spec] theorem table_rule : (meaning S claim).operation .table .nil = .call .table .done := rfl
@[spec] theorem recv_rule : (meaning S claim).operation .recv .nil = .call .recv .done := rfl
@[spec] theorem draw_rule : (meaning S claim).operation .draw .nil = .call .draw .done := rfl
@[spec] theorem init_rule (handle : T) :
    (meaning S claim).operation .init (.cons handle .nil) = .done (handle, [], claim) := rfl
@[spec] theorem check_rule (st : T × List F × F) (m : F × F) :
    (meaning S claim).operation .check (.cons st (.cons m .nil)) =
      if m.1 + m.2 = st.2.2 then .done m else .halt .reject := rfl
@[spec] theorem fold_rule (st : T × List F × F) (m : F × F) (r : F) :
    (meaning S claim).operation .fold (.cons st (.cons m (.cons r .nil))) =
      .done (st.1, st.2.1 ++ [r], (1 - r) * m.1 + r * m.2) := rfl
@[spec] theorem final_rule (st : T × List F × F) :
    (meaning S claim).operation .final (.cons st .nil) =
      .done (st.1, decide (st.2.2 = S st.1 st.2.1)) := rfl

end Rules

attribute [local construction_simp] absorb

variable [Fintype F] [SampleableType F]

noncomputable abbrev charge : List (Ev T F) → Ev T F → ℝ≥0∞ := fun _ _ => 1 / Fintype.card F

variable (S : T → List F → F) (claim : F)

/-- The statement of a handle: its table sums to the claim. The handle is the one the prover
sent, so the extractor of this statement is the identity on that message. -/
abbrev Extracted (handle : T) : Prop := claim = S handle []

section Extraction

noncomputable abbrev logic :
    WPMonad (Process (VSig T F)) (Assert (Ev T F)) (StopAssert (Ev T F)) :=
  chargedMonad absorb (boundedEscape charge) (boundedEscape_antitone charge)

attribute [local instance] logic

/-- The invariant: agreement with the reference already implies the extracted statement. -/
abbrev Linked (st : T × List F × F) : Assert (Ev T F) :=
  fun _ => ⟨st.2.2 = S st.1 st.2.1 → Extracted S claim st.1⟩

@[spec high] theorem round_linked (laws : ∀ handle, Laws (S handle))
    (env : Environment (meaning S claim).Value [.state]) :
    ⦃Linked S claim (env .here)⦄
      round.denote (meaning S claim).regionMeaning env
    ⦃fun out => Linked S claim (out.get .here); estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold round
  construct_region
  intro linked message value recovered
  rcases message with handle | pair
  · cases recovered
  obtain rfl : (pair.1, pair.2) = value := Option.some.inj recovered
  split
  · rename_i checked
    by_cases known : Extracted S claim (env .here).1
    · -- The extracted statement already holds: no challenge is excluded.
      refine (prEvent_mono _ _ (fun _ => False) fun raw escaped => ?_).trans (by simp)
      obtain ⟨reply, decoded, outside⟩ := escaped
      exact outside fun _ => known
    · have wrong : (env .here).2.2 ≠ S (env .here).1 (env .here).2.1 :=
        fun same => known (linked same)
      refine (prEvent_mono _ _ _ fun raw escaped => ?_).trans
        (escape_le (laws (env .here).1) (env .here).2.1 (env .here).2.2 pair.1 pair.2 wrong checked)
      obtain ⟨reply, decoded, outside⟩ := escaped
      obtain rfl : raw = reply := Option.some.inj decoded
      by_contra different
      exact outside fun same => absurd same different
  · trivial

@[spec high] theorem rounds_linked (laws : ∀ handle, Laws (S handle)) (count : Nat) {Γ : List Ty}
    (env : Environment (meaning S claim).Value (.state :: Γ)) :
    ⦃Linked S claim (env .here)⦄
      (rounds count).denote (meaning S claim).regionMeaning env
    ⦃fun out => Linked S claim (out.get .here); estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold rounds
  construct_region with_invariants [fun _ st => Linked S claim st]

/-- From any history, an accepting run returns a handle whose table sums to the claim; the
handle is the message the prover sent. -/
theorem game_extracts (laws : ∀ handle, Laws (S handle)) (count : Nat) :
    ⦃fun _ => ⟨True⟩⦄ game S claim count
    ⦃fun out _ => ⟨out.2 = true → Extracted S claim out.1⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold game verifier
  construct_region
  intro _ linked accepted
  exact linked (of_decide_eq_true accepted)

end Extraction

section Cost

noncomputable abbrev budget :
    WPMonad (Process (VSig T F)) (CostAssert (Ev T F)) (CostStopAssert (Ev T F)) :=
  costMonad absorb charge

attribute [local instance] budget

omit [SampleableType F] in
@[spec high] theorem round_cost (rest : ℝ≥0∞) (env : Environment (meaning S claim).Value [.state]) :
    ⦃fun _ cost => ⟨1 / (Fintype.card F : ℝ≥0∞) + rest ≤ cost⟩⦄
      round.denote (meaning S claim).regionMeaning env
    ⦃fun _ _ cost => ⟨rest ≤ cost⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  unfold round
  construct_region
  intro budget message value _
  split
  · exact ⟨rest, budget, fun _ => le_rfl⟩
  · trivial

omit [SampleableType F] in
@[spec high] theorem rounds_cost (count : Nat) (rest : ℝ≥0∞) {Γ : List Ty}
    (env : Environment (meaning S claim).Value (.state :: Γ)) :
    ⦃fun _ cost => ⟨count * (1 / (Fintype.card F : ℝ≥0∞)) + rest ≤ cost⟩⦄
      (rounds count).denote (meaning S claim).regionMeaning env
    ⦃fun _ _ cost => ⟨rest ≤ cost⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  unfold rounds
  construct_region with_invariants [fun remaining _ => fun _ cost =>
    ⟨remaining * (1 / (Fintype.card F : ℝ≥0∞)) + rest ≤ cost⟩]
  · intro budget
    refine le_trans (le_of_eq ?_) budget
    push_cast
    ring
  · intro _ cost budget
    simpa using budget

omit [SampleableType F] in
theorem game_cost (count : Nat) :
    ⦃fun _ cost => ⟨count * (1 / (Fintype.card F : ℝ≥0∞)) + 0 ≤ cost⟩⦄
      game S claim count
    ⦃fun _ _ cost => ⟨0 ≤ cost⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  unfold game verifier
  construct_region

end Cost

/-- Soundness for the prover-chosen handle in the transformed verifier: the probability that it
accepts while the table behind the returned handle, which the prover sent in the clear, does not
sum to the claim is at most `(queries + count) / |F|`. The statement is extraction-shaped with the
identity extractor on that message; it is not extraction from a commitment. The endpoint is the
soundness endpoint at the acceptance predicate "accepted and the statement of the returned handle
fails". -/
theorem extraction_soundness [DecidableEq T] (laws : ∀ handle, Laws (S handle)) (count : Nat)
    (prover : OracleComp (OracleSpec.ofFn fun _ : List (Ev T F) => F) (List (T ⊕ (F × F))))
    (queries : Nat) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (fixedExperiment absorb (game S claim count) [] prover)).run' ∅}[
      Accepted (fun out => out.2 = true ∧ ¬ Extracted S claim out.1) result.1] ≤
      (queries + count) * (1 / (Fintype.card F : ℝ≥0∞)) := by
  have extracted : absorb.Charged (boundedEscape charge)
      (fun _ out => out.2 = true → Extracted S claim out.1) (game S claim count) [] :=
    charged_of_triple absorb (boundedEscape charge) (boundedEscape_antitone charge)
      (game_extracts S claim laws count) [] trivial
  have priced : ChargedCostBound absorb charge (game S claim count) []
      (count * (1 / (Fintype.card F : ℝ≥0∞))) :=
    costBound_of_triple absorb charge (game_cost S claim count) [] _ (by simp)
  have bound := soundness_charged
    (certificate (absorb := absorb) (charge := charge)
      (Post := fun _ (out : T × Bool) => out.2 = true → Extracted S claim out.1)
      (fun out : T × Bool => out.2 = true ∧ ¬ Extracted S claim out.1)
      (by intro _ value holds bad; exact bad.2 (holds bad.1)))
    (game S claim count) [] (certificate_doomed.mpr extracted) _ priced prover
    (queries * (1 / (Fintype.card F : ℝ≥0∞)))
    (worstCaseCostBound_of_isTotalQueryBound _
      (keyCharge_le (fun _ _ => le_rfl)) prover queries proverBound)
  simpa [add_mul] using bound

#print axioms extraction_soundness

end ProtocolProofExamples.ExtractionSumcheck
