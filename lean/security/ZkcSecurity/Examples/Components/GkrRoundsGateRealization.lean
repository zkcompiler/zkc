module

public import ZkcSecurity.Examples.Components.GkrRoundsRealization

@[expose] public section

/-! Local GKR Rounds realization gate. The caller supplies the split-variable
layout, decoded shape and logical capacity; none of these premises asserts
circuit correctness, target truth or honesty of a received verifier message. -/

set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.GkrRoundsGateRealization
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsInputs
open GkrRoundsHelpers GkrRoundsProcesses GkrRoundsReference GkrRoundsRealization
open Zkc.Polynomial.Multilinear
open ZkcSecurity.Families.Sumcheck

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- All four factors, every future degree premise, and exact shape/capacity. -/
def Represents {n : Nat} (raw : RawState F) (s : State F n) : Prop :=
  Decodes raw s ∧ admissible s ∧ 2 ^ n < indexLimit

omit [DecidableEq F] in
theorem smaller_capacity (n count : Nat) (small : 2 ^ (n + count) < indexLimit) :
    2 ^ n < indexLimit :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (Nat.le_add_right n count)) small

omit [DecidableEq F] in
theorem restriction_represents {n : Nat} (raw : RawState F) (s : State F (n + 1))
    (represented : Represents raw s) (r : F) : Represents (raw.restrict r) (restrict s r) :=
  ⟨restriction_decodes raw s represented.1 r, represented.2.1.2 r,
    smaller_capacity n 1 represented.2.2⟩

omit [DecidableEq F] in
/-- Zero, partial and complete prefixes are all covered, for every challenge. -/
theorem prefix_represents {n : Nat} (count : Nat) (raw : RawState F)
    (s : State F (n + count)) (represented : Represents raw s) (challenges : Fin count → F) :
    Represents (raw.prefix count challenges) ((data F).restrictPrefix count s challenges) :=
  ⟨prefix_decodes count raw s represented.1 challenges,
    prefix_admissible count s challenges represented.2.1,
    smaller_capacity n count represented.2.2⟩

/-- Execute the actual four-factor helper once per challenge. Each bind keeps
the imported helper's stopping behavior; this is an operational prefix. -/
noncomputable def executeRestrictions : (count : Nat) →
    Values (assignment F G) [vector, vector, vector, vector] → (Fin count → F) →
    PIR.Process (participantInterface F G)
      (Values (assignment F G) [vector, vector, vector, vector])
  | 0, args, _ => .done args
  | count + 1, args, challenges =>
    (invoke table gateRestrictionHelper (args.append (.cons (challenges 0) .nil))).bind
      fun result => executeRestrictions count result (challenges ∘ Fin.succ)

/-- Mathematical prefixes are the results of executing the actual helper,
including the empty prefix and the terminal, one-entry-per-factor state. -/
theorem prefix_execution {n : Nat} (count : Nat) (raw : RawState F)
    (s : State F (n + count)) (represented : Represents raw s) (challenges : Fin count → F) :
    executeRestrictions (G := G) count raw.values challenges =
      .done (raw.prefix count challenges).values := by
  induction count generalizing raw with
  | zero => rfl
  | succ count ih =>
    rw [executeRestrictions,
      fixGates_success raw s represented.1
        (smaller_capacity (n + count) 1 represented.2.2) (challenges 0)]
    exact ih (raw.restrict (challenges 0)) (restrict s (challenges 0))
      (restriction_represents raw s represented (challenges 0)) (challenges ∘ Fin.succ)

omit [DecidableEq F] in
/-- The actual residual vectors decode to restrictions of each original
factor. In particular, no Boolean table of a product replaces those factors. -/
theorem prefix_separate_decodes {n : Nat} (count : Nat) (raw : RawState F)
    (s : State F (n + count)) (represented : Represents raw s) (challenges : Fin count → F) :
    Decodes (raw.prefix count challenges)
      ⟨fixPrefix count s.add challenges, fixPrefix count s.mul challenges,
        fixPrefix count s.left challenges, fixPrefix count s.right challenges⟩ := by
  simpa only [prefix_factors] using prefix_decodes count raw s represented.1 challenges

/-- The active restriction of an individual factor, before gate products. -/
noncomputable def factorPolynomial {n : Nat} (factor : Table F (n + 1))
    (bits : Fin n → Bool) : Polynomial F :=
  Polynomial.C (half factor false bits) +
    Polynomial.C (half factor true bits - half factor false bits) * Polynomial.X

omit [DecidableEq F] in
theorem factor_degree {n : Nat} (factor : Table F (n + 1)) (bits : Fin n → Bool) :
    (factorPolynomial factor bits).natDegree ≤ 1 := by
  unfold factorPolynomial
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
    (Polynomial.natDegree_mul_le.trans
      (by rw [Polynomial.natDegree_C, zero_add]; exact Polynomial.natDegree_X_le)))

omit [DecidableEq F] in
theorem factor_evaluation {n : Nat} (factor : Table F (n + 1))
    (bits : Fin n → Bool) (r : F) :
    (factorPolynomial factor bits).eval r = fixFirst factor r bits := by
  simp only [factorPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, fixFirst, half]
  ring

omit [DecidableEq F] in
/-- At each nonterminal operational prefix, all four factors separately have
active degree at most one, and one wire factor is active-variable independent. -/
theorem prefix_factor_degrees {n : Nat} (count : Nat) (raw : RawState F)
    (s : State F ((n + 1) + count)) (represented : Represents raw s)
    (challenges : Fin count → F) (bits : Fin n → Bool) :
    let current := (data F).restrictPrefix count s challenges
    independent current ∧
    (factorPolynomial current.add bits).natDegree ≤ 1 ∧
    (factorPolynomial current.mul bits).natDegree ≤ 1 ∧
    (factorPolynomial current.left bits).natDegree ≤ 1 ∧
    (factorPolynomial current.right bits).natDegree ≤ 1 :=
  ⟨(prefix_represents count raw s represented challenges).2.1.1,
    factor_degree _ bits, factor_degree _ bits, factor_degree _ bits, factor_degree _ bits⟩

/-- Both actual full helpers, with the same decoded reference and separate
factor update. Successful message realization does not assume admissibility;
admissibility is used for the reference's evaluation and boundary laws. -/
theorem helper_realization {n : Nat} (raw : RawState F) (s : State F (n + 1))
    (represented : Represents raw s) (r : F) :
    invoke (table (G := G)) roundMessageHelper raw.values =
      .done (.cons (message s).constant (.cons (message s).linear (.cons (message s).quadratic .nil))) ∧
    invoke (table (G := G)) gateRestrictionHelper (raw.values.append (.cons r .nil)) =
      .done (raw.restrict r).values ∧
    Represents (raw.restrict r) (restrict s r) ∧
    ((data F).polynomial s).natDegree ≤ 2 ∧
    boundaryPoly ((data F).polynomial s) = total s ∧
    ((data F).polynomial s).eval r = total (restrict s r) := by
  have capacity := smaller_capacity n 1 represented.2.2
  exact ⟨round_success raw s represented.1 capacity,
    fixGates_success raw s represented.1 capacity r,
    restriction_represents raw s represented r,
    laws.degree_le s represented.2.1, laws.boundary_eq s represented.2.1,
    laws.evaluation_eq s r represented.2.1⟩

/-- The full local gate holds at any reachable prefix, including after the
left/right phase transition. The received challenge is unrestricted. -/
theorem prefix_helper_realization {n : Nat} (count : Nat) (raw : RawState F)
    (s : State F ((n + 1) + count)) (represented : Represents raw s)
    (challenges : Fin count → F) (r : F) :
    let residual := (data F).restrictPrefix count s challenges
    let vectors := raw.prefix count challenges
    invoke (table (G := G)) roundMessageHelper vectors.values =
      .done (.cons (message residual).constant
        (.cons (message residual).linear (.cons (message residual).quadratic .nil))) ∧
    invoke (table (G := G)) gateRestrictionHelper (vectors.values.append (.cons r .nil)) =
      .done (vectors.restrict r).values ∧
    Represents (vectors.restrict r) (restrict residual r) ∧
    ((data F).polynomial residual).natDegree ≤ 2 ∧
    boundaryPoly ((data F).polynomial residual) = total residual ∧
    ((data F).polynomial residual).eval r = total (restrict residual r) :=
  helper_realization _ _ (prefix_represents count raw s represented challenges) r

/-- The concrete mathematical construction of the source `layer_gates` layout.
The imported caller's construction equation is a separate caller obligation. -/
def callerVectors (width : Nat) (add mul : Table F (width + width)) (below : Table F width) :
    RawState F :=
  ⟨GkrRoundsLayout.encode add, GkrRoundsLayout.encode mul,
    (GkrRoundsLayout.encode below).flatMap (fun value => List.replicate (2 ^ width) value),
    (List.replicate (2 ^ width) (GkrRoundsLayout.encode below)).flatten⟩

omit [DecidableEq F] in
theorem concrete_caller (width : Nat) (add mul : Table F (width + width))
    (below : Table F width) (capacity : 2 ^ (width + width) < indexLimit) :
    Represents (callerVectors width add mul below)
      (GkrRoundsLayout.state add mul below below) := by
  refine ⟨?_, GkrRoundsLayout.admissible_state width width add mul below below, capacity⟩
  unfold Decodes callerVectors GkrRoundsLayout.state
  rw [← GkrRoundsLayout.encode_replicate width width below,
    ← GkrRoundsLayout.encode_tile width width below]
  exact ⟨GkrRoundsLayout.decode_encode _, GkrRoundsLayout.decode_encode _,
    GkrRoundsLayout.decode_encode _, GkrRoundsLayout.decode_encode _⟩

omit [DecidableEq F] in
theorem caller_represents {x y : Nat} (raw : RawState F) (s : State F (y + x))
    (decoded : Decodes raw s) (layout : GkrRoundsLayout.CallerLayout (x := x) (y := y) s)
    (capacity : 2 ^ (y + x) < indexLimit) : Represents raw s :=
  ⟨decoded, GkrRoundsLayout.caller_admissible s layout, capacity⟩

omit [DecidableEq F] in
/-- All adversarial coefficient triples have their own decoder degree bound.
This theorem has no layout or honest-message hypothesis. -/
theorem arbitrary_message_degree (m : F × F × F) :
    ((Message.coefficientTriples F).polynomial m).natDegree ≤ 2 :=
  Message.coefficientTriples_laws.degree_le m

omit [DecidableEq F] in
theorem wire_boundary (c0 c1 c2 : F) :
    c0 + c0 + c1 + c2 = (Message.ofTriple (c0, c1, c2)).boundary := by
  simp only [Message.ofTriple, Zkc.Protocols.AlgebraicRounds.Message.boundary,
    Zkc.Protocols.AlgebraicRounds.Message.evaluate]
  ring

omit [DecidableEq F] in
theorem wire_evaluation (c0 c1 c2 r : F) :
    c0 + r * (c1 + r * c2) = (Message.ofTriple (c0, c1, c2)).evaluate r := by
  simp only [Message.ofTriple, Zkc.Protocols.AlgebraicRounds.Message.evaluate]
  ring

end ZkcSecurity.Examples.Components.GkrRoundsGateRealization
