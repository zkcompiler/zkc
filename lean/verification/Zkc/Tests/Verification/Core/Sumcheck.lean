import Zkc.Tests.IR.Core.Sumcheck
import Zkc.Tools.Verification.CoreConstruction
import Zkc.Protocol.Library.Mathematics.Algebra.Polynomial

/-! The verifier of the imported Sumcheck package under the charged and cost readings.

The program is the side meaning of the imported protocol `sumcheck` for the verifier's role:
a `repeat` whose body applies the two-role protocol `round`, followed by a call of the function
`final_check`. The contract of a round is proved once, for the side that the `apply` runs it at:
a wrong running claim stays wrong, except on a set of challenges of probability at most
`1 / |F|`. The whole protocol is proved by a loop invariant that reuses the contract through
the `apply`; the round is not constructed again. Adequacy turns the charged and the cost triple
into the existing judgments, and the interactive theorem and the Fiat–Shamir theorem bound the
acceptance of a false claim.

The mathematics is stated on the model. The scalar carrier is a finite field, the model's
field operations are the field's, and the reference of the table, the sum of its restriction
to a point, is multilinear in the next variable at every point shorter than the number of
variables (`Laws`). The laws are restricted to such points on purpose: a table has no further
variable to split. The invariant therefore counts the rounds to go, and the theorems ask that
the round count is at most the number of variables. The model at the end, which restricts a
table of `2 ^ arity` scalars by folding, satisfies the laws; at that model the bound has no
hypothesis left. Every sampling law that returns a scalar is read as the uniform law on the
field. -/

set_option autoImplicit false
set_option experimental.vcgen true

open PIR Zkc.Source Zkc.Core Zkc.Core.Transcript Zkc.Transcript Std.WP ProtocolProof
open OracleComp OracleSpec ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition
open ZkcSecurity.FiatShamir.Typed
open Zkc.Tests.Core.Sumcheck
open scoped ENNReal

register_core_entries sumcheck

namespace Zkc.Tests.Verification.Core.Sumcheck

noncomputable section

/-! ### The mathematics -/

/-- The fold of a checked pair for a false claim agrees with a line through values that sum to
another claim at one challenge at most. -/
theorem fold_agreement_le {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (claim low high zero one : F) (wrong : claim ≠ zero + one) (checked : low + high = claim) :
    Pr{let r ← $ᵗ F}[low + r * (high - low) = (1 - r) * zero + r * one] ≤
      1 / (Fintype.card F : ℝ≥0∞) := by
  let p : Polynomial F := Polynomial.C low + Polynomial.X * Polynomial.C (high - low)
  let q : Polynomial F := Polynomial.C zero + Polynomial.X * Polynomial.C (one - zero)
  have degree : ∀ a b : F,
      (Polynomial.C a + Polynomial.X * Polynomial.C b).natDegree ≤ 1 := fun a b =>
    (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      ((Polynomial.natDegree_mul_C_le _ _).trans Polynomial.natDegree_X_le))
  have different : p ≠ q := by
    intro same
    have at0 := congrArg (Polynomial.eval 0) same
    have at1 := congrArg (Polynomial.eval 1) same
    simp only [p, q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, zero_mul, add_zero, one_mul] at at0 at1
    apply wrong
    rw [← checked, ← at0]
    linear_combination at1
  have bound := ZkcSecurity.Algebra.Polynomial.agreement_uniform_le p q different
    (degree _ _) (degree _ _)
  have same : Pr{let r ← $ᵗ F}[low + r * (high - low) = (1 - r) * zero + r * one] =
      Pr{let r ← $ᵗ F}[p.eval r = q.eval r] := by
    refine prEvent_congr ($ᵗ F) _ _ fun r => ?_
    simp only [p, q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    constructor <;> intro h <;> linear_combination h
  rw [same]
  simpa using bound

variable (M : Model)

/-! ### The model's operations and laws -/

/-- The operations of the model that the proof names, beside those of the import test. -/
def length (v : M.Value vector) : Nat :=
  (M.pure (.of sumcheck.row.«vector.length(domain scalar)») (.cons v .nil)).get .here
def restrict (values point : M.Value vector) : M.Value vector :=
  (M.pure (.of sumcheck.row.«multilinear.restrict_prefix(domain scalar)»)
    (.cons values (.cons point .nil))).get .here
def sum (v : M.Value vector) : M.Value field :=
  (M.pure (.of sumcheck.row.«vector.sum(domain scalar)») (.cons v .nil)).get .here

/-- The reference of a table at a point: the sum of the table restricted to the point. -/
def reference (values point : M.Value vector) : M.Value field := sum M (restrict M values point)

variable [Field (M.Carrier 0)] [Fintype (M.Carrier 0)] [DecidableEq (M.Carrier 0)]
  [SampleableType (M.Carrier 0)]

/-- The laws of the model that the proof uses, for a table with `arity` variables: the field
operations of the model are those of the field, the length of a point counts its coordinates,
and the reference is multilinear in the next variable at every point with fewer than `arity`
coordinates. -/
structure Laws (values : M.Value vector) (arity : Nat) : Prop where
  add : ∀ a b : M.Value field, add M a b = a + b
  sub : ∀ a b : M.Value field, sub M a b = a - b
  mul : ∀ a b : M.Value field, mul M a b = a * b
  equal : ∀ a b : M.Value field, equal M a b = true ↔ a = b
  length_empty : length M (empty M) = 0
  length_append : ∀ point r, length M (append M point r) = length M point + 1
  split : ∀ point, length M point < arity →
    reference M values point =
      reference M values (append M point 0) + reference M values (append M point 1)
  line : ∀ point r, length M point < arity →
    reference M values (append M point r) =
      (1 - r) * reference M values (append M point 0) + r * reference M values (append M point 1)

/-! ### Sample spaces -/

/-- The sample space of a law by its output type: the scalars for a law that returns a scalar.
No other law is sampled. -/
@[reducible] def Sample : Ty → Type
  | .nominal 0 => M.Carrier 0
  | _ => PUnit

/-- The reading of a sample: a scalar is read as itself. -/
def readSample : (type : Ty) → Sample M type → Option (M.Value type)
  | .nominal 0, raw => some raw
  | _, _ => none

instance sampling : Sampling M where
  Raw law _ := Sample M law.output
  decode law _ := readSample M law.output

instance sampleSpace : (type : Ty) → SampleableType (Sample M type)
  | .nominal 0 => inferInstanceAs (SampleableType (M.Carrier 0))
  | .nominal (_ + 1) => inferInstanceAs (SampleableType PUnit)
  | .unit => inferInstanceAs (SampleableType PUnit)
  | .bool => inferInstanceAs (SampleableType PUnit)
  | .index => inferInstanceAs (SampleableType PUnit)
  | .array _ => inferInstanceAs (SampleableType PUnit)
  | .tuple _ => inferInstanceAs (SampleableType PUnit)
  | .variant _ _ => inferInstanceAs (SampleableType PUnit)

instance sampled (law : SamplingRow) (inputs : Values M.Value law.inputs) :
    SampleableType (Sampling.Raw law inputs) := sampleSpace M law.output

omit [Field (M.Carrier 0)] [Fintype (M.Carrier 0)] [DecidableEq (M.Carrier 0)]
  [SampleableType (M.Carrier 0)] in
/-- The uniform law on the scalars reads every sample as itself. -/
theorem decode_uniform (raw : M.Carrier 0) :
    Sampling.decode (model := M) uniform .nil raw = some raw := rfl

attribute [local construction_simp] decode_uniform

omit [Field (M.Carrier 0)] [Fintype (M.Carrier 0)] [DecidableEq (M.Carrier 0)]
  [SampleableType (M.Carrier 0)] in
/-- The final check returns the comparison of the reference at the point with the claim, under
every reading. -/
@[spec] theorem final_check_returns {Pred EPred : Type} [Assertion Pred] [Assertion EPred]
    [WPMonad (Process (Effects M)) Pred EPred] (values point : M.Value vector)
    (claim : M.Value field) (post : Values M.Value [.bool] → Pred) (stopped : EPred) :
    ⦃post (.cons (equal M (reference M values point) claim) .nil)⦄
      sumcheck.final_check.meaning M (.cons values (.cons point (.cons claim .nil)))
    ⦃post; stopped⦄ := by
  open_core_definition
  construct_region

/-- Every challenge is charged `1 / |F|`. -/
abbrev charge : List (Event M.Value) → Event M.Value → ℝ≥0∞ :=
  fun _ _ => 1 / (Fintype.card (M.Carrier 0) : ℝ≥0∞)

section Soundness

/-- The charged reading at the bounded judgment. -/
abbrev logic : WPMonad (Process (Effects M)) (Assert (Event M.Value)) (StopAssert (Event M.Value)) :=
  chargedMonad (interface .refused) (boundedEscape (charge M)) (boundedEscape_antitone (charge M))

attribute [local instance] logic

variable {M}

/-- The doomed assertion with `remaining` rounds to go: the running claim differs from the
reference at the point, and the rounds to go fit the table. -/
abbrev Wrong (values : M.Value vector) (arity rounds remaining : Nat)
    (claim : M.Value field) (point : M.Value vector) : Assert (Event M.Value) :=
  fun _ => ⟨claim ≠ reference M values point ∧ length M point + remaining = rounds ∧
    rounds ≤ arity⟩

/-- The contract of a round, for the side that `sumcheck` applies it at: a wrong running claim
stays wrong, except on a set of challenges of probability at most `1 / |F|`. The rounds to go
and the round count are parameters of the contract, so that it states the step of the
invariant of `sumcheck`. -/
@[spec] theorem round_wrong {values : M.Value vector} {arity : Nat}
    (laws : Laws M values arity) (rounds remaining : Nat)
    (claim : M.Value field) (point : M.Value vector) :
    ⦃Wrong values arity rounds (remaining + 1) claim point⦄
      sumcheck.round.meaning M (Side.preimage [0, 1] verifier)
        (.cons () (.cons claim (.cons point .nil)))
    ⦃fun out => Wrong values arity rounds remaining (out.get (.there .here))
        (out.get (.there (.there .here)));
      estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  open_core_definition
  construct_region
  -- The one remaining obligation is the mathematics of the challenge site.
  rintro ⟨wrong, counted, _⟩ low high
  show if equal M (add M low high) claim = true then
      Pr{let raw ← $ᵗ (M.Carrier 0)}[∃ challenge, some raw = some challenge ∧
        ¬ (¬ add M low (mul M challenge (sub M high low)) =
            reference M values (append M point challenge) ∧
          length M (append M point challenge) + remaining = rounds ∧ True)] ≤
        1 / (Fintype.card (M.Carrier 0) : ℝ≥0∞)
    else True
  split
  · rename_i checked
    have short : length M point < arity := by omega
    have summed : low + high = claim := by
      rw [← laws.add]
      exact (laws.equal _ _).mp checked
    refine (prEvent_mono _ _ _ fun raw escaped => ?_).trans
      (fold_agreement_le claim low high (reference M values (append M point 0))
        (reference M values (append M point 1)) (laws.split point short ▸ wrong) summed)
    obtain ⟨challenge, decoded, outside⟩ := escaped
    obtain rfl : raw = challenge := Option.some.inj decoded
    by_contra different
    refine outside ⟨?_, ?_, trivial⟩
    · rwa [laws.add, laws.mul, laws.sub, laws.line point raw short]
    · rw [laws.length_append]
      omega
  · trivial

/-- A verifier started on a false claim never returns `true`, except on the challenges that
the rounds charge. The invariant is the doomed assertion on the carried claim and point; each
iteration applies the contract of a round. -/
theorem verifier_rejects {values : M.Value vector} {arity : Nat} (laws : Laws M values arity)
    (claim : M.Value field) (rounds : Nat) (within : rounds ≤ arity) :
    ⦃fun _ => ⟨claim ≠ reference M values (empty M)⟩⦄
      sumcheck.sumcheck.meaning M verifier
        (.cons () (.cons () (.cons values (.cons claim (.cons rounds .nil)))))
    ⦃fun out _ => ⟨out.get .here = false⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  open_core_definition
  construct_region with_invariants [fun remaining state =>
    Wrong values arity rounds remaining (state.get (.there .here))
      (state.get (.there (.there .here)))]
  -- The invariant holds at the empty point.
  · intro wrong
    exact ⟨wrong, show length M (empty M) + rounds = rounds by
      rw [laws.length_empty, Nat.zero_add], trivial⟩
  -- After the last round the final check compares a wrong claim with the reference.
  · rintro _ ⟨wrong, -, -⟩
    exact Bool.eq_false_iff.mpr fun accepted => wrong ((laws.equal _ _).mp accepted).symm

end Soundness

/-! ### The cost triple of the same program -/

section Cost

/-- The cost reading of the same interface and charge. -/
abbrev budget :
    WPMonad (Process (Effects M)) (CostAssert (Event M.Value)) (CostStopAssert (Event M.Value)) :=
  costMonad (interface .refused) (charge M)

attribute [local instance] budget

omit [Field (M.Carrier 0)] [DecidableEq (M.Carrier 0)] [SampleableType (M.Carrier 0)] in
/-- A round pays for one challenge. -/
@[spec] theorem round_cost (rest : ℝ≥0∞) (claim : M.Value field) (point : M.Value vector) :
    ⦃fun _ cost => ⟨1 / (Fintype.card (M.Carrier 0) : ℝ≥0∞) + rest ≤ cost⟩⦄
      sumcheck.round.meaning M (Side.preimage [0, 1] verifier)
        (.cons () (.cons claim (.cons point .nil)))
    ⦃fun _ _ cost => ⟨rest ≤ cost⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  open_core_definition
  construct_region
  intro budget low high
  split
  · exact ⟨rest, budget, fun _ => le_rfl⟩
  · trivial

omit [Field (M.Carrier 0)] [DecidableEq (M.Carrier 0)] [SampleableType (M.Carrier 0)] in
/-- The verifier pays for one challenge per round. -/
theorem verifier_cost (values : M.Value vector) (claim : M.Value field) (rounds : Nat) :
    ⦃fun _ cost => ⟨rounds * (1 / (Fintype.card (M.Carrier 0) : ℝ≥0∞)) + 0 ≤ cost⟩⦄
      sumcheck.sumcheck.meaning M verifier
        (.cons () (.cons () (.cons values (.cons claim (.cons rounds .nil)))))
    ⦃fun _ _ cost => ⟨0 ≤ cost⟩; estack⟨fun _ _ _ => ⟨True⟩⟩⦄ := by
  open_core_definition
  construct_region with_invariants [fun remaining _ => fun _ cost =>
    ⟨remaining * (1 / (Fintype.card (M.Carrier 0) : ℝ≥0∞)) + 0 ≤ cost⟩]
  · intro budget
    refine le_trans (le_of_eq ?_) budget
    push_cast
    ring
  · intro _ cost budget
    simp

end Cost

/-! ### The endpoints

The two triples are the only inputs that depend on the protocol. Adequacy turns them into the
existing judgments. The verifier samples no secret, so one interface serves the interactive
experiment and the Fiat–Shamir transform. -/

/-- The verifier's side on a table, a claim and a round count. -/
local notation "game[" values ", " claim ", " rounds "]" =>
  Program.meaning M sumcheck.sumcheck verifier
    (Values.cons () (Values.cons () (Values.cons values (Values.cons claim
      (Values.cons rounds Values.nil)))))

/-- The charged reading of the verifier on a false claim, from the derived triple. -/
theorem verifier_charged {values : M.Value vector} {arity : Nat} (laws : Laws M values arity)
    (claim : M.Value field) (rounds : Nat) (within : rounds ≤ arity)
    (wrong : claim ≠ reference M values (empty M)) :
    (interface (model := M) .refused).Charged (boundedEscape (charge M))
      (fun _ out => out.get .here = false) game[values, claim, rounds] [] :=
  charged_of_triple (interface .refused) (boundedEscape (charge M))
    (boundedEscape_antitone (charge M)) (verifier_rejects laws claim rounds within) [] wrong

omit [Field (M.Carrier 0)] [DecidableEq (M.Carrier 0)] [SampleableType (M.Carrier 0)] in
/-- The pathwise cost of the verifier, from the derived cost triple. -/
theorem verifier_priced (values : M.Value vector) (claim : M.Value field) (rounds : Nat) :
    ChargedCostBound (interface (model := M) .refused) (charge M) game[values, claim, rounds] []
      (rounds * (1 / (Fintype.card (M.Carrier 0) : ℝ≥0∞))) :=
  costBound_of_triple (interface .refused) (charge M) (verifier_cost M values claim rounds) [] _
    (by simp)

/-- Interactive soundness of the imported verifier against a prover that sees every earlier
challenge: for a table with `arity` variables in a model that satisfies the laws, a claim that
differs from the reference at the empty point is accepted after `rounds ≤ arity` rounds with
probability at most `rounds / |F|`. -/
theorem interactive_soundness {values : M.Value vector} {arity : Nat} (laws : Laws M values arity)
    (claim : M.Value field) (rounds : Nat) (within : rounds ≤ arity)
    (wrong : claim ≠ reference M values (empty M))
    (strategy : ZkcSecurity.Interactive.Strategy (Event M.Value) (Message M) (Answer M)) :
    Pr{let result ← ZkcSecurity.Interactive.interact (interface .refused) strategy
        game[values, claim, rounds] [] []}[
      Accepted (fun out => out.get .here = true) result.1] ≤
      rounds * (1 / (Fintype.card (M.Carrier 0) : ℝ≥0∞)) := by
  have bound := ZkcSecurity.Interactive.soundness_accepted (interface .refused) strategy (charge M)
    (fun _ out => out.get .here = false) (fun out => out.get .here = true)
    (fun _ _ rejects accepted => Bool.noConfusion (rejects.symm.trans accepted))
    game[values, claim, rounds] [] (verifier_charged M laws claim rounds within wrong) _
    (verifier_priced M values claim rounds)
  exact bound

/-- The Fiat–Shamir transform of the imported verifier, run on a proof produced by any prover
with at most `queries` random-oracle queries, accepts such a claim with probability at most
`(queries + rounds) / |F|`. -/
theorem fiat_shamir_soundness [DecidableEq (Event M.Value)] {values : M.Value vector}
    {arity : Nat} (laws : Laws M values arity) (claim : M.Value field) (rounds : Nat)
    (within : rounds ≤ arity) (wrong : claim ≠ reference M values (empty M))
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Answer M))) (List (Message M)))
    (queries : Nat) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (fixedExperiment (interface .refused) game[values, claim, rounds] [] prover)).run' ∅}[
      Accepted (fun out => out.get .here = true) result.1] ≤
      (queries + rounds) * (1 / (Fintype.card (M.Carrier 0) : ℝ≥0∞)) := by
  have bound := soundness_charged
    (certificate (absorb := interface (model := M) .refused) (charge := charge M)
      (fun out => out.get .here = true) (Post := fun _ out => out.get .here = false)
      (fun _ _ rejects accepted => Bool.noConfusion (rejects.symm.trans accepted)))
    game[values, claim, rounds] []
    (certificate_doomed.mpr (verifier_charged M laws claim rounds within wrong)) _
    (verifier_priced M values claim rounds) prover
    (queries * (1 / (Fintype.card (M.Carrier 0) : ℝ≥0∞)))
    (worstCaseCostBound_of_isTotalQueryBound _
      (keyCharge_le (fun _ _ => le_rfl)) prover queries proverBound)
  simpa [add_mul] using bound

/-! ### A model that satisfies the laws

The laws are hypotheses about a model. The model below satisfies them for every table of
`2 ^ arity` scalars, so the statements above are not vacuous and they apply to the multilinear
extension of a table. Its scalars are the elements of a field and its vectors are lists, with
the field's own arithmetic. Restricting a table to a point fixes one variable per coordinate:
each pair of neighbours becomes its value on the line through them. -/

section Folding

variable {F : Type} [Field F]

/-- Fix the first variable of a table: each pair of neighbours gives its value on the line. -/
def fold : List F → F → List F
  | low :: high :: rest, r => ((1 - r) * low + r * high) :: fold rest r
  | _, _ => []

theorem fold_length : ∀ (table : List F) (r : F), (fold table r).length = table.length / 2
  | [], _ => by simp [fold]
  | [_], _ => by simp [fold]
  | low :: high :: rest, r => by
    simp only [fold, List.length_cons, fold_length rest r]
    omega

/-- The sum of a folded table is linear in the coordinate. -/
theorem sum_fold_line : ∀ (table : List F) (r : F),
    (fold table r).sum = (1 - r) * (fold table 0).sum + r * (fold table 1).sum
  | [], r => by simp [fold]
  | [_], r => by simp [fold]
  | low :: high :: rest, r => by
    simp only [fold, List.sum_cons, sum_fold_line rest r]
    ring

/-- A table of even length is the two tables that fix its first variable. -/
theorem sum_fold_split : ∀ (table : List F), table.length % 2 = 0 →
    (fold table 0).sum + (fold table 1).sum = table.sum
  | [], _ => by simp [fold]
  | [_], odd => by simp at odd
  | low :: high :: rest, even => by
    have rest_even : rest.length % 2 = 0 := by
      simp only [List.length_cons] at even
      omega
    simp only [fold, List.sum_cons, ← sum_fold_split rest rest_even]
    ring

theorem length_restrict : ∀ (point values : List F),
    (point.foldl fold values).length = values.length / 2 ^ point.length
  | [], values => by simp
  | r :: rest, values => by
    simp only [List.foldl_cons, length_restrict rest (fold values r), fold_length, List.length_cons,
      Nat.div_div_eq_div_mul, pow_succ]
    rw [Nat.mul_comm]

/-- A table of `2 ^ arity` entries restricted to fewer than `arity` coordinates has even
length: it has a further variable. -/
theorem even_restrict (values point : List F) (arity : Nat) (size : values.length = 2 ^ arity)
    (short : point.length < arity) : (point.foldl fold values).length % 2 = 0 := by
  rw [length_restrict, size, Nat.pow_div (Nat.le_of_lt short) (by norm_num)]
  obtain ⟨more, split⟩ : ∃ more, arity - point.length = more + 1 :=
    ⟨arity - point.length - 1, by omega⟩
  rw [split, pow_succ, Nat.mul_mod_left]

variable (F) [DecidableEq F]

/-- The carriers: scalars, vectors of scalars, and one-point carriers elsewhere. -/
def Carrier : Nat → Type
  | 0 => F
  | 1 => List F
  | _ + 2 => PUnit

def carrier : (row : Nat) → Carrier F row
  | 0 => (0 : F)
  | 1 => ([] : List F)
  | _ + 2 => PUnit.unit

/-- A model of the package's rows over a field: the field's arithmetic, lists, and the
restriction of a table by folding. A row of another number or signature returns a value of each
of its output types. -/
def foldModel : Model where
  Carrier := Carrier F
  pure row := match row with
    | ⟨1, [.nominal 1], [.index]⟩ => fun arguments =>
        .cons (List.length (α := F) (arguments.get .here)) .nil
    | ⟨7, [.nominal 0, .nominal 0], [.nominal 0]⟩ => fun arguments =>
        .cons (id (α := F) (arguments.get .here) + id (α := F) (arguments.get (.there .here))) .nil
    | ⟨8, [.nominal 0, .nominal 0], [.nominal 0]⟩ => fun arguments =>
        .cons (id (α := F) (arguments.get .here) - id (α := F) (arguments.get (.there .here))) .nil
    | ⟨9, [.nominal 0, .nominal 0], [.nominal 0]⟩ => fun arguments =>
        .cons (id (α := F) (arguments.get .here) * id (α := F) (arguments.get (.there .here))) .nil
    | ⟨10, [.nominal 0, .nominal 0], [.bool]⟩ => fun arguments =>
        .cons (decide (id (α := F) (arguments.get .here) =
          id (α := F) (arguments.get (.there .here)))) .nil
    | ⟨11, [], [.nominal 1]⟩ => fun _ => .cons ([] : List F) .nil
    | ⟨12, [.nominal 1, .nominal 0], [.nominal 1]⟩ => fun arguments =>
        .cons (id (α := List F) (arguments.get .here) ++
          [id (α := F) (arguments.get (.there .here))]) .nil
    | ⟨13, [.nominal 1, .nominal 1], [.nominal 1]⟩ => fun arguments =>
        .cons (List.foldl fold (id (α := List F) (arguments.get .here))
          (id (α := List F) (arguments.get (.there .here)))) .nil
    | ⟨14, [.nominal 1], [.nominal 0]⟩ => fun arguments =>
        .cons (List.sum (α := F) (arguments.get .here)) .nil
    | row => fun _ => Ty.inhabitants (carrier F) row.outputs
  «partial» _ _ := .error .abort

instance : Field ((foldModel F).Carrier 0) := inferInstanceAs (Field F)
instance : DecidableEq ((foldModel F).Carrier 0) := inferInstanceAs (DecidableEq F)
instance [Fintype F] : Fintype ((foldModel F).Carrier 0) := inferInstanceAs (Fintype F)
instance [SampleableType F] : SampleableType ((foldModel F).Carrier 0) :=
  inferInstanceAs (SampleableType F)

/-- The model satisfies the laws for every table of `2 ^ arity` scalars. -/
theorem fold_laws (values : List F) (arity : Nat) (size : values.length = 2 ^ arity) :
    Laws (foldModel F) values arity where
  add _ _ := rfl
  sub _ _ := rfl
  mul _ _ := rfl
  equal a b := by
    show decide (id (α := F) a = id (α := F) b) = true ↔ a = b
    exact decide_eq_true_iff
  length_empty := rfl
  length_append point r := by
    show List.length (id (α := List F) point ++ [id (α := F) r]) =
      List.length (id (α := List F) point) + 1
    exact List.length_append
  split point short := by
    show (List.foldl fold values (id (α := List F) point)).sum =
      (List.foldl fold values (id (α := List F) point ++ [(0 : F)])).sum +
        (List.foldl fold values (id (α := List F) point ++ [(1 : F)])).sum
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact (sum_fold_split _ (even_restrict values point arity size short)).symm
  line point r short := by
    show (List.foldl fold values (id (α := List F) point ++ [id (α := F) r])).sum =
      (1 - id (α := F) r) * (List.foldl fold values (id (α := List F) point ++ [(0 : F)])).sum +
        id (α := F) r * (List.foldl fold values (id (α := List F) point ++ [(1 : F)])).sum
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact sum_fold_line _ _

/-- The interactive bound at this model, with no hypothesis left: the imported verifier, run on
a table of `2 ^ arity` scalars for `arity` rounds against any strategy, accepts a claim that is
not the sum of the table with probability at most `arity / |F|`. -/
theorem table_soundness [Fintype F] [SampleableType F] (values : List F) (arity : Nat)
    (size : values.length = 2 ^ arity) (claim : F) (wrong : claim ≠ values.sum)
    (strategy : ZkcSecurity.Interactive.Strategy (Event (foldModel F).Value)
      (Message (foldModel F)) (Answer (foldModel F))) :
    Pr{let result ← ZkcSecurity.Interactive.interact (interface .refused) strategy
        (sumcheck.sumcheck.meaning (foldModel F) verifier
          (.cons () (.cons () (.cons values (.cons claim (.cons arity .nil)))))) [] []}[
      Accepted (fun out => out.get .here = true) result.1] ≤
      arity * (1 / (Fintype.card F : ℝ≥0∞)) :=
  interactive_soundness (foldModel F) (fold_laws F values arity size) claim arity le_rfl wrong
    strategy

end Folding

end

end Zkc.Tests.Verification.Core.Sumcheck

#print axioms Zkc.Tests.Verification.Core.Sumcheck.interactive_soundness
#print axioms Zkc.Tests.Verification.Core.Sumcheck.fiat_shamir_soundness
#print axioms Zkc.Tests.Verification.Core.Sumcheck.table_soundness
