import ZkcExamples.StructuredPrograms

/-! Kernel-checked integration controls for authored mathematical regions.
The reply tape is an independent test handler, not an honesty assumption.
No test establishes native correspondence or cryptographic security.
-/

set_option autoImplicit false

namespace StructuredProgramsTests
open PIR Zkc.Source ZkcExamples.StructuredPrograms

local macro "vals[" xs:term,* "]" : term => do
  let mut result ← `(Values.nil)
  for x in xs.getElems.reverse do
    result ← `(Values.cons $x $result)
  return result

inductive Event where
  | received (channel reply : Nat)
  | sent (channel payload : Nat)
  | failedSend (channel payload : Nat)
  | missing (channel : Nat)
  deriving DecidableEq, Repr

structure Tape where
  replies : List Nat
  calls : Nat := 0
  deriving DecidableEq, Repr

def handler : Handler interface Tape Event
  | .receive channel, ⟨[], calls⟩ =>
      ⟨.stopped .incomplete, ⟨[], calls + 1⟩, [.missing channel]⟩
  | .receive channel, ⟨reply :: rest, calls⟩ =>
      ⟨.returned reply, ⟨rest, calls + 1⟩, [.received channel reply]⟩
  | .send channel payload, ⟨replies, calls⟩ =>
      ⟨.returned (), ⟨replies, calls + 1⟩, [.sent channel payload]⟩

def failingSendHandler : Handler interface Tape Event
  | .receive channel, state => handler (.receive channel) state
  | .send channel payload, ⟨replies, calls⟩ =>
      ⟨.stopped .abort, ⟨replies, calls + 1⟩, [.failedSend channel payload]⟩

def runOpening (xs ys : List Nat) (left right : Bool) (seed scale : Nat)
    (replies : List Nat) :=
  (opening.denote meaning (openingInputs xs ys left right seed scale).get).run handler ⟨replies, 0⟩

def runVerifier (base key challenge : Nat) (enabled : Bool) (audit : List Nat)
    (admitted : Bool) (replies : List Nat) :=
  (verifier.denote meaning (verifierInputs base key challenge enabled audit admitted).get).run
    handler ⟨replies, 0⟩

-- The seed and scale are different from each other and from the carried total.
theorem opening_success : runOpening [2, 3] [5, 7] true true 7 2 [69, 10, 21] =
    ⟨.returned vals[69, 7], ⟨[], 6⟩,
      [.received 0 69, .received 1 10, .sent 2 27, .received 1 21, .sent 2 69, .sent 3 69]⟩ := rfl

theorem opening_wrong_first_product : runOpening [2, 3] [5, 7] true true 7 2 [69, 9, 21] =
    ⟨.stopped .reject, ⟨[21], 2⟩, [.received 0 69, .received 1 9]⟩ := rfl

theorem opening_wrong_later_product :
    runOpening [2, 3, 4] [5, 7, 9] true true 7 2 [141, 10, 99, 36] =
    ⟨.stopped .reject, ⟨[36], 4⟩,
      [.received 0 141, .received 1 10, .sent 2 27, .received 1 99]⟩ := rfl

theorem opening_wrong_total : runOpening [2, 3] [5, 7] true true 7 2 [70, 10, 21] =
    ⟨.stopped .reject, ⟨[], 5⟩,
      [.received 0 70, .received 1 10, .sent 2 27, .received 1 21, .sent 2 69]⟩ := rfl

theorem opening_empty_seed : runOpening [] [] true true 7 99 [7, 123] =
    ⟨.returned vals[7, 7], ⟨[123], 2⟩, [.received 0 7, .sent 3 7]⟩ := rfl

theorem opening_empty_failed_admission : runOpening [] [] true false 7 99 [7, 123] =
    ⟨.stopped .exhausted, ⟨[123], 1⟩, [.received 0 7]⟩ := rfl

theorem opening_strict_zip_mismatch : runOpening [2] [5, 7] true true 7 2 [27, 10] =
    ⟨.stopped .refused, ⟨[10], 1⟩, [.received 0 27]⟩ := rfl

theorem opening_admission_before_mismatch : runOpening [] [5] true false 7 2 [7, 10] =
    ⟨.stopped .exhausted, ⟨[10], 1⟩, [.received 0 7]⟩ := rfl

theorem opening_first_admission_wins : runOpening [] [5] false false 7 2 [7] =
    ⟨.stopped .refused, ⟨[], 1⟩, [.received 0 7]⟩ := rfl

theorem opening_missing_reply_preserves_prefix : runOpening [2, 3] [5, 7] true true 7 2 [69, 10] =
    ⟨.stopped .incomplete, ⟨[], 4⟩,
      [.received 0 69, .received 1 10, .sent 2 27, .missing 1]⟩ := rfl

theorem opening_send_failure_preserves_post_state :
    (opening.denote meaning (openingInputs [2, 3] [5, 7] true true 7 2).get).run
      failingSendHandler ⟨[69, 10, 21], 0⟩ =
      ⟨.stopped .abort, ⟨[21], 3⟩,
        [.received 0 69, .received 1 10, .failedSend 2 27]⟩ := rfl

-- 11 * 2 = 7 + 5 * 3. Commitment and response remain distinct replies.
theorem verifier_success : runVerifier 2 3 5 true [] true [7, 11, 999] =
    ⟨.returned vals[11, 7, 5], ⟨[999], 5⟩,
      [.received 10 7, .sent 11 5, .received 12 11, .sent 13 11, .sent 14 7]⟩ := rfl

theorem verifier_independent_response_rejected : runVerifier 2 3 5 true [] true [7, 12, 999] =
    ⟨.stopped .reject, ⟨[999], 3⟩,
      [.received 10 7, .sent 11 5, .received 12 12]⟩ := rfl

theorem verifier_independent_commitment_rejected : runVerifier 2 3 5 true [] true [8, 11, 999] =
    ⟨.stopped .reject, ⟨[999], 3⟩,
      [.received 10 8, .sent 11 5, .received 12 11]⟩ := rfl

theorem verifier_disabled_callback_stops_suffix : runVerifier 2 3 5 false [] true [7, 11, 999] =
    ⟨.stopped .abort, ⟨[999], 3⟩,
      [.received 10 7, .sent 11 5, .received 12 11]⟩ := rfl

theorem verifier_unused_empty_admission : runVerifier 2 3 5 true [] false [7, 11] =
    ⟨.stopped .refused, ⟨[7, 11], 0⟩, []⟩ := rfl

theorem verifier_unused_nonempty_admission : runVerifier 2 3 5 true [42] false [7, 11] =
    ⟨.stopped .refused, ⟨[7, 11], 0⟩, []⟩ := rfl

theorem verifier_failed_challenge_send_prevents_receive :
    (verifier.denote meaning (verifierInputs 2 3 5 true [] true).get).run
      failingSendHandler ⟨[7, 11], 0⟩ =
      ⟨.stopped .abort, ⟨[11], 2⟩, [.received 10 7, .failedSend 11 5]⟩ := rfl

/-- A deliberately incorrect reference ignores the independently received
response and substitutes a value satisfying the equation in this instance. -/
def substitutedResponse : Proc interface (Values Value (Numbers 3)) :=
  .call (.receive 10) fun commitment =>
    .call (.send 11 5) fun _ =>
      .call (.receive 12) fun _ =>
        .call (.send 13 11) fun _ =>
          .call (.send 14 commitment) fun _ => .done vals[11, commitment, 5]

theorem independent_receive_counterexample :
    verifier.denote meaning (verifierInputs 2 3 5 true [] true).get ≠ substitutedResponse := by
  intro same
  have rejected := verifier_independent_response_rejected
  unfold runVerifier at rejected
  rw [same] at rejected
  have impossible := congrArg Execution.outcome rejected
  cases impossible

theorem discarded_admission_cannot_be_erased :
    verifier.denote meaning (verifierInputs 2 3 5 true [] false).get ≠
      verifier.denote meaning (verifierInputs 2 3 5 true [] true).get := by
  intro same
  have impossible := congrArg (fun process => (process.run handler ⟨[7, 11], 0⟩).outcome) same
  cases impossible

-- Zero results do not authorize removal of a checked domain constructor.
def zeroResultCheck : Region dialect [.boolean, .vector] [] :=
  .letOp (.admitVector .exhausted) vals[.here, .there .here] .nil (.ret vals[])

theorem zero_result_admitted :
    zeroResultCheck.denote meaning (vals[true, []] : Values Value [.boolean, .vector]).get =
      .done vals[] := rfl

theorem zero_result_rejected :
    zeroResultCheck.denote meaning (vals[false, []] : Values Value [.boolean, .vector]).get =
      .halt .exhausted := rfl

-- A generic zip fold can carry zero values and still execute stopping callbacks.
def zeroStateFold : Region dialect OpeningInputs [] :=
  .letOp (.zipFold [] [])
    vals[.here, .there .here, .there (.there .here), .there (.there (.there .here))]
    (.cons (.stop .abort) .nil) (.stop .reject)

theorem empty_zero_state_retains_admission :
    zeroStateFold.denote meaning (openingInputs [] [] true false 0 0).get =
      .halt .exhausted := rfl

theorem zero_state_callback_prevents_suffix :
    zeroStateFold.denote meaning (openingInputs [2] [3] true true 0 0).get =
      .halt .abort := rfl

theorem empty_zero_state_skips_callback :
    zeroStateFold.denote meaning (openingInputs [] [] true true 0 0).get =
      .halt .reject := rfl

-- The operation is also instantiated with two carried values and no captures.
-- Each reached item replaces the state by its ordered pair, exposing binding order.
def pairStateFold : Region dialect OpeningInputs [.number, .number] :=
  .letOp (.zipFold [.number, .number] [])
    vals[.here, .there .here, .there (.there .here), .there (.there (.there .here)),
      .there (.there (.there (.there .here))), .there (.there (.there (.there (.there .here))))]
    (.cons (.ret vals[.there (.there .here), .there (.there (.there .here))]) .nil)
    (.ret vals[.here, .there .here])

theorem multiple_fold_results_ordered :
    pairStateFold.denote meaning (openingInputs [2, 3] [5, 7] true true 11 13).get =
      .done vals[3, 7] := rfl

theorem multiple_fold_empty_seed_ordered :
    pairStateFold.denote meaning (openingInputs [] [] true true 11 13).get =
      .done vals[11, 13] := rfl

-- First failure wins even against a suffix with a different reason.
theorem stopped_binding_never_runs_suffix :
    (Region.bind (dialect := dialect) (Γ := []) (mid := []) (out := [])
      (.stop .exhausted) (.stop .abort)).denote meaning Values.nil.get =
      .halt .exhausted := rfl

-- Each branch has zero results; bind stores the common suffix exactly once.
def emptyBranch : Region dialect [.boolean] [] :=
  .letOp (.branch [] []) vals[.here]
    (.cons (.ret vals[]) (.cons (.ret vals[]) .nil)) (.ret vals[])

def repeatedBranches : Nat → Region dialect [.boolean] []
  | 0 => .ret vals[]
  | count + 1 => .bind emptyBranch (repeatedBranches count)

theorem emptyBranch_denote (env : Environment Value [.boolean]) :
    emptyBranch.denote meaning env = .done vals[] := by
  change (if env .here then Proc.done (vals[] : Values Value []) else Proc.done vals[]).bind _ = _
  split <;> rfl

theorem repeatedBranches_denote (count : Nat) (env : Environment Value [.boolean]) :
    (repeatedBranches count).denote meaning env = .done vals[] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (emptyBranch.denote meaning env).bind _ = _
      rw [emptyBranch_denote]
      exact ih

/-- Counts structural constructors, not allocation, execution time or native IR. -/
theorem repeatedBranches_linear_size (count : Nat) :
    (repeatedBranches count).nodeCount = 5 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [repeatedBranches, Region.nodeCount, emptyBranch, Regions.nodeCount, ih]
      omega

theorem repeatedBranches_stress_size : (repeatedBranches 64).nodeCount = 321 := by
  exact repeatedBranches_linear_size 64

theorem repeatedBranches_stress_result :
    (repeatedBranches 64).denote meaning (vals[false] : Values Value [.boolean]).get =
      .done vals[] := repeatedBranches_denote _ _

-- The contextual replacement is visible at the whole endpoint, under arbitrary
-- handlers and residual states, including stopping handlers.
theorem replacement_preserves_execution {S E : Type} (h : Handler interface S E)
    (state : S) (inputs : Values Value OpeningInputs) :
    (opening.denote meaning inputs.get).run h state =
      ((openingWith (openingStepWith true)).denote meaning inputs.get).run h state :=
  congrArg (fun process => process.run h state) (opening_contextual_replacement inputs.get)

#print axioms opening_correspondence
#print axioms verifier_correspondence
#print axioms opening_contextual_replacement
#print axioms independent_receive_counterexample
#print axioms discarded_admission_cannot_be_erased
#print axioms repeatedBranches_linear_size
#print axioms replacement_preserves_execution

end StructuredProgramsTests
