module

public import ZkcExamples.Executable.SumcheckProof
public import Zkc.Executable.Completeness

@[expose] public section

/-! The charges of the executable Sumcheck verifier.

A run of the compiled Sumcheck validator charges at most `charge rounds`
instructions, `68 + 61 * rounds`, for a table of `2 ^ rounds` values, whatever
the claim, the proof and the challenge answers (`sufficient`); the honest run
charges exactly that. The charges are those of the reading
(`lowered_code`): the empty point's call, the loop's start, 39 per round (its
body, the point extension's call included, and its yield), the terminal check's
call and the return. The terminal check's body charges `62 + 22 * n` on a
well-shaped table and a point of `n` coordinates (`check_cost`): it checks the
table's shape, with a doubling loop of `n` iterations of three instructions,
twice, and folds the table over the point in `n` iterations of sixteen.
-/

set_option autoImplicit false

namespace ZkcExamples.Executable.SumcheckCharges
open Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Source.Structured
open ZkcExamples.Structured ZkcExamples.Structured.SumcheckHelperBodies
open ZkcExamples.Executable.SumcheckHelpers
open Zkc.Polynomial.Multilinear

abbrev validator : Validator := SumcheckProofProgramData.validator
abbrev participant : Participant := ZkcExamples.Construction.SumcheckProof.participant
abbrev context : Context := ZkcExamples.Construction.SumcheckProof.context

/-- The scalar field's domain. -/
abbrev scalar : String := "bls12-381.fr"

/-- The instructions a complete run charges for `rounds` rounds. -/
def charge (rounds : Nat) : Nat := 68 + 61 * rounds

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-! ## The terminal check's charges -/

section Check

/-- One installed operation that returns, with its exact charge. -/
local macro "charged_operation " evaluates:term : tactic =>
  `(tactic| apply Evaluated.ReturnsAfter.operation installed validator (by rfl) (by rfl) $evaluates (by rfl))

/-- A region whose condition is decided and whose branch returns `results`. -/
local macro "charged_cond " results:term : tactic =>
  `(tactic| apply Evaluated.ReturnsAfter.cond installed validator (results := $results) (by rfl) (by rfl)
    (length := by rfl))

/-- A Boolean constant. -/
local macro "charged_constant" : tactic =>
  `(tactic| apply Evaluated.ReturnsAfter.constant installed validator)

/-- A yield of found values. -/
local macro "charged_yield" : tactic =>
  `(tactic| exact Evaluated.ReturnsAfter.yield installed validator (by rfl))

/-- A loop over found bounds whose iterations return `results`. -/
local macro "charged_iterate " results:term : tactic =>
  `(tactic| apply Evaluated.ReturnsAfter.iterate installed validator (results := $results) (by rfl) (by rfl)
    (by rfl) (by rfl) (length := by rfl))

/-- The doubling loop of the authored shape check charges three instructions an
iteration. -/
theorem doubling_cost {first second two doubled carried induction : String}
    (carriedTwo : (carried == two) = false) (carriedInduction : (carried == induction) = false) :
    ∀ (count k start : Nat), k + count < 64 →
      (evalFor (fun env => evalSteps installed validator
          [.operation first "zkl_binding_0" [.text "2"] [] [two],
            .operation second "zkl_binding_6" [] [carried, two] [doubled], .yield [doubled]] env)
        induction [carried] [] (List.range' start count) [(.index (2 ^ k) : Value F G)]).ReturnsAfter
        [.index (2 ^ (k + count))] (3 * count)
  | 0, _, _, _ => Evaluated.ReturnsAfter.for_nil
  | count + 1, k, start, small => by
      have product : 2 ^ k * 2 < indexLimit := by
        rw [← pow_succ]
        exact indexLimit_pow (by omega)
      apply Evaluated.ReturnsAfter.of_eq
      · apply Evaluated.ReturnsAfter.for_cons (yielded := [.index (2 ^ k * 2)]) (length := rfl)
        · charged_operation (constant_returns 2)
          apply Evaluated.ReturnsAfter.operation installed validator (by rfl)
            (by simp [lookupAll, List.lookup, carriedTwo, carriedInduction])
            (mul_returns (indexLimit_pow (by omega)) (by decide) product) (by rfl)
          exact Evaluated.ReturnsAfter.yield installed validator (by simp [lookupAll, List.lookup])
        · rw [← pow_succ, show k + (count + 1) = k + 1 + count by omega]
          exact doubling_cost carriedTwo carriedInduction count (k + 1) (start + 1) (by omega)
      · omega

/-- The fold loop of the check charges sixteen instructions an iteration. -/
theorem restriction_cost (point : List F) (small : point.length < 64) :
    ∀ (count start : Nat) (current : List F), start + count = point.length →
      current.length = 2 ^ count →
      (evalFor (fun env => evalSteps installed validator restrictionBody env) "v180"
          ["v181", "v182", "v183"]
          [("v120", .vector "bls12-381.fr" point), ("v178", .index point.length)]
          (List.range' start count)
          [(.vector "bls12-381.fr" current : Value F G), .index count, .index 1]).ReturnsAfter
        [.vector "bls12-381.fr" (restrictPrefixValues current (point.drop start)), .index 0, .index 1]
        (16 * count)
  | 0, start, current, ends, _ => by
      have dropped : point.drop start = [] := List.drop_eq_nil_of_le (by omega)
      rw [dropped]
      exact Evaluated.ReturnsAfter.for_nil
  | count + 1, start, current, ends, shape => by
      have inside : start < point.length := by omega
      have bounded : 2 ^ count < indexLimit := indexLimit_pow (by omega)
      have doubled : current.length = 2 * 2 ^ count := by rw [shape, pow_succ, Nat.mul_comm]
      have sixtyFour : (64 : Nat) < indexLimit := by decide
      have countBound : count + 1 < indexLimit := by omega
      have positive : 0 < 2 ^ count := Nat.two_pow_pos count
      apply Evaluated.ReturnsAfter.of_eq
      · apply Evaluated.ReturnsAfter.for_cons (yielded := [.vector "bls12-381.fr"
          (List.zipWith (· + ·) (current.take (current.length / 2))
            ((List.zipWith (· - ·) (current.drop (current.length / 2)) (current.take (current.length / 2))).map
              (· * point[start]))), .index (count + 1 - 1), .index 1]) (length := rfl)
        · charged_operation (get_returns inside)
          charged_operation (constant_returns 0)
          charged_operation (less_true (a := 0) (by decide) countBound (by omega))
          charged_cond []
          · charged_yield
          charged_operation (split_returns (by omega) (by omega))
          charged_operation (length_returns (by simp only [List.length_take]; omega))
          charged_operation (length_returns (by simp only [List.length_drop]; omega))
          charged_operation (equal_true (by simp only [List.length_take, List.length_drop]; omega))
          charged_operation require_returns
          charged_operation (subtract_returns (by simp only [List.length_take, List.length_drop]; omega))
          charged_operation scale_returns
          charged_operation (add_returns (by
            simp only [List.length_take, List.length_drop, List.length_map, List.length_zipWith]; omega))
          charged_operation (constant_returns 1)
          charged_operation (sub_returns (b := 1) countBound (by decide) (by omega))
          charged_yield
        · rw [interpolate_eq, List.drop_eq_getElem_cons inside, restrictPrefixValues_cons]
          exact restriction_cost point small count (start + 1) (restrictValues current point[start]) (by omega)
            (restrictValues_length current point[start] doubled)
      · omega

/-- With a well-shaped table, the check charges `62 + 22 * n` instructions for a
point of `n` coordinates. -/
theorem check_shaped_cost {xs point : List F} {claim : F} (pointBound : point.length < indexLimit)
    (small : point.length < 64) (vectorBound : xs.length < indexLimit)
    (shaped : xs.length = 2 ^ point.length) :
    (evalSteps installed validator checkFunction.body (checkEnv (G := G) xs point claim)).ReturnsAfter
      [.data (.boolean (decide ((restrictPrefixValues xs point).foldl (· + ·) 0 = claim)))]
      (62 + 22 * point.length) := by
  apply Evaluated.ReturnsAfter.of_eq
  · charged_operation (length_returns pointBound)
    charged_operation (constant_returns 1)
    charged_operation (constant_returns 0)
    charged_operation (less_true (a := 0) (b := 1) (by decide) (by decide) (by decide))
    charged_cond [.data (.boolean true)]
    · charged_operation (constant_returns 64)
      charged_operation (less_true pointBound (by decide) small)
      charged_yield
    charged_cond [.data (.boolean true)]
    · charged_operation (length_returns vectorBound)
      charged_operation (mod_returns (b := 1) vectorBound (by decide) (by decide))
      charged_operation (constant_returns 0)
      charged_operation (equal_true (Nat.mod_one _))
      charged_yield
    charged_cond [.data (.boolean true)]
    · charged_operation (length_returns vectorBound)
      charged_operation (div_returns (b := 1) vectorBound (by decide) (by decide))
      charged_operation (constant_returns 64)
      charged_operation (less_true pointBound (by decide) small)
      charged_cond []
      · charged_yield
      charged_operation (constant_returns 1)
      charged_operation (constant_returns 0)
      charged_iterate [.index (2 ^ (0 + point.length))]
      · refine ⟨?_, ?_, ?_⟩ <;> omega
      · exact doubling_cost (count := point.length) (k := 0) (start := 0) (by decide) (by decide) (by omega)
      charged_operation (equal_true (by simpa using shaped))
      charged_yield
    charged_cond [.data (.boolean (decide ((restrictPrefixValues xs point).foldl (· + ·) 0 = claim)))]
    · charged_operation (length_returns pointBound)
      charged_operation (constant_returns 1)
      charged_operation (constant_returns 0)
      charged_operation (less_true (a := 0) (b := 1) (by decide) (by decide) (by decide))
      charged_cond [.data (.boolean true)]
      · charged_operation (constant_returns 64)
        charged_operation (less_true pointBound (by decide) small)
        charged_yield
      charged_cond [.data (.boolean true)]
      · charged_operation (length_returns vectorBound)
        charged_operation (mod_returns (b := 1) vectorBound (by decide) (by decide))
        charged_operation (constant_returns 0)
        charged_operation (equal_true (Nat.mod_one _))
        charged_yield
      charged_cond [.data (.boolean true)]
      · charged_operation (length_returns vectorBound)
        charged_operation (div_returns (b := 1) vectorBound (by decide) (by decide))
        charged_operation (constant_returns 64)
        charged_operation (less_true pointBound (by decide) small)
        charged_cond []
        · charged_yield
        charged_operation (constant_returns 1)
        charged_operation (constant_returns 0)
        charged_iterate [.index (2 ^ (0 + point.length))]
        · refine ⟨?_, ?_, ?_⟩ <;> omega
        · exact doubling_cost (count := point.length) (k := 0) (start := 0) (by decide) (by decide) (by omega)
        charged_operation (equal_true (by simpa using shaped))
        charged_yield
      charged_cond []
      · charged_yield
      charged_operation (length_returns pointBound)
      charged_operation (constant_returns 0)
      charged_iterate [.vector "bls12-381.fr" (restrictPrefixValues xs (point.drop 0)), .index 0, .index 1]
      · refine ⟨?_, ?_, ?_⟩ <;> omega
      · exact restriction_cost point small point.length 0 xs (by simp) shaped
      charged_operation sum_returns
      charged_operation fieldEqual_returns
      charged_yield
    exact Evaluated.ReturnsAfter.ret installed validator (by rfl)
  · omega

/-- The terminal check's charge on a well-shaped table: what the helper call
charges for its body. -/
theorem check_cost {xs point : List F} {claim : F} (small : point.length < 64)
    (shaped : xs.length = 2 ^ point.length) :
    helperCost installed validator checkHelper.name
      [(.vector "bls12-381.fr" xs : Value F G), .vector "bls12-381.fr" point,
        .data (.field "bls12-381.fr" claim)] = 62 + 22 * point.length := by
  have pointBound : point.length < indexLimit := lt_trans small (by decide)
  have vectorBound : xs.length < indexLimit := by
    rw [shaped]
    exact indexLimit_pow small
  have evaluated := check_shaped_cost (G := G) (claim := claim) pointBound small vectorBound shaped
  unfold helperCost Validator.evaluateCall
  rw [checkFunction_eq]
  simp only [show checkFunction.inputs.length = 3 from rfl, List.length_cons, List.length_nil]
  simp only [ite_true]
  have envEq : (checkFunction.inputs.map (·.1)).zip
      [(.vector "bls12-381.fr" xs : Value F G), .vector "bls12-381.fr" point,
        .data (.field "bls12-381.fr" claim)] = checkEnv xs point claim := rfl
  rw [envEq, evaluated]
  rfl

/-- The empty point's body charges two instructions. -/
theorem empty_cost : helperCost installed validator emptyHelper.name ([] : List (Value F G)) = 2 := rfl

/-- The point extension's body charges two instructions. -/
theorem append_cost (point : List F) (challenge : F) :
    helperCost installed validator appendHelper.name
      [(.vector "bls12-381.fr" point : Value F G), .data (.field "bls12-381.fr" challenge)] = 2 := rfl

end Check

/-! ## Helper calls on the ideal side -/

section Calls

/-- The empty point helper returns the empty vector. -/
theorem empty_call :
    callHelper (helperTable ZkcExamples.Construction.SumcheckProof.program F G) emptyHelper.name [] =
      .returned [.vector scalar []] := by
  rw [call_eq SumcheckSourceContracts.bodies.empty [] .nil rfl,
    SumcheckUnitContracts.empty_equation SumcheckSourceViews.unit.linked SumcheckSourceContracts.bodies]
  rfl

/-- The point extension helper appends the challenge to the point. -/
theorem append_call (point : List F) (challenge : F) :
    callHelper (helperTable ZkcExamples.Construction.SumcheckProof.program F G) appendHelper.name
      [.vector scalar point, .data (.field scalar challenge)] =
      .returned [.vector scalar (point ++ [challenge])] := by
  rw [call_eq SumcheckSourceContracts.bodies.append _ (.cons point (.cons challenge .nil)) rfl,
    SumcheckUnitContracts.append_equation SumcheckSourceViews.unit.linked SumcheckSourceContracts.bodies]
  rfl

end Calls

/-! ## The reading -/

/-- An instruction of the constructed validator: the empty point, the round loop
and the terminal check. -/
def topInstruction (index : Nat) : Zkc.Construction.Instruction :=
  participant.instructions.getD index ⟨.unsupported "", [], [], []⟩

/-- An instruction of the round loop's body. -/
def roundInstruction (index : Nat) : Zkc.Construction.Instruction :=
  (topInstruction 1).body.getD index ⟨.unsupported "", [], [], []⟩

/-- The round loop's site. -/
def roundSite : String :=
  match (topInstruction 1).operation with
  | .loop site _ _ => site
  | _ => ""

/-- The reading of one round: the constructed instructions with the charges of
the transparent calls that compute them. -/
def roundCode : List Code :=
  [.step (roundInstruction 0) 1, .charge 1, .step (roundInstruction 1) 1, .step (roundInstruction 2) 1,
    .step (roundInstruction 3) 1, .charge 1,
    .step (roundInstruction 4) 1, .charge 1, .step (roundInstruction 5) 1, .step (roundInstruction 6) 1,
    .step (roundInstruction 7) 1, .charge 1,
    .charge 1, .step (roundInstruction 8) 1, .step (roundInstruction 9) 1, .step (roundInstruction 10) 2,
    .charge 1,
    .charge 1, .step (roundInstruction 11) 1, .step (roundInstruction 12) 1, .step (roundInstruction 13) 1,
    .charge 1,
    .charge 1, .step (roundInstruction 14) 1, .step (roundInstruction 15) 1, .step (roundInstruction 16) 1,
    .charge 1,
    .helper (roundInstruction 17),
    .charge 1, .step (roundInstruction 18) 1, .step (roundInstruction 19) 1, .step (roundInstruction 20) 1,
    .step (roundInstruction 21) 1, .step (roundInstruction 22) 1, .charge 1]

/-- The reading of the executable validator. -/
def readingCode : List Code :=
  [.helper (topInstruction 0),
    .loop roundSite 2 [26, 31, 25] [2, 4, 1, 3] (topInstruction 1).results roundCode,
    .helper (topInstruction 2)]

set_option maxRecDepth 20000 in
/-- The reading the lowering rule computes, with the charge of every item. -/
theorem lowered_code : SumcheckProof.lowered.code = readingCode := by
  decide +kernel

/-! ## Every run fits -/

section Fits

/-- A calculation with one field result returns one field value. -/
theorem calculate_field {calculation : Calculation} {arguments values : List (Value F G)} {domain : String}
    (results : calculation.op.results = [.field domain])
    (computed : Zkc.Construction.calculate calculation arguments = .returned values) :
    ∃ value, values = [.data (.field domain value)] := by
  have length := calculate_length calculation computed
  rw [results] at length
  rcases values with _ | ⟨first, _ | ⟨_, _⟩⟩ <;> simp at length
  obtain ⟨value, encoded⟩ := calculate_sorted computed 0 first (.data (.field domain)) rfl (by rw [results]; rfl)
  exact ⟨value, by rw [← encoded]; rfl⟩

/-- A calculation with one result returns one value. -/
theorem calculate_one {calculation : Calculation} {arguments values : List (Value F G)}
    (results : calculation.op.results.length = 1)
    (computed : Zkc.Construction.calculate calculation arguments = .returned values) :
    ∃ value, values = [value] := by
  have length := calculate_length calculation computed
  rw [results] at length
  rcases values with _ | ⟨first, _ | ⟨_, _⟩⟩ <;> simp at length
  exact ⟨first, rfl⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A payload of a field type is a field element of that domain. -/
theorem payload_field {payload : Payload F G} {domain : String}
    (typed : payload.ty = .field domain) : ∃ value, payload = .field domain value := by
  cases payload with
  | boolean => simp [Payload.ty] at typed
  | field other value =>
      simp only [Payload.ty, Common.Native.Ty.field.injEq] at typed
      exact ⟨value, by rw [typed]⟩
  | group => simp [Payload.ty] at typed

abbrev table := helperTable ZkcExamples.Construction.SumcheckProof.program F G

/-- The data inputs and the host's transcript, followed by the empty point. -/
def outer (values : List F) (claim : F) (rounds : Nat) (initial : History F G) : List (Value F G) :=
  [.vector scalar values, .data (.field scalar claim), .index rounds, .transcript initial, .vector scalar []]

-- Following the reading step by step must not unfold the predicates.
attribute [local irreducible] Continues FitsK in
/-- One round charges 38 instructions before its yield, and hands on the point
extended by one challenge, a claim and a transcript. -/
theorem round_fits (budget : Nat) (values : List F) (claim : F) (rounds : Nat) (initial : History F G)
    (index : Nat) (point : List F) (current : F) (history : History F G) (proof : Proof F G) (used : Nat)
    (holds : List (Value F G) → Proof F G → Nat → Prop) (within : used + 38 ≤ budget)
    (finishes : ∀ (final : List (Value F G)) (unread : Proof F G) (challenge current' : F)
      (history' : History F G),
      read final [26, 31, 25] = some [.vector scalar (point ++ [challenge]), .data (.field scalar current'),
        .transcript history'] → holds final unread (used + 38)) :
    FitsK context table (helperCost installed validator) budget roundCode
      (outer values claim rounds initial ++
        .index index :: [.vector scalar point, .data (.field scalar current), .transcript history])
      proof used holds := by
  simp only [roundCode, roundInstruction, topInstruction, participant,
    ZkcExamples.Construction.SumcheckProof.participant,
    ZkcExamples.Construction.SumcheckProofParticipant.participant, List.getD_eq_getElem?_getD,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  -- The first round message.
  refine FitsK.step _ _ _ _ (by omega) ?_
  refine Continues.receive _ _ (common := .field scalar) rfl ?_
  rintro first unread₁ - typed₁
  obtain ⟨low, rfl⟩ := payload_field typed₁
  refine FitsK.charge _ _ _ _ (by omega) ?_
  refine FitsK.step _ _ _ _ (by omega) (Continues.indicesEmpty _ _ ?_)
  refine FitsK.step _ _ _ _ (by omega) (Continues.indicesAppend _ _ fun _ => ?_)
  refine FitsK.step _ _ _ _ (by omega) (Continues.observe _ _ ?_)
  rintro history₁ - - - - -
  refine FitsK.charge _ _ _ _ (by omega) ?_
  refine FitsK.step _ _ _ _ (by omega) ?_
  refine Continues.receive _ _ (common := .field scalar) rfl ?_
  rintro second unread₂ - typed₂
  obtain ⟨high, rfl⟩ := payload_field typed₂
  refine FitsK.charge _ _ _ _ (by omega) ?_
  refine FitsK.step _ _ _ _ (by omega) (Continues.indicesEmpty _ _ ?_)
  refine FitsK.step _ _ _ _ (by omega) (Continues.indicesAppend _ _ fun _ => ?_)
  refine FitsK.step _ _ _ _ (by omega) (Continues.observe _ _ ?_)
  rintro history₂ - - - - -
  refine FitsK.charge _ _ _ _ (by omega) ?_
  refine FitsK.charge _ _ _ _ (by omega) ?_
  refine FitsK.step _ _ _ _ (by omega) (Continues.calculate _ _ ?_)
  rintro sumArguments sum - computed
  obtain ⟨_, rfl⟩ := calculate_one rfl computed
  refine FitsK.step _ _ _ _ (by omega) (Continues.calculate _ _ ?_)
  rintro checkArguments checked - computed
  obtain ⟨_, rfl⟩ := calculate_one rfl computed
  refine FitsK.step _ _ _ _ (by omega) (Continues.guard _ _ ?_)
  rintro -
  refine FitsK.charge _ _ _ _ (by omega) ?_
  refine FitsK.charge _ _ _ _ (by omega) ?_
  refine FitsK.step _ _ _ _ (by omega) (Continues.indicesEmpty _ _ ?_)
  refine FitsK.step _ _ _ _ (by omega) (Continues.indicesAppend _ _ fun _ => ?_)
  refine FitsK.step _ _ _ _ (by omega) (Continues.challenge _ _ ?_)
  rintro history₃ origin₃ answer - -
  refine FitsK.charge _ _ _ _ (by omega) ?_
  refine FitsK.charge _ _ _ _ (by omega) ?_
  refine FitsK.step _ _ _ _ (by omega) (Continues.indicesEmpty _ _ ?_)
  refine FitsK.step _ _ _ _ (by omega) (Continues.indicesAppend _ _ fun _ => ?_)
  refine FitsK.step _ _ _ _ (by omega) (Continues.observe _ _ ?_)
  rintro history₄ origin₄ delivered - - -
  refine FitsK.charge _ _ _ _ (by omega) ?_
  -- The point extension.
  refine FitsK.helper _ _ _ _ (helper := appendHelper.name)
    (arguments := [(.vector scalar point : Value F G), .data (.field scalar answer)]) rfl ?read
    ?fits (Continues.call _ _ ?_)
  case read =>
    simp only [outer, Zkc.Construction.read, List.mapM_cons, List.mapM_nil, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
    rfl
  case fits => rw [append_cost]; omega
  intro arguments extended found called _
  obtain rfl : arguments = [.vector scalar point, .data (.field scalar answer)] := by
    simp only [outer, Zkc.Construction.read, List.mapM_cons, List.mapM_nil, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero] at found
    exact (Option.some.inj found).symm
  rw [append_call] at called
  cases called
  rw [append_cost]
  -- The claim update.
  refine FitsK.charge _ _ _ _ (by omega) ?_
  refine FitsK.step _ _ _ _ (by omega) (Continues.calculate _ _ ?_)
  rintro arguments₁ one - computed₁
  obtain ⟨_, rfl⟩ := calculate_one rfl computed₁
  refine FitsK.step _ _ _ _ (by omega) (Continues.calculate _ _ ?_)
  rintro arguments₂ difference - computed₂
  obtain ⟨_, rfl⟩ := calculate_one rfl computed₂
  refine FitsK.step _ _ _ _ (by omega) (Continues.calculate _ _ ?_)
  rintro arguments₃ lowPart - computed₃
  obtain ⟨_, rfl⟩ := calculate_one rfl computed₃
  refine FitsK.step _ _ _ _ (by omega) (Continues.calculate _ _ ?_)
  rintro arguments₄ highPart - computed₄
  obtain ⟨_, rfl⟩ := calculate_one rfl computed₄
  refine FitsK.step _ _ _ _ (by omega) (Continues.calculate _ _ ?_)
  rintro arguments₅ updated - computed₅
  obtain ⟨current', rfl⟩ := calculate_field rfl computed₅
  refine FitsK.charge _ _ _ _ (by omega) (FitsK.done _ _ _ _ ?_)
  apply finishes _ _ answer current' (history₄ ++ [.message origin₄ delivered])
  simp only [outer, Zkc.Construction.read, List.mapM_cons, List.mapM_nil, List.cons_append, List.nil_append,
    List.getElem?_cons_succ, List.getElem?_cons_zero]
  rfl

attribute [local irreducible] Continues FitsK in
/-- The rounds of the loop charge 39 instructions each, their yields included,
and hand on a point extended by one challenge per round. -/
theorem rounds_fits (budget : Nat) (values : List F) (claim : F) (rounds : Nat) (initial : History F G) :
    ∀ (count start : Nat) (point : List F) (current : F) (history : History F G) (proof : Proof F G)
      (used : Nat) (holds : List (Value F G) → Proof F G → Nat → Prop),
      used + 39 * count ≤ budget →
      (∀ (point' : List F) (current' : F) (history' : History F G) (unread : Proof F G),
        point'.length = point.length + count →
        holds [.vector scalar point', .data (.field scalar current'), .transcript history'] unread
          (used + 39 * count)) →
      FitsIterate budget (fun start unread used' holds' =>
          FitsK context table (helperCost installed validator) budget roundCode start unread used' holds')
        (outer values claim rounds initial) [26, 31, 25] (List.range' start count)
        [.vector scalar point, .data (.field scalar current), .transcript history] proof used holds
  | 0, _, point, current, history, proof, used, holds, _, finishes => by
      simpa [FitsIterate] using finishes point current history proof rfl
  | count + 1, start, point, current, history, proof, used, holds, within, finishes => by
      simp only [List.range'_succ, FitsIterate]
      apply round_fits budget values claim rounds initial start point current history proof used _ (by omega)
      intro final unread challenge current' history' found
      refine ⟨by omega, ?_⟩
      intro carried' readEq
      rw [found] at readEq
      cases readEq
      apply rounds_fits budget values claim rounds initial count (start + 1) (point ++ [challenge]) current'
        history' unread (used + 38 + 1) holds (by omega)
      intro point'' current'' history'' unread' length
      have same : used + 38 + 1 + 39 * count = used + 39 * (count + 1) := by ring
      rw [same]
      exact finishes point'' current'' history'' unread' (by simp at length; omega)

attribute [local irreducible] Continues FitsK in
/-- On a table of `2 ^ rounds` values, every run of the reading charges at most
`charge rounds` instructions, whatever the claim, the proof and the challenge
answers. -/
theorem sufficient (budget : Nat) (values : List F) (claim : F) (rounds : Nat) (initial : History F G)
    (proof : Proof F G) (shaped : values.length = 2 ^ rounds) (fits : charge rounds ≤ budget) :
    Sufficient context table (helperCost installed validator) budget SumcheckProof.lowered
      (ZkcExamples.Construction.SumcheckProof.inputs values claim rounds ++ [.transcript initial]) proof := by
  unfold Sufficient charge at *
  rw [lowered_code]
  simp only [readingCode, topInstruction, participant, ZkcExamples.Construction.SumcheckProof.participant,
    ZkcExamples.Construction.SumcheckProofParticipant.participant, List.getD_eq_getElem?_getD,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  -- The empty point.
  refine FitsK.helper _ _ _ _ (helper := emptyHelper.name) (arguments := ([] : List (Value F G))) rfl
    ?emptyRead
    ?emptyFits (Continues.call _ _ ?_)
  case emptyRead => rfl
  case emptyFits => rw [empty_cost]; omega
  intro arguments started found called _
  obtain rfl : arguments = [] := (Option.some.inj found).symm
  rw [empty_call] at called
  cases called
  rw [empty_cost]
  -- The round loop.
  refine FitsK.loop _ _ _ _ (bound := rounds)
    (carried := [.vector scalar [], .data (.field scalar claim), .transcript initial]) ?countEq ?initialEq ?_
  case countEq => rfl
  case initialEq => rfl
  intro bounded
  refine ⟨by omega, ?_⟩
  rw [List.range_eq_range']
  apply rounds_fits budget values claim rounds initial rounds 0 [] claim initial proof (0 + 1 + 2 + 1) _ (by omega)
  intro point current history unread length
  simp only [List.length_nil, Nat.zero_add] at length
  -- The terminal check.
  have checked := check_cost (G := G) (xs := values) (point := point) (claim := current) (by omega)
    (by rw [length]; exact shaped)
  refine FitsK.helper _ _ _ _ (helper := checkHelper.name)
    (arguments := [(.vector scalar values : Value F G), .vector scalar point, .data (.field scalar current)])
    rfl ?checkRead
    ?checkFits (Continues.call _ _ ?_)
  case checkRead => rfl
  case checkFits => rw [checked, length]; omega
  intro _ _ _ _ _
  rw [checked, length]
  exact FitsK.done _ _ _ _ (by omega)

end Fits
