module

public import ZkcExamples.Executable.SumcheckCharges
public import Zkc.Protocols.Sumcheck.Multilinear.Fold

@[expose] public section

/-! Honest-prover completeness of the executable Sumcheck verifier.

The honest producer of a Fiat–Shamir Sumcheck proof absorbs what the verifier
absorbs and draws what it draws: in each round it sends the sums of the low and
high halves of its current table, and then restricts the table at the challenge
the absorbed history determines (`honestRounds`). Its messages are framed and
encoded by a codec that the host's decoder inverts (`honestBytes`).

For every challenge function, every table of `2 ^ rounds` values with
`rounds ≤ 2`, its true sum as the claim, every initial transcript and expected
binding, host validation of the honest proof bytes accepts at every budget of at
least `charge rounds` (`honest_accepted`): 68, 129 and 190 instructions for
zero, one and two rounds. The proof composes the charge bound
(`SumcheckCharges.sufficient`) with `Zkc.Executable.validate_sufficient` and the
lowering rule, and evaluates the constructed validator's ideal meaning on the
decoded honest proof: each round check holds because the claim is the sum of the
current table, and the terminal check holds because the final claim is the sum of
the table restricted at the drawn point.
-/

set_option autoImplicit false

namespace ZkcExamples.Executable.SumcheckCompleteness
open Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Source.Structured
open ZkcExamples.Structured ZkcExamples.Structured.SumcheckHelperBodies
open ZkcExamples.Executable.SumcheckHelpers ZkcExamples.Executable.SumcheckCharges
open Zkc.Polynomial.Multilinear
open Zkc.Protocols.Sumcheck.Multilinear (restrictValues_sum)

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-! ## The honest producer -/

/-- The occurrence template of a round's observation or challenge. -/
def roundTemplate (index : Nat) : Template :=
  match roundInstruction index with
  | ⟨.observe _ template, _, _, _⟩ => template
  | ⟨.challenge _ _ template, _, _, _⟩ => template
  | _ => ⟨"", [], []⟩

/-- The occurrence a round's observation or challenge names under the Entry's
context. -/
def roundOrigin (index : Nat) : Origin := ((roundTemplate index).origin context).getD ⟨"", [], none⟩

theorem origin_of_isSome {template : Template} (present : (template.origin context).isSome = true) :
    template.origin context = some ((template.origin context).getD ⟨"", [], none⟩) := by
  cases found : template.origin context with
  | none => simp [found] at present
  | some origin => rfl

/-- Every round template names an occurrence. -/
theorem origin_eq (index : Nat) (present : ((roundTemplate index).origin context).isSome = true) :
    (roundTemplate index).origin context = some (roundOrigin index) :=
  origin_of_isSome present

theorem template_named : ((roundTemplate 3).origin context).isSome = true ∧
    ((roundTemplate 7).origin context).isSome = true ∧ ((roundTemplate 13).origin context).isSome = true ∧
    ((roundTemplate 16).origin context).isSome = true := by
  decide +kernel

/-- The history from which a round's challenge is drawn: the round's two
messages absorbed, and the challenge's occurrence. -/
def drawn (history : History F G) (low high : F) : History F G :=
  history ++ [.message (roundOrigin 3) (.field scalar low)] ++ [.message (roundOrigin 7) (.field scalar high)] ++
    [.challenge (roundOrigin 13)]

/-- The history after a round: its challenge delivered. -/
def delivered (history : History F G) (low high challenge : F) : History F G :=
  drawn history low high ++ [.message (roundOrigin 16) (.field scalar challenge)]

/-- The low half's sum of a table. -/
def lowSum (table : List F) : F := (table.take (table.length / 2)).sum

/-- The high half's sum of a table. -/
def highSum (table : List F) : F := (table.drop (table.length / 2)).sum

/-- The honest producer's messages for `count` rounds on the current table,
from the absorbed history: each round the sums of the table's halves, then the
table restricted at the challenge drawn from the history. -/
def honestRounds (oracle : History F G → F) : History F G → List F → Nat → List F
  | _, _, 0 => []
  | history, table, count + 1 =>
      lowSum table :: highSum table ::
        honestRounds oracle
          (delivered history (lowSum table) (highSum table) (oracle (drawn history (lowSum table) (highSum table))))
          (restrictValues table (oracle (drawn history (lowSum table) (highSum table)))) count

/-- The honest proof of a table's sum: its messages as field payloads. -/
def honestProof (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat) : Proof F G :=
  (honestRounds oracle initial values rounds).map (.field scalar)

/-! ## Calculations on field values -/

section Calculations

theorem calculate_add (a b : F) :
    Zkc.Construction.calculate (F := F) (G := G) (.fieldAdd scalar)
        [.data (.field scalar a), .data (.field scalar b)] = .returned [.data (.field scalar (a + b))] := by
  simp [Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op, Op.arguments,
    Calculation.evaluate]
  rfl

theorem calculate_sub (a b : F) :
    Zkc.Construction.calculate (F := F) (G := G) (.fieldSubtract scalar)
        [.data (.field scalar a), .data (.field scalar b)] = .returned [.data (.field scalar (a - b))] := by
  simp [Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op, Op.arguments,
    Calculation.evaluate]
  rfl

theorem calculate_mul (a b : F) :
    Zkc.Construction.calculate (F := F) (G := G) (.fieldMultiply scalar)
        [.data (.field scalar a), .data (.field scalar b)] = .returned [.data (.field scalar (a * b))] := by
  simp [Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op, Op.arguments,
    Calculation.evaluate]
  rfl

theorem calculate_equal (a b : F) :
    Zkc.Construction.calculate (F := F) (G := G) (.fieldEqual scalar)
        [.data (.field scalar a), .data (.field scalar b)] = .returned [.data (.boolean (decide (a = b)))] := by
  simp [Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op, Op.arguments,
    Calculation.evaluate]
  rfl

theorem calculate_one :
    Zkc.Construction.calculate (F := F) (G := G) (.fieldConstant scalar 1) [] =
      .returned [.data (.field scalar 1)] := by
  simp only [Zkc.Construction.calculate, decodeValues, Calculation.op, Op.arguments, Calculation.evaluate,
    Nat.cast_one]
  rfl

end Calculations

/-! ## The ideal meaning on the honest proof -/

section Ideal

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem id_bind {α β : Type} (value : α) (next : α → Id β) : (value >>= next : Id β) = next value := rfl

/-- One round of the constructed validator on the round's two messages: when
the claim is their sum, the round checks, draws its challenge from the absorbed
history, delivers it, extends the point and updates the claim. -/
theorem round_ideal (oracle : History F G → F) (values : List F) (claim : F) (rounds : Nat)
    (initial : History F G) (index : Nat) (point : List F) (current low high : F) (history : History F G)
    (rest : Proof F G) (sum : current = low + high) :
    ∃ final, read final [26, 31, 25] = some [.vector scalar (point ++ [oracle (drawn history low high)]),
        .data (.field scalar ((1 - oracle (drawn history low high)) * low + oracle (drawn history low high) * high)),
        .transcript (delivered history low high (oracle (drawn history low high)))] ∧
      ∀ (R : Type) (next : List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)),
        idealK (m := Id) context oracle table (topInstruction 1).body
            (outer values claim rounds initial ++
              .index index :: [.vector scalar point, .data (.field scalar current), .transcript history])
            (.field scalar low :: .field scalar high :: rest) next = next final rest := by
  simp only [topInstruction, participant, ZkcExamples.Construction.SumcheckProof.participant,
    ZkcExamples.Construction.SumcheckProofParticipant.participant, List.getD_eq_getElem?_getD,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  subst sum
  refine ⟨?final, ?read, fun R next => ?run⟩
  case run =>
    -- The round's two messages.
    refine (idealK_receive _ _ _ (common := .field scalar) rfl rfl).trans ?_
    refine (idealK_indicesEmpty _ _ _).trans ?_
    refine (idealK_indicesAppend _ _ _ (current := []) (appended := index) (by rfl) (by rfl)).trans ?_
    refine (idealK_observe _ _ _ (origin := roundOrigin 3) (by rfl) (origin_eq 3 template_named.1) (by rfl)).trans ?_
    refine (idealK_receive _ _ _ (common := .field scalar) rfl rfl).trans ?_
    refine (idealK_indicesEmpty _ _ _).trans ?_
    refine (idealK_indicesAppend _ _ _ (current := []) (appended := index) (by rfl) (by rfl)).trans ?_
    refine (idealK_observe _ _ _ (origin := roundOrigin 7) (by rfl) (origin_eq 7 template_named.2.1) (by rfl)).trans ?_
    -- The round check.
    refine (idealK_calculate _ _ _ (by rfl) (calculate_add low high)).trans ?_
    refine (idealK_calculate _ _ _ (by rfl) (calculate_equal (low + high) (low + high))).trans ?_
    refine (idealK_guard _ _ _ (by simp [outer])).trans ?_
    -- The challenge and its delivery.
    refine (idealK_indicesEmpty _ _ _).trans ?_
    refine (idealK_indicesAppend _ _ _ (current := []) (appended := index) (by rfl) (by rfl)).trans ?_
    refine (idealK_challenge _ _ _ (origin := roundOrigin 13) (by rfl) (origin_eq 13 template_named.2.2.1)).trans ?_
    simp only [id_bind]
    refine (idealK_indicesEmpty _ _ _).trans ?_
    refine (idealK_indicesAppend _ _ _ (current := []) (appended := index) (by simp [indicesAt, outer])
      (by simp [indexAt, outer])).trans ?_
    refine (idealK_observe _ _ _ (origin := roundOrigin 16) (history := drawn history low high)
      (payload := .field scalar (oracle (drawn history low high))) (by simp [transcriptAt, outer, drawn])
      (origin_eq 16 template_named.2.2.2) (by simp [dataAt, outer, drawn])).trans ?_
    -- The point extension and the claim update.
    refine (idealK_call _ _ _ (by simp [Zkc.Construction.read, outer, drawn])
      (append_call point (oracle (drawn history low high))) rfl).trans ?_
    refine (idealK_calculate _ _ _ (by simp [Zkc.Construction.read, outer, drawn]) calculate_one).trans ?_
    refine (idealK_calculate _ _ _ (by simp [Zkc.Construction.read, outer, drawn])
      (calculate_sub 1 (oracle (drawn history low high)))).trans ?_
    refine (idealK_calculate _ _ _ (by simp [Zkc.Construction.read, outer, drawn])
      (calculate_mul (1 - oracle (drawn history low high)) low)).trans ?_
    refine (idealK_calculate _ _ _ (by simp [Zkc.Construction.read, outer, drawn])
      (calculate_mul (oracle (drawn history low high)) high)).trans ?_
    refine (idealK_calculate _ _ _ (by simp [Zkc.Construction.read, outer, drawn])
      (calculate_add ((1 - oracle (drawn history low high)) * low) (oracle (drawn history low high) * high))).trans ?_
    exact rfl
  case read => simp [Zkc.Construction.read, delivered, drawn, outer]

theorem check_call {xs point : List F} {claim : F} (vectorBound : xs.length < indexLimit)
    (pointBound : point.length < indexLimit) :
    callHelper (helperTable ZkcExamples.Construction.SumcheckProof.program F G) checkHelper.name
        [.vector scalar xs, .vector scalar point, .data (.field scalar claim)] =
      .returned [.data (.boolean (decide (PrimitiveLibrary.HasShape xs point.length 1 ∧
        (restrictPrefixValues xs point).sum = claim)))] := by
  rw [call_eq SumcheckSourceAssociations.check_association _ (SumcheckHelperLaws.checkInputs xs point claim) rfl,
    SumcheckSourceContracts.check_equation xs point claim vectorBound pointBound]
  rfl

/-- The honest producer's rounds take the verifier from a point to the point
extended by the challenges, the claim to the sum of the table restricted there. -/
theorem rounds_ideal (oracle : History F G → F) (values : List F) (claim : F) (rounds : Nat)
    (initial : History F G) :
    ∀ (count start : Nat) (point : List F) (history : History F G) (rest : Proof F G),
      (restrictPrefixValues values point).length = 2 ^ count →
      ∃ (point' : List F) (history' : History F G), point'.length = point.length + count ∧
        ∀ (R : Type) (next : List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)),
        iterateM (fun start unread continuation =>
            idealK (m := Id) context oracle table (topInstruction 1).body start unread continuation)
          (outer values claim rounds initial) [26, 31, 25] (List.range' start count)
          [.vector scalar point, .data (.field scalar (restrictPrefixValues values point).sum), .transcript history]
          ((honestRounds oracle history (restrictPrefixValues values point) count).map (.field scalar) ++ rest)
          next =
        next [.vector scalar point', .data (.field scalar (restrictPrefixValues values point').sum),
          .transcript history'] rest
  | 0, _, point, history, rest, _ => ⟨point, history, rfl, fun _ _ => by simp [honestRounds, iterateM]⟩
  | count + 1, start, point, history, rest, shape => by
      set table := restrictPrefixValues values point with tableEq
      have even : table.length % 2 = 0 := by rw [shape, pow_succ]; simp
      obtain ⟨final, found, run⟩ := round_ideal oracle values claim rounds initial start point
        table.sum (lowSum table) (highSum table) history
        ((honestRounds oracle (delivered history (lowSum table) (highSum table)
            (oracle (drawn history (lowSum table) (highSum table))))
          (restrictValues table (oracle (drawn history (lowSum table) (highSum table)))) count).map
            (.field scalar) ++ rest)
        (by simp [lowSum, highSum, List.sum_take_add_sum_drop])
      set challenge := oracle (drawn history (lowSum table) (highSum table))
      have restricted : restrictPrefixValues values (point ++ [challenge]) = restrictValues table challenge := by
        rw [restrictPrefixValues_append]
        rfl
      have updated : (1 - challenge) * lowSum table + challenge * highSum table =
          (restrictPrefixValues values (point ++ [challenge])).sum := by
        rw [restricted, restrictValues_sum table challenge even]
        rfl
      have length : (restrictPrefixValues values (point ++ [challenge])).length = 2 ^ count := by
        rw [restricted]
        exact restrictValues_length table challenge (by rw [shape, pow_succ, Nat.mul_comm])
      obtain ⟨point', history', pointLength, iterated⟩ := rounds_ideal oracle values claim rounds initial count
        (start + 1) (point ++ [challenge]) (delivered history (lowSum table) (highSum table) challenge) rest
        length
      refine ⟨point', history', by simp at pointLength; omega, fun R next => ?_⟩
      simp only [List.range'_succ, iterateM, honestRounds, List.map_cons, List.cons_append]
      rw [run, found]
      simp only
      rw [updated, ← iterated R next, restricted]

/-- The constructed validator returns true on the honest proof of a table's
sum, and reads all of it. -/
theorem participant_instructions :
    participant.instructions =
      [topInstruction 0,
        ⟨.loop roundSite 2 [26, 31, 25], [2, 4, 1, 3], (topInstruction 1).results, (topInstruction 1).body⟩,
        topInstruction 2] := by
  decide +kernel

theorem participant_returned : participant.returned = [8, 7] := rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem outer_eq (values : List F) (claim : F) (rounds : Nat) (initial : History F G) :
    ZkcExamples.Construction.SumcheckProof.inputs values claim rounds ++ [.transcript initial] ++
      [.vector scalar []] = outer values claim rounds initial := rfl

theorem honest_run (oracle : History F G → F) (values : List F) (rounds : Nat) (admitted : rounds ≤ 2)
    (shaped : values.length = 2 ^ rounds) (initial : History F G) :
    ∃ history', ideal (m := Id) context oracle table participant.returned participant.instructions
        (ZkcExamples.Construction.SumcheckProof.inputs values values.sum rounds ++ [.transcript initial])
        (honestProof oracle initial values rounds) =
      (.returned [.data (.boolean true), .transcript history'], []) := by
  have small : rounds < 64 := by omega
  have vectorBound : values.length < indexLimit := by rw [shaped]; exact indexLimit_pow small
  obtain ⟨point, history, pointLength, iterated⟩ := rounds_ideal oracle values values.sum rounds initial rounds 0
    [] initial [] (by rw [show restrictPrefixValues values [] = values from rfl]; exact shaped)
  simp only [List.length_nil, Nat.zero_add] at pointLength
  refine ⟨history, ?_⟩
  unfold ideal honestProof
  rw [participant_instructions, participant_returned]
  refine (idealK_call _ _ _ (by rfl) empty_call rfl).trans ?_
  rw [outer_eq]
  refine (idealK_loop _ _ _ (bound := rounds)
    (carried := [.vector scalar [], .data (.field scalar values.sum), .transcript initial]) (by rfl) (by rfl)
    admitted).trans ?_
  rw [List.range_eq_range']
  have start := iterated (List (Value F G))
  simp only [show restrictPrefixValues values [] = values from rfl, List.append_nil] at start
  rw [start]
  refine (idealK_call _ _ _ (by simp [Zkc.Construction.read, outer])
    (check_call (xs := values) (point := point) (claim := (restrictPrefixValues values point).sum) vectorBound
      (by rw [pointLength]; exact lt_trans small (by decide))) rfl).trans ?_
  have shape : PrimitiveLibrary.HasShape values rounds 1 := by
    simp [PrimitiveLibrary.HasShape, shaped, small, Nat.mod_one]
  simp [idealK, finish, Zkc.Construction.read, outer, pointLength, shape]
  rfl

end Ideal




/-! ## Proof bytes -/

section Bytes

/-- A count's little-endian bytes. -/
def lengthBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | count + 1, value => UInt8.ofNat (value % 256) :: lengthBytes count (value / 256)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem lengthBytes_length : ∀ (count value : Nat), (lengthBytes count value).length = count
  | 0, _ => rfl
  | count + 1, value => by simp [lengthBytes, lengthBytes_length count]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem littleEndian_lengthBytes : ∀ (count value : Nat),
    littleEndian (lengthBytes count value) = value % 256 ^ count
  | 0, value => by simp [lengthBytes, littleEndian, Nat.mod_one]
  | count + 1, value => by
      rw [lengthBytes, littleEndian, littleEndian_lengthBytes count, UInt8.toNat_ofNat',
        show (2 : Nat) ^ 8 = 256 by norm_num, Nat.mod_mod, pow_succ', Nat.mod_mul]

/-- One length-framed message: its eight-byte little-endian length, then its
bytes. -/
def frame (payload : List UInt8) : List UInt8 := lengthBytes 8 payload.length ++ payload

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem readFrame_frame (payload rest : List UInt8) (short : payload.length ≤ proofLimit) :
    readFrame (frame payload ++ rest) = some (payload, rest) := by
  have small : payload.length < 256 ^ 8 := lt_of_le_of_lt short (by decide)
  have prefixEq : (frame payload ++ rest).take 8 = lengthBytes 8 payload.length := by
    simp [frame, lengthBytes_length]
  have suffixEq : (frame payload ++ rest).drop 8 = payload ++ rest := by
    simp [frame, lengthBytes_length]
  have lengthEq : littleEndian (lengthBytes 8 payload.length) = payload.length := by
    rw [littleEndian_lengthBytes, Nat.mod_eq_of_lt small]
  have enough : ¬ (payload ++ rest).length < payload.length := by simp
  unfold readFrame
  simp [lengthEq, frame, lengthBytes_length, short]

/-- The honest proof bytes: the framing magic, the expected binding and every
message framed after its encoding. -/
def honestBytes (encode : F → List UInt8) (binding : List UInt8) (messages : List F) : List UInt8 :=
  magic ++ binding ++ (messages.map fun value => frame (encode value)).flatten

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem decode_frames (decode : PhysicalType → List UInt8 → Option (Payload F G)) (encode : F → List UInt8)
    (roundtrip : ∀ value, decode SumcheckProof.coordinate (encode value) = some (.field scalar value))
    (bounded : ∀ value, (encode value).length ≤ proofLimit) :
    ∀ messages : List F,
      decodeProof decode (List.replicate messages.length SumcheckProof.coordinate)
        (messages.map fun value => frame (encode value)).flatten = messages.map (.field scalar)
  | [] => rfl
  | value :: messages => by
      simp only [List.length_cons, List.replicate_succ, List.map_cons, List.flatten_cons, decodeProof,
        readFrame_frame _ _ (bounded value), roundtrip, decode_frames decode encode roundtrip bounded messages]

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem honestRounds_length (oracle : History F G → F) :
    ∀ (history : History F G) (table : List F) (count : Nat),
      (honestRounds oracle history table count).length = 2 * count
  | _, _, 0 => rfl
  | history, table, count + 1 => by
      simp only [honestRounds, List.length_cons, honestRounds_length oracle _ _ count]
      ring

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem receives_eq {rounds : Nat} (admitted : rounds ≤ 2) :
    SumcheckProof.receives rounds = List.replicate (2 * rounds) SumcheckProof.coordinate := by
  unfold SumcheckProof.receives
  simp only [admitted, ite_true]
  clear admitted
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [List.replicate_succ, List.flatten_cons, ih, show 2 * (rounds + 1) = 2 + 2 * rounds by ring,
        List.replicate_add]
      rfl

end Bytes

/-! ## Completeness -/

/-- Honest-prover completeness of the executable Sumcheck verifier. For every
challenge function, codec whose decoder inverts its encoder on the round
messages, budget of at least `charge rounds`, expected binding, initial
transcript and table of `2 ^ rounds` values with at most two rounds, host
validation accepts the honest proof bytes of the table's sum. -/
theorem honest_accepted (oracle : History F G → F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (encode : F → List UInt8)
    (roundtrip : ∀ value, decode SumcheckProof.coordinate (encode value) = some (.field scalar value))
    (bounded : ∀ value, (encode value).length ≤ proofLimit) (budget : Nat) (binding : List UInt8)
    (bindingLength : binding.length = 32) (values : List F) (rounds : Nat) (admitted : rounds ≤ 2)
    (shaped : values.length = 2 ^ rounds) (initial : History F G) (fits : charge rounds ≤ budget) :
    validate (m := Id) installed SumcheckProof.validator context oracle decode budget binding
      ZkcExamples.Construction.SumcheckProof.acceptancePosition
      (ZkcExamples.Construction.SumcheckProof.inputs values values.sum rounds) initial
      (honestBytes encode binding (honestRounds oracle initial values rounds)) = true := by
  obtain ⟨reading, same, inputs, -⟩ := checkLowering_sound (F := F) (G := G) SumcheckProof.accepted
  have magicLength : magic.length = 8 := rfl
  have header : (honestBytes encode binding (honestRounds oracle initial values rounds)).take 40 =
      magic ++ binding := by
    simp [honestBytes, List.take_append, magicLength, bindingLength]
  have dropped : (honestBytes encode binding (honestRounds oracle initial values rounds)).drop 40 =
      ((honestRounds oracle initial values rounds).map fun value => frame (encode value)).flatten := by
    simp [honestBytes, List.drop_append, magicLength, bindingLength]
  have decoded : decodeProof decode (Plan.types (ZkcExamples.Construction.SumcheckProof.inputs (G := G) values
      values.sum rounds) SumcheckProof.lowered.plan)
      ((honestRounds oracle initial values rounds).map fun value => frame (encode value)).flatten =
      honestProof oracle initial values rounds := by
    rw [SumcheckProof.plan_types, receives_eq admitted, ← honestRounds_length oracle initial values rounds,
      decode_frames decode encode roundtrip bounded]
    rfl
  have enough : Sufficient context table (helperCost installed SumcheckProof.validator) budget SumcheckProof.lowered
      (ZkcExamples.Construction.SumcheckProof.inputs values values.sum rounds ++ [.transcript initial])
      (decodeProof decode (Plan.types (ZkcExamples.Construction.SumcheckProof.inputs (G := G) values values.sum
        rounds) SumcheckProof.lowered.plan)
        ((honestBytes encode binding (honestRounds oracle initial values rounds)).drop 40)) := by
    have base := sufficient (G := G) budget values values.sum rounds initial (honestProof oracle initial values rounds)
      shaped fits
    rw [dropped, decoded]
    exact base
  rw [validate_sufficient (m := Id) installed SumcheckProof.validator context oracle table decode budget _
    SumcheckProof.prepared reading binding _ _ initial _ (SumcheckProof.admitted values values.sum rounds) header
    enough]
  have sorted := admits_sorted (SumcheckProof.admitted (G := G) values values.sum rounds) initial
  rw [inputs] at sorted
  rw [dropped, decoded, same (m := Id) context oracle table SumcheckProof.helpersSorted _ sorted]
  obtain ⟨history, run⟩ := honest_run oracle values rounds admitted shaped initial
  change Accepts _ (idealObservation (ideal (m := Id) context oracle table participant.returned
    participant.instructions _ _)) = true
  rw [run]
  simp [Accepts, idealObservation, observation, Decision, selectedTrue,
    ZkcExamples.Construction.SumcheckProof.acceptancePosition_eq]

end ZkcExamples.Executable.SumcheckCompleteness
