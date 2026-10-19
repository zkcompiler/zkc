module

public import ZkcExamples.Executable.SumcheckShape
public import ZkcExamples.Structured.PrimitiveRows
public import Zkc.Executable.NormalizationSoundness
public import Zkc.Executable.Framing
public import Zkc.Executable.Installed
public import Zkc.Construction.Structured
public import Zkc.Protocols.Sumcheck.Multilinear.Fold

@[expose] public section

/-! The executable Sumcheck proof verifier, for every artifact of the family.

An `Artifact` is a compiled Sumcheck proof validator: its constructed validator
and executable program, their deployment context and admitted original, and the
per-compile facts the kernel checks for it: the lowering rule's acceptance, the
family's shape (`SumcheckShape`) with the Entry's static maximum, the reading's
code and receive plan, and the helper meanings and preparation the original's
helper table gives. Nothing in this module depends on the maximum or on the
artifact's names.

One statement describes a round (`round_passes`): on every proof and under every
answer a relation admits, the round either stops (refused when its two messages
are not scalar coordinates, rejected when their sum is not the claim) or passes
on to the point extended by the drawn answer, the claim updated by the answer
and the transcript with both messages, the challenge and its delivery absorbed.
The charge bound and honest completeness both follow from it:

* `sufficient`: a run on a table of `2 ^ rounds` values charges at most
  `charge rounds`, the empty point's call, the loop's entry, the rounds' charges
  computed from the reading (`roundCharge`, by evaluation) and their yields, the
  terminal check's call with what its body charges, and the return. The loop is
  bounded by `Zkc.Executable.FitsK.loop_invariant` with the invariant that the
  carried point has one coordinate per completed round;
* `honest_accepted`: for every round count up to the static maximum, host
  validation accepts the honest proof bytes of a table's sum. The honest rounds
  follow from the round statement with the answers of the challenge function and
  no stop (`Zkc.Executable.idealK_oracle`), composed by
  `Zkc.Executable.iterateM_invariant` with the fold invariant: the claim is the
  sum of the table restricted at the point;
* `prunes`: at every budget and with every framing header, host validation of
  proof bytes prunes the ideal acceptance of the decoded proof, which a
  soundness theorem about the constructed validator transfers through.
-/

set_option autoImplicit false

namespace ZkcExamples.Executable.SumcheckFamily
open Zkc.Construction Zkc.Executable Zkc.Source
open ZkcExamples.Executable.SumcheckShape
open Zkc.Polynomial.Multilinear
open Zkc.Protocols.Sumcheck.Multilinear (restrictValues_sum)
open ZkcExamples.Structured (PrimitiveLibrary.HasShape)

/-- A compiled Sumcheck proof validator of the family, with the facts the kernel
checks for it. -/
structure Artifact where
  validator : Validator
  participant : Participant
  context : Context
  program : Structured.Program
  lowered : Lowered
  accepted : checkLowering installed participant validator = .ok lowered
  names : Names
  maximum : Nat
  small : maximum < 64
  shape : participant.instructions = SumcheckShape.instructions names maximum
  code : lowered.code = SumcheckShape.code names maximum
  returned : participant.returned = [8, 7]
  sorts : participant.inputs = [.data (.vector names.scalar), .data (.field names.scalar), .data .index,
    .transcript names.suite]
  coordinate : PhysicalType
  plan : lowered.plan = [.loop 2 maximum [.receive coordinate, .receive coordinate]]
  admitted : ∀ {F G : Type} (values : List F) (claim : F) (rounds : Nat),
    validator.admits [(.vector names.scalar values : Value F G), .data (.field names.scalar claim), .index rounds] = true
  templates : (names.firstMessage.origin context).isSome ∧ (names.secondMessage.origin context).isSome ∧
    (names.draw.origin context).isSome ∧ (names.delivery.origin context).isSome
  emptyBound : helperBound validator names.emptyHelper = some 2
  roundCharges : (Code.charges (helperBound validator) (roundCode names)).isSome
  empty_call : ∀ {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G],
    callHelper (helperTable program F G) names.emptyHelper [] = .returned [.vector names.scalar []]
  append_call : ∀ {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (point : List F) (answer : F),
    callHelper (helperTable program F G) names.appendHelper [.vector names.scalar point, .data (.field names.scalar answer)] =
      .returned [.vector names.scalar (point ++ [answer])]
  check_call : ∀ {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (xs point : List F) (claim : F), xs.length < Structured.indexLimit → point.length < Structured.indexLimit →
    callHelper (helperTable program F G) names.checkHelper
        [.vector names.scalar xs, .vector names.scalar point, .data (.field names.scalar claim)] =
      .returned [.data (.boolean (decide (PrimitiveLibrary.HasShape xs point.length 1 ∧
        (restrictPrefixValues xs point).sum = claim)))]
  check_cost : ∀ {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (xs point : List F) (claim : F), point.length < 64 → xs.length = 2 ^ point.length →
    helperCost installed validator names.checkHelper
        [(.vector names.scalar xs : Value F G), .vector names.scalar point, .data (.field names.scalar claim)] =
      62 + 22 * point.length
  prepared : ∀ {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G],
    ∀ name ∈ Instruction.helpers participant.instructions, Prepared installed validator (helperTable program F G) name
  helpersSorted : ∀ {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G],
    ∀ call ∈ Instruction.callList participant.instructions, HelperSorted (helperTable program F G) call.1 call.2

namespace Artifact

variable (a : Artifact)

/-- The occurrence an occurrence template names under the artifact's context. -/
def origin (template : Template) : Origin := (template.origin a.context).getD ⟨"", [], none⟩

theorem origin_eq {template : Template} (present : (template.origin a.context).isSome) :
    template.origin a.context = some (a.origin template) := by
  unfold origin
  cases found : template.origin a.context with
  | none => simp [found] at present
  | some origin => rfl

/-- The data inputs: the table, the claim and the round count. -/
def inputs {F G : Type} (values : List F) (claim : F) (rounds : Nat) : List (Value F G) :=
  [.vector a.names.scalar values, .data (.field a.names.scalar claim), .index rounds]

theorem admits {F G : Type} (values : List F) (claim : F) (rounds : Nat) :
    a.validator.admits (a.inputs (G := G) values claim rounds) = true :=
  a.admitted values claim rounds

/-- The receive types of a run: two coordinates per admitted round. -/
def receives (rounds : Nat) : List PhysicalType :=
  if rounds ≤ a.maximum then (List.replicate rounds [a.coordinate, a.coordinate]).flatten else []

theorem plan_types {F G : Type} (data : List (Value F G)) (rounds : Nat) (count : data[2]? = some (.index rounds)) :
    Plan.types data a.lowered.plan = a.receives rounds := by
  rw [a.plan]
  unfold receives
  by_cases bounded : rounds ≤ a.maximum <;> simp [Plan.types, count, bounded]

/-- What a round charges, its yield excluded, by evaluation of the reading. -/
def roundCharge : Nat := (Code.charges (helperBound a.validator) (roundCode a.names)).getD 0

/-- What the terminal check's body charges on a point of `count` coordinates. -/
def checkCharge (count : Nat) : Nat := 62 + 22 * count

/-- What a complete run of `rounds` rounds charges: the empty point's call and
its body, the loop's entry, the rounds' charges and yields, the terminal check's
call and body, and the return. -/
def charge (rounds : Nat) : Nat :=
  1 + 2 + 1 + chargeSum (fun _ => a.roundCharge) 0 rounds + 1 + checkCharge rounds + 1

/-- The history from which a round's challenge is drawn: its two messages
absorbed, then the challenge's occurrence. -/
def drawn {F G : Type} (history : History F G) (low high : F) : History F G :=
  history ++ [.message (a.origin a.names.firstMessage) (.field a.names.scalar low)] ++
    [.message (a.origin a.names.secondMessage) (.field a.names.scalar high)] ++
    [.challenge (a.origin a.names.draw)]

/-- The history after a round: its challenge delivered. -/
def delivered {F G : Type} (history : History F G) (low high answer : F) : History F G :=
  a.drawn history low high ++ [.message (a.origin a.names.delivery) (.field a.names.scalar answer)]

end Artifact

/-! ## One round -/

section Round
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem calculate_add (domain : String) (x y : F) :
    Zkc.Construction.calculate (F := F) (G := G) (.fieldAdd domain)
        [.data (.field domain x), .data (.field domain y)] = .returned [.data (.field domain (x + y))] := by
  simp [Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op, Structured.Op.arguments,
    Calculation.evaluate]
  rfl

theorem calculate_sub (domain : String) (x y : F) :
    Zkc.Construction.calculate (F := F) (G := G) (.fieldSubtract domain)
        [.data (.field domain x), .data (.field domain y)] = .returned [.data (.field domain (x - y))] := by
  simp [Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op, Structured.Op.arguments,
    Calculation.evaluate]
  rfl

theorem calculate_mul (domain : String) (x y : F) :
    Zkc.Construction.calculate (F := F) (G := G) (.fieldMultiply domain)
        [.data (.field domain x), .data (.field domain y)] = .returned [.data (.field domain (x * y))] := by
  simp [Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op, Structured.Op.arguments,
    Calculation.evaluate]
  rfl

theorem calculate_equal (domain : String) (x y : F) :
    Zkc.Construction.calculate (F := F) (G := G) (.fieldEqual domain)
        [.data (.field domain x), .data (.field domain y)] = .returned [.data (.boolean (decide (x = y)))] := by
  simp [Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op, Structured.Op.arguments,
    Calculation.evaluate]
  rfl

theorem calculate_one (domain : String) :
    Zkc.Construction.calculate (F := F) (G := G) (.fieldConstant domain 1) [] =
      .returned [.data (.field domain 1)] := by
  simp only [Zkc.Construction.calculate, decodeValues, Calculation.op, Structured.Op.arguments, Calculation.evaluate,
    Nat.cast_one]
  rfl

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

variable (a : Artifact)

-- Following the round instruction by instruction must not unfold the predicates.
attribute [local irreducible] Passes PassesStep in
/-- One round, on every proof and under every answer `admitted` allows: it stops
refused when its two messages are not scalar coordinates and rejected when their
sum is not the claim; otherwise it passes on to the point extended by the drawn
answer, the claim updated by the answer and the transcript with the round
absorbed. -/
theorem round_passes (admitted : History F G → F → Prop) (stopped : PIR.Outcome Unit × Proof F G → Prop)
    (first second third fourth fifth : Value F G) (index : Nat) (point : List F) (current : F)
    (history : History F G) (proof : Proof F G) (post : List (Value F G) → Proof F G → Prop)
    (malformed : (∀ low high rest, proof ≠ .field a.names.scalar low :: .field a.names.scalar high :: rest) →
      ∀ unread, stopped (.stopped .refused, unread))
    (rejected : ∀ low high rest, proof = .field a.names.scalar low :: .field a.names.scalar high :: rest →
      current ≠ low + high → stopped (.stopped .reject, rest))
    (passes : ∀ low high rest answer, proof = .field a.names.scalar low :: .field a.names.scalar high :: rest →
      current = low + high → admitted (a.drawn history low high) answer →
      ∀ final, read final yielded = some [.vector a.names.scalar (point ++ [answer]),
          .data (.field a.names.scalar ((1 - answer) * low + answer * high)),
          .transcript (a.delivered history low high answer)] →
        post final rest) :
    Passes a.context (helperTable a.program F G) admitted stopped (roundBody a.names)
      [first, second, third, fourth, fifth, .index index, .vector a.names.scalar point,
        .data (.field a.names.scalar current), .transcript history] proof post := by
  have messageOne := a.origin_eq a.templates.1
  have messageTwo := a.origin_eq a.templates.2.1
  have drawOrigin := a.origin_eq a.templates.2.2.1
  have deliveryOrigin := a.origin_eq a.templates.2.2.2
  simp only [roundBody]
  -- The first message.
  refine Passes.cons _ _ (PassesStep.receive _ _ (common := .field a.names.scalar) rfl ?_ ?_ ?_)
  try simp only [List.cons_append, List.nil_append]
  · intro payload rest found typed
    refine malformed (fun low high rest' same => ?_) _
    rw [found] at same
    simp only [List.cons.injEq] at same
    rw [same.1] at typed
    exact typed rfl
  · intro found
    exact malformed (fun low high rest same => by rw [found] at same; cases same) _
  intro payload afterFirst found typed
  obtain ⟨low, rfl⟩ := payload_field typed
  refine Passes.cons _ _ (PassesStep.indicesEmpty _ _ ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.indicesAppend _ _ fun _ => ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.observe _ _ (history := history) (payload := .field a.names.scalar low)
    rfl messageOne rfl ?_)
  -- The second message.
  refine Passes.cons _ _ (PassesStep.receive _ _ (common := .field a.names.scalar) rfl ?_ ?_ ?_)
  try simp only [List.cons_append, List.nil_append]
  · intro payload rest found' typed'
    refine malformed (fun low' high rest' same => ?_) _
    rw [found, found'] at same
    simp only [List.cons.injEq] at same
    rw [same.2.1] at typed'
    exact typed' rfl
  · intro found'
    exact malformed (fun low' high rest same => by
      rw [found, found'] at same; simp only [List.cons.injEq] at same; exact List.cons_ne_nil _ _ same.2.symm) _
  intro payload rest found' typed'
  obtain ⟨high, rfl⟩ := payload_field typed'
  have proofEq : proof = .field a.names.scalar low :: .field a.names.scalar high :: rest := by rw [found, found']
  refine Passes.cons _ _ (PassesStep.indicesEmpty _ _ ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.indicesAppend _ _ fun _ => ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.observe _ _ (payload := .field a.names.scalar high) rfl messageTwo rfl ?_)
  try simp only [List.cons_append, List.nil_append]
  -- The round check.
  refine Passes.cons _ _ (PassesStep.calculate _ _ rfl (calculate_add a.names.scalar low high) ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.calculate _ _ rfl (calculate_equal a.names.scalar current (low + high)) ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.guard _ _ (decision := decide (current = low + high)) rfl ?_ ?_)
  try simp only [List.cons_append, List.nil_append]
  · intro failed
    exact rejected low high rest proofEq (by simpa using failed)
  intro checked
  have sum : current = low + high := by simpa using checked
  -- The challenge and its delivery.
  refine Passes.cons _ _ (PassesStep.indicesEmpty _ _ ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.indicesAppend _ _ fun _ => ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.draw _ _ rfl drawOrigin fun answer allowed => ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.indicesEmpty _ _ ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.indicesAppend _ _ fun _ => ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.observe _ _ (payload := .field a.names.scalar answer) rfl deliveryOrigin rfl ?_)
  try simp only [List.cons_append, List.nil_append]
  -- The point extension and the claim update.
  refine Passes.cons _ _ (PassesStep.call _ _ rfl (a.append_call point answer) rfl ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.calculate _ _ rfl (calculate_one a.names.scalar) ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.calculate _ _ rfl (calculate_sub a.names.scalar 1 answer) ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.calculate _ _ rfl (calculate_mul a.names.scalar (1 - answer) low) ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.calculate _ _ rfl (calculate_mul a.names.scalar answer high) ?_)
  try simp only [List.cons_append, List.nil_append]
  refine Passes.cons _ _ (PassesStep.calculate _ _ rfl
    (calculate_add a.names.scalar ((1 - answer) * low) (answer * high)) ?_)
  exact Passes.nil _ _ (passes low high rest answer proofEq sum allowed _ rfl)

end Round

/-! ## Charges -/

section Charges
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (a : Artifact)

theorem roundCharges_eq : Code.charges (helperBound a.validator) (roundCode a.names) = some a.roundCharge := by
  unfold Artifact.roundCharge
  cases found : Code.charges (helperBound a.validator) (roundCode a.names) with
  | none => have := a.roundCharges; rw [found] at this; cases this
  | some charge => rfl

/-- What carried values look like after `count` rounds: a point of `count`
coordinates, a claim and a transcript. -/
def Carried (count : Nat) (carried : List (Value F G)) (_ : Proof F G) : Prop :=
  ∃ point current history, carried = [.vector a.names.scalar point, .data (.field a.names.scalar current),
    .transcript history] ∧ point.length = count

attribute [local irreducible] Continues FitsK in
/-- On a table of `2 ^ rounds` values, every run of the reading charges at most
`charge rounds` instructions, whatever the claim, the proof and the challenge
answers. -/
theorem sufficient (budget : Nat) (values : List F) (claim : F) (rounds : Nat) (initial : History F G)
    (proof : Proof F G) (shaped : values.length = 2 ^ rounds) (fits : a.charge rounds ≤ budget) :
    Sufficient a.context (helperTable a.program F G) (helperCost installed a.validator) budget a.lowered
      (a.inputs values claim rounds ++ [.transcript initial]) proof := by
  unfold Sufficient Artifact.charge Artifact.checkCharge at *
  rw [a.code]
  simp only [SumcheckShape.code, emptyCall, checkCall]
  have emptyCost : helperCost installed a.validator a.names.emptyHelper ([] : List (Value F G)) ≤ 2 :=
    helperCost_le installed a.validator a.emptyBound []
  -- The empty point.
  refine FitsK.helper _ _ _ _ (helper := a.names.emptyHelper) (arguments := []) rfl rfl (by omega)
    (Continues.call _ _ ?_)
  intro arguments started found called _
  obtain rfl : arguments = [] := (Option.some.inj found).symm
  rw [a.empty_call] at called
  cases called
  -- The round loop.
  refine FitsK.loop_invariant _ _ _ _ (bound := rounds)
    (carried := [.vector a.names.scalar [], .data (.field a.names.scalar claim), .transcript initial]) rfl rfl
    (Carried (F := F) (G := G) a) (fun _ => a.roundCharge) ⟨[], claim, initial, rfl, rfl⟩ ?_ ?_ ?_
  · -- One round fits within its charge, by evaluation of the reading.
    intro index carried unread used inside carriedShape within
    obtain ⟨point, current, history, rfl, length⟩ := carriedShape
    refine FitsK.of_charges _ _ _ _ (bound := helperBound a.validator)
      (fun helper most arguments bounded => helperCost_le installed a.validator bounded arguments)
      (roundCode a.names) a.roundCharge _ unread used _ (roundCharges_eq a) within ?_
    rw [roundCode_instructions]
    exact round_passes a (fun _ _ => True) (fun _ => True) _ _ _ _ _ index point current history unread _
      (fun _ _ => trivial) (fun _ _ _ _ _ => trivial)
      (fun low high rest answer _ _ _ final readEq used' smaller =>
        ⟨smaller, fun carried' carriedEq => ⟨point ++ [answer], _, _, by rw [readEq] at carriedEq; exact
          (Option.some.inj carriedEq).symm, by simp [length]⟩⟩)
  · intro bounded
    have := a.small
    simp only [chargeSum_const] at fits ⊢
    omega
  · -- The terminal check.
    intro bounded carried' unread used' carriedShape smaller
    obtain ⟨point, current, history, rfl, length⟩ := carriedShape
    have small : point.length < 64 := by have := a.small; omega
    have checked := a.check_cost (F := F) (G := G) values point current small (by rw [length]; exact shaped)
    refine FitsK.helper _ _ _ _ (helper := a.names.checkHelper)
      (arguments := [.vector a.names.scalar values, .vector a.names.scalar point,
        .data (.field a.names.scalar current)]) rfl rfl ?_ (Continues.call _ _ ?_)
    · rw [checked, length]
      simp only [chargeSum_const] at fits smaller
      omega
    · intro _ _ _ _ _
      rw [checked, length]
      exact FitsK.done _ _ _ _ (by simp only [chargeSum_const] at fits smaller; omega)

end Charges

/-! ## Honest completeness -/

section Honest
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (a : Artifact)

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
          (a.delivered history (lowSum table) (highSum table) (oracle (a.drawn history (lowSum table) (highSum table))))
          (restrictValues table (oracle (a.drawn history (lowSum table) (highSum table)))) count

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem honestRounds_length (oracle : History F G → F) :
    ∀ (history : History F G) (table : List F) (count : Nat),
      (honestRounds a oracle history table count).length = 2 * count
  | _, _, 0 => rfl
  | history, table, count + 1 => by
      simp only [honestRounds, List.length_cons, honestRounds_length oracle _ _ count]
      ring

/-- The honest proof bytes: the framing magic, the expected binding and every
round message framed after its encoding. -/
def honestBytes (encode : F → List UInt8) (binding : List UInt8) (messages : List F) : List UInt8 :=
  messageBytes encode binding messages

/-- Carried values and the unread proof before round `index` of an honest run on
a table of `2 ^ rounds` values: the point of the challenges drawn so far, the sum
of the table restricted there as the claim, and the honest messages of the
remaining rounds. -/
def Honest (oracle : History F G → F) (values : List F) (rounds : Nat) (index : Nat)
    (carried : List (Value F G)) (proof : Proof F G) : Prop :=
  ∃ point history, carried = [.vector a.names.scalar point,
      .data (.field a.names.scalar (restrictPrefixValues values point).sum), .transcript history] ∧
    point.length = index ∧ (restrictPrefixValues values point).length = 2 ^ (rounds - index) ∧
    proof = (honestRounds a oracle history (restrictPrefixValues values point) (rounds - index)).map
      (.field a.names.scalar)

/-- One honest round, in `Id`: the claim is the sum of the current table, the
round passes on, and the fold invariant holds of what it carries. -/
theorem honest_round (oracle : History F G → F) (values : List F) (rounds : Nat)
    (first second third fourth fifth : Value F G) (index : Nat) (carried : List (Value F G)) (proof : Proof F G)
    (inside : index < rounds) (honest : Honest a oracle values rounds index carried proof) :
    ∃ final carried' unread, read final yielded = some carried' ∧
      Honest a oracle values rounds (index + 1) carried' unread ∧
      ∀ (R : Type) (next : List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)),
        idealK (m := Id) a.context oracle (helperTable a.program F G) (roundBody a.names)
            ([first, second, third, fourth, fifth] ++ .index (0 + index) :: carried) proof next =
          next final unread := by
  obtain ⟨point, history, rfl, length, shape, rfl⟩ := honest
  set table := restrictPrefixValues values point with tableEq
  obtain ⟨remaining, remainingEq⟩ : ∃ remaining, rounds - index = remaining + 1 := ⟨rounds - index - 1, by omega⟩
  rw [remainingEq] at shape
  have even : table.length % 2 = 0 := by rw [shape, pow_succ]; simp
  have passes := round_passes a (oracleAnswers oracle) (fun _ => False) first second third fourth fifth (0 + index)
    point table.sum history
    ((honestRounds a oracle history table (rounds - index)).map (.field a.names.scalar))
    (fun final unread => ∃ carried', read final yielded = some carried' ∧
      Honest a oracle values rounds (index + 1) carried' unread)
    (fun never _ => by
      rw [remainingEq] at never
      exact never _ _ _ rfl)
    (fun low high rest same different => by
      rw [remainingEq] at same
      simp only [honestRounds, List.map_cons, List.cons.injEq, Payload.field.injEq, true_and] at same
      apply different
      rw [← same.1, ← same.2.1]
      exact (List.sum_take_add_sum_drop table _).symm)
    (fun low high rest answer same _ drawnAnswer final readEq => by
      rw [remainingEq] at same
      simp only [honestRounds, List.map_cons, List.cons.injEq, Payload.field.injEq, true_and] at same
      obtain ⟨rfl, rfl, rfl⟩ := same
      simp only [oracleAnswers] at drawnAnswer
      subst drawnAnswer
      set answer := oracle (a.drawn history (lowSum table) (highSum table))
      have updated : (1 - answer) * lowSum table + answer * highSum table =
          (restrictPrefixValues values (point ++ [answer])).sum := by
        rw [restrictPrefixValues_append, show restrictPrefixValues table [answer] = restrictValues table answer from rfl,
          restrictValues_sum table answer even]
        rfl
      refine ⟨_, readEq, point ++ [answer], _, by rw [updated], ?_, ?_, ?_⟩
      · simp [length]
      · rw [restrictPrefixValues_append]
        rw [show rounds - (index + 1) = remaining by omega]
        exact restrictValues_length table _ (by rw [shape, pow_succ, Nat.mul_comm])
      · rw [restrictPrefixValues_append, show rounds - (index + 1) = remaining by omega]
        rfl)
  obtain ⟨final, unread, ⟨carried', readEq, honest'⟩, run⟩ :=
    idealK_oracle a.context (helperTable a.program F G) oracle (roundBody a.names) _ _ _ passes
  refine ⟨final, carried', unread, readEq, ?_, run⟩
  -- The claim the round hands on is the sum of the table restricted at the new point.
  obtain ⟨point', history', carriedEq, length', shape', unreadEq⟩ := honest'
  exact ⟨point', history', carriedEq, length', shape', unreadEq⟩

end Honest

section Run
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (a : Artifact)

theorem indexLimit_pow {k : Nat} (small : k < 64) : 2 ^ k < Structured.indexLimit :=
  Nat.pow_lt_pow_right (by decide) small

/-- The receive types of an admitted round count: two coordinates a round. -/
theorem receives_eq {rounds : Nat} (admitted : rounds ≤ a.maximum) :
    a.receives rounds = List.replicate (2 * rounds) a.coordinate := by
  unfold Artifact.receives
  simp only [admitted, ite_true]
  clear admitted
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [List.replicate_succ, List.flatten_cons, ih, show 2 * (rounds + 1) = 2 + 2 * rounds by ring,
        List.replicate_add]
      rfl

/-- The constructed validator returns true on the honest proof of a table's
sum, for every round count up to the static maximum, and reads all of it. -/
theorem honest_run (oracle : History F G → F) (values : List F) (rounds : Nat) (admitted : rounds ≤ a.maximum)
    (shaped : values.length = 2 ^ rounds) (initial : History F G) :
    ∃ history', ideal (m := Id) a.context oracle (helperTable a.program F G) a.participant.returned
        a.participant.instructions (a.inputs values values.sum rounds ++ [.transcript initial])
        ((honestRounds a oracle initial values rounds).map (.field a.names.scalar)) =
      (.returned [.data (.boolean true), .transcript history'], []) := by
  have small : rounds < 64 := lt_of_le_of_lt admitted a.small
  have vectorBound : values.length < Structured.indexLimit := by rw [shaped]; exact indexLimit_pow small
  obtain ⟨carried, unread, honest, run⟩ := iterateM_invariant
    (fun R start unread continuation =>
      idealK (m := Id) a.context oracle (helperTable a.program F G) (roundBody a.names) start unread continuation)
    [.vector a.names.scalar values, .data (.field a.names.scalar values.sum), .index rounds, .transcript initial,
      .vector a.names.scalar []] yielded (Honest a oracle values rounds) 0 rounds
    (fun index carried proof inside honest =>
      honest_round a oracle values rounds _ _ _ _ _ index carried proof inside honest)
    rounds 0 _ ((honestRounds a oracle initial values rounds).map (.field a.names.scalar)) (by omega)
    ⟨[], initial, rfl, rfl, by exact shaped, by simp; rfl⟩
  obtain ⟨point, history, rfl, pointLength, -, unreadEq⟩ := honest
  simp only [Nat.zero_add, Nat.sub_self, honestRounds, List.map_nil] at pointLength unreadEq
  subst unreadEq
  refine ⟨history, ?_⟩
  rw [a.shape, a.returned]
  unfold ideal
  simp only [SumcheckShape.instructions, emptyCall, checkCall]
  refine (idealK_call _ _ _ (by rfl) a.empty_call rfl).trans ?_
  refine (idealK_loop _ _ _ (bound := rounds)
    (carried := [.vector a.names.scalar [], .data (.field a.names.scalar values.sum), .transcript initial]) (by rfl)
    (by rfl) admitted).trans ?_
  rw [List.range_eq_range']
  refine (run (List (Value F G)) _).trans ?_
  refine (idealK_call _ _ _ (by rfl)
    (a.check_call values point (restrictPrefixValues values point).sum vectorBound
      (by rw [pointLength]; exact lt_trans small (by decide))) rfl).trans ?_
  have shape : PrimitiveLibrary.HasShape values rounds 1 := by
    simp [PrimitiveLibrary.HasShape, shaped, small, Nat.mod_one]
  simp [idealK, finish, Zkc.Construction.read, pointLength, shape]
  rfl

/-- Honest-prover completeness of the executable Sumcheck verifier, for every
round count up to the Entry's static maximum. For every challenge function,
codec whose decoder inverts its encoder on the round messages, budget of at
least `charge rounds`, expected binding and initial transcript, and table of
`2 ^ rounds` values, host validation accepts the honest proof bytes of the
table's sum. -/
theorem honest_accepted (oracle : History F G → F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (encode : F → List UInt8)
    (roundtrip : ∀ value, decode a.coordinate (encode value) = some (.field a.names.scalar value))
    (bounded : ∀ value, (encode value).length ≤ proofLimit) (budget : Nat) (binding : List UInt8)
    (bindingLength : binding.length = 32) (values : List F) (rounds : Nat) (admitted : rounds ≤ a.maximum)
    (shaped : values.length = 2 ^ rounds) (initial : History F G) (fits : a.charge rounds ≤ budget) :
    validate (m := Id) installed a.validator a.context oracle decode budget binding 0
      (a.inputs values values.sum rounds) initial
      (honestBytes encode binding (honestRounds a oracle initial values rounds)) = true := by
  obtain ⟨reading, same, inputs, -⟩ := checkLowering_sound (F := F) (G := G) a.accepted
  have header : (honestBytes encode binding (honestRounds a oracle initial values rounds)).take 40 = magic ++ binding :=
    messageBytes_header encode bindingLength (honestRounds a oracle initial values rounds)
  have dropped : (honestBytes encode binding (honestRounds a oracle initial values rounds)).drop 40 =
      messageFrames encode (honestRounds a oracle initial values rounds) :=
    messageBytes_body encode bindingLength (honestRounds a oracle initial values rounds)
  have decoded : decodeProof decode (Plan.types (a.inputs (G := G) values values.sum rounds) a.lowered.plan)
      (messageFrames encode (honestRounds a oracle initial values rounds)) =
      (honestRounds a oracle initial values rounds).map (.field a.names.scalar) := by
    rw [a.plan_types _ rounds rfl, receives_eq a admitted, ← honestRounds_length a oracle initial values rounds]
    exact decodeProof_messages decode a.coordinate encode (.field a.names.scalar) roundtrip bounded _
  have enough : Sufficient a.context (helperTable a.program F G) (helperCost installed a.validator) budget a.lowered
      (a.inputs values values.sum rounds ++ [.transcript initial])
      (decodeProof decode (Plan.types (a.inputs (G := G) values values.sum rounds) a.lowered.plan)
        ((honestBytes encode binding (honestRounds a oracle initial values rounds)).drop 40)) := by
    have base := sufficient a budget values values.sum rounds initial
      ((honestRounds a oracle initial values rounds).map (.field a.names.scalar)) shaped fits
    rw [dropped, decoded]
    exact base
  rw [validate_sufficient (m := Id) installed a.validator a.context oracle (helperTable a.program F G) decode budget _
    a.prepared reading binding _ _ initial _ (a.admits values values.sum rounds) header enough]
  have sorted := admits_sorted (a.admits (G := G) values values.sum rounds) initial
  rw [inputs] at sorted
  rw [dropped, decoded, same (m := Id) a.context oracle (helperTable a.program F G) a.helpersSorted _ sorted]
  obtain ⟨history, run⟩ := honest_run a oracle values rounds admitted shaped initial
  change Accepts _ (idealObservation (ideal (m := Id) a.context oracle (helperTable a.program F G)
    a.participant.returned a.participant.instructions _ _)) = true
  rw [run]
  simp [Accepts, idealObservation, observation, Decision, selectedTrue]

end Run

section Bytes
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (a : Artifact)

/-- For every challenge function in every lawful monad, decoder, budget,
framing header and acceptance position, host validation of proof bytes prunes,
by rejections, the constructed validator's ideal acceptance of the proof the
message bytes decode to at the artifact's receive types. -/
theorem prunes {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat) (binding : List UInt8)
    (acceptance : Nat) (values : List F) (claim : F) (rounds : Nat) (initial : History F G)
    (bytes : List UInt8) :
    Prunes (fun accepted => accepted = false)
      (validate installed a.validator a.context challenge decode budget binding acceptance
        (a.inputs values claim rounds) initial bytes)
      ((fun result => Accepts acceptance (idealObservation result)) <$>
        ideal a.context challenge (helperTable a.program F G) a.participant.returned a.participant.instructions
          (a.inputs values claim rounds ++ [.transcript initial])
          (decodeProof decode (a.receives rounds) (bytes.drop 40))) := by
  rw [← a.plan_types (a.inputs values claim rounds) rounds rfl]
  exact validate_prunes_export installed a.validator a.context challenge _ decode budget a.accepted a.prepared
    a.helpersSorted binding acceptance _ initial bytes (a.admits values claim rounds)

end Bytes

end ZkcExamples.Executable.SumcheckFamily
