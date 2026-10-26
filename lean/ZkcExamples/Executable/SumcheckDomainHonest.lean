module

public import Zkc.Executable.DomainSuccessRules
public import ZkcExamples.Executable.SumcheckMetadata
public import ZkcExamples.Executable.SumcheckMessages
public import ZkcExamples.Executable.SumcheckHelpers
public import ZkcExamples.Construction.SumcheckDomainVerifier

@[expose] public section

/-! Honest messages succeed at the actual retained Domain round and loop. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckDomainHonest
open Zkc Zkc.Construction Zkc.Executable Zkc.Source Zkc.Source.Structured
open Zkc.Construction.Uniform Zkc.Construction.Uniform.DomainAdapter
open ZkcExamples.Construction.SumcheckDomainConnection
open Zkc.Polynomial.Multilinear
open SumcheckMessages (lowSum highSum)

variable {F G : Type} [Field F] [DecidableEq F]

/-- Occurrences are read from the admitted Entry's transcript templates. -/
abbrev transcript : SumcheckMessages.Transcript := SumcheckProof.transcript

abbrev messages (oracle : History F G → F) := SumcheckMessages.honestRounds transcript oracle

omit [Field F] [DecidableEq F] in
/-- Existing honest framing and messages, without an Instruction execution theorem. -/
theorem drawn_eq (history : History F G) (low high : F) :
    transcript.drawn history low high = history ++
      [.message (staticOrigin lowTemplate) (.field "bls12-381.fr" low),
       .message (staticOrigin highTemplate) (.field "bls12-381.fr" high), .challenge (staticOrigin drawTemplate)] := by
  simp only [SumcheckMessages.Transcript.drawn, List.append_assoc, List.cons_append, List.nil_append]
  rfl

omit [Field F] [DecidableEq F] in
theorem delivered_eq (history : History F G) (low high answer : F) :
    transcript.delivered history low high answer = history ++
      [.message (staticOrigin lowTemplate) (.field "bls12-381.fr" low),
       .message (staticOrigin highTemplate) (.field "bls12-381.fr" high), .challenge (staticOrigin drawTemplate),
       .message (staticOrigin deliveryTemplate) (.field "bls12-381.fr" answer)] := by
  simp only [SumcheckMessages.Transcript.delivered, drawn_eq, List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- Every required receive and mapped oracle reply succeeds on honest heads. -/
theorem round_passes (oracle : History F G → F) (initial : History F G) (index : Nat)
    (point : List F) (low high : F) (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix) (proof : Proof F G) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (roundState index point (low + high) history)
      (.field "bls12-381.fr" low :: .field "bls12-381.fr" high :: proof)
      (fun state unread =>
        let answer := oracle (transcript.drawn (initial ++ suffix) low high)
        state.point = point ++ [answer] ∧ state.scalar = (1 - answer) * low + answer * high ∧
        ∃ suffix', readbackHistory Origin.withoutCoordinates state.history = some suffix' ∧
          initial ++ suffix' = transcript.delivered (initial ++ suffix) low high answer ∧ unread = proof) := by
  have key : Origin.withoutCoordinates (roundDrawOrigin index) = staticOrigin drawTemplate := by
    rw [roundDrawOrigin_actual]
    exact (legacy_origins index).2.2.1
  have queried : query (m := Id) Origin.withoutCoordinates initial oracle
      (history ++
        [.message (Domain.atCoordinates (staticOrigin lowTemplate) [index]) (.field "bls12-381.fr" low),
         .message (Domain.atCoordinates (staticOrigin highTemplate) [index]) (.field "bls12-381.fr" high)])
      (roundDrawOrigin index) = .returned (oracle (transcript.drawn (initial ++ suffix) low high)) := by
    have result := query_draw (m := Id) Origin.withoutCoordinates initial oracle _
      (roundDrawOrigin index).entry (roundDrawOrigin index).event
      "bls12-381.fr" _ (mapped_messages history suffix mapped index low high)
    change query (m := Id) Origin.withoutCoordinates initial oracle _ (roundDrawOrigin index) =
      .returned (oracle (initial ++ _ ++ [.challenge (Origin.withoutCoordinates (roundDrawOrigin index))])) at result
    simpa only [key, drawn_eq, List.append_assoc, List.cons_append, List.nil_append] using result
  simp only [roundState, DomainVM.Passes, Value.decode, ite_true, queried,
    show Domain.drawRequest (roundDrawOrigin index) = true from rfl, true_and]
  refine ⟨suffix ++
    [.message (staticOrigin lowTemplate) (.field "bls12-381.fr" low),
     .message (staticOrigin highTemplate) (.field "bls12-381.fr" high),
     .challenge (staticOrigin drawTemplate),
     .message (staticOrigin deliveryTemplate)
       (.field "bls12-381.fr" (oracle (transcript.drawn (initial ++ suffix) low high)))], ?_, ?_, trivial⟩
  · rw [roundDrawOrigin_actual]
    simpa only [drawn_eq, List.append_assoc] using mapped_round history suffix mapped index low high
      (oracle (transcript.drawn (initial ++ suffix) low high))
  · rw [delivered_eq]
    simp only [drawn_eq, List.append_assoc]

/-- Expose the existing recursive round process as the shared ordered fold. -/
theorem reduce_eq_fold (indices : List Nat) (state : RoundState F G) :
    reduce indices state.point state.scalar state.history =
      Finite.fold (fun state index => roundState index state.point state.scalar state.history) indices state := by
  induction indices generalizing state with
  | nil => cases state; rfl
  | cons index rest ih =>
      simp only [reduce, Finite.fold]
      congr 1
      funext state
      exact ih state

/-- Honest fold invariant: the claim is the restricted table's sum and the
proof contains exactly the honest messages of the remaining rounds. -/
def Honest (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (indices : List Nat) (state : RoundState F G) (proof : Proof F G) : Prop :=
  state.point.length + indices.length = rounds ∧
  (restrictPrefixValues values state.point).length = 2 ^ indices.length ∧
  state.scalar = (restrictPrefixValues values state.point).sum ∧
  ∃ suffix, readbackHistory Origin.withoutCoordinates state.history = some suffix ∧
    proof = (messages oracle (initial ++ suffix) (restrictPrefixValues values state.point) indices.length).map
      (.field "bls12-381.fr")

/-- The actual round constructs the invariant at the next point from the two
honest half sums; no successful-execution premise is assumed. -/
theorem honest_step (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (index : Nat) (rest : List Nat) (state : RoundState F G) (proof : Proof F G)
    (honest : Honest oracle initial values rounds (index :: rest) state proof) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (roundState index state.point state.scalar state.history) proof
      (fun next unread => Honest oracle initial values rounds rest next unread) := by
  obtain ⟨length, shape, scalar, suffix, mapped, proofEq⟩ := honest
  let table := restrictPrefixValues values state.point
  have even : table.length % 2 = 0 := by rw [shape, List.length_cons, pow_succ]; simp
  have sumEq : table.sum = lowSum table + highSum table :=
    (List.sum_take_add_sum_drop table _).symm
  rw [scalar, sumEq, proofEq]
  simp only [messages, SumcheckMessages.honestRounds, List.length_cons, List.map_cons]
  apply DomainVM.Passes.mono Origin.withoutCoordinates initial oracle _ _ _ _ ?_
    (round_passes oracle initial index state.point (lowSum table) (highSum table)
      state.history suffix mapped _)
  intro next unread result
  obtain ⟨pointEq, scalarEq, suffix', mapped', historyEq, unreadEq⟩ := result
  refine ⟨?_, ?_, ?_, suffix', mapped', ?_⟩
  · simp only [pointEq, List.length_append, List.length_cons, List.length_nil] at length ⊢
    omega
  · rw [pointEq, restrictPrefixValues_append]
    exact restrictValues_length table _ (by rw [shape, List.length_cons, pow_succ, Nat.mul_comm])
  · rw [scalarEq, pointEq, restrictPrefixValues_append]
    exact (Zkc.Protocols.Sumcheck.Multilinear.restrictValues_sum table _ even).symm
  · rw [unreadEq, historyEq, pointEq, restrictPrefixValues_append]
    rfl

/-- The invariant composes for an arbitrary number and list of round indices. -/
theorem reduce_passes (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (indices : List Nat) (state : RoundState F G) (proof : Proof F G)
    (honest : Honest oracle initial values rounds indices state proof) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (reduce indices state.point state.scalar state.history) proof
      (fun next unread => Honest oracle initial values rounds [] next unread) := by
  rw [reduce_eq_fold]
  exact DomainVM.Passes.fold Origin.withoutCoordinates initial oracle _
    (Honest oracle initial values rounds)
    (fun index rest state proof => honest_step oracle initial values rounds index rest state proof)
    indices state proof honest

/-- The mathematical terminal check accepts the invariant's complete point. -/
theorem terminal_passes (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (small : rounds < 64) (shaped : values.length = 2 ^ rounds)
    (state : RoundState F G) (proof : Proof F G)
    (honest : Honest oracle initial values rounds [] state proof) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle (terminal values state) proof
      (fun returned unread => returned[0]? = some (.data (.boolean true)) ∧ unread = [] ∧
        ∃ history, returned = [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history] ∧
          ∃ suffix, readbackHistory Origin.withoutCoordinates history = some suffix) := by
  obtain ⟨length, shape, scalar, suffix, mapped, proofEq⟩ := honest
  simp only [List.length_nil, Nat.add_zero] at length
  have pointBound : state.point.length < indexLimit := by rw [length]; exact lt_trans small (by decide)
  have pointSmall : state.point.length < 64 := by omega
  have vectorBound : values.length < indexLimit := by rw [shaped]; exact SumcheckHelpers.indexLimit_pow small
  have decoded : (ofList? (0 + state.point.length) values).isSome :=
    (ofList?_isSome_iff values).mpr (by simpa only [Nat.zero_add, length] using shaped)
  obtain ⟨table, tableEq⟩ := Option.isSome_iff_exists.mp decoded
  have checked : Zkc.Protocols.Sumcheck.Multilinear.check (n := 0 + state.point.length) values
      (Zkc.Polynomial.Quadratic.point state.point.length
        (Zkc.Polynomial.coordinates state.point.length state.point) Fin.elim0) state.scalar = true := by
    rw [Zkc.Protocols.Sumcheck.Multilinear.check, tableEq, scalar,
      restrictPrefixValues_complete values state.point table tableEq, List.sum_singleton]
    simp
  simp only [terminal, pointBound, pointSmall, vectorBound, ite_true, checked, DomainVM.Passes]
  refine ⟨rfl, ?_, state.history, rfl, suffix, mapped⟩
  simp only [proofEq, messages, SumcheckMessages.honestRounds, List.length_nil, List.map_nil]

/-- Honest success of the retained all-input root, for every admitted round
count. The fold proof above is independent of the static maximum. -/
theorem root_passes (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (admitted : rounds ≤ ZkcExamples.Executable.SumcheckProof.maximum)
    (shaped : values.length = 2 ^ rounds) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (rootProcess values values.sum rounds [])
      ((messages oracle initial values rounds).map (.field "bls12-381.fr"))
      (fun returned unread => returned[0]? = some (.data (.boolean true)) ∧ unread = [] ∧
        ∃ history, returned = [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history] ∧
          ∃ suffix, readbackHistory Origin.withoutCoordinates history = some suffix) := by
  have bounded : rounds ≤ 2 := admitted
  have small : rounds < 64 := by omega
  rw [rootProcess, ite_eq_left bounded, DomainVM.Passes.bind]
  apply DomainVM.Passes.mono Origin.withoutCoordinates initial oracle _ _ _ _ ?_
    (reduce_passes oracle initial values rounds (List.range rounds) ⟨[], values.sum, []⟩ _ ?_)
  · intro state proof valid
    exact terminal_passes oracle initial values rounds small shaped state proof valid
  · exact ⟨by simp, by simpa only [restrictPrefixValues_nil, List.length_range] using shaped, rfl, [], rfl, by simp [restrictPrefixValues_nil]⟩

variable [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Transport any constructed successful retained root to its canonical Code
observation, preserving its postcondition and every unread message. -/
theorem of_root_passes (oracle : History F G → F) (initial : History F G)
    (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (uniformCarriers F G)) (proof : Proof F G)
    (holds : DomainVM.Environment F G → Proof F G → Prop)
    (passes : DomainVM.Passes Origin.withoutCoordinates initial oracle
      (rootProcess values claim rounds history) proof holds) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (DomainVM.observation ZkcExamples.Construction.SumcheckProof.program
        ZkcExamples.Construction.SumcheckProof.context
        (Code.instructions ZkcExamples.Executable.SumcheckProof.lowered.code)
        ZkcExamples.Executable.SumcheckProof.lowered.returned (frame values claim rounds history)) proof holds := by
  have instructions : Code.instructions ZkcExamples.Executable.SumcheckProof.lowered.code =
      ZkcExamples.Construction.SumcheckProof.participant.instructions := by
    rw [← Code.instructionList_eq]
    decide +kernel
  have returned : ZkcExamples.Executable.SumcheckProof.lowered.returned =
      ZkcExamples.Construction.SumcheckProof.participant.returned := by kernel_rfl
  rw [instructions, returned]
  apply DomainVM.Passes.participant_observation
  change DomainVM.Passes Origin.withoutCoordinates initial oracle (rootProjection values claim rounds history) _ _
  rw [root_projection]
  exact passes

/-- Real success at the canonical observation of the retained instructions. -/
theorem observation_passes (oracle : History F G → F) (initial : History F G)
    (values : List F) (rounds : Nat) (admitted : rounds ≤ ZkcExamples.Executable.SumcheckProof.maximum)
    (shaped : values.length = 2 ^ rounds) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (DomainVM.observation ZkcExamples.Construction.SumcheckProof.program
        ZkcExamples.Construction.SumcheckProof.context
        (Code.instructions ZkcExamples.Executable.SumcheckProof.lowered.code)
        ZkcExamples.Executable.SumcheckProof.lowered.returned (frame values values.sum rounds []))
      ((messages oracle initial values rounds).map (.field "bls12-381.fr"))
      (fun returned unread => returned[0]? = some (.data (.boolean true)) ∧ unread = [] ∧
        ∃ history, returned = [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history] ∧
          ∃ suffix, readbackHistory Origin.withoutCoordinates history = some suffix) := by
  exact of_root_passes oracle initial values values.sum rounds [] _ _
    (root_passes oracle initial values rounds admitted shaped)

end ZkcExamples.Executable.SumcheckDomainHonest
