module

public import ZkcExamples.Executable.SumcheckProof
public import ZkcExamples.Construction.SumcheckSourceConnection
public import ZkcExamples.Structured.SumcheckVerifierTerminal
public import Zkc.Construction.Uniform.ScalarCheckedBytes
public import Zkc.Executable.DomainSuccessRules

@[expose] public section

/-! Honest success is a property of the admitted source and its existing scalar
handler. The compiler connection below remains unrestricted on all inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Executable.SumcheckSourceHonest
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Executable
open Uniform Uniform.DomainAdapter
open ZkcExamples.Structured SumcheckVerifierLaws SumcheckSourceVerifier
attribute [local implicit_reducible] CheckedProtocol.signature
open Zkc.Polynomial.Multilinear SumcheckMessages

abbrev context := ZkcExamples.Construction.SumcheckProof.context
abbrev program := ZkcExamples.Construction.SumcheckProof.program

def transcript : SumcheckMessages.Transcript :=
  ⟨"bls12-381.fr", context.message (lowSite childContext) 0 1,
    context.message (highSite childContext) 0 1,
    context.query (challengeSite childContext) (.draw "bls12-381.fr"),
    context.message (deliverySite childContext) 1 0⟩

theorem transcript_identity : transcript = SumcheckProof.transcript := by kernel_rfl

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev viewRound (handle : Nat) (state : (List F × F) × Domain.History (uniformCarriers F G)) :=
  SourceProcess.sourceView context
    ((roundPresent (G := G) childContext handle state.1).interpret CommonAdapter.project) state.2

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Both honest receives, their absorption, the scalar draw and delivery occur
at the actual source sites and leave the exact supplied proof suffix. -/
theorem round_passes (oracle : History F G → F) (initial : History F G) (handle : Nat)
    (point : List F) (low high : F) (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory SourceProcess.legacyOrigin history = some suffix) (proof : Proof F G) :
    DomainVM.Passes SourceProcess.legacyOrigin initial oracle
      (viewRound handle ((point, low + high), history))
      (.field "bls12-381.fr" low :: .field "bls12-381.fr" high :: proof)
      (fun result unread =>
        let answer := oracle (transcript.drawn (initial ++ suffix) low high)
        result.1 = (point ++ [answer], (1 - answer) * low + answer * high) ∧
        ∃ suffix', readbackHistory SourceProcess.legacyOrigin result.2 = some suffix' ∧
          initial ++ suffix' = transcript.delivered (initial ++ suffix) low high answer ∧ unread = proof) := by
  let messages := history ++ [.message transcript.firstMessage (.field "bls12-381.fr" low)] ++
    [.message transcript.secondMessage (.field "bls12-381.fr" high)]
  have mappedMessages : readbackHistory SourceProcess.legacyOrigin messages =
      some (suffix ++ [.message transcript.firstMessage (.field "bls12-381.fr" low)] ++
        [.message transcript.secondMessage (.field "bls12-381.fr" high)]) :=
    SourceProcess.readback_message _ _ (SourceProcess.readback_message _ _ mapped _ (.field _ low)) _ (.field _ high)
  have queried := query_draw (m := Id) SourceProcess.legacyOrigin initial oracle messages
    transcript.draw.entry transcript.draw.event "bls12-381.fr" _ mappedMessages
  have queried' : query (m := Id) SourceProcess.legacyOrigin initial oracle messages transcript.draw =
      .returned (oracle (transcript.drawn (initial ++ suffix) low high)) := by
    simpa only [transcript, Context.query, Origin.query, SourceProcess.legacyOrigin,
      Transcript.drawn, List.append_assoc, bind, pure, Id.instMonad] using queried
  simp only [viewRound, roundPresent, PIR.Process.interpret, CommonAdapter.project, PIR.Process.bind,
    SourceProcess.sourceView, SourceProcess.receive, SourceProcess.query, SourceProcess.send, Payload.ofValue,
    DomainVM.Passes, Value.decode, ite_true]
  simp only [show childContext.roles 0 = 0 from rfl, show context.validator = 1 from rfl]
  change Domain.drawRequest transcript.draw = true ∧ _
  rw [show Domain.drawRequest transcript.draw = true from rfl]
  simp only [true_and]
  have queriedSource : query (m := Id) SourceProcess.legacyOrigin initial oracle
      (history ++ [.message (context.message (lowSite childContext) 0 1) (.field "bls12-381.fr" low)] ++
        [.message (context.message (highSite childContext) 0 1) (.field "bls12-381.fr" high)])
      (context.query (challengeSite childContext) (.draw "bls12-381.fr")) =
        .returned (oracle (transcript.drawn (initial ++ suffix) low high)) := queried'
  rw [queriedSource]
  refine ⟨rfl, suffix ++ [.message transcript.firstMessage (.field "bls12-381.fr" low)] ++
    [.message transcript.secondMessage (.field "bls12-381.fr" high)] ++ [.challenge transcript.draw] ++
      [.message transcript.delivery (.field "bls12-381.fr" (oracle (transcript.drawn (initial ++ suffix) low high)))],
      ?_, ?_, trivial⟩
  · exact SourceProcess.readback_message _ _
      (SourceProcess.readback_challenge _ _ mappedMessages _) _ (.field _ _)
  · simp only [Transcript.delivered, Transcript.drawn, show transcript.scalar = "bls12-381.fr" from rfl, List.append_assoc]

def Honest (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (items : List Unit) (state : (List F × F) × Domain.History (uniformCarriers F G)) (proof : Proof F G) : Prop :=
  state.1.1.length + items.length = rounds ∧
  (restrictPrefixValues values state.1.1).length = 2 ^ items.length ∧
  state.1.2 = (restrictPrefixValues values state.1.1).sum ∧
  ∃ suffix, readbackHistory SourceProcess.legacyOrigin state.2 = some suffix ∧
    proof = (honestRounds transcript oracle (initial ++ suffix) (restrictPrefixValues values state.1.1) items.length).map
      (.field "bls12-381.fr")

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem honest_step (oracle : History F G → F) (initial : History F G) (values : List F) (rounds handle : Nat)
    (rest : List Unit) (state : (List F × F) × Domain.History (uniformCarriers F G)) (proof : Proof F G)
    (honest : Honest oracle initial values rounds (() :: rest) state proof) :
    DomainVM.Passes SourceProcess.legacyOrigin initial oracle (viewRound handle state) proof
      (fun next unread => Honest oracle initial values rounds rest next unread) := by
  obtain ⟨length, shaped, scalar, suffix, mapped, proofEq⟩ := honest
  let table := restrictPrefixValues values state.1.1
  have even : table.length % 2 = 0 := by rw [shaped, List.length_cons, pow_succ]; simp
  have sumEq : table.sum = lowSum table + highSum table := (List.sum_take_add_sum_drop table _).symm
  have stateEq : state = ((state.1.1, lowSum table + highSum table), state.2) := by
    rw [← sumEq, ← scalar]
  rw [stateEq, proofEq]
  simp only [honestRounds, List.length_cons, List.map_cons]
  apply DomainVM.Passes.mono _ _ _ _ _ _ _ ?_
    (round_passes oracle initial handle state.1.1 (lowSum table) (highSum table) state.2 suffix mapped _)
  intro next unread result
  obtain ⟨point, suffix', mapped', delivered, rfl⟩ := result
  refine ⟨?_, ?_, ?_, suffix', mapped', ?_⟩
  · simp only [point, List.length_append, List.length_cons, List.length_nil] at length ⊢
    omega
  · rw [point, restrictPrefixValues_append]
    exact restrictValues_length table _ (by rw [shaped, List.length_cons, pow_succ, Nat.mul_comm])
  · rw [point, restrictPrefixValues_append]
    exact (Zkc.Protocols.Sumcheck.Multilinear.restrictValues_sum table _ even).symm
  · rw [delivered, point, restrictPrefixValues_append]
    rfl

def SourceSuccess (result : Values (Component (assignment F G)) [.boolean] ×
    Domain.History (uniformCarriers F G)) (unread : Proof F G) : Prop :=
  result.1 = .cons (some true) .nil ∧ unread = [] ∧
    ∃ suffix, readbackHistory SourceProcess.legacyOrigin result.2 = some suffix

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem initial_honest (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (shaped : values.length = 2 ^ rounds) :
    Honest oracle initial values rounds (List.replicate rounds ()) (([], values.sum), [])
      ((honestRounds transcript oracle initial values rounds).map (.field "bls12-381.fr")) := by
  refine ⟨by simp, ?_, rfl, [], rfl, ?_⟩
  · simpa only [List.length_replicate, restrictPrefixValues, List.foldl_nil] using shaped
  · simp only [List.length_replicate, List.append_nil, restrictPrefixValues, List.foldl_nil]

/-- The unchanged honest producer succeeds at the full source return, with
exact exhaustion of its messages and readable transcript suffix. -/
theorem source_passes (oracle : History F G → F) (initial : History F G) (values : List F) (rounds handle : Nat)
    (admitted : rounds ≤ SumcheckProof.maximum) (shaped : values.length = 2 ^ rounds) :
    DomainVM.Passes SourceProcess.legacyOrigin initial oracle
      (SourceProcess.sourceView context ((program.participant F G 1
        (ZkcExamples.Construction.SumcheckProof.verifierInputs values values.sum rounds handle)).interpret
          CommonAdapter.project) [])
      ((honestRounds transcript oracle initial values rounds).map (.field "bls12-381.fr"))
      SourceSuccess := by
  have expansion := verifier_optional (F := F) (G := G) (some values) (some values.sum) (some rounds) (some handle)
  change program.participant F G 1
    (ZkcExamples.Construction.SumcheckProof.verifierInputs values values.sum rounds handle) = _ at expansion
  change DomainVM.Passes SourceProcess.legacyOrigin initial oracle
    (SourceProcess.sourceView context ((program.participant F G 1
      (ZkcExamples.Construction.SumcheckProof.verifierInputs values values.sum rounds handle)).interpret
        CommonAdapter.project) []) _ SourceSuccess
  rw [expansion]
  have within : rounds ≤ SumcheckSourceNormalForms.reduceMaximum := admitted
  simp only [SumcheckVerifierPrelude.admittedRounds, SumcheckVerifierPrelude.pendingRounds, within, ite_true]
  rw [repeat_present (G := G) childContext handle rounds ([], values.sum)]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, PIR.Process.interpret_bind, Zkc.Source.interpret_repeat]
  rw [LoopedSourceProcess.sourceView_bind, ← Finite.fold_replicate,
    LoopedSourceProcess.sourceView_finite, DomainVM.Passes.bind]
  have loop := DomainVM.Passes.fold SourceProcess.legacyOrigin initial oracle
    (fun state (_ : Unit) => viewRound handle state) (Honest oracle initial values rounds)
    (fun _ rest state proof => honest_step oracle initial values rounds handle rest state proof)
    (List.replicate rounds ()) (([], values.sum), [])
    ((honestRounds transcript oracle initial values rounds).map (.field "bls12-381.fr"))
    (initial_honest oracle initial values rounds shaped)
  apply DomainVM.Passes.mono _ _ _ _ _ _ _ ?_ loop
  intro result unread valid
  obtain ⟨length, tableShape, scalar, suffix, mapped, proofEq⟩ := valid
  have pointLength : result.1.1.length = rounds := by simpa using length
  have small : result.1.1.length < 64 := by
    have : SumcheckProof.maximum < 64 := by decide +kernel
    omega
  have pointBound : result.1.1.length < indexLimit := lt_trans small (by decide)
  have vectorBound : values.length < indexLimit := by
    have maximum : SumcheckProof.maximum = 2 := by kernel_rfl
    have bound : rounds ≤ 2 := by omega
    have power : 2 ^ rounds ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) bound
    rw [shaped]
    exact lt_of_le_of_lt power (by decide)
  rw [SumcheckVerifierTerminal.terminal_equation 1 values result.1.1 result.1.2 vectorBound pointBound]
  have shape : PrimitiveLibrary.HasShape values result.1.1.length 1 := by
    change 0 < 1 ∧ result.1.1.length < 64 ∧ values.length % 1 = 0 ∧ values.length / 1 = 2 ^ result.1.1.length
    exact ⟨by decide, small, Nat.mod_one _, by simpa only [pointLength, Nat.div_one] using shaped⟩
  simp only [shape, scalar, and_self, decide_true, PIR.Process.interpret, SourceProcess.sourceView, DomainVM.Passes]
  exact ⟨rfl, by simpa only [List.length_nil, honestRounds, List.map_nil] using proofEq, suffix, mapped⟩

end ZkcExamples.Executable.SumcheckSourceHonest
