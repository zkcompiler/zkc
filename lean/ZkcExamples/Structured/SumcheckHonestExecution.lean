module

public import ZkcExamples.Structured.SumcheckProverRoots
public import ZkcExamples.Structured.SumcheckContractBindings
public import Zkc.Source.PeerExecution
public import Zkc.Protocols.Sumcheck.Multilinear.Fold

@[expose] public section

/-! Honest-prover completeness of the actual imported Sumcheck pair.

Both participants run their own actual role-local process of one root
invocation with the same inputs. The verifier's receives and sends are routed
to the prover's actual residual process by `peerHandler`; the verifier's
challenge queries are answered from a tape. The prover's messages are never
supplied by a formula: each one is the value of the prover's actual send,
computed from the challenges it actually received. Completeness holds for
every tape that supplies the requested number of challenges. -/
namespace ZkcExamples.Structured.SumcheckHonestExecution
open Zkc.Source Zkc.Source.Structured Zkc.Source.Participant PrimitiveLibrary
open SumcheckProverLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open Zkc.Protocols.Sumcheck.Multilinear (restrictValues_sum)

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Answers every query in order from a supplied tape, whatever its site, field
or handle; the Sumcheck verifier's only queries are its challenges. An empty
tape stops incomplete; every other action refuses. -/
def challengeTape : PIR.Handler (participantInterface F G) (List F) Unit
  | .query _ _ _, r :: rest => ⟨.returned r, rest, []⟩
  | .query _ _ _, [] => ⟨.stopped .incomplete, [], []⟩
  | _, tape => ⟨.stopped .refused, tape, []⟩

/-- Honest delivery between the prover endpoint and the verifier endpoint of `ctx`. -/
abbrev network {A : Type} (ctx : ProtocolContext) :
    PIR.Handler (participantInterface F G) (Peer Nat Ty services (assignment F G) A (List F)) Unit :=
  peerHandler (ctx.roles 1) (ctx.roles 0) challengeTape

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The next tape value answers a verifier query; the prover is untouched. -/
theorem tape_query {A B : Type} (ctx : ProtocolContext) (site : String) (field : services.Op)
    (handle : Nat)
    (prover : PIR.Process (participantInterface F G) A) (r : F) (tape : List F)
    (continuation : F → PIR.Process (participantInterface F G) B) :
    (PIR.Process.call (Action.query site field (.cons handle .nil)) continuation).run
        (network (G := G) ctx) ⟨prover, r :: tape⟩ =
      (continuation r).run (network ctx) ⟨prover, tape⟩ := by
  simp only [PIR.Process.run, network, peerHandler, challengeTape, PIR.Execution.follow, List.nil_append]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- A table of positive remaining dimension has an even flat length. -/
private theorem restricted_even (raw : List F) (count : Nat) (shape : raw.length = 2 ^ count)
    (point : List F) (remaining : point.length < count) :
    (restrictPrefixValues raw point).length % 2 = 0 := by
  have rawLength : raw.length = 2 ^ ((count - point.length) + point.length) := by
    rw [Nat.sub_add_cancel (Nat.le_of_lt remaining), shape]
  rw [restrictPrefixValues_length raw point rawLength]
  obtain ⟨m, hm⟩ : ∃ m, count - point.length = m + 1 := ⟨count - point.length - 1, by omega⟩
  rw [hm, Nat.pow_succ]
  simp

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
-- The service operation type is a definitional alias of String in the source vocabulary.
set_option backward.isDefEq.respectTransparency false in
/-- One coupled round: the verifier receives the prover's actual half sums, its
guard holds because the claim is the true sum of the prover's current table,
and the prover folds at the verifier's challenge. -/
theorem coupled_round {A B : Type} (ctx : ProtocolContext) (handle : Nat) (raw : List F)
    (count : Nat) (shape : raw.length = 2 ^ count) (point : List F)
    (remaining : point.length < count) (r : F) (tape : List F)
    (verifier : List F × F → PIR.Process (participantInterface F G) A)
    (prover : List F → PIR.Process (participantInterface F G) B) :
    ((SumcheckVerifierLaws.roundPresent ctx handle
        (point, (restrictPrefixValues raw point).sum)).bind verifier).run
        (network ctx) ⟨(roundHonest ctx raw count point).bind prover, r :: tape⟩ =
      (verifier (point ++ [r], (restrictPrefixValues raw (point ++ [r])).sum)).run
        (network ctx) ⟨prover (point ++ [r]), tape⟩ := by
  have even := restricted_even raw count shape point remaining
  simp only [roundHonest, remaining, ↓reduceIte, SumcheckProverLaws.roundPresent,
    SumcheckVerifierLaws.roundPresent, PIR.Process.bind]
  rw [peer_receive, peer_receive]
  simp only [honestState, List.sum_take_add_sum_drop, ↓reduceIte, PIR.Process.bind]
  rw [tape_query, peer_send, ← restrictValues_sum _ r even, restrictPrefixValues_append]
  rfl


omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Coupled rounds from any honest prefix: the verifier's point is the tape
prefix the prover also received, and its claim is the true sum of the
prover's folded table. -/
theorem coupled_rounds {A B : Type} (ctx : ProtocolContext) (handle : Nat) (raw : List F)
    (count : Nat) (shape : raw.length = 2 ^ count) (rounds : Nat) :
    ∀ (point tape : List F), point.length + rounds ≤ count → rounds ≤ tape.length →
    ∀ (verifier : List F × F → PIR.Process (participantInterface F G) A)
      (prover : List F → PIR.Process (participantInterface F G) B),
    ((PIR.repeatN rounds (SumcheckVerifierLaws.roundPresent ctx handle)
        (point, (restrictPrefixValues raw point).sum)).bind verifier).run
        (network ctx) ⟨(PIR.repeatN rounds (roundHonest ctx raw count) point).bind prover, tape⟩ =
      (verifier (point ++ tape.take rounds,
          (restrictPrefixValues raw (point ++ tape.take rounds)).sum)).run
        (network ctx) ⟨prover (point ++ tape.take rounds), tape.drop rounds⟩ := by
  induction rounds with
  | zero =>
    intro point tape _ _ verifier prover
    simp only [PIR.repeatN, PIR.Process.bind, List.take_zero, List.append_nil, List.drop_zero]
  | succ rounds ih =>
    intro point tape fits supply verifier prover
    cases tape with
    | nil => simp at supply
    | cons r rest =>
      simp only [PIR.repeatN, PIR.Process.bind_assoc]
      rw [coupled_round ctx handle raw count shape point (by omega) r rest]
      rw [ih (point ++ [r]) rest (by simp; omega) (by simp at supply; omega)]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.append_assoc, List.singleton_append]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- A shaped one-column table decodes to its multilinear table. -/
theorem decode_of_shape (raw : List F) (count : Nat) (shape : HasShape raw count 1) :
    ∃ table, ofList? count raw = some table := by
  have present := (ofList?_isSome_iff (n := count) raw).mpr
    (by simpa only [Nat.mul_one] using shape.length)
  cases decoded : ofList? count raw with
  | none => rw [decoded] at present; cases present
  | some table => exact ⟨table, rfl⟩

/-! ### Complete Source root -/

/-- Honest-prover completeness of the complete imported Source pair. Both
participants run the actual root with the same inputs, the claim is the true
sum of the table and the verifier's challenges come from any tape with enough
values. The verifier returns `true`, the prover's residual process has returned
its own (absent) output, and exactly the used challenges are consumed. -/
theorem source_complete (raw : List F) (count : Nat) (shape : HasShape raw count 1)
    (bound : raw.length < indexLimit) (admitted : count ≤ SumcheckSourceNormalForms.reduceMaximum) (handle : Nat)
    (tape : List F) (supply : count ≤ tape.length) :
    (SumcheckSourceViews.program.participant F G 1
        (SumcheckSourceVerifier.sourceRootInputs (some raw) (some raw.sum) (some count)
          (some handle))).run
      (network SumcheckSourceVerifier.childContext)
      ⟨SumcheckSourceViews.program.participant F G 0
        (SumcheckSourceVerifier.sourceRootInputs (some raw) (some raw.sum) (some count)
          (some handle)), tape⟩ =
      ⟨.returned (.cons (some true) .nil), ⟨.done (.cons none .nil), tape.drop count⟩, []⟩ := by
  obtain ⟨table, decoded⟩ := decode_of_shape raw count shape
  have rawLength : raw.length = 2 ^ count := by simpa only [Nat.mul_one] using shape.length
  rw [SumcheckSourceVerifier.verifier_checked count admitted raw (some raw.sum) (some handle)
      table decoded bound,
    SumcheckProverRoots.source_prover raw count shape bound admitted (some raw.sum) (some handle)]
  change ((PIR.repeatN count (SumcheckVerifierLaws.roundPlain SumcheckSourceVerifier.childContext
    (some handle)) (some ([] : List F), some (restrictPrefixValues raw ([] : List F)).sum)).bind _).run _ _ = _
  rw [SumcheckVerifierLaws.repeat_present SumcheckSourceVerifier.childContext handle count
    ([], (restrictPrefixValues raw []).sum), PIR.Process.bind_assoc,
    coupled_rounds SumcheckSourceVerifier.childContext handle raw count rawLength count [] tape
      (by simp) supply]
  have length : ([] ++ tape.take count).length = count := by simp; omega
  have value := Zkc.Protocols.Sumcheck.Multilinear.partialEvaluation_complete table _ _
    (Zkc.Protocols.Sumcheck.Multilinear.partialEvaluation_restrict raw table decoded
      ([] ++ tape.take count) (by rw [length])) length
  simp only [PIR.Process.bind, length, value, and_self, decide_true]
  rfl

/-! ### Complete Reduction root -/

/-- The Reduction root's child application context. -/
abbrev reductionChild : ProtocolContext := ProtocolContext.enter {} "s3" [0, 1]

/-- Honest-prover completeness of the complete imported Reduction pair. Both
participants run the actual root with the same inputs and the true initial
claim. The verifier returns the tape prefix it used as its point and the true
sum of the prover's folded table as its value; the prover returns the same
point and that folded table. -/
theorem reduction_complete (raw : List F) (count rounds : Nat) (shape : HasShape raw count 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ 4) (enough : rounds ≤ count)
    (handle : Nat) (tape : List F) (supply : rounds ≤ tape.length) :
    (SumcheckReduceViews.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) (some raw.sum)
          (some rounds) (some handle))).run
      (network reductionChild)
      ⟨SumcheckReduceViews.program.participant F G 0
        (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) (some raw.sum)
          (some rounds) (some handle)), tape⟩ =
      ⟨.returned (SumcheckReduceVerifier.reduceRootResults
          (some (tape.take rounds), some (restrictPrefixValues raw (tape.take rounds)).sum)),
        ⟨.done (SumcheckProverRoots.reductionResults raw (tape.take rounds)), tape.drop rounds⟩,
        []⟩ := by
  have rawLength : raw.length = 2 ^ count := by simpa only [Nat.mul_one] using shape.length
  have verifier : SumcheckReduceViews.program.participant F G 1
      (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) (some raw.sum)
        (some rounds) (some handle)) =
      (PIR.repeatN rounds (SumcheckVerifierLaws.roundPresent reductionChild handle)
        ([], (restrictPrefixValues raw []).sum)).bind
        (fun pc => .done (SumcheckReduceVerifier.reduceRootResults (some pc.1, some pc.2))) := by
    rw [SumcheckReduceVerifier.verifier_optional]
    simp only [SumcheckVerifierPrelude.admittedRounds, admitted, ↓reduceIte]
    change (PIR.repeatN rounds (SumcheckVerifierLaws.roundPlain reductionChild
      (some handle)) (some ([] : List F), some (restrictPrefixValues raw ([] : List F)).sum)).bind _ = _
    rw [SumcheckVerifierLaws.repeat_present reductionChild handle rounds
      ([], (restrictPrefixValues raw []).sum), PIR.Process.bind_assoc]
    rfl
  rw [verifier, SumcheckProverRoots.reduction_prover raw count rounds shape bound admitted enough
      (some raw.sum) (some handle)]
  refine (coupled_rounds reductionChild handle raw count rawLength rounds [] tape
    (by simpa using enough) supply _ _).trans ?_
  simp only [List.nil_append]
  rfl

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The honest run's verifier outputs satisfy the residual request that the
security consumer refutes: the returned value is the original table's sum over
the remaining Boolean variables at the returned point. The prover's returned
residual decodes to that same partial evaluation. -/
theorem honest_residual (remaining rounds : Nat) (raw : List F)
    (table : Table F (remaining + rounds)) (decoded : ofList? (remaining + rounds) raw = some table)
    (point : List F) (length : point.length = rounds) :
    SumcheckContractBindings.Residual remaining rounds table point
        (restrictPrefixValues raw point).sum ∧
      ofList? remaining (restrictPrefixValues raw point) =
        some (fixPrefix rounds table (coordinates rounds point)) := by
  have residual := ofList?_restrictPrefixValues_of_length rounds raw point table length decoded
  refine ⟨⟨coordinates rounds point, ofFn_coordinates point length, ?_⟩, residual⟩
  exact booleanSum_ofList? _ _ residual

/-- The honest Reduction run composed with the residual request: for a table of
`remaining + rounds` variables, the run is the one of `reduction_complete`, and
its verifier outputs, the tape prefix and the folded sum, satisfy the residual
request of the security consumer for the original table, while the prover's
returned residual decodes to the partial evaluation at that same point. -/
theorem reduction_complete_residual (remaining rounds : Nat) (raw : List F)
    (table : Table F (remaining + rounds)) (decoded : ofList? (remaining + rounds) raw = some table)
    (shape : HasShape raw (remaining + rounds) 1) (bound : raw.length < indexLimit)
    (admitted : rounds ≤ 4) (handle : Nat) (tape : List F) (supply : rounds ≤ tape.length) :
    (SumcheckReduceViews.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs (some raw) (some (remaining + rounds))
          (some raw.sum) (some rounds) (some handle))).run
      (network reductionChild)
      ⟨SumcheckReduceViews.program.participant F G 0
        (SumcheckReduceVerifier.reduceRootInputs (some raw) (some (remaining + rounds))
          (some raw.sum) (some rounds) (some handle)), tape⟩ =
      ⟨.returned (SumcheckReduceVerifier.reduceRootResults
          (some (tape.take rounds), some (restrictPrefixValues raw (tape.take rounds)).sum)),
        ⟨.done (SumcheckProverRoots.reductionResults raw (tape.take rounds)), tape.drop rounds⟩,
        []⟩ ∧
    SumcheckContractBindings.Residual remaining rounds table (tape.take rounds)
        (restrictPrefixValues raw (tape.take rounds)).sum ∧
      ofList? remaining (restrictPrefixValues raw (tape.take rounds)) =
        some (fixPrefix rounds table (coordinates rounds (tape.take rounds))) :=
  ⟨reduction_complete raw (remaining + rounds) rounds shape bound admitted (Nat.le_add_left _ _)
      handle tape supply,
    honest_residual remaining rounds raw table decoded (tape.take rounds) (by simp; omega)⟩

end ZkcExamples.Structured.SumcheckHonestExecution
