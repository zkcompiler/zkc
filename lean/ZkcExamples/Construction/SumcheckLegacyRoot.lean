module

public import ZkcExamples.Construction.SumcheckLegacyLoop
public import ZkcExamples.Construction.SumcheckDomainVerifier

@[expose] public section
/-! Complete outcome, return and unread-proof transport for the retained
Sumcheck artifact. This finite comparison has no relation-validity premise. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Executable (idealK_call idealK_loop idealK_nil)
open Zkc.Construction.Uniform.DomainAdapter
open ZkcExamples.Structured ZkcExamples.Executable
attribute [local irreducible] reduce roundState
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem legacy_check_total (values point : List F) (claim : F) :
    callHelper (Uniform.helperTable SumcheckProof.program F G) SumcheckHelperBodies.checkHelper.name
      [.vector "bls12-381.fr" values, .vector "bls12-381.fr" point, .data (.field "bls12-381.fr" claim)] =
      if point.length < indexLimit then
        if point.length < 64 then
          if values.length < indexLimit then
            .returned [.data (.boolean (Protocols.Sumcheck.Multilinear.check
              (n := 0 + point.length) values
              (Polynomial.Quadratic.point point.length
                (Polynomial.coordinates point.length point) Fin.elim0) claim))]
          else .stopped .exhausted
        else .returned [.data (.boolean false)]
      else .stopped .exhausted := by
  rw [SumcheckHelpers.call_eq SumcheckSourceAssociations.check_association _
    (SumcheckHelperLaws.checkInputs values point claim) rfl, SumcheckSourceContracts.check_all]
  split_ifs <;> rfl

abbrev terminalInstruction : Construction.Instruction :=
  SumcheckProof.participant.instructions[2]'(by decide +kernel)

omit [LawfulMonad m] in
theorem terminal_transport (challenge : History F G → m F) (initial : History F G)
    (values : List F) (claim : F) (rounds : Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory legacyOrigin history = some suffix) (proof : Proof F G) :
    idealK SumcheckProof.context challenge (Uniform.helperTable SumcheckProof.program F G)
      [terminalInstruction]
      ((SumcheckProof.inputs values claim rounds ++ [.transcript initial, .vector "bls12-381.fr" []]) ++
        legacyCarried point scalar (initial ++ suffix)) proof
      (fun final unread => pure (finish SumcheckProof.participant.returned final, unread)) =
    runK legacyOrigin initial challenge (terminal values ⟨point, scalar, history⟩) proof (nominalFinish initial) := by
  have checkResult := legacy_check_total (F := F) (G := G) values point scalar
  rw [idealK]
  simp only [terminalInstruction, SumcheckProof.participant, SumcheckProofParticipant.participant,
    List.getElem_cons_succ, List.getElem_cons_zero, idealStep, SumcheckProof.inputs,
    legacyCarried, Construction.read, List.mapM_cons, List.mapM_nil, Bind.bind, Option.bind,
    Option.pure_def, List.cons_append, List.nil_append, List.getElem?_cons_zero,
    List.getElem?_cons_succ, checkResult]
  split_ifs <;> simp [terminal, *, idealK_nil, finish, Construction.read, runK,
    nominalFinish, readbackOutcome, readbackValues, readbackValue, readbackData]

/-- Exact preservation for this artifact, not a universal model identification.
The public table and claim are arbitrary, and the oracle supplies every reply
in any lawful monad. Resource stops, returns and unread proof are all retained. -/
theorem retained_legacy (challenge : History F G → m F) (values : List F) (claim : F) (rounds : Nat)
    (initial : History F G) (proof : Proof F G) :
    ideal SumcheckProof.context challenge (Uniform.helperTable SumcheckProof.program F G)
        SumcheckProof.participant.returned SumcheckProof.participant.instructions
        (SumcheckProof.inputs values claim rounds ++ [.transcript initial]) proof =
      retained challenge values claim rounds initial proof := by
  rw [retained_root]
  unfold ideal
  simp only [SumcheckProof.participant, SumcheckProofParticipant.participant]
  rw [idealK_call _ _ _ rfl (SumcheckHelpers.empty_call (F := F) (G := G)) rfl]
  by_cases bounded : rounds ≤ 2
  · rw [idealK_loop _ _ _ rfl rfl bounded]
    let capture : List (Value F G) :=
      SumcheckProof.inputs values claim rounds ++ [.transcript initial, .vector "bls12-381.fr" []]
    let next := fun final unread =>
      idealK SumcheckProof.context challenge (Uniform.helperTable SumcheckProof.program F G)
        [terminalInstruction] (capture ++ final) unread
        (fun final unread => pure (finish SumcheckProof.participant.returned final, unread))
    change iterateM (fun start unread continuation => idealK SumcheckProof.context challenge
      (Uniform.helperTable SumcheckProof.program F G) roundBody start unread continuation)
      [.vector "bls12-381.fr" values, .data (.field "bls12-381.fr" claim), .index rounds,
        .transcript initial, .vector "bls12-381.fr" []] [26, 31, 25] (List.range rounds)
      (legacyCarried [] claim initial) proof next = _
    have loopEq := legacy_loop challenge initial (.vector "bls12-381.fr" values)
      (.data (.field "bls12-381.fr" claim)) (.index rounds) (.transcript initial)
      (.vector "bls12-381.fr" []) (List.range rounds) [] claim [] [] rfl proof next
    simp only [List.append_nil] at loopEq
    rw [loopEq]
    simp only [rootProcess, bounded, ite_true, runK_bind, readbackCarriedK]
    apply runK_congr_yields _ _ _ _ _ (reduce_mapped (List.range rounds) [] claim [] [] rfl)
    intro state unread hasMapping
    cases found : readbackHistory legacyOrigin state.history with
    | none => simp [found] at hasMapping
    | some suffix =>
        simp only [readbackRoundK, found]
        exact terminal_transport challenge initial values claim rounds state.point state.scalar
          state.history suffix found unread
  · rw [idealK]
    simp [idealStep, SumcheckProof.inputs, Construction.read, indexAt, bounded, rootProcess, runK]

/-- An arity-correct raw input with a Boolean in the selected scalar slot. -/
def illSortedLegacyInputs (initial : History F G) : List (Value F G) :=
  [.vector "bls12-381.fr" [], .data (.boolean true), .index 1, .transcript initial]

def illSortedDomainInputs : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" []), .data (.boolean true), .data (.index 1),
    .transcript SumcheckProof.context.suite []]

/-- On the actual artifact, the historical model reads both messages before
discovering the wrongly sorted captured claim. -/
theorem raw_legacy_consumes (initial : History F G) (low high : F) (tail : Proof F G) :
    ideal (m := Id) SumcheckProof.context (fun _ => (0 : F)) SumcheckProof.table
      SumcheckProof.participant.returned SumcheckProof.participant.instructions
      (illSortedLegacyInputs initial)
      (.field "bls12-381.fr" low :: .field "bls12-381.fr" high :: tail) =
        (.stopped .refused, tail) := by kernel_rfl

/-- Domain checks the actual artifact's input declaration before either
receive, preserving the entire unread proof. -/
theorem raw_domain_refuses (initial : History F G) (low high : F) (tail : Proof F G) :
    Uniform.DomainAdapter.validate (m := Id) SumcheckProof.program SumcheckProof.context SumcheckProof.participant
      legacyOrigin (fun _ => (0 : F)) illSortedDomainInputs initial
      (.field "bls12-381.fr" low :: .field "bls12-381.fr" high :: tail) =
      (.stopped .refused, .field "bls12-381.fr" low :: .field "bls12-381.fr" high :: tail) := by kernel_rfl

/-- A checked counterexample on the unmodified selected artifact. The raw
arity-only statement cannot be transported by asserting model equality. -/
theorem raw_model_disagreement (initial : History F G) (low high : F) (tail : Proof F G) :
    ideal (m := Id) SumcheckProof.context (fun _ => (0 : F)) SumcheckProof.table
      SumcheckProof.participant.returned SumcheckProof.participant.instructions
      (illSortedLegacyInputs initial)
      (.field "bls12-381.fr" low :: .field "bls12-381.fr" high :: tail) ≠
    Uniform.DomainAdapter.validate (m := Id) SumcheckProof.program SumcheckProof.context SumcheckProof.participant
      legacyOrigin (fun _ => (0 : F)) illSortedDomainInputs initial
      (.field "bls12-381.fr" low :: .field "bls12-381.fr" high :: tail) := by
  rw [raw_legacy_consumes, raw_domain_refuses]
  intro same
  have lengths := congrArg (fun result => result.2.length) same
  simp only [List.length_cons] at lengths
  omega

end ZkcExamples.Construction.SumcheckDomainConnection
