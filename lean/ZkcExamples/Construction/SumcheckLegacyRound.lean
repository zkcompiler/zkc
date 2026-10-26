module

public import ZkcExamples.Construction.SumcheckScalarProtocol
public import ZkcExamples.Executable.SumcheckHelpers
public import ZkcExamples.Executable.SumcheckFamily

@[expose] public section
/-! A finite comparison with the historical Sumcheck instruction model.
The normal form below describes this protocol's two messages and query. It
does not inspect or recursively interpret constructed instructions. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open ZkcExamples.Structured
open ZkcExamples.Executable Zkc.Executable
open ZkcExamples.Executable.SumcheckFamily
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]

def legacyYieldK {R : Type}
    (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (final : List (Value F G)) (unread : Proof F G) : m (PIR.Outcome R × Proof F G) :=
  match Construction.read final [26, 31, 25] with
  | some values => next values unread
  | none => pure (.stopped .refused, unread)

theorem legacy_round {R : Type} (challenge : History F G → m F)
    (a b c d e : Value F G) (index : Nat) (point : List F) (scalar : F)
    (history : History F G) (proof : Proof F G)
    (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) :
    idealK SumcheckProof.context challenge (Uniform.helperTable SumcheckProof.program F G) roundBody
        ([a, b, c, d, e] ++ [.index index, .vector "bls12-381.fr" point,
          .data (.field "bls12-381.fr" scalar), .transcript history]) proof (legacyYieldK next) =
      scalarRoundK challenge point scalar history proof (fun point scalar history unread =>
        next [.vector "bls12-381.fr" point, .data (.field "bls12-381.fr" scalar), .transcript history] unread) := by
  have lowResolved : lowTemplate.origin SumcheckProof.context = some (staticOrigin lowTemplate) := by kernel_rfl
  have highResolved : highTemplate.origin SumcheckProof.context = some (staticOrigin highTemplate) := by kernel_rfl
  have drawResolved : drawTemplate.origin SumcheckProof.context = some (staticOrigin drawTemplate) := by kernel_rfl
  have deliveryResolved : deliveryTemplate.origin SumcheckProof.context = some (staticOrigin deliveryTemplate) := by kernel_rfl
  simp only [lowTemplate, highTemplate, drawTemplate, deliveryTemplate, roundBody, roundInstruction,
    SumcheckProof.participant, SumcheckProofParticipant.participant,
    List.getElem_cons_zero, List.getElem_cons_succ] at lowResolved highResolved drawResolved deliveryResolved
  simp only [roundBody, roundInstruction, SumcheckProof.participant,
    SumcheckProofParticipant.participant, List.getElem_cons_succ, List.getElem_cons_zero]
  cases proof with
  | nil => rfl
  | cons low unread =>
      cases low with
      | boolean => rfl
      | group => rfl
      | field domain low =>
          by_cases lowDomain : domain = "bls12-381.fr"
          · subst domain
            rw [idealK_receive SumcheckProof.context challenge _ rfl rfl,
              idealK_indicesEmpty, idealK_indicesAppend _ _ _ rfl rfl,
              idealK_observe _ _ _ rfl lowResolved rfl]
            cases unread with
            | nil => rfl
            | cons high rest =>
                cases high with
                | boolean => rfl
                | group => rfl
                | field domain high =>
                    by_cases highDomain : domain = "bls12-381.fr"
                    · subst domain
                      rw [idealK_receive SumcheckProof.context challenge _ rfl rfl,
                        idealK_indicesEmpty, idealK_indicesAppend _ _ _ rfl rfl,
                        idealK_observe _ _ _ rfl highResolved rfl,
                        idealK_calculate _ _ _ rfl (calculate_add _ low high),
                        idealK_calculate _ _ _ rfl (calculate_equal _ scalar (low + high))]
                      by_cases valid : scalar = low + high
                      · simp only [valid, decide_true]
                        rw [idealK_guard _ _ _ rfl, idealK_indicesEmpty,
                          idealK_indicesAppend _ _ _ rfl rfl,
                          idealK_challenge _ _ _ rfl drawResolved]
                        simp only [scalarRoundK, ite_true, List.append_assoc, List.cons_append, List.nil_append]
                        let drawn : History F G := history ++
                            [.message (staticOrigin lowTemplate) (.field "bls12-381.fr" low),
                              .message (staticOrigin highTemplate) (.field "bls12-381.fr" high),
                              .challenge (staticOrigin drawTemplate)]
                        apply congrArg (fun continuation : F → m (PIR.Outcome R × Proof F G) =>
                          challenge drawn >>= continuation)
                        funext answer
                        rw [idealK_indicesEmpty, idealK_indicesAppend _ _ _ rfl rfl,
                          idealK_observe _ _ _ rfl deliveryResolved rfl,
                          idealK_call _ _ _ rfl (SumcheckHelpers.append_call point answer) rfl,
                          idealK_calculate _ _ _ rfl (calculate_one _),
                          idealK_calculate _ _ _ rfl (calculate_sub _ 1 answer),
                          idealK_calculate _ _ _ rfl (calculate_mul _ (1 - answer) low),
                          idealK_calculate _ _ _ rfl (calculate_mul _ answer high),
                          idealK_calculate _ _ _ rfl (calculate_add _ ((1 - answer) * low) (answer * high)),
                          idealK_nil]
                        simp [legacyYieldK, Construction.read, List.append_assoc]
                        kernel_rfl
                      · rw [idealK]
                        simp [idealStep, valid, scalarRoundK, List.append_assoc]
                    · rw [idealK]
                      simp [idealStep, scalarType, Payload.ty, scalarRoundK, highDomain]
          · rw [idealK]
            simp [idealStep, scalarType, Payload.ty, scalarRoundK, lowDomain]

end ZkcExamples.Construction.SumcheckDomainConnection
