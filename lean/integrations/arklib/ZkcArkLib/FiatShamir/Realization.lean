module

public import ZkcArkLib.FiatShamir.Upstream
public import ZkcSecurity.Transformations.FiatShamir.Soundness

@[expose] public section

/-! Transport of process-form certificates to participant validators.

An imported ArkLib verifier has a typed certificate over its process form's
transcript interface (`ZkcSecurity.FiatShamir.Upstream`). A compiled Entry's
original validator is a participant process over the common participant actions,
whose transcript interface is `ZkcSecurity.FiatShamir.interface`. `Realizes`
relates the two operation by operation, a morphism of the two interfaces along a
pair of processes:

* a participant receive realizes a prover-message round, reading the round's
  message from the received value by any map;
* a participant query realizes a challenge round, reading the round's challenge
  from the field challenge by a bijection, and its occurrence is charged at least
  the round's error;
* a participant send realizes no round: it delivers a value the process form does
  not read, so the process-form residual stays where it is;
* a returned value realizes a returned verdict related to it by `results`.

`Realizes.certificate` turns a certificate of the process form into one of the
participant interface with field challenges: the doomed participant residuals are
those realizing a doomed process-form residual. Receives and sends keep them
doomed because the process form's messages do; a query escapes at most as often
as the challenge round, since the bijection carries the uniform field challenge
to the uniform round challenge; a returned value accepted under `accepts'` would
be a verdict accepted under `accepts`. With `experiment_eq` and
`acceptance_le_of_image`, a worst-case round-by-round soundness proof of an ArkLib
verifier then bounds the acceptance of a compiled verifier whose original
validator realizes the verifier's process form
(`ZkcSecurity.Examples.CompiledGuessFiatShamir`).
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Upstream
open OracleComp OracleSpec ProtocolSpec
open Zkc.Source Zkc.Construction Zkc.Source.Common.Native

variable {n : ℕ} {pSpec : ProtocolSpec n} {F G A A' : Type} (context : Context)
  (error : pSpec.ChallengeIdx → NNReal) (error' : Zkc.Construction.Event F G → ENNReal)
  (results : A → A' → Prop)

/-- A participant process realizes a process-form residual, operation by
operation: receives realize message rounds, queries realize challenge rounds by
a bijection whose occurrence is charged at least the round's error, sends realize
no round, and returned values realize related verdicts. -/
inductive Realizes : PIR.Process (signature pSpec) A → PIR.Process (Actions F G) A' → Prop where
  | done {value : A} {value' : A'} : results value value' →
      Realizes (.done value) (.done value')
  | send {process : PIR.Process (signature pSpec) A} {ty : Ty} {site : String} {receiver : Nat}
      {sent : ScalarValue F G ty} {next' : Unit → PIR.Process (Actions F G) A'} :
      Realizes process (next' ()) → Realizes process (.call (.send site receiver sent) next')
  | receive {round : Fin n} {next : pSpec.«Type» round → PIR.Process (signature pSpec) A}
      {ty : Ty} {site : String} {sender : Nat}
      {next' : ScalarValue F G ty → PIR.Process (Actions F G) A'}
      (message : pSpec.dir round = .P_to_V) (read : ScalarValue F G ty → pSpec.«Type» round) :
      (∀ value, Realizes (next (read value)) (next' value)) →
      Realizes (.call (I := signature pSpec) round next) (.call (.receive ty site sender) next')
  | query {round : Fin n} {next : pSpec.«Type» round → PIR.Process (signature pSpec) A}
      {site field : String} {arguments : Values (ScalarValue F G) (services.arguments field)}
      {next' : F → PIR.Process (Actions F G) A'}
      (challengeRound : pSpec.dir round = .V_to_P)
      (read : F ≃ pSpec.Challenge ⟨round, challengeRound⟩)
      (charged : roundError pSpec error round ≤
        error' (.challenge (context.query site (.draw field)))) :
      (∀ challenge, Realizes (next (read challenge)) (next' challenge)) →
      Realizes (.call (I := signature pSpec) round next)
        (.call (.query site field arguments) next')

variable {StmtIn : Type} [∀ index, SampleableType (pSpec.Challenge index)] [SampleableType F]

/-- The participant certificate of a process-form certificate: a participant
residual is doomed when it realizes a doomed process-form residual. Each
participant query is charged its occurrence's `error'`. -/
def Realizes.certificate {accepts : A → Prop} {accepts' : A' → Prop}
    (preserves : ∀ value value', results value value' → accepts' value' → accepts value)
    (certificate : Typed.Certificate (absorb pSpec StmtIn) accepts (eventError error)) :
    Typed.Certificate (interface (G := G) context id) accepts' error' where
  doomed process' := ∃ process, certificate.doomed process ∧
    Realizes context error error' results process process'
  step process' := by
    rintro ⟨process, doomed, realizes⟩
    have step := certificate.step process doomed
    cases realizes with
    | done related =>
        exact fun accepted => step (preserves _ _ related accepted)
    | send realizes =>
        rename_i ty site receiver sent next'
        simp only [Typed.Step, interface]
        cases Payload.ofValue ty sent with
        | none => trivial
        | some payload => exact ⟨process, doomed, realizes⟩
    | receive message read realizes =>
        rename_i round next ty site sender next'
        have notChallenge : ¬ pSpec.dir round = .V_to_P := by
          rw [message]
          decide
        simp only [Typed.Step, absorb, notChallenge, ↓reduceDIte] at step
        simp only [Typed.Step, interface]
        exact fun value => ⟨next (read value), step (read value), realizes value⟩
    | query challengeRound read charged realizes =>
        rename_i round next site field arguments next'
        simp only [Typed.Step, absorb, challengeRound, ↓reduceDIte] at step
        simp only [Typed.Step, interface, id]
        have source := step
        have toRaw := SampleableType.prEvent_uniformSample_equiv (α := ChallengeRaw pSpec round)
          (β := pSpec.Challenge ⟨round, challengeRound⟩)
          (Equiv.cast (challengeRaw_eq pSpec challengeRound))
          fun challenge : pSpec.Challenge ⟨round, challengeRound⟩ =>
            ¬ certificate.doomed (next challenge)
        have toField := SampleableType.prEvent_uniformSample_equiv read
          fun challenge : pSpec.Challenge ⟨round, challengeRound⟩ =>
            ¬ certificate.doomed (next challenge)
        refine (prEvent_mono _ _
          (fun challenge : F => ¬ certificate.doomed (next (read challenge)))
          fun challenge escaping => ?_).trans ?_
        · obtain ⟨value, decoded, outside⟩ := escaping
          cases Option.some.inj decoded
          exact fun inside => outside ⟨_, inside, realizes challenge⟩
        · rw [toField, ← toRaw]
          refine (le_of_eq (prEvent_congr _ _ _ fun raw => ?_)).trans (source.trans ?_)
          · exact ⟨fun outside => ⟨_, rfl, outside⟩, fun ⟨_, decoded, outside⟩ => by
              cases Option.some.inj decoded
              exact outside⟩
          · exact charged

end ZkcSecurity.FiatShamir.Upstream
