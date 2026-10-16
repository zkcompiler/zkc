module

public import Zkc.Construction.FiatShamir

@[expose] public section

/-! Soundness of the transcript-construction rule.

For every program the rule accepts, every challenge function in every lawful
monad, every data input, initial transcript, service handle and proof, the
ideal meaning equals the Fiat–Shamir transform of the program's interactive
reading. Outcomes, stops and the unread proof suffix are all equal; no typing
premise on the supplied values is needed because both sides perform the same
dynamic checks.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source Zkc.Source.Common.Native

variable {F G : Type}

section Environment
variable {env : List (Value F G)}

theorem getElem?_append_of_lt {values : List (Value F G)} {index : Nat}
    (bound : index < env.length) : (env ++ values)[index]? = env[index]? :=
  List.getElem?_append_left bound

theorem transcriptAt_lt {index : Nat} {history : History F G}
    (found : transcriptAt env index = some history) : index < env.length := by
  unfold transcriptAt at found
  by_contra outside
  rw [List.getElem?_eq_none (by omega)] at found
  cases found

theorem dataAt_lt {index : Nat} {payload : Payload F G}
    (found : dataAt env index = some payload) : index < env.length := by
  unfold dataAt at found
  by_contra outside
  rw [List.getElem?_eq_none (by omega)] at found
  cases found

theorem transcriptAt_append {values : List (Value F G)} {index : Nat} {history : History F G}
    (found : transcriptAt env index = some history) :
    transcriptAt (env ++ values) index = some history := by
  have bound := transcriptAt_lt found
  unfold transcriptAt at found ⊢
  rw [getElem?_append_of_lt bound]
  exact found

theorem dataAt_append {values : List (Value F G)} {index : Nat} {payload : Payload F G}
    (found : dataAt env index = some payload) :
    dataAt (env ++ values) index = some payload := by
  have bound := dataAt_lt found
  unfold dataAt at found ⊢
  rw [getElem?_append_of_lt bound]
  exact found

end Environment

variable {m : Type → Type} [Monad m]

/-- The simulation invariant: the transform's absorbed history is the current
transcript state, followed by the one observation the rule requires next. -/
def Synchronized (state : CheckState) (env : List (Value F G))
    (absorbed : History F G) : Prop :=
  env.length = state.sorts.length ∧
  ∃ current, transcriptAt env state.current = some current ∧
    match state.pending with
    | .none => absorbed = current
    | .observe index origin =>
        ∃ payload, dataAt env index = some payload ∧ absorbed = current ++ [.message origin payload]

/-- Apply a function to a returned value; stops are unchanged. -/
def mapOutcome {A B : Type} (f : A → B) : PIR.Outcome A → PIR.Outcome B
  | .returned value => .returned (f value)
  | .stopped stop => .stopped stop

/-- A pure final projection commutes with the transform. -/
theorem transform_bind_done [LawfulMonad m] {A B : Type} (context : Context)
    (challenge : History F G → m F) (f : A → B) (process : PIR.Proc (Actions F G) A) :
    ∀ (history : History F G) (proof : Proof F G),
      transform context challenge (process.bind fun value => .done (f value)) history proof =
        (fun result => (mapOutcome f result.1, result.2)) <$>
          transform context challenge process history proof := by
  induction process with
  | done value => intro history proof; simp [PIR.Proc.bind, transform, mapOutcome]
  | halt stop => intro history proof; simp [PIR.Proc.bind, transform, mapOutcome]
  | call operation next ih =>
      intro history proof
      cases operation with
      | receive ty site sender =>
          cases proof with
          | nil => simp [PIR.Proc.bind, transform, mapOutcome]
          | cons payload rest =>
              simp only [PIR.Proc.bind, transform]
              cases payload.value ty with
              | none => simp [mapOutcome]
              | some value => exact ih value _ _
      | query site field arguments =>
          simp only [PIR.Proc.bind, transform, map_bind]
          congr 1
          funext answer
          exact ih answer _ _
      | send site receiver sent =>
          simp only [PIR.Proc.bind, transform]
          cases Payload.ofValue _ sent with
          | none => simp [mapOutcome]
          | some payload => exact ih () _ _

variable [LawfulMonad m] [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem checkFrom_sound (context : Context) (challenge : History F G → m F) (handle : Nat)
    (returned : List Nat) (instructions : List Instruction) :
    ∀ (state final : CheckState) (env : List (Value F G)) (absorbed : History F G)
      (proof : Proof F G),
      checkFrom context state instructions = some final →
      Synchronized state env absorbed →
      ideal challenge returned instructions env proof =
        transform context challenge
          (spec context handle returned instructions env state.drawn) absorbed proof := by
  induction instructions with
  | nil =>
      intro state final env absorbed proof _ _
      simp only [ideal, spec, finish]
      split <;> rw [transform]
  | cons instruction rest ih =>
      intro state final env absorbed proof accepted synchronized
      obtain ⟨length, current, currentAt, pending⟩ := synchronized
      simp only [checkFrom] at accepted
      cases stepped : checkStep context state instruction with
      | none => simp [stepped] at accepted
      | some successor =>
        simp only [stepped] at accepted
        have next := ih successor final
        obtain ⟨operation, operands, results⟩ := instruction
        cases operation with
        | receive site schema peer ty =>
            cases operands with
            | cons => simp [checkStep] at stepped
            | nil =>
              cases pendingEq : state.pending with
              | observe => simp [checkStep, pendingEq] at stepped
              | none =>
                simp only [checkStep, pendingEq] at stepped
                split at stepped
                · cases stepped
                  rw [pendingEq] at pending
                  subst absorbed
                  cases proof with
                  | nil =>
                      simp [ideal, idealStep, spec, transform]
                  | cons payload unread =>
                      simp only [ideal, idealStep, spec, transform]
                      cases decoded : payload.value ty with
                      | none =>
                          have different : ¬ payload.ty = ty := by
                            have := Payload.value_isSome (payload := payload) (ty := ty)
                            rw [decoded] at this
                            simpa using this.symm
                          simp [different]
                      | some value =>
                          have same : payload.ty = ty := by
                            have := Payload.value_isSome (payload := payload) (ty := ty)
                            rw [decoded] at this
                            simpa using this.symm
                          simp only [same, ite_true, pure_bind, Payload.value_some decoded]
                          refine next _ _ _ accepted ?_
                          refine ⟨by simp [length], current, transcriptAt_append currentAt, ?_⟩
                          refine ⟨payload, ?_, rfl⟩
                          unfold dataAt
                          simp [length]
                · cases stepped
        | send => simp [checkStep] at stepped
        | indicesEmpty =>
            cases operands with
            | cons => simp [checkStep] at stepped
            | nil =>
              simp only [checkStep] at stepped
              split at stepped
              · cases stepped
                simp only [ideal, idealStep, spec, pure_bind]
                refine next _ _ _ accepted ?_
                refine ⟨by simp [length], current, transcriptAt_append currentAt, ?_⟩
                cases pendingEq : state.pending with
                | none => rw [pendingEq] at pending; exact pending
                | observe index origin =>
                    rw [pendingEq] at pending
                    obtain ⟨payload, found, absorbedEq⟩ := pending
                    exact ⟨payload, dataAt_append found, absorbedEq⟩
              · cases stepped
        | observe suite origin =>
            match operands, pendingEq : state.pending with
            | [stateRef, valueRef, coordinates], .observe expected expectedOrigin =>
                simp only [checkStep, pendingEq] at stepped
                split at stepped
                · rename_i conditions
                  obtain ⟨_, currentRef, valueEq, originEq, _, _⟩ := conditions
                  cases stepped
                  rw [pendingEq] at pending
                  obtain ⟨payload, found, absorbedEq⟩ := pending
                  subst currentRef valueEq originEq absorbedEq
                  simp only [ideal, idealStep, spec, currentAt, found, pure_bind]
                  refine next _ _ _ accepted ?_
                  refine ⟨by simp [length], current ++ [.message origin payload], ?_, rfl⟩
                  unfold transcriptAt
                  simp [length]
                · cases stepped
            | [], _ => simp [checkStep] at stepped
            | [_], _ => simp [checkStep] at stepped
            | [_, _], _ => simp [checkStep] at stepped
            | _ :: _ :: _ :: _ :: _, _ => simp [checkStep] at stepped
            | [_, _, _], .none => simp [checkStep, pendingEq] at stepped
        | challenge suite field origin =>
            match operands, pendingEq : state.pending with
            | [stateRef, coordinates], .none =>
                simp only [checkStep, pendingEq] at stepped
                cases drawnEq : context.draws[state.drawn]? with
                | none => simp [drawnEq] at stepped
                | some sites =>
                  obtain ⟨site, delivery⟩ := sites
                  simp only [drawnEq] at stepped
                  split at stepped
                  · rename_i conditions
                    obtain ⟨_, currentRef, originEq, _, _⟩ := conditions
                    cases stepped
                    rw [pendingEq] at pending
                    subst currentRef originEq absorbed
                    simp only [ideal, idealStep, spec, currentAt, drawnEq, transform,
                      bind_map_left, Payload.ofValue]
                    congr 1
                    funext answer
                    refine next _ _ _ accepted ?_
                    refine ⟨by simp [length], current ++ [.challenge (context.query site field)],
                      ?_, ⟨.field field answer, ?_, by simp⟩⟩
                    · unfold transcriptAt
                      simp [length]
                    · unfold dataAt
                      simp [length]
                  · cases stepped
            | [], _ => simp [checkStep] at stepped
            | [_], _ => simp [checkStep] at stepped
            | _ :: _ :: _ :: _, _ => simp [checkStep] at stepped
            | [_, _], .observe _ _ => simp [checkStep, pendingEq] at stepped
        | calculate op =>
            cases pendingEq : state.pending with
            | observe => simp [checkStep, pendingEq] at stepped
            | none =>
              have shape : successor =
                  ⟨state.sorts ++ [.data (language.result op)], state.current, .none, state.drawn⟩ := by
                simp only [checkStep, pendingEq] at stepped
                split_ifs at stepped
                · exact (Option.some.inj stepped).symm
              subst shape
              rw [pendingEq] at pending
              simp only [ideal, idealStep, spec]
              cases computed : (operands.mapM (dataAt env) >>= calculate op) with
              | none => simp [transform]
              | some payload =>
                  simp only [pure_bind]
                  exact next _ _ _ accepted
                    ⟨by simp [length], current, transcriptAt_append currentAt, pending⟩
        | unsupported => simp [checkStep] at stepped

/-- The transcript-construction rule is sound: an accepted program's ideal
meaning is the Fiat–Shamir transform of its interactive reading. -/
theorem check_sound (context : Context) (participant : Participant)
    (accepted : check context participant = true) (challenge : History F G → m F)
    (handle : Nat) (data : List (Payload F G)) (initial : History F G) (proof : Proof F G)
    (arity : data.length + 1 = participant.inputs.length) :
    ideal challenge participant.returned participant.instructions
        (data.map .data ++ [.transcript initial]) proof =
      transform context challenge
        (spec context handle participant.returned participant.instructions
          (data.map .data ++ [.transcript initial]) 0) initial proof := by
  unfold check at accepted
  split at accepted
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
    obtain ⟨⟨_, _⟩, rest⟩ := accepted
    split at rest
    · rename_i final checked
      apply checkFrom_sound context challenge handle participant.returned
        participant.instructions _ final _ initial proof checked
      refine ⟨by simp; omega, initial, ?_, rfl⟩
      unfold transcriptAt
      have index : participant.inputs.length - 1 = (data.map Value.data).length := by
        simp; omega
      simp [index]
    · cases rest
  · cases accepted

end Zkc.Construction
