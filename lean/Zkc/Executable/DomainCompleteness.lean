module

public import Zkc.Executable.DomainSoundness

@[expose] public section

/-! Run-dependent budget certificates for Code over canonical Domain Processes.
Instruction work uses Process continuation laws; only Code's charges, helper
work and loop/yield schedule are inspected by these predicates. -/
set_option autoImplicit false

namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (program : Structured.Program) (context : Context)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

private theorem step_loop (program : Structured.Program) (context : Context)
    (site : String) (maximum : Nat) (yielded operands : List Nat)
    (declared : List ValueSort) (body : List Instruction) (env : Environment F G) :
    Domain.step (Structured.ringModel F G) program context
      ⟨.loop site maximum yielded, operands, declared, body⟩ env =
    (match operands with
    | [] => .halt .refused
    | count :: refs => match env[count]?, Domain.read env refs with
      | some (.data (.index bound)), some carried =>
          if bound ≤ maximum ∧ Domain.sortsMatch declared carried then
            (Domain.iterate (Domain.evaluate (Structured.ringModel F G) program context body)
              env yielded declared (List.range bound) carried).bind
              (fun final => if Domain.sortsMatch declared final then .done (env ++ final) else .halt .refused)
          else .halt .refused
      | _, _ => .halt .refused) := by
  cases operands with
  | nil => simp only [Domain.step]
  | cons count refs =>
      simp only [Domain.step]
      cases env[count]? with
      | none => rfl
      | some value =>
          cases value with
          | transcript | indices => rfl
          | data payload =>
              rcases payload with ⟨ty, admissible, contents⟩
              cases ty <;> cases Domain.read env refs <;> rfl

def FitsIterate
    (body : Environment F G → Proof F G → Nat →
      (Environment F G → Proof F G → Nat → Prop) → Prop)
    (outer : Environment F G) (yielded : List Nat) (declared : List ValueSort) :
    List Nat → Environment F G → Proof F G → Nat →
      (Environment F G → Proof F G → Nat → Prop) → Prop
  | [], carried, proof, used, holds => holds carried proof used
  | index :: rest, carried, proof, used, holds =>
      body (outer ++ .data (.index index) :: carried) proof used fun final unread charged =>
        charged + 1 ≤ budget ∧ ∀ values, Domain.read final yielded = some values →
          Domain.sortsMatch declared values = true →
          FitsIterate body outer yielded declared rest values unread (charged + 1) holds

mutual
def FitsK : List Code → Environment F G → Proof F G → Nat →
    (Environment F G → Proof F G → Nat → Prop) → Prop
  | [], env, proof, used, holds => holds env proof used
  | code :: rest, env, proof, used, holds =>
      FitsStep code env proof used fun final unread charged => FitsK rest final unread charged holds

def FitsStep : Code → Environment F G → Proof F G → Nat →
    (Environment F G → Proof F G → Nat → Prop) → Prop
  | .charge count, env, proof, used, holds => used + count ≤ budget ∧ holds env proof (used + count)
  | .step instruction charged, env, proof, used, holds =>
      used + charged ≤ budget ∧
        Continues (Domain.step (Structured.ringModel F G) program context instruction env) proof
          (fun final unread => holds final unread (used + charged))
  | .helper instruction, env, proof, used, holds =>
      used + 1 ≤ budget ∧
        match instruction.operation, Domain.read env instruction.operands with
        | .call name, some values =>
            ∃ scalar, arguments values = some scalar ∧ used + 1 + cost name scalar ≤ budget ∧
              Continues (Domain.step (Structured.ringModel F G) program context instruction env) proof
                (fun final unread => holds final unread (used + 1 + cost name scalar))
        | .call _, none => True
        | _, _ => False
  | .loop _ maximum yielded operands declared body, env, proof, used, holds =>
      match operands with
      | count :: refs =>
          match env[count]?, Domain.read env refs with
          | some (.data (.index bound)), some carried =>
              bound ≤ maximum ∧ Domain.sortsMatch declared carried = true →
                used + 1 ≤ budget ∧
                  FitsIterate budget (fun start unread charged post => FitsK body start unread charged post)
                    env yielded declared (List.range bound) carried proof (used + 1)
                    (fun final unread charged => Domain.sortsMatch declared final = true →
                      holds (env ++ final) unread charged)
          | _, _ => True
      | [] => True
end

def Sufficient (lowered : Lowered) (env : Environment F G) (proof : Proof F G) : Prop :=
  FitsK program context cost budget lowered.code env proof 0 (fun _ _ used => used + 1 ≤ budget)

section Soundness
variable {m : Type → Type} [Monad m]
variable (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem meteredIterate_fits {R : Type}
    (body : Environment F G → PIR.Process (Domain.effects (Structured.uniformCarriers F G))
      (Environment F G))
    (meter : Environment F G → Proof F G → Nat →
      (Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
        m (PIR.Outcome R × Proof F G))
    (fitsBody : Environment F G → Proof F G → Nat →
      (Environment F G → Proof F G → Nat → Prop) → Prop)
    (bodySound : ∀ env proof used post next next', fitsBody env proof used post →
      (∀ final unread charged, post final unread charged → next final unread charged = next' final unread) →
      meter env proof used next = DomainAdapter.runK key initial challenge (body env) proof next')
    (outer : Environment F G) (yielded : List Nat) (declared : List ValueSort) :
    ∀ items carried proof used post next next',
      FitsIterate budget fitsBody outer yielded declared items carried proof used post →
      (∀ final unread charged, post final unread charged → next final unread charged = next' final unread) →
      meteredIterate budget meter outer yielded declared items carried proof used next =
        DomainAdapter.runK key initial challenge
          (Domain.iterate body outer yielded declared items carried) proof next'
  | [], carried, proof, used, post, next, next', fits, continues => continues carried proof used fits
  | index :: rest, carried, proof, used, post, next, next', fits, continues => by
      simp only [FitsIterate] at fits
      simp only [meteredIterate, Domain.iterate, DomainAdapter.runK_bind]
      apply bodySound _ _ _ _ _ _ fits
      intro final unread charged found
      simp only [found.1, ite_true]
      cases readEq : Domain.read final yielded with
      | none => rfl
      | some values =>
          by_cases sorted : Domain.sortsMatch declared values = true
          · simp only [sorted, ite_true]
            exact meteredIterate_fits body meter fitsBody bodySound outer yielded declared
              rest values unread (charged + 1) post next next' (found.2 values readEq sorted) continues
          · simp only [sorted]; rfl

mutual
theorem meteredK_fits {R : Type} :
    ∀ (code : List Code) (env : Environment F G) (proof : Proof F G) (used : Nat)
      (post : Environment F G → Proof F G → Nat → Prop)
      (next : Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G))
      (next' : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)),
      FitsK program context cost budget code env proof used post →
      (∀ final unread charged, post final unread charged → next final unread charged = next' final unread) →
      meteredK program context key initial challenge cost budget code env proof used next =
        DomainAdapter.runK key initial challenge
          (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions code) env) proof next'
  | [], env, proof, used, post, next, next', fits, continues => by
      simpa only [meteredK, Code.instructions, Domain.evaluate, DomainAdapter.runK] using
        continues env proof used fits
  | code :: rest, env, proof, used, post, next, next', fits, continues => by
      rw [meteredK]
      have go := meteredStep_fits code env proof used
        (fun final unread charged => FitsK program context cost budget rest final unread charged post)
        (fun final unread charged => meteredK program context key initial challenge cost budget
          rest final unread charged next)
        (fun final unread => DomainAdapter.runK key initial challenge
          (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions rest) final)
          unread next') fits
        (fun final unread charged found => meteredK_fits rest final unread charged post next next' found continues)
      cases code <;> simpa only [Code.instructions, Domain.evaluate, DomainAdapter.runK,
        DomainAdapter.runK_bind] using go

theorem meteredStep_fits {R : Type} :
    ∀ (code : Code) (env : Environment F G) (proof : Proof F G) (used : Nat)
      (post : Environment F G → Proof F G → Nat → Prop)
      (next : Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G))
      (next' : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)),
      FitsStep program context cost budget code env proof used post →
      (∀ final unread charged, post final unread charged → next final unread charged = next' final unread) →
      meteredStep program context key initial challenge cost budget code env proof used next =
        (match code with
        | .charge _ => next' env proof
        | .step instruction _ | .helper instruction =>
            DomainAdapter.runK key initial challenge
              (Domain.step (Structured.ringModel F G) program context instruction env) proof next'
        | .loop site maximum yielded operands declared body =>
            DomainAdapter.runK key initial challenge
              (Domain.step (Structured.ringModel F G) program context
                ⟨.loop site maximum yielded, operands, declared, Code.instructions body⟩ env) proof next')
  | .charge count, env, proof, used, post, next, next', fits, continues => by
      simp only [FitsStep] at fits
      simp only [meteredStep, fits.1, ite_true]
      exact continues _ _ _ fits.2
  | .step instruction charged, env, proof, used, post, next, next', fits, continues => by
      simp only [FitsStep] at fits
      simp only [meteredStep, fits.1, ite_true]
      exact runK_congr_continues key initial challenge _ proof _ fits.2 _ _
        (fun final unread found => continues final unread _ found)
  | .helper instruction, env, proof, used, post, next, next', fits, continues => by
      obtain ⟨first, called⟩ := fits
      simp only [meteredStep, first, ite_true]
      rcases instruction with ⟨operation, operands, results, body⟩
      cases operation <;> simp only at called
      rename_i name
      cases found : Domain.read env operands with
      | none =>
          cases body <;> simp [found, Domain.step, DomainAdapter.runK]
      | some values =>
          simp only [found] at called ⊢
          obtain ⟨scalar, scalarEq, charged, reached⟩ := called
          simp only [scalarEq, charged, ite_true]
          exact runK_congr_continues key initial challenge _ proof _ reached _ _
            (fun final unread good => continues final unread _ good)
  | .loop site maximum yielded operands declared body, env, proof, used, post, next, next', fits, continues => by
      simp only [FitsStep] at fits
      simp only [meteredStep]
      rw [step_loop program context site maximum yielded operands declared (Code.instructions body) env]
      cases operands with
      | nil => rfl
      | cons count refs =>
          simp only at fits ⊢
          cases countEq : env[count]? with
          | none => simp [DomainAdapter.runK]
          | some value =>
              cases readEq : Domain.read env refs with
              | none =>
                  cases value with
                  | transcript | indices => simp [DomainAdapter.runK]
                  | data payload =>
                      rcases payload with ⟨ty, admissible, contents⟩
                      cases ty <;> simp [DomainAdapter.runK]
              | some carried =>
                  cases value with
                  | transcript | indices => simp [DomainAdapter.runK]
                  | data payload =>
                      rcases payload with ⟨ty, admissible, contents⟩
                      cases ty <;> try (simp [DomainAdapter.runK])
                      simp only [countEq, readEq] at fits ⊢
                      by_cases admitted : contents ≤ maximum ∧ Domain.sortsMatch declared carried = true
                      · obtain ⟨first, iterations⟩ := fits admitted
                        simp only [admitted, and_self, ite_true, first, DomainAdapter.runK_bind]
                        apply meteredIterate_fits budget key initial challenge
                          (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions body))
                          (fun start unread charged continuation =>
                            meteredK program context key initial challenge cost budget body start unread charged continuation)
                          (fun start unread charged holds => FitsK program context cost budget body start unread charged holds)
                          (fun start unread charged holds continuation continuation' good agree =>
                            meteredK_fits body start unread charged holds continuation continuation' good agree)
                          env yielded declared _ _ _ _ _ _ _ iterations
                        intro final unread charged good
                        by_cases sorted : Domain.sortsMatch declared final = true
                        · simp only [sorted, ite_true, DomainAdapter.runK]
                          exact continues _ _ _ (good sorted)
                        · simp only [sorted]; rfl
                      · simp only [admitted, ite_false, DomainAdapter.runK]
end

theorem metered_sufficient (lowered : Lowered) (env : Environment F G) (proof : Proof F G)
    (fits : Sufficient program context cost budget lowered env proof) :
    metered program context key initial challenge cost budget lowered env proof =
      DomainAdapter.runK key initial challenge
        (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions lowered.code) env)
        proof (fun final unread => pure
          (match Domain.read final lowered.returned with
          | some returned => .returned returned
          | none => .stopped .refused, unread)) := by
  unfold metered
  apply meteredK_fits program context cost budget key initial challenge _ _ _ _ _ _ _ fits
  intro final unread charged good
  simp only [good, ite_true]
  cases Domain.read final lowered.returned <;> rfl

end Soundness
end Zkc.Executable.DomainVM
