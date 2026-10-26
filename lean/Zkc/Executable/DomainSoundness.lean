module

public import Zkc.Executable.DomainLowering
public import Zkc.Executable.DomainProcesses

@[expose] public section

/-! Code charge laws against handled canonical Domain execution. All semantic
work is supplied by the actual Domain Process; the proofs recurse on Code or
Process, never on an independent constructed-instruction interpreter. -/
set_option autoImplicit false

namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source
open Zkc.Construction.Uniform
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]
variable (program : Structured.Program) (context : Context)
  (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

/-- Flattened local calls retain exactly their Code charge sequence. -/
theorem meteredK_append {R : Type} :
    ∀ (first rest : List Code) (env : Environment F G) (proof : Proof F G) (used : Nat)
      (next : Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G)),
      meteredK program context key initial challenge cost budget (first ++ rest) env proof used next =
        meteredK program context key initial challenge cost budget first env proof used
          (fun final unread charged =>
            meteredK program context key initial challenge cost budget rest final unread charged next)
  | [], rest, env, proof, used, next => rfl
  | code :: first, rest, env, proof, used, next => by
      simp only [List.cons_append, meteredK]
      congr 1
      funext final unread charged
      exact meteredK_append first rest final unread charged next

/-- At a static sufficient budget, Code has exactly the canonical handled
outcome, unread proof and challenge actions, including failures. -/
theorem meteredK_static {R : Type} :
    ∀ (code : List Code) {total : Nat}, Code.static code = some total →
      ∀ (env : Environment F G) (proof : Proof F G) (used : Nat)
        (next : Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G)),
        used + total ≤ budget →
        meteredK program context key initial challenge cost budget code env proof used next =
          DomainAdapter.runK key initial challenge
            (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions code) env)
            proof (fun final unread => next final unread (used + total))
  | [], total, static, env, proof, used, next, _ => by
      simp only [Code.static, Option.some.injEq] at static
      subst total
      simp [meteredK, Code.instructions, Domain.evaluate, DomainAdapter.runK]
  | .charge count :: rest, total, static, env, proof, used, next, fits => by
      simp only [Code.static] at static
      cases restStatic : Code.static rest with
      | none => simp [restStatic] at static
      | some restTotal =>
          simp only [restStatic, Option.map_some, Option.some.injEq] at static
          subst total
          simp only [meteredK, meteredStep, Code.instructions,
            show used + count ≤ budget by omega, ite_true]
          rw [meteredK_static rest restStatic _ _ _ _ (by omega)]
          simp only [Nat.add_assoc]
  | .step instruction charged :: rest, total, static, env, proof, used, next, fits => by
      simp only [Code.static] at static
      cases restStatic : Code.static rest with
      | none => simp [restStatic] at static
      | some restTotal =>
          simp only [restStatic, Option.map_some, Option.some.injEq] at static
          subst total
          simp only [meteredK, meteredStep, Code.instructions, Domain.evaluate,
            DomainAdapter.runK, DomainAdapter.runK_bind,
            show used + charged ≤ budget by omega, ite_true]
          congr 1
          funext final unread
          rw [meteredK_static rest restStatic _ _ _ _ (by omega)]
          simp only [Nat.add_assoc]
  | .helper _ :: _, _, static, _, _, _, _, _ => by simp [Code.static] at static
  | .loop _ _ _ _ _ _ :: _, _, static, _, _, _, _, _ => by simp [Code.static] at static

/-- The final return charge is included in `Lowered.total?`. -/
theorem metered_static {lowered : Lowered} {total : Nat}
    (static : lowered.total? = some total) (sufficient : total ≤ budget)
    (env : Environment F G) (proof : Proof F G) :
    metered program context key initial challenge cost budget lowered env proof =
      DomainAdapter.runK key initial challenge
        (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions lowered.code) env)
        proof (fun final unread => pure
          (match Domain.read final lowered.returned with
          | some values => .returned values
          | none => .stopped .refused, unread)) := by
  unfold Lowered.total? at static
  cases codeStatic : Code.static lowered.code with
  | none => simp [codeStatic] at static
  | some charges =>
      simp only [codeStatic, Option.map_some, Option.some.injEq] at static
      unfold metered
      rw [meteredK_static program context key initial challenge cost budget lowered.code
        codeStatic env proof 0 _ (by omega)]
      congr 1
      funext final unread
      simp only [Nat.zero_add, show charges + 1 ≤ budget by omega, ite_true]
      cases Domain.read final lowered.returned <;> rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Each loop yield retains its canonical sort check. A short budget prunes
at the yield after preserving every preceding challenge action. -/
theorem meteredIterate_prunes {R : Type}
    (body : Environment F G → PIR.Process (Domain.effects (Structured.uniformCarriers F G))
      (Environment F G))
    (meter : Environment F G → Proof F G → Nat →
      (Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
        m (PIR.Outcome R × Proof F G))
    (bodyPrunes : ∀ env proof used next next',
      (∀ final unread charged, Prunes Stopped (next final unread charged) (next' final unread)) →
      Prunes Stopped (meter env proof used next)
        (DomainAdapter.runK key initial challenge (body env) proof next'))
    (outer : Environment F G) (yielded : List Nat) (declared : List ValueSort) :
    ∀ items carried proof used next next',
      (∀ final unread charged, Prunes Stopped (next final unread charged) (next' final unread)) →
      Prunes Stopped (meteredIterate budget meter outer yielded declared items carried proof used next)
        (DomainAdapter.runK key initial challenge
          (Domain.iterate body outer yielded declared items carried) proof next')
  | [], carried, proof, used, next, next', continues => continues carried proof used
  | index :: rest, carried, proof, used, next, next', continues => by
      simp only [meteredIterate, Domain.iterate, DomainAdapter.runK_bind]
      apply bodyPrunes
      intro final unread charged
      by_cases fits : charged + 1 ≤ budget
      · simp only [fits, ite_true]
        cases found : Domain.read final yielded with
        | none => exact .refl _
        | some values =>
            by_cases sorted : Domain.sortsMatch declared values = true
            · simp only [sorted, ite_true]
              exact meteredIterate_prunes body meter bodyPrunes outer yielded declared
                rest values unread (charged + 1) next next' continues
            · simp only [sorted]
              exact .refl _
      · simp only [fits, ite_false]
        exact stopped_pure (m := m) _ _ _

mutual
/-- Every Code budget prunes the canonical Domain Process. This statement is
about complete outcomes and unread proof, rather than just accepting results. -/
theorem meteredK_prunes {R : Type} :
    ∀ (code : List Code) (env : Environment F G) (proof : Proof F G) (used : Nat)
      (next : Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G))
      (next' : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ final unread charged, Prunes Stopped (next final unread charged) (next' final unread)) →
      Prunes Stopped (meteredK program context key initial challenge cost budget code env proof used next)
        (DomainAdapter.runK key initial challenge
          (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions code) env)
          proof next')
  | [], env, proof, used, next, next', continues => by
      simpa only [meteredK, Code.instructions, Domain.evaluate, DomainAdapter.runK] using continues env proof used
  | code :: rest, env, proof, used, next, next', continues => by
      rw [meteredK]
      have go := meteredStep_prunes code env proof used
        (fun final unread charged => meteredK program context key initial challenge cost budget
          rest final unread charged next)
        (fun final unread => DomainAdapter.runK key initial challenge
          (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions rest) final)
          unread next')
        (fun final unread charged => meteredK_prunes
          rest final unread charged next next' continues)
      cases code <;> simpa only [Code.instructions, Domain.evaluate, DomainAdapter.runK,
        DomainAdapter.runK_bind] using go

theorem meteredStep_prunes {R : Type} :
    ∀ (code : Code) (env : Environment F G) (proof : Proof F G) (used : Nat)
      (next : Environment F G → Proof F G → Nat → m (PIR.Outcome R × Proof F G))
      (next' : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ final unread charged, Prunes Stopped (next final unread charged) (next' final unread)) →
      Prunes Stopped (meteredStep program context key initial challenge cost budget code env proof used next)
        (match code with
        | .charge _ => next' env proof
        | .step instruction _ | .helper instruction =>
            DomainAdapter.runK key initial challenge
              (Domain.step (Structured.ringModel F G) program context instruction env) proof next'
        | .loop site maximum yielded operands declared body =>
            DomainAdapter.runK key initial challenge
              (Domain.step (Structured.ringModel F G) program context
                ⟨.loop site maximum yielded, operands, declared, Code.instructions body⟩ env) proof next')
  | .charge count, env, proof, used, next, next', continues => by
      simp only [meteredStep]
      split
      · exact continues _ _ _
      · exact stopped_pure (m := m) _ _ _
  | .step instruction charged, env, proof, used, next, next', continues => by
      simp only [meteredStep]
      split
      · exact runK_prunes key initial challenge _ proof _ _ (fun final unread => continues final unread _)
      · exact stopped_pure (m := m) _ _ _
  | .helper instruction, env, proof, used, next, next', continues => by
      simp only [meteredStep]
      split
      · split
        · split
          · split
            · exact runK_prunes key initial challenge _ proof _ _ (fun final unread => continues final unread _)
            · exact stopped_pure (m := m) _ _ _
          · exact stopped_pure (m := m) _ _ _
        · exact stopped_pure (m := m) _ _ _
      · exact stopped_pure (m := m) _ _ _
  | .loop site maximum yielded operands declared body, env, proof, used, next, next', continues => by
      simp only [meteredStep]
      cases operands with
      | nil => exact stopped_pure (m := m) _ _ _
      | cons count refs =>
          simp only
          cases countEq : env[count]? with
          | none => exact stopped_pure (m := m) _ _ _
          | some value =>
              cases carriedEq : Domain.read env refs with
              | none =>
                  cases value with
                  | transcript | indices => exact stopped_pure (m := m) _ _ _
                  | data payload =>
                      rcases payload with ⟨ty, admissible, contents⟩
                      cases ty <;> exact stopped_pure (m := m) _ _ _
              | some carried =>
                  cases value with
                  | transcript | indices => exact stopped_pure (m := m) _ _ _
                  | data payload =>
                      rcases payload with ⟨ty, data, value⟩
                      cases ty <;> try (exact stopped_pure (m := m) _ _ _)
                      by_cases admitted : value ≤ maximum ∧ Domain.sortsMatch declared carried = true
                      · simp only [admitted, and_self, ite_true]
                        by_cases fits : used + 1 ≤ budget
                        · simp only [fits, ite_true, Domain.step, countEq, carriedEq, admitted, and_self, ite_true,
                            DomainAdapter.runK_bind]
                          apply meteredIterate_prunes key initial challenge budget
                            (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions body))
                            (fun start unread charged continuation =>
                              meteredK program context key initial challenge cost budget body start unread charged continuation)
                            (fun start unread charged continuation continuation' good =>
                              meteredK_prunes body start unread charged continuation continuation' good)
                          intro final unread charged
                          by_cases sorted : Domain.sortsMatch declared final = true
                          · simpa only [sorted, ite_true, DomainAdapter.runK] using continues (env ++ final) unread charged
                          · simp only [sorted]
                            exact .refl _
                        · simp only [fits, ite_false]; exact stopped_pure (m := m) _ _ _
                      · simp only [admitted, ite_false]; exact stopped_pure (m := m) _ _ _

end

/-- All budgets preserve the canonical action prefix. Return exhaustion is a
pruning stop after all effects of the body, rather than an effect-free result
that could erase earlier oracle calls. -/
theorem metered_prunes (lowered : Lowered) (env : Environment F G) (proof : Proof F G) :
    Prunes Stopped
      (metered program context key initial challenge cost budget lowered env proof)
      (DomainAdapter.runK key initial challenge
        (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions lowered.code) env)
        proof (fun final unread => pure
          (match Domain.read final lowered.returned with
          | some returned => .returned returned
          | none => .stopped .refused, unread))) := by
  unfold metered
  apply meteredK_prunes program context key initial challenge cost budget
  intro final unread charged
  by_cases fits : charged + 1 ≤ budget
  · simp only [fits, ite_true]
    cases Domain.read final lowered.returned <;> exact Prunes.refl (m := m) _
  · simp only [fits, ite_false]
    exact stopped_pure (m := m) _ _ _

end Zkc.Executable.DomainVM
