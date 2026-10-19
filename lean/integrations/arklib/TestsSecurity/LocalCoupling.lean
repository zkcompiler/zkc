import ZkcSecurity.VCVio.Coupling
import ZkcSecurity.VCVio.Execution
import Zkc.Source.Structure

/-! Finite controls and two typed Region clients for local execution coupling.
These are protocol shapes, not cryptographic security theorems. -/
namespace TestsSecurity.LocalCoupling

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational
open ZkcSecurity.VCVio.Execution ZkcSecurity.VCVio.Coupling
open Zkc.Source
open scoped ENNReal

abbrev Bit := Fin 2

inductive Event where
  | before
  | after (bit : Bit)
  | sent (bit : Bit)
  | received (site counter : Nat)
  deriving DecidableEq, Repr

inductive Action where
  | receive (site : Nat)
  | draw (site : String) (handle : Nat)
  | send (bit : Bit)
  deriving DecidableEq, Repr

abbrev interface : PIR.Signature where
  Op := Action
  Reply
    | .receive _ | .draw _ _ => Bit
    | .send _ => Unit

def before : Phase Nat Event Unit := fun s => pure ⟨.returned (), s + 1, [.before]⟩

def after (selective : Bool) (r : Bit) : Phase Nat Event Unit := fun s =>
  pure ⟨if selective && r == 0 then .stopped .exhausted else .returned (),
    s + 1, [.after r]⟩

/-- Both receive sites and every service alias share the same mutable counter. -/
def handler (selective : Bool) : PIR.MonadHandler ProbComp interface Nat Event
  | .receive site, s => pure ⟨.returned ⟨s % 2, Nat.mod_lt _ (by decide)⟩,
      s + 1, [.received site s]⟩
  | .draw site handle, s =>
      if site = "challenge" ∧ handle = 7 then freshQuery (F := Bit) before (after selective) s
      else pure ⟨.stopped .refused, s, []⟩
  | .send r, s => pure ⟨.returned (), s + 1, [.sent r]⟩

def draw : PIR.Proc interface Bit := .call (.draw "challenge" 7) .done

def withSend : PIR.Proc interface Bool :=
  draw.bind fun r => .call (.send r) fun _ => .done true

def expected (s : Nat) (r : Bit) : PIR.Execution Nat Event Bool :=
  if r = 0 then ⟨.stopped .exhausted, s + 2, [.before, .after r]⟩
  else ⟨.returned true, s + 3, [.before, .after r, .sent r]⟩

theorem stopped_bit_exact (s : Nat) :
    withSend.runM (handler true) s = (do let r ← ($ᵗ Bit); pure (expected s r)) := by
  simp only [withSend, draw, PIR.Proc.bind, PIR.Proc.runM, handler]
  simp only [and_self, ↓reduceIte, freshQuery, before, pure_bind, PIR.Execution.followM]
  simp only [after, Bool.true_and, bind_assoc, pure_bind]
  apply bind_congr
  intro r
  by_cases hr : r = 0 <;>
    simp [hr, result, expected, Nat.add_assoc]

/-- The stopped branch keeps two increments and the entire ordered prefix. -/
theorem stopped_branch_skips_send (s : Nat) :
    expected s 0 = ⟨.stopped .exhausted, s + 2, [.before, .after 0]⟩ := by
  simp [expected]

theorem returned_branch_records_send (s : Nat) :
    expected s 1 = ⟨.returned true, s + 3, [.before, .after 1, .sent 1]⟩ := by
  simp [expected]

theorem stop_mass (s : Nat) :
    mass (do let e ← withSend.runM (handler true) s
             pure (e.outcome = .stopped .exhausted)) = 1 / 2 := by
  rw [stopped_bit_exact]
  simp only [bind_assoc, pure_bind]
  have observation (r : Bit) :
      (expected s r).outcome = .stopped .exhausted ↔ r = 0 := by
    by_cases h : r = 0 <;> simp [expected, h]
  simp_rw [propext (observation _)]
  change Pr{let r ← ($ᵗ Bit)}[r = 0] = _
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num [Bit]

theorem acceptance_mass (s : Nat) :
    mass (do let e ← withSend.runM (handler true) s
             pure (e.outcome = .returned true)) = 1 / 2 := by
  rw [stopped_bit_exact]
  simp only [bind_assoc, pure_bind]
  have observation (r : Bit) :
      (expected s r).outcome = .returned true ↔ r = 1 := by
    fin_cases r <;> simp [expected]
  simp_rw [propext (observation _)]
  change Pr{let r ← ($ᵗ Bit)}[r = 1] = _
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num [Bit]

theorem draw_exact (s : Nat) :
    draw.runM (handler true) s = (do
      let r ← ($ᵗ Bit)
      pure ⟨if r = 0 then .stopped .exhausted else .returned r,
        s + 2, [.before, .after r]⟩) := by
  simp only [draw, PIR.Proc.runM, handler]
  simp only [and_self, ↓reduceIte, freshQuery, before, pure_bind, PIR.Execution.followM]
  simp only [after, Bool.true_and, bind_assoc, pure_bind]
  apply bind_congr
  intro r
  by_cases hr : r = 0 <;> simp [hr, result, Nat.add_assoc]

noncomputable def returnedMass (s : Nat) (r : Bit) : ENNReal :=
  mass (do let e ← draw.runM (handler true) s; pure (e.outcome = .returned r))

noncomputable def survivalMass (s : Nat) : ENNReal :=
  mass (do let e ← draw.runM (handler true) s
           pure (returnedSatisfies (fun _ => True) e))

theorem returned_zero_mass (s : Nat) : returnedMass s 0 = 0 := by
  unfold returnedMass
  rw [draw_exact]
  simp only [bind_assoc, pure_bind]
  have observation (r : Bit) :
      (if r = 0 then PIR.Outcome.stopped .exhausted else .returned r) = .returned 0 ↔ False := by
    by_cases h : r = 0 <;> simp [h]
  simp_rw [propext (observation _)]
  simp [mass]

theorem returned_one_mass (s : Nat) : returnedMass s 1 = 1 / 2 := by
  unfold returnedMass
  rw [draw_exact]
  simp only [bind_assoc, pure_bind]
  have observation (r : Bit) :
      (if r = 0 then PIR.Outcome.stopped .exhausted else .returned r) = .returned 1 ↔ r = 1 := by
    fin_cases r <;> simp
  simp_rw [propext (observation _)]
  change Pr{let r ← ($ᵗ Bit)}[r = 1] = _
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num [Bit]

theorem survival_mass (s : Nat) : survivalMass s = 1 / 2 := by
  unfold survivalMass
  rw [draw_exact]
  simp only [bind_assoc, pure_bind]
  have observation (r : Bit) :
      returnedSatisfies (fun _ : Bit => True)
        ⟨if r = 0 then .stopped .exhausted else .returned r,
          s + 2, [Event.before, .after r]⟩ ↔ r = 1 := by
    fin_cases r <;> simp [returnedSatisfies]
  simp_rw [propext (observation _)]
  change Pr{let r ← ($ᵗ Bit)}[r = 1] = _
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num [Bit]

/-- Explicit finite conditioning: the denominator is positive, and the mass of
one among returned challenges is one, whereas the original bit mass is 1/2. -/
theorem conditional_survival_not_uniform (s : Nat) :
    survivalMass s ≠ 0 ∧ returnedMass s 0 / survivalMass s = 0 ∧
    returnedMass s 1 / survivalMass s = 1 ∧
    returnedMass s 1 / survivalMass s ≠ 1 / 2 := by
  rw [survival_mass, returned_zero_mass, returned_one_mass]
  have ratio : (1 / 2 : ENNReal) / (1 / 2) = 1 :=
    ENNReal.div_self (by norm_num) (by finiteness)
  simp only [ratio]
  norm_num
  intro impossible
  have realEquality := congrArg ENNReal.toReal impossible
  norm_num at realEquality

/-- This exact OracleComp equation eliminates the draw itself, not only its
observation. The arbitrary after callback and suffix cannot run. -/
theorem before_stop {A : Type} (afterWork : Bit → Phase Nat Event Unit)
    (suffix : Bit → Nat → ProbComp (PIR.Execution Nat Event A)) (s : Nat) :
    (do let e ← freshQuery
          (fun s => pure ⟨.stopped .abort, s + 1, [Event.before]⟩) afterWork s
        e.followM suffix) = pure ⟨.stopped .abort, s + 1, [.before]⟩ := by
  simp [freshQuery, PIR.Execution.followM]

def twoReceives : PIR.Proc interface (Bit × Bit) :=
  .call (.receive 0) fun low => .call (.receive 1) fun high => .done (low, high)

theorem shared_mutable_receives : twoReceives.runM (handler false) 0 =
    pure ⟨.returned (0, 1), 2, [.received 0 0, .received 1 1]⟩ := by
  simp [twoReceives, PIR.Proc.runM, handler, PIR.Execution.followM]

/-- The same service handle is called twice, threading one shared counter. -/
def twoDraws : PIR.Proc interface (Bit × Bit) :=
  draw.bind fun a => draw.bind fun b => .done (a, b)

theorem unselective_draw (s : Nat) :
    draw.runM (handler false) s = (do
      let r ← ($ᵗ Bit)
      pure ⟨.returned r, s + 2, [.before, .after r]⟩) := by
  simp [draw, PIR.Proc.runM, handler, freshQuery, before, after,
    PIR.Execution.followM, result, Nat.add_assoc]

theorem shared_handle_two_draws (s : Nat) :
    twoDraws.runM (handler false) s = (do
      let a ← ($ᵗ Bit)
      let b ← ($ᵗ Bit)
      pure ⟨.returned (a, b), s + 4, [.before, .after a, .before, .after b]⟩) := by
  simp only [twoDraws, PIR.runM_bind, unselective_draw, bind_assoc, pure_bind,
    PIR.Execution.followM]
  simp [PIR.Proc.runM, Nat.add_assoc]

theorem wrong_route_refuses (s : Nat) :
    (PIR.Proc.call (I := interface) (.draw "other" 7) PIR.Proc.done).runM (handler false) s =
      pure ⟨.stopped .refused, s, []⟩ := by
  simp [PIR.Proc.runM, handler, PIR.Execution.followM]

def stoppingSend : PIR.MonadHandler ProbComp interface Nat Event
  | .send bit, s => pure ⟨.stopped .abort, s + 1, [.sent bit]⟩
  | action, s => handler false action s

/-- A send stop suppresses the subsequent receive, retaining its own effect. -/
theorem stopped_send_skips_receive (s : Nat) (r : Bit) :
    (PIR.Proc.call (I := interface) (.send r) fun _ =>
      PIR.Proc.call (.receive 9) PIR.Proc.done).runM stoppingSend s =
      pure ⟨.stopped .abort, s + 1, [.sent r]⟩ := by
  simp [PIR.Proc.runM, stoppingSend, PIR.Execution.followM]

/-- A service that caches its first draw, unlike the installed fresh service. -/
def cachedDraw : Phase (Option Bit) Event Bit
  | some r => pure ⟨.returned r, some r, [.after r]⟩
  | none => do
      let r ← ($ᵗ Bit)
      pure ⟨.returned r, some r, [.after r]⟩

theorem cached_second_zero_mass :
    mass (do let e ← cachedDraw (some 0); pure (e.outcome = .returned 1)) = 0 := by
  simp [cachedDraw, mass]

theorem fresh_one_mass (s : Nat) :
    mass (do let e ← draw.runM (handler false) s; pure (e.outcome = .returned 1)) =
      1 / 2 := by
  rw [unselective_draw]
  simp only [bind_assoc, pure_bind, PIR.Outcome.returned.injEq]
  change Pr{let r ← ($ᵗ Bit)}[r = 1] = _
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num [Bit]

/-- Once zero is cached, even the reply marginal of a fresh second draw fails. -/
theorem cached_second_not_fresh (s : Nat) :
    mass (do let e ← cachedDraw (some 0); pure (e.outcome = .returned 1)) ≠
      mass (do let e ← draw.runM (handler false) s; pure (e.outcome = .returned 1)) := by
  rw [cached_second_zero_mass, fresh_one_mass]
  intro impossible
  have realEquality := congrArg ENNReal.toReal impossible
  norm_num at realEquality

structure Stored where
  count : Nat
  privateFlag : Bool

/-- Different state/event representations; the extra event is private. -/
def representedHandler (selective : Bool) :
    PIR.MonadHandler ProbComp interface Stored (Option Event) := fun action t => do
  let e ← handler selective action t.count
  pure ⟨e.outcome, ⟨e.state, !t.privateFlag⟩, none :: e.events.map some⟩

def observe : Option Event → List Event
  | none => []
  | some e => [e]

def stateRelated (s : Nat) (t : Stored) : Prop := s = t.count

theorem representation_action_law (selective : Bool) (action : Action)
    (s : Nat) (t : Stored) (related : stateRelated s t) :
    RelTriple (handler selective action s) (representedHandler selective action t)
      (PIR.Related stateRelated (fun e => [e]) observe) := by
  unfold stateRelated at related
  subst s
  have coupled : RelTriple
      (handler selective action t.count >>= fun e => (pure e : ProbComp _))
      (representedHandler selective action t)
      (PIR.Related stateRelated (fun e => [e]) observe) := by
    unfold representedHandler
    apply relTriple_bind (relTriple_refl (handler selective action t.count))
    intro a b same
    change a = b at same
    subst b
    apply relTriple_pure_pure
    refine ⟨rfl, rfl, ?_⟩
    simp [PIR.observeEvents, observe, List.flatMap_map]
  simpa only [bind_pure] using coupled

theorem unequal_state_representations (selective : Bool) {A : Type}
    (process : PIR.Proc interface A) (s : Nat) (flag : Bool) :
    RelTriple (process.runM (handler selective) s)
      (process.runM (representedHandler selective) ⟨s, flag⟩)
      (PIR.Related stateRelated (fun e => [e]) observe) :=
  runM_relTriple stateRelated _ _ _ _ (representation_action_law selective) _ _ _ rfl

end TestsSecurity.LocalCoupling
