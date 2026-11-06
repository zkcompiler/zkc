module

public import ZkcArkLib.Fri.PhasesCausal
public import ZkcSecurity.Mathematics.Oracle.Coupling

/-!
# Scalar and block query phases

Scalar requests and deliveries alternate. Block makes one product-position request and one
delivery. Delivery callbacks can change hidden state and abort after seeing the draw. The
successful vector's unnormalized event mass is dominated by uniform product sampling. It is
not conditionally uniform given success. Only the complete interactive phase has the product
bound; no scalar draw is assigned the compound query error or a block Fiat--Shamir key.
-/

@[expose] public section

set_option autoImplicit false

namespace ZkcSecurity.ArkLib.Fri.Phases

open OracleComp

inductive QueryPolicy where
  | scalar | block
  deriving DecidableEq, Repr

/-- Exact mathematical request/delivery ABI, before source framing and encoding. -/
inductive SamplingOperation (n : ℕ) where
  | scalar (ordinal : ℕ)
  | block (count : ℕ)
  | revealScalar (ordinal : ℕ) (position : Fin (2 ^ n))
  | revealBlock (count : ℕ) (positions : Fin count → Fin (2 ^ n))

def SamplingOperation.Reply {n : ℕ} : SamplingOperation n → Type
  | .scalar _ => Fin (2 ^ n)
  | .block count => Fin count → Fin (2 ^ n)
  | .revealScalar .. | .revealBlock .. => Unit

def samplingOperations (n : ℕ) : PIR.Signature := ⟨SamplingOperation n, SamplingOperation.Reply⟩

/-- First request, delivery, then the remaining requests. Ordinals preserve source order. -/
def scalarQueries (n : ℕ) : (count : ℕ) → ℕ →
    PIR.Process (samplingOperations n) (Fin count → Fin (2 ^ n))
  | 0, _ => .done Fin.elim0
  | count + 1, ordinal => .call (.scalar ordinal) fun position =>
      .call (.revealScalar ordinal position) fun _ =>
        (scalarQueries n count (ordinal + 1)).bind
          (fun tail ↦ .done (Fin.cons position tail))

def blockQueries (n count : ℕ) :
    PIR.Process (samplingOperations n) (Fin count → Fin (2 ^ n)) :=
  .call (.block count) fun positions =>
    .call (.revealBlock count positions) fun _ => .done positions

def queries (policy : QueryPolicy) (n count : ℕ) :
    PIR.Process (samplingOperations n) (Fin count → Fin (2 ^ n)) :=
  match policy with
  | .scalar => scalarQueries n count 0
  | .block => blockQueries n count

/-- Request histories are separate from their decoded mathematical distribution. -/
inductive PositionRequest where
  | scalar (bound : ℕ)
  | block (bound count : ℕ)
  deriving DecidableEq, Repr

def requestHistory (policy : QueryPolicy) (n count : ℕ) : List PositionRequest :=
  match policy with
  | .scalar => List.replicate count (.scalar (2 ^ n))
  | .block => [.block (2 ^ n) count]

theorem requestHistory_distinct (n count : ℕ) :
    requestHistory .scalar n count ≠ requestHistory .block n count := by
  cases count <;> simp [requestHistory, List.replicate_succ]

/-- The provider may stop or update private state at either delivery boundary. -/
structure QueryProver (n : ℕ) (S E : Type) where
  scalar : ℕ → Fin (2 ^ n) → S → ProbComp (PIR.Execution S E Unit)
  block : (count : ℕ) → (Fin count → Fin (2 ^ n)) → S → ProbComp (PIR.Execution S E Unit)

/-- These are mathematical history events, not claimed equal to source audit events. -/
inductive SamplingEvent (n : ℕ) (E : Type) where
  | drawScalar (ordinal : ℕ) (position : Fin (2 ^ n))
  | drawBlock (count : ℕ) (positions : Fin count → Fin (2 ^ n))
  | deliveredScalar (ordinal : ℕ) (position : Fin (2 ^ n))
  | deliveredBlock (count : ℕ) (positions : Fin count → Fin (2 ^ n))
  | provider (event : E)

/-- Retain callback stops and poststates; only a successful delivery emits its completion. -/
def deliveryRecord {n : ℕ} {S E : Type} (event : SamplingEvent n E)
    (result : PIR.Execution S E Unit) : PIR.Execution S (SamplingEvent n E) Unit :=
  ⟨result.outcome, result.state, result.events.map .provider ++
    match result.outcome with | .returned _ => [event] | .stopped _ => []⟩

def QueryProver.handler {n : ℕ} {S E : Type} (prover : QueryProver n S E) :
    PIR.MonadHandler ProbComp (samplingOperations n) S (SamplingEvent n E)
  | .scalar ordinal, state => do
      let position ← $ᵗ (Fin (2 ^ n))
      pure ⟨.returned position, state, [.drawScalar ordinal position]⟩
  | .block count, state => do
      let positions ← $ᵗ (Fin count → Fin (2 ^ n))
      pure ⟨.returned positions, state, [.drawBlock count positions]⟩
  | .revealScalar ordinal position, state =>
      deliveryRecord (.deliveredScalar ordinal position) <$> prover.scalar ordinal position state
  | .revealBlock count positions, state =>
      deliveryRecord (.deliveredBlock count positions) <$> prover.block count positions state

/-- The reference product sampler in the same natural ordinal order as the scalar process. -/
def productPositions (n : ℕ) : (count : ℕ) → ProbComp (Fin count → Fin (2 ^ n))
  | 0 => pure Fin.elim0
  | count + 1 => do
      let position ← $ᵗ (Fin (2 ^ n))
      let tail ← productPositions n count
      pure (Fin.cons position tail)

open MeasureTheory ProbabilityTheory in
theorem evalDist_productPositions (n : ℕ) :
    ∀ count [MeasurableSpace (Fin count → Fin (2 ^ n))]
      [MeasurableSingletonClass (Fin count → Fin (2 ^ n))],
      𝒟[productPositions n count] = uniformOn Set.univ := by
  intro count
  induction count with
  | zero =>
      intro _ _
      apply Measure.ext_of_singleton
      intro x
      simp [productPositions, Subsingleton.elim x Fin.elim0,
        uniformOn_univ_apply_singleton]
  | succ count ih =>
      intro _ _
      let : MeasurableSpace (Fin count → Fin (2 ^ n)) := ⊤
      let : MeasurableSpace (Fin (2 ^ n)) := ⊤
      simpa only [productPositions, seq_eq_bind_map, bind_map_left, bind_pure_comp] using
        evalDist_seq_map_eq_uniformOn ($ᵗ (Fin (2 ^ n))) (productPositions n count)
        (fun (position : Fin (2 ^ n)) (tail : Fin count → Fin (2 ^ n)) ↦
          Fin.cons (α := fun _ : Fin (count + 1) ↦ Fin (2 ^ n)) position tail)
        SampleableType.evalDist_uniformSample ih Measurable.of_discrete
        (Fin.consEquiv (fun _ ↦ Fin (2 ^ n))).bijective

theorem productPositions_sameDist (n count : ℕ) :
    productPositions n count =ᵈ $ᵗ (Fin count → Fin (2 ^ n)) := by
  let : MeasurableSpace (Fin count → Fin (2 ^ n)) := ⊤
  exact EvalDistEq.of_evalDist_eq (by
    rw [evalDist_productPositions, SampleableType.evalDist_uniformSample])

/-- Compound phase domination under adaptive state changes and arbitrary delivery aborts. -/
theorem scalarQueries_domination {n : ℕ} {S E : Type} (prover : QueryProver n S E) :
    ∀ count ordinal (state : S) (event : (Fin count → Fin (2 ^ n)) → Prop),
      Pr{let result ← (scalarQueries n count ordinal).runM prover.handler state}[
        returned event result] ≤ Pr{let positions ← productPositions n count}[event positions] := by
  intro count
  induction count with
  | zero => intro ordinal state event; simp [scalarQueries, productPositions,
      PIR.Process.runM, returned]
  | succ count ih =>
      intro ordinal state event
      simp only [scalarQueries, productPositions, PIR.Process.runM, QueryProver.handler,
        bind_assoc, pure_bind]
      simp only [← bind_pure_comp, bind_assoc]
      apply prEvent_bind_mono_of_support
      intro position _
      simp only [bind_pure_comp]
      rw [prEvent_followM]
      dsimp only
      rw [← map_bind]
      apply prEvent_bind_le_of_forall_le
      intro delivery
      rw [prEvent_followM]
      cases delivery with
      | mk outcome after events =>
          cases outcome with
          | stopped why => exact bot_le
          | returned acknowledgment =>
              rw [prEvent_runM_repack]
              simpa only [bind_pure_comp, Functor.map_map, Function.comp_def] using
                ih (ordinal + 1) after (fun tail ↦ event (Fin.cons position tail))

theorem blockQueries_domination {n : ℕ} {S E : Type} (prover : QueryProver n S E)
    (count : ℕ) (state : S) (event : (Fin count → Fin (2 ^ n)) → Prop) :
    Pr{let result ← (blockQueries n count).runM prover.handler state}[returned event result] ≤
      Pr{let positions ← $ᵗ (Fin count → Fin (2 ^ n))}[event positions] := by
  simp only [blockQueries, PIR.Process.runM, QueryProver.handler, bind_assoc, pure_bind]
  simp only [← bind_pure_comp, bind_assoc]
  apply prEvent_bind_mono_of_support
  intro positions _
  simp only [bind_pure_comp]
  rw [prEvent_followM]
  dsimp only
  apply prEvent_bind_le_of_forall_le
  intro delivery
  rw [prEvent_followM]
  cases delivery with
  | mk outcome after events =>
      cases outcome <;> simp [returned]

/-- The same probability bound applies to each policy's full phase, with its own history. -/
theorem queries_domination {n : ℕ} {S E : Type} (prover : QueryProver n S E)
    (policy : QueryPolicy) (count : ℕ) (state : S)
    (event : (Fin count → Fin (2 ^ n)) → Prop) :
    Pr{let result ← (queries policy n count).runM prover.handler state}[returned event result] ≤
      Pr{let positions ← $ᵗ (Fin count → Fin (2 ^ n))}[event positions] := by
  cases policy with
  | scalar =>
      exact (scalarQueries_domination prover count 0 state event).trans_eq
        ((productPositions_sameDist n count).prEvent_eq event)
  | block => exact blockQueries_domination prover count state event

open OracleComp.ProgramLogic.Relational in
/-- A parent can transport the phase bound across differing provider states using only
local action couplings. The parent must first associate its source expansion with this
mathematical phase; this theorem supplies neither that association nor a source-root law. -/
theorem queries_domination_of_local_coupling {n : ℕ} {S T E G O : Type}
    (prover : QueryProver n T E)
    (handler : PIR.MonadHandler ProbComp (samplingOperations n) S G)
    (relation : S → T → Prop) (left : G → List O) (right : SamplingEvent n E → List O)
    (localLaw : ∀ action state ideal, relation state ideal →
      RelTriple (handler action state) (prover.handler action ideal)
        (PIR.Related relation left right))
    (policy : QueryPolicy) (count : ℕ) (state : S) (ideal : T)
    (initial : relation state ideal) (event : (Fin count → Fin (2 ^ n)) → Prop) :
    Pr{let result ← (queries policy n count).runM handler state}[returned event result] ≤
      Pr{let positions ← $ᵗ (Fin count → Fin (2 ^ n))}[event positions] := by
  refine (prEvent_le_of_relTriple
    (ZkcSecurity.VCVio.Coupling.runM_relTriple relation left right handler prover.handler
      localLaw (queries policy n count) state ideal initial) ?_).trans
        (queries_domination prover policy count ideal event)
  intro actual reference related
  unfold returned
  rw [← related.outcome]
  exact id

end ZkcSecurity.ArkLib.Fri.Phases
