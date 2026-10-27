module

public import ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot

@[expose] public section

/-! Focused changed-representation controls. These checks exercise the actual
source client, nominal transport, exact shape, update square and sample space.
The generated bindings retain the actual native export and its root consumer. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace TestsSecurity.KoalaBearSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Polynomial.Multilinear
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Domains.KoalaBear (Base Octic q embed generator)
open ZkcSecurity.Domains.KoalaBearModel (model baseIdentity octicIdentity)
open ZkcSecurity.Examples.Components.KoalaBearSumcheck

/-- This is an extension challenge outside the embedded base field. -/
theorem generator_not_base (a : Base) : generator ≠ embed a := by
  intro same
  have coefficient := congrArg (fun x : Octic => CompPoly.Extension.Ext.coeff x (1 : Fin 8)) same
  change (1 : Base) = 0 at coefficient
  exact one_ne_zero coefficient

/-- A real source producer/verifier run at a genuinely non-base challenge.
The proof packets and coin are both consumed, with residual truth preserved. -/
example : ∃ result events,
    (actual (17, initial (0 : Base) 1 ())).run handler
      (((ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.producer 0 1).run
        (producerHandler generator) ()).events, [generator]) =
      ⟨.returned result, ([], []), events⟩ ∧ representation.Yes result :=
  source_honest 0 1 () 17 generator

example : Fintype.card Octic = q ^ 8 := challenge_cardinality
example : (1 : ENNReal) / ((q ^ 8 : Nat) : ENNReal) ≠ 1 / (q : ENNReal) := wrong_denominator
example : model.Field baseIdentity ≠ model.Field octicIdentity :=
  ZkcSecurity.Domains.KoalaBearModel.carriers_ne

example : ZkcSecurity.Domains.KoalaBearModel.catalogue.requireEmbedding
    baseIdentity octicIdentity ≠ .ok () := by decide

/-- Same characteristic does not authorize nominal transport. -/
example (a : Base) : (Domain.Payload.field (carriers := model.toCarriers) baseIdentity a).value
    (.field octicIdentity) = none := rfl

example (a : Base) (r : Octic) :
    handler (.receive (.field octicIdentity) "low" 0) ([Domain.Payload.field baseIdentity a], [r]) =
      ⟨.stopped .refused, ([Domain.Payload.field baseIdentity a], [r]), []⟩ := rfl

/-- The affine shift has the right host types and the wrong embedding laws. -/
theorem shifted_embedding_refused {B E : Type} [Field B] [Field E] (e : B →+* E) :
    ¬ EmbeddingLaw (fun x => e x + 1) := by
  intro law
  have bad := law.map_zero
  simp only [map_zero, zero_add] at bad
  exact one_ne_zero bad

example : ¬ EmbeddingLaw (fun x : Base => embed x + 1) := shifted_embedding_refused embed

/-- The list decoder refuses an actual malformed table. The dimension-indexed
family also cannot construct a state with this original list and empty prefix. -/
example : Zkc.Polynomial.Multilinear.ofList? 1 ([0] : List Base) = none := by
  unfold Zkc.Polynomial.Multilinear.ofList?
  simp

example : ¬ ∃ state : State Unit 1, state.original = [0] ∧ state.point = [] := by
  rintro ⟨state, original, point⟩
  have shape := state.shape
  rw [original, point] at shape
  norm_num at shape

example (state : State Unit 1) :
    readback state (.cons none (.cons (some generator) .nil)) = .halt .incomplete := rfl
example (state : State Unit 1) :
    readback state (.cons (some generator) (.cons none .nil)) = .halt .incomplete := rfl

/-- Raw sealed carries require both fields and exactly one point extension. -/
example (priorPoint : List Octic) (value : Octic) :
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.decodeEvaluation priorPoint
      (.cons none (.cons (some value) .nil)) = .halt .incomplete := rfl
example (priorPoint point : List Octic) :
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.decodeEvaluation priorPoint
      (.cons (some point) (.cons none .nil)) = .halt .incomplete := rfl
example (priorPoint : List Octic) (value : Octic) :
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.decodeEvaluation priorPoint
      (.cons (some priorPoint) (.cons (some value) .nil)) = .halt .reject := by
  simp [ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.decodeEvaluation,
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.decodeCarry, Values.get]
example (r value : Octic) :
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.decodeEvaluation []
      (.cons (some [r, r]) (.cons (some value) .nil)) = .halt .reject := rfl
example (p r value : Octic) (different : p ≠ r) :
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.decodeEvaluation [p]
      (.cons (some [r, r]) (.cons (some value) .nil)) = .halt .reject := by
  simp [ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.decodeEvaluation,
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.decodeCarry, Values.get, List.take, Ne.symm different]

/-- Returning the two octic fields in the wrong order changes the state. Host
types alone would accept this mistake; the whole-body binding does not. -/
theorem swapped_readback_refused (state : State Unit 1) (x r : Octic) (different : x ≠ r) :
    readback state (.cons (some r) (.cons (some x) .nil)) ≠
      readback state (.cons (some x) (.cons (some r) .nil)) := by
  intro same
  have states : { state.advance (0, 0) x with scalar := r } =
      { state.advance (0, 0) r with scalar := x } := PIR.Process.done.inj same
  exact different (congrArg (fun s : State Unit 0 => s.scalar) states).symm

/-- A view which forgets the accumulated prefix agrees initially and then
fails the update square, for every extension challenge. -/
def frozenView {n : Nat} (state : State Unit n) : List Octic := state.original.map embed

example (a b : Base) : frozenView (initial a b ()) = layout.entries (initial a b ()) := rfl

theorem frozen_update_refused (a b : Base) (r : Octic) :
    frozenView ((initial a b ()).advance (embed a, embed b) r) ≠
      restrictValues (frozenView (initial a b ())) r := by
  intro same
  have lengths := congrArg List.length same
  have unchanged : (frozenView ((initial a b ()).advance (embed a, embed b) r)).length = 2 := rfl
  have reduced := restrictValues_length (frozenView (initial a b ())) r (m := 1) rfl
  rw [unchanged, reduced] at lengths
  omega

/-- The complete actual Root accepts at a challenge outside the embedded base. -/
example : ∃ events,
    (ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.verifier 0 1 1 17).run handler
      (((ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.producer 0 1).run
        (producerHandler generator) ()).events, [generator]) =
      ⟨.returned (some true), ([], []), events⟩ := by
  simpa only [zero_add] using
    (ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.completeness (0 : Base) 1 () 17 generator)

example (a b claim : Base) (handle : Nat) (r : Octic) :
    (ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.verifier a b claim handle).run handler ([], [r]) =
      ⟨.stopped .refused, ([], [r]), []⟩ := by
  rw [ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.verifier,
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.root_verifier_equation,
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.verifier_equation]
  rfl

/-- Nominal packet refusal retains the complete state, even at the full root. -/
example (a b claim : Base) (handle : Nat) (r : Octic) (suffix : List Packet) :
    (ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.verifier a b claim handle).run handler
      (.field baseIdentity a :: suffix, [r]) =
      ⟨.stopped .refused, (.field baseIdentity a :: suffix, [r]), []⟩ := by
  rw [ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.verifier,
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.root_verifier_equation,
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.verifier_equation]
  rfl

/-- Missing root inputs are not replaced by mathematical defaults. -/
example (a b : Base) (handle : Nat) :
    ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.rootSource 1
      (.cons (some a) (.cons (some b) (.cons none (.cons (some handle) .nil)))) =
      PIR.Process.halt .incomplete := by
  apply (ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.root_verifier_binding
    (.cons (some a) (.cons (some b) (.cons none (.cons (some handle) .nil))))).trans
  kernel_rfl

#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.verifier_equation
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheck.binding
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheck.octic_soundness
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheck.source_honest
#print axioms ZkcSecurity.Domains.KoalaBear.card_octic
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.root_verifier_equation
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.soundness
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.completeness
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.query_bound
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckRoot.source_doomed
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.target_association
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckSource.source_relation

end TestsSecurity.KoalaBearSumcheck
