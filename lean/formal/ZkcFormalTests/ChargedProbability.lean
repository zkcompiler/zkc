import ZkcFormal.ChargedProbability
import ZkcFormal.OracleProcess
import ZkcFormal.Written.UniformChallenge
import ZkcFormal.Written.SiteAllowance

/-!
The judgment with fees meets the probability library on one uniform draw of a field of five
elements. The process draws once and returns the draw; a bad return is zero.

The hypotheses of the bridge are met by a service that answers: it draws uniformly at the one
port (`follows`, `permitted`). The process is judged within one fifth (`judged`), so the
probability of a bad return is at most one fifth (`bounded`); it is one fifth (`attained`), so
the bound of the bridge is reached. No budget below one fifth judges the process
(`not_within_less`). The same probability is that of VCVio's simulation of the process by the
service's handler (`simulation_attained`).

The last section is about the two parts of one event, for every model: a charge allows the
owner and a hearer the same, and under the samplers of the owning port a hearer pays nothing.
-/

open Zkc.Core ZkcFormal ZkcFormal.ProbabilisticProcess ZkcFormal.Written OracleComp
open ZkcFormal.Written.UniformChallenge (M port draw ask permitted)
open ProbComp
open scoped NNRat ENNReal

namespace ZkcFormalTests.ChargedProbability

variable (peers : List Role) (at_ : Occurrence)

/-- The samplers of the one port: its reply is drawn uniformly. No other effect has one. -/
noncomputable abbrev samplers : Samplers (RSig M) := portSamplers M (port peers at_) draw

theorem zero_weight : Pr{let v ← draw}[v = (0 : ZMod 5)] = 1 / 5 := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card]
  norm_num

theorem fifth : toProbability (1 / 5) = 1 / 5 := by
  simp [toProbability]

/-- The process is judged within one fifth: the fee of the draw pays for the reply zero. -/
theorem judged :
    (ask peers at_).interpret (.charged (Permitted M) (paysBy (samplers peers at_)))
      (fun a _ => ¬ a = 0) (fun _ _ => True) (1 / 5) :=
  ⟨1 / 5, fun v : ZMod 5 => v = 0, le_rfl,
    Or.inr ⟨draw, portSamplers_at M (port peers at_) draw, (zero_weight).le.trans fifth.ge⟩, fun _ _ kept => kept⟩

/-- The service answers only at the port, and what it answers there is permitted. -/
theorem answers_permitted (op : ROp M) (s : Unit) (reply : (RSig M).Reply op) (t : Unit)
    (reached : (some reply, t) ∈ support (serveAt M (port peers at_) draw op s)) :
    Permitted M op reply :=
  serveAt_permitted M (port peers at_) draw (fun v _ => permitted peers at_ v) op s reply t reached

/-- The service draws as the samplers do. -/
theorem follows : (serveAt M (port peers at_) draw).Follows (samplers peers at_) :=
  serveAt_follows M (port peers at_) draw

/-- The probability of a bad return is at most the budget of the judgment. -/
theorem bounded :
    Pr{let out ← run (serveAt M (port peers at_) draw) (ask peers at_) ()}[
      ∃ a, out.1 = .returned a ∧ a = 0] ≤ 1 / 5 :=
  (sampled_bounds_probability _ (samplers peers at_) (Permitted M) (fun a => a = 0)
    (answers_permitted peers at_) (follows peers at_) (ask peers at_) (1 / 5) ()
    (judged peers at_)).trans fifth.le

/-- The bound is reached. -/
theorem attained :
    Pr{let out ← run (serveAt M (port peers at_) draw) (ask peers at_) ()}[
      ∃ a, out.1 = .returned a ∧ a = 0] = 1 / 5 := by
  rw [← UniformChallenge.probability peers at_ 0]
  refine prEvent_congr_of_support _ _ _ fun out _ => ⟨?_, fun same => ⟨0, same, rfl⟩⟩
  rintro ⟨a, same, rfl⟩
  exact same

/-- The same about VCVio's simulation of the process, read as a computation with oracles, by
the service's handler: what is stated about the simulation is what is proved about the run. -/
theorem simulation_attained :
    Pr{let out ← (simulateQ (handlerOf (serveAt M (port peers at_) draw))
        (embed (ask peers at_))).run.run ()}[∃ a, out.1 = some (.inl a) ∧ a = 0] = 1 / 5 := by
  rw [← attained peers at_, prEvent_run _ _ _ fun outcome => ∃ a, outcome = .returned a ∧ a = 0]
  exact prEvent_congr _ _ _ fun out =>
    exists_congr fun _ => and_congr_left fun _ => outcomeOf_eq_returned.symm

/-- No smaller budget judges the process: a judgment within less than one fifth would bound the
probability below what it is. -/
theorem not_within_less (budget : ℚ≥0) (below : budget < 1 / 5) :
    ¬ (ask peers at_).interpret (.charged (Permitted M) (paysBy (samplers peers at_)))
      (fun a _ => ¬ a = 0) (fun _ _ => True) budget := by
  intro within
  have bound := sampled_bounds_probability _ (samplers peers at_) (Permitted M) (fun a => a = 0)
    (answers_permitted peers at_) (follows peers at_) (ask peers at_) budget () within
  rw [attained, ← fifth] at bound
  exact absurd (toProbability_le_iff.mp bound) (not_le.mpr below)

/-! ## The parts of one event

A draw is one event at one address. The role that owns it and a role that hears it have an
effect at that address each, and a written charge allows both the same. The samplers of the
owning port have none where the event is heard, so a role that hears pays no fee there and
excludes no reply. -/

section
open Zkc.Subject (DrawCharge)
variable {V : Vocabulary} (N : Model V) (kind : GivenKind V) (peers : List Role) (owner : Role)
  (at_ : Occurrence) (ty : V.Ty)

/-- A charge allows the two parts of an event the same. -/
theorem same_allowance (charge : DrawCharge) (key : Key) (path : List Frame) :
    allowance N charge key path ((InputPort.own kind peers at_ ty).operation N) =
      allowance N charge key path (.hear kind owner at_ ty) := rfl

/-- The samplers of the owning port have none where the event is heard. -/
theorem no_sampler_at_hearer
    (drawn : ProbComp ((RSig N).Reply ((InputPort.own kind peers at_ ty).operation N))) :
    portSamplers N (.own kind peers at_ ty) drawn (.hear kind owner at_ ty) = none := by
  simp [portSamplers, InputPort.ofOp]

/-- Under those samplers a role that hears the event pays nothing and excludes nothing. -/
theorem hearing_is_free
    (drawn : ProbComp ((RSig N).Reply ((InputPort.own kind peers at_ ty).operation N)))
    (allowance : ROp N → ℚ≥0) (fee : ℚ≥0)
    (excluded : (RSig N).Reply (.hear kind owner at_ ty) → Prop)
    (paid : paysWithin (portSamplers N (.own kind peers at_ ty) drawn) allowance
      (.hear kind owner at_ ty) fee excluded) :
    fee = 0 ∧ ∀ v, ¬ excluded v := by
  rcases paid.1 with free | ⟨sampler, present, _⟩
  · exact free
  · rw [no_sampler_at_hearer N kind peers owner at_ ty drawn] at present
    cases present

end

end ZkcFormalTests.ChargedProbability
