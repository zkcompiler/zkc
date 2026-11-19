import Zkc.Formal.ChargedProbability
import Zkc.Formal.Written.UniformChallenge

/-!
The judgment with fees meets the probability library on one uniform draw of a field of five
elements. The process draws once and returns the draw; a bad return is zero.

The hypotheses of the bridge are met by a service that answers: it draws uniformly at the one
port (`follows`, `permitted`). The process is judged within one fifth (`judged`), so the
probability of a bad return is at most one fifth (`bounded`); it is one fifth (`attained`), so
the bound of the bridge is reached. No smaller budget judges the process: one sixth does not
(`not_within_a_sixth`).
-/

open Zkc.Core Zkc.Formal Zkc.Formal.ProbabilisticProcess Zkc.Formal.Written OracleComp
open Zkc.Formal.Written.UniformChallenge (M port draw ask serveAt serves_at permitted)
open ProbComp
open scoped NNRat ENNReal

namespace Zkc.Tests.Formal.ChargedProbability

variable (peers : List Role) (at_ : Occurrence)

/-- The samplers of the one port: its reply is drawn uniformly. No other effect has one. -/
noncomputable def samplers : Samplers (RSig M) := fun op =>
  if h : InputPort.ofOp M op = some (port peers at_) then
    some (cast (congrArg (fun o => ProbComp ((RSig M).Reply o))
      (InputPort.operation_ofOp M h).symm) draw)
  else none

theorem samplers_port :
    samplers peers at_ ((port peers at_).operation M) = some draw := by
  simp only [samplers, InputPort.ofOp_operation, ↓reduceDIte]
  rfl

theorem zero_weight : Pr{let v ← draw}[v = (0 : ZMod 5)] = 1 / 5 := by
  change Pr{let i ← uniformFin 4}[i = (0 : Fin 5)] = _
  rw [prEvent_uniformFin]
  simp only [Finset.filter_eq', Finset.mem_univ, ite_true, Finset.card_singleton, Nat.cast_one]
  norm_num

theorem fifth : ProbabilisticProcess.probability (1 / 5) = 1 / 5 := by
  simp [ProbabilisticProcess.probability]

/-- The process is judged within one fifth: the fee of the draw pays for the reply zero. -/
theorem judged :
    (ask peers at_).interpret (.charged (Permitted M) (paysBy (samplers peers at_)))
      (fun a _ => ¬ a = 0) (fun _ _ => True) (1 / 5) :=
  ⟨1 / 5, fun v : ZMod 5 => v = 0, le_rfl,
    Or.inr ⟨draw, samplers_port peers at_, (zero_weight).le.trans fifth.ge⟩, fun _ _ kept => kept⟩

/-- The service answers only at the port, and what it answers there is permitted. -/
theorem answers_permitted (op : ROp M) (s : Unit) (reply : (RSig M).Reply op) (t : Unit)
    (reached : (some reply, t) ∈ support (serveAt M (port peers at_) draw op s)) :
    Permitted M op reply := by
  by_cases at_port : InputPort.ofOp M op = some (port peers at_)
  · obtain rfl := InputPort.operation_ofOp M at_port
    exact permitted peers at_ reply
  · simp only [serveAt, at_port, ↓reduceDIte, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at reached

/-- The service draws as the samplers do. -/
theorem follows : (serveAt M (port peers at_) draw).Follows (samplers peers at_) := by
  intro op sampler has s excluded
  by_cases at_port : InputPort.ofOp M op = some (port peers at_)
  · obtain rfl := InputPort.operation_ofOp M at_port
    rw [samplers_port] at has
    obtain rfl := Option.some.inj has
    have served := serves_at M (port peers at_) draw s
    rw [served]
    refine (prEvent_map (mx := draw) (f := fun answer => (some answer, s))
      (p := fun out : Option (ZMod 5) × Unit => ∃ v, out.1 = some v ∧ excluded v)).le.trans ?_
    exact prEvent_mono _ _ _ fun v ⟨w, same, ex⟩ => Option.some.inj same ▸ ex
  · simp only [samplers, at_port, ↓reduceDIte, reduceCtorEq] at has

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

/-- A sixth is not enough: a judgment within it would bound the probability below what it is. -/
theorem not_within_a_sixth :
    ¬ (ask peers at_).interpret (.charged (Permitted M) (paysBy (samplers peers at_)))
      (fun a _ => ¬ a = 0) (fun _ _ => True) (1 / 6) := by
  intro within
  have bound := sampled_bounds_probability _ (samplers peers at_) (Permitted M) (fun a => a = 0)
    (answers_permitted peers at_) (follows peers at_) (ask peers at_) (1 / 6) () within
  rw [attained, ← fifth] at bound
  exact absurd (probability_le_iff.mp bound) (by norm_num)

end Zkc.Tests.Formal.ChargedProbability
