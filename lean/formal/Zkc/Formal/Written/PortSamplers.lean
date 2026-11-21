module

public import Zkc.Formal.ChargedProbability
public import Zkc.Formal.Written.Source
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-!
The service and the samplers of one port, and the uniform draw of a position.

A port is one effect of a role, fully specified: the law or the flow, the other roles, the
occurrence and the type of the reply. Its service answers at that effect by a draw, and nowhere
else; its samplers draw the reply of that effect and of no other. The service follows the
samplers, and what it answers is permitted when what the draw gives is. These are the
hypotheses of the bridge from the judgment with fees to a probability, met by a service that
answers. The run of a process that begins with the port, against that service, is the draw and
then what follows the reply (`prEvent_run_serveAt`).

The uniform law on `fin n` draws a position: in a model whose positions are naturals, a natural
below `n`, by VCVio's uniform sampler of `Fin n`. A set of positions has the probability of its
count over `n`; the count of the positions of a list that hold a value is Mathlib's.
-/

namespace Zkc.Formal.Written
open Core ProbabilisticProcess OracleComp ProbComp
open scoped NNRat ENNReal

/-- A service for one fully specified port. Matching uses the typed law, audience, arguments,
reply type and occurrence represented by the source port. -/
def serveAt {V : Vocabulary} (M : Model V) (port : InputPort V)
    (draw : ProbComp ((RSig M).Reply (port.operation M))) : Service (RSig M) Unit :=
  fun op s ↦ if h : InputPort.ofOp M op = some port then
    let replyEq := congrArg (RSig M).Reply (InputPort.operation_ofOp M h).symm
    (fun answer ↦ (some (cast replyEq answer),s)) <$> draw
  else pure (none,s)

theorem serves_at {V : Vocabulary} (M : Model V) (port : InputPort V)
    (draw : ProbComp ((RSig M).Reply (port.operation M))) (s : Unit) :
    serveAt M port draw (port.operation M) s = (fun answer ↦ (some answer,s)) <$> draw := by
  simp [serveAt, InputPort.ofOp_operation]

theorem unavailable_of_different_port {V : Vocabulary} (M : Model V) {p q : InputPort V}
    (draw : ProbComp ((RSig M).Reply (p.operation M))) (apart : q ≠ p) (s : Unit) :
    serveAt M p draw (q.operation M) s = pure (none,s) := by
  simp [serveAt, InputPort.ofOp_operation, apart]

section
variable {V : Vocabulary} (M : Model V) (port : InputPort V)
  (draw : ProbComp ((RSig M).Reply (port.operation M)))

/-- The samplers of one port: its reply is drawn by `draw`. No other effect has one. -/
noncomputable def portSamplers : Samplers (RSig M) := fun op =>
  if h : InputPort.ofOp M op = some port then
    some (cast (congrArg (fun o => ProbComp ((RSig M).Reply o))
      (InputPort.operation_ofOp M h).symm) draw)
  else none

theorem portSamplers_at : portSamplers M port draw (port.operation M) = some draw := by
  simp only [portSamplers, InputPort.ofOp_operation, ↓reduceDIte]
  rfl

/-- The service of the port draws as its samplers do. -/
theorem serveAt_follows :
    (serveAt M port draw).Follows (portSamplers M port draw) := by
  intro op sampler has s excluded
  by_cases at_port : InputPort.ofOp M op = some port
  · obtain rfl := InputPort.operation_ofOp M at_port
    rw [portSamplers_at] at has
    obtain rfl := Option.some.inj has
    rw [serves_at M port draw s]
    refine (prEvent_map (mx := draw) (f := fun answer => (some answer, s))
      (p := fun out : Option ((RSig M).Reply (port.operation M)) × Unit =>
        ∃ v, out.1 = some v ∧ excluded v)).le.trans ?_
    exact prEvent_mono _ _ _ fun v ⟨w, same, ex⟩ => Option.some.inj same ▸ ex
  · simp only [portSamplers, at_port, ↓reduceDIte, reduceCtorEq] at has

/-- The service of the port answers only at the port, and there only what the draw gives. -/
theorem serveAt_permitted
    (allowed : ∀ v, v ∈ support draw → Permitted M (port.operation M) v)
    (op : ROp M) (s : Unit) (reply : (RSig M).Reply op) (t : Unit)
    (reached : (some reply, t) ∈ support (serveAt M port draw op s)) :
    Permitted M op reply := by
  by_cases at_port : InputPort.ofOp M op = some port
  · obtain rfl := InputPort.operation_ofOp M at_port
    rw [serves_at M port draw s] at reached
    simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at reached
    obtain ⟨v, drawn, rfl, _⟩ := reached
    exact allowed v drawn
  · simp only [serveAt, at_port, ↓reduceDIte, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at reached

/-- The run of a process that begins with the port, against the service of the port whose draw
is a map of another: when what follows each reply ends with a known outcome, an event of the
outcome has the probability of the draws whose outcome is in it. -/
theorem prEvent_run_serveAt {ι H A : Type} (base : ProbComp ι)
    (reply : ι → (RSig M).Reply (port.operation M))
    (next : (RSig M).Reply (port.operation M) → Process (RSig M) H A)
    (outcome : ι → ProbabilisticProcess.Outcome H A)
    (ends : ∀ i, run (serveAt M port (reply <$> base)) (next (reply i)) () = pure (outcome i, ()))
    (event : ProbabilisticProcess.Outcome H A → Prop) :
    Pr{let out ← run (serveAt M port (reply <$> base)) (.call (port.operation M) next) ()}[
        event out.1] = Pr{let i ← base}[event (outcome i)] := by
  have runs : run (serveAt M port (reply <$> base)) (.call (port.operation M) next) () =
      (fun i => (outcome i, ())) <$> base := by
    rw [run_call, serves_at, Functor.map_map, bind_map_left]
    change (base >>= fun i => run (serveAt M port (reply <$> base)) (next (reply i)) ()) = _
    rw [show (fun i => run (serveAt M port (reply <$> base)) (next (reply i)) ()) =
      fun i => pure (outcome i, ()) from funext ends]
    exact bind_pure_comp _ _
  rw [runs, prEvent_map]

end

/-- A position below `n + 1`, drawn uniformly. -/
noncomputable def drawPosition (n : ℕ) : ProbComp ℕ :=
  (fun i : Fin (n + 1) => (i : ℕ)) <$> ($ᵗ (Fin (n + 1)))

/-- A set of positions has the probability of its count among the `n + 1` positions. -/
theorem prEvent_drawPosition (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    Pr{let v ← drawPosition n}[p v] =
      ((Finset.univ.filter fun i : Fin (n + 1) => p i).card : ℝ≥0∞) / (n + 1) := by
  rw [drawPosition, prEvent_map, SampleableType.prEvent_uniformSample, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one]

/-- A drawn position is a given one with probability at most one over the positions. -/
theorem prEvent_drawPosition_eq_le (n position : ℕ) :
    Pr{let v ← drawPosition n}[v = position] ≤
      toProbability (((1 : ℕ) : ℚ≥0) / ((n + 1 : ℕ) : ℚ≥0)) := by
  rw [prEvent_drawPosition, toProbability_natCast_div 1 (n + 1) (Nat.succ_pos n)]
  have few : (Finset.univ.filter fun i : Fin (n + 1) => (i : ℕ) = position).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb =>
      Fin.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  push_cast
  exact ENNReal.div_le_div_right (by exact_mod_cast few) _

/-- What a draw of a position gives is a position. -/
theorem lt_of_mem_support_drawPosition (n v : ℕ) (drawn : v ∈ support (drawPosition n)) :
    v < n + 1 := by
  simp only [drawPosition, support_map, Set.mem_image] at drawn
  obtain ⟨i, _, rfl⟩ := drawn
  exact i.isLt

/-! ## The entry at a drawn position -/

section
variable {α : Type} [DecidableEq α]

/-- The positions of a list at which the entry is `v` are as many as the entries that are `v`. -/
theorem card_positions (xs : List α) (n : ℕ) (length : xs.length = n) (v : α) :
    (Finset.univ.filter fun i : Fin n => xs[(i : ℕ)]? = some v).card = xs.count v := by
  subst length
  have counted := List.count_ofFn (fun i : Fin xs.length => xs[(i : ℕ)]) v
  rw [List.ofFn_getElem] at counted
  rw [counted]
  refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
  rw [List.getElem?_eq_getElem i.isLt, Option.some.injEq]

/-- The entries that are `v` and the entries that are not are all the entries. -/
theorem count_add_countP_ne (xs : List α) (v : α) :
    xs.count v + xs.countP (· ≠ v) = xs.length := by
  rw [List.length_eq_countP_add_countP (· == v) (l := xs), List.count]
  congr 2

/-- The entry of a list at a drawn position is `v` with the probability of the count of `v`
among the entries. -/
theorem prEvent_drawPosition_entry (xs : List α) (n : ℕ) (length : xs.length = n + 1) (v : α) :
    Pr{let z ← drawPosition n}[xs[z]? = some v] = (xs.count v : ℝ≥0∞) / (n + 1) := by
  rw [prEvent_drawPosition, card_positions xs (n + 1) length v]

end

end Zkc.Formal.Written
