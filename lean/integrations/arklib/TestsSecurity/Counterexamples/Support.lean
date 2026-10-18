import ZkcSecurity.FiatShamir.Roles
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-! Support for the counterexamples.

`numerals` closes an equation or a strict or weak inequality between finite
`ENNReal` numeral expressions through `toReal`. On a finite key type, an event
of a computation in the lazily sampled oracle has the probability of the same
event of its evaluation against a uniform table (`prEvent_randomOracle_table`);
when the event reads only the answers at two distinct keys, that of a uniform
pair (`prEvent_randomOracle_two`). Among `n` independent uniform answers one
hits an event with probability `1 - miss ^ n` (`prEvent_exists_uniform`), and
one coordinate of a uniform tuple is uniform (`prEvent_coordinate`). -/

namespace TestsSecurity.Counterexamples
open OracleComp OracleSpec ZkcSecurity.FiatShamir

/-- Prove an equation or inequality between finite `ENNReal` numeral quotients. -/
macro "numerals" : tactic => `(tactic| first
  | (rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
     simp only [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
       ENNReal.toReal_one, ENNReal.toReal_zero, ENNReal.toReal_pow, ENNReal.toReal_natCast]
     norm_num)
  | (rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
     simp only [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
       ENNReal.toReal_one, ENNReal.toReal_zero, ENNReal.toReal_pow, ENNReal.toReal_natCast]
     norm_num)
  | (rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
     simp only [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
       ENNReal.toReal_one, ENNReal.toReal_zero, ENNReal.toReal_pow, ENNReal.toReal_natCast]
     norm_num))

/-- An event that, against every total answer table, reads only the answers at
two distinct keys has the probability of that reading on a uniform pair. -/
theorem prEvent_randomOracle_two {D R α : Type} [Fintype D] [DecidableEq D] [Fintype R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (computation : OracleComp (D →ₒ R) α) (event : α → Prop) {first second : D}
    (distinct : first ≠ second) (reading : R × R → Prop)
    (reads : ∀ table : D → R,
      event (evalWithAnswerFn (QueryImpl.ofFn table) computation) ↔ reading (table first, table second)) :
    Pr{let result ← (simulateQ randomOracle computation).run' ∅}[event result] =
      Pr{let pair ← $ᵗ (R × R)}[reading pair] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_congr_of_evalDist_eq _ _
    (evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable computation) event]
  simp only [bind_assoc, pure_bind]
  rw [prEvent_congr _ _ (fun table : D → R => reading (table first, table second)) reads]
  exact prEvent_roles_gate first second distinct reading

/-- On a finite key type, the lazily sampled oracle gives every event of a
computation the probability of that event of its evaluation against a uniform
answer table. -/
theorem prEvent_randomOracle_table {D R α : Type} [Fintype D] [DecidableEq D]
    [SampleableType R] [SampleableType (D → R)] (computation : OracleComp (D →ₒ R) α)
    (event : α → Prop) :
    Pr{let result ← (simulateQ randomOracle computation).run' ∅}[event result] =
      Pr{let table ← $ᵗ (D → R)}[event (evalWithAnswerFn (QueryImpl.ofFn table) computation)] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_congr_of_evalDist_eq _ _
    (evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable computation) event]
  simp only [bind_assoc, pure_bind]

/-- With every attempt's answer uniform and independent, at least one of `n`
attempts hits an event of probability `1 - miss` with probability
`1 - miss ^ n`. -/
theorem prEvent_exists_uniform {B : Type} [SampleableType B] [Fintype B] (n : ℕ) (hit : B → Prop)
    {miss : ENNReal} (missing : Pr{let answer ← $ᵗ B}[¬ hit answer] = miss) :
    Pr{let answers ← $ᵗ (Fin n → B)}[∃ index, hit (answers index)] = 1 - miss ^ n := by
  have total := prEvent_add_prEvent_not_eq_prEvent_true ($ᵗ (Fin n → B))
    fun answers => ∃ index, hit (answers index)
  rw [(SampleableType.prEvent_uniformSample_eq_one_iff fun _ => True).mpr fun _ => trivial] at total
  have none : Pr{let answers ← $ᵗ (Fin n → B)}[¬ ∃ index, hit (answers index)] = miss ^ n := by
    rw [prEvent_congr _ _ (fun answers : Fin n → B => ∀ index, ¬ hit (answers index))
      fun _ => not_exists, prEvent_uniform_pi (fun _ answer => ¬ hit answer), missing,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [none] at total
  have finite : miss ^ n ≠ ⊤ := by
    rw [← none]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _ _)
  exact ENNReal.eq_sub_of_add_eq finite total

/-- One coordinate of a uniform tuple is uniform. -/
theorem prEvent_coordinate {B : Type} [SampleableType B] [Fintype B] {n : ℕ} (index : Fin n)
    (event : B → Prop) :
    Pr{let answers ← $ᵗ (Fin n → B)}[event (answers index)] = Pr{let answer ← $ᵗ B}[event answer] := by
  classical
  rw [prEvent_congr _ _ (fun answers : Fin n → B => ∀ other, other = index → event (answers other))
    fun answers => ⟨fun holds other same => same ▸ holds, fun holds => holds index rfl⟩,
    prEvent_uniform_pi (fun other answer => other = index → event answer),
    Finset.prod_eq_single index]
  · simp
  · intro other _ different
    exact (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun _ same =>
      absurd same different
  · simp

end TestsSecurity.Counterexamples
