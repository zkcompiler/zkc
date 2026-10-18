import ZkcSecurity.FiatShamir.Roles
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-! Support for the counterexamples.

`numerals` closes an equation or a strict or weak inequality between finite
`ENNReal` numeral expressions through `toReal`. `prEvent_randomOracle_two`
computes an event of a computation in the lazily sampled oracle on a finite key
type when, against every total answer table, the event reads only the answers
at two distinct keys: its probability is that of a uniform pair. -/

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

end TestsSecurity.Counterexamples
