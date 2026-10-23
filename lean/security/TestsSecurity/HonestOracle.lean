import ZkcSecurity.FiatShamir.Honest

/-! One cached key is correlated across phases; resetting the cache instead
samples twice. These are concrete experiment controls, not native receipts. -/
set_option autoImplicit false
namespace TestsSecurity.HonestOracle
open OracleComp OracleSpec ZkcSecurity.FiatShamir

abbrev Raw (_ : Unit) := Fin 2
abbrev Spec := Honest.Spec Raw

def once : OracleComp Spec (Fin 2) := Typed.ask (R := Typed.ByLast Raw) (Raw := Raw) [] ()

def twice : OracleComp Spec (Fin 2 × Fin 2) := do
  let first ← once
  let second ← once
  pure (first, second)

theorem coherent : Pr{let result ← Honest.run twice}[result.1.1 = result.1.2] = 1 := by
  apply (Honest.success_probability_one_iff twice (fun pair => pair.1 = pair.2)).mpr
  intro answers
  simp [twice, once, Typed.ask, Typed.answer, evalWithAnswerFn_bind, evalWithAnswerFn_map]

theorem fresh_key (cache : Spec.QueryCache) (absent : cache [()] = none) :
    (Spec.randomOracle [()]).run cache =
      ($ᵗ (Typed.ByLast Raw [()])) >>= fun answer =>
        pure (answer, cache.cacheQuery [()] answer) := Honest.fresh _ _ absent

theorem memoized_key (cache : Spec.QueryCache) (answer : Typed.ByLast Raw [()])
    (found : cache [()] = some answer) :
    (Spec.randomOracle [()]).run cache = pure (answer, cache) := Honest.cached _ _ _ found

def reset : ProbComp (Fin 2 × Fin 2) := do
  let first ← Honest.run once
  let second ← Honest.run once
  pure (first.1, second.1)

theorem once_uniform : (Prod.fst <$> Honest.run once) = $ᵗ (Fin 2) := by
  simp only [Honest.run, once, Typed.ask, Typed.answer, simulateQ_map,
    StateT.run_map, simulateQ_spec_query, randomOracle.run_eq,
    Typed.ReadsByOccurrence.read, Typed.ByLast.read,
    QueryCache.empty_apply, bind_pure_comp]
  change (id <$> ($ᵗ (Fin 2))) = $ᵗ (Fin 2)
  exact id_map _

theorem reset_independent : reset = (do
    let first ← $ᵗ (Fin 2)
    let second ← $ᵗ (Fin 2)
    pure (first, second)) := by
  calc reset = (do
      let first ← Prod.fst <$> Honest.run once
      let second ← Prod.fst <$> Honest.run once
      pure (first, second)) := by simp only [reset, bind_map_left]
    _ = _ := by rw [once_uniform]

theorem reset_agreement : Pr{let pair ← reset}[pair.1 = pair.2] = 1 / 2 := by
  rw [reset_independent, ← SampleableType.uniformSample_prod_eq_bind]
  rw [SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun pair : Fin 2 × Fin 2 => pair.1 = pair.2).card = 2 := by
    decide +kernel
  rw [count, Fintype.card_prod, Fintype.card_fin]
  norm_num only [Nat.cast_ofNat, Nat.cast_mul]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
  norm_num

theorem reset_changes_experiment : Pr{let pair ← reset}[pair.1 = pair.2] ≠
    Pr{let observed ← Honest.run twice}[observed.1.1 = observed.1.2] := by
  rw [reset_agreement, coherent]
  norm_num

-- An entirely absent successful result has failure one, even if there are no
-- returned records satisfying a separately proposed failure predicate.
example : (1 : ENNReal) - 0 = 1 := by simp

def missingResult : OptionT ProbComp Bool := OptionT.mk (pure none)

theorem missing_mass_is_failure :
    (1 : ENNReal) - Pr{let result ← missingResult}[result = true] = 1 := by
  simp [missingResult, OptionT.prEvent_mk]

theorem no_returned_failure : Pr{let result ← missingResult}[result ≠ true] = 0 := by
  simp [missingResult, OptionT.prEvent_mk]

#print axioms coherent
#print axioms fresh_key
#print axioms memoized_key
#print axioms reset_changes_experiment
#print axioms missing_mass_is_failure

end TestsSecurity.HonestOracle
