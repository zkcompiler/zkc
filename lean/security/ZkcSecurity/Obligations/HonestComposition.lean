module

public import Zkc.Semantics.WeakestPrecondition
public import VCVio.EvalDist.ProbabilityBounds

@[expose] public section

/-! Honest sequential composition over the existing execution and probability
semantics. The intermediate invariant is established at the actual return;
neither rule restarts a component or resets shared state.

The probability rule uses `1 - success`, including missing mass. It applies to
`ProbComp` and to its existing `OptionT` subdistribution semantics. A caller
must carry the full shared runtime/oracle state in the intermediate observation
and prove its experiment's bind equation. In particular, this does not extend
`PrivatePairWP`'s deterministic-validator consumer to privately randomized
validators or issue a canonical completeness receipt.

Boundary-record integration needs no new records here: instantiate the
intermediate predicate with the output readback and independently proved
execution scope, then use the chosen connection's honest transport to establish
the suffix precondition. Exact body equations must identify these runs with the
admitted components. A quantitative canonical-pair adapter still needs to prove
the sampled experiment's bind equation with the same cache and runtime state,
its supported intermediate invariant, and the fixed request's success event. -/

set_option autoImplicit false

namespace ZkcSecurity.Obligations.HonestComposition

open PIR.WeakestPrecondition

/-- Compose returning honest executions with a scope/readback invariant at the
actual value, state and accumulated history. An impossible stop postcondition
requires both components to return. The suffix premise concerns only the exact
first execution, rather than every imaginable state. -/
theorem deterministic_bind {I : PIR.Signature} {S E A B : Type}
    (handler : PIR.Handler I S E) (first : PIR.Process I A)
    (next : A → PIR.Process I B) (initial : S) (preceding : List E)
    (intermediate : A → S → List E → Prop) (post : B → S → List E → Prop)
    (honestPrefix : satisfies (first.run handler initial) intermediate
      (fun _ _ _ => False) preceding)
    (honestSuffix : ∀ value reached events,
      first.run handler initial = ⟨.returned value, reached, events⟩ →
      intermediate value reached (preceding ++ events) →
      satisfies ((next value).run handler reached) post
        (fun _ _ _ => False) (preceding ++ events)) :
    satisfies ((first.bind next).run handler initial) post
      (fun _ _ _ => False) preceding := by
  rw [PIR.run_bind]
  cases observed : first.run handler initial with
  | mk outcome reached events =>
    rw [observed] at honestPrefix
    cases outcome with
    | stopped reason => exact honestPrefix.elim
    | returned value =>
      have suffix := honestSuffix value reached events observed honestPrefix
      cases tail : (next value).run handler reached with
      | mk outcome final tailEvents =>
        rw [tail] at suffix
        cases outcome with
        | stopped reason => exact suffix.elim
        | returned result =>
          simpa only [PIR.Execution.follow, tail, satisfies, List.append_assoc] using suffix

/-- A supported intermediate observation supplies both execution scope and the
logical premise of the suffix. Failure bounds include stops, failed preparation,
rejection and genuinely absent results. No normalization or independence is
assumed: the continuation may depend on the entire reached observation.

For `ProbComp`, explicit stops/failed preparation must be unsuccessful returned
observations. For `OptionT ProbComp`, absent outputs also contribute to the
complement, although they are absent from `support`. -/
theorem probabilistic_bind {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadAttach m] [WeaklyLawfulMonadAttach m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {A B : Type}
    (first : m A) (next : A → m B) (scope intermediate : A → Prop)
    (success : B → Prop) (prefixError suffixError : ENNReal)
    (preservesScope : ∀ reached ∈ support first, scope reached)
    (honestPrefix : 1 - Pr{let reached ← first}[intermediate reached] ≤ prefixError)
    (honestSuffix : ∀ reached ∈ support first, scope reached → intermediate reached →
      1 - Pr{let result ← next reached}[success result] ≤ suffixError) :
    1 - Pr{let result ← first >>= next}[success result] ≤ prefixError + suffixError := by
  have lower : Pr{let reached ← first}[intermediate reached] * (1 - suffixError) ≤
      Pr{let result ← first >>= next}[success result] := by
    rw [bind_eq_attach_bind first next]
    apply mul_le_prEvent_bind_of_forall _ _ (fun reached => intermediate reached.1) success
    · have same : Pr{let reached ← first}[intermediate reached] =
          Pr{let reached ← MonadAttach.attach first}[intermediate reached.1] := by
        conv_lhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := first)]
        rw [prEvent_map]
      exact same.le
    · intro reached inside
      have enough := tsub_le_iff_right.mp
        (honestSuffix reached.1 reached.2 (preservesScope reached.1 reached.2) inside)
      exact tsub_le_iff_right.mpr (by simpa only [add_comm] using enough)
  have mass : Pr{let reached ← first}[intermediate reached] ≤
      Pr{let result ← first >>= next}[success result] + suffixError := by
    calc
      _ = Pr{let reached ← first}[intermediate reached] * 1 := (mul_one _).symm
      _ ≤ Pr{let reached ← first}[intermediate reached] * ((1 - suffixError) + suffixError) :=
        mul_le_mul' le_rfl le_tsub_add
      _ = _ := mul_add _ _ _
      _ ≤ _ := add_le_add lower (mul_le_of_le_one_left' (prEvent_le_one _))
  apply tsub_le_iff_right.mpr
  calc
    1 ≤ (1 - Pr{let reached ← first}[intermediate reached]) +
        Pr{let reached ← first}[intermediate reached] := le_tsub_add
    _ ≤ prefixError + (Pr{let result ← first >>= next}[success result] + suffixError) :=
      add_le_add honestPrefix mass
    _ = _ := by ac_rfl

end ZkcSecurity.Obligations.HonestComposition
