module

public import ZkcSecurity.HashChain.Bridge

@[expose] public section

/-! The hash-chain provider simulation and its composition with the typed
engine.

`simulation` is the `ZkcSecurity.FiatShamir.Provider.Simulation` of the native
hash-chain construction, for one event of the experiment's result (soundness
first), one validator family and one bound on the verifier's primitive calls:

- the primitive is one hash; all its calls form one family, so a budget is the
  adversary's number of calls `q`;
- the private tape for budget `q` is `q` digests, and the simulator is
  `chainSimulator width q`;
- every family carries attempts; the TranscriptQuery budget is `q`;
- the verifier expansion is the bound `V` on the verifier's primitive calls,
  initialization included (`CallBound` plus the initial history);
- the loss is `(q + V)² / |S|`.

Its inequality combines the coupling with the collision-or-prediction bound
(`ZkcSecurity.HashChain.concrete_le_simulated`) and the equality in law of the
lazily sampling simulation with the translated adversary
(`ZkcSecurity.HashChain.simulatedExperiment_eq_translated`).

`concrete_soundness` composes the simulation with the typed engine: a typed
certificate for the validator bounds the concrete hash-chain experiment by
`(q + budget) * bound + (q + V)² / |S|`, where `budget` bounds the validator's
queries (`ZkcSecurity.FiatShamir.Typed.adaptive_soundness`, through
`ZkcSecurity.FiatShamir.Provider.Simulation.concrete_le`).
`concrete_soundness_weighted` is the same with per-site errors, through the
simulation's weighted budget.
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain
open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {E S X : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] [Inhabited S]
  [SampleableType S] [Fintype S] {width : ℕ} {I : PIR.Signature} {P A Stmt : Type}

/-- An event of the concrete hash-chain experiment's result. -/
noncomputable def concreteEvent (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E)
    (event : Stmt × (PIR.Outcome A × List P) → Prop)
    (adversary : OracleComp (Primitive E S X) (Stmt × List P)) (_ : Unit) : ENNReal :=
  Pr{let result ← (simulateQ randomOracle (experiment absorb validator initial adversary)).run' ∅}[
    event result]

/-- The same event of the typed engine's adaptive experiment, for a mixture of
provers. -/
noncomputable def idealEvent (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E)
    (event : Stmt × (PIR.Outcome A × List P) → Prop)
    (provers : ProbComp (OracleComp (OracleSpec.ofFn (Raw E S width)) (Stmt × List P)))
    (_ : Unit) : ENNReal :=
  Pr{let result ← provers >>= fun prover =>
      (simulateQ randomOracle (Typed.experiment absorb validator initial prover)).run' ∅}[
    event result]

/-- The hash-chain provider simulation. -/
noncomputable def simulation (positive : 0 < width) (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E)
    (nonempty : ∀ statement, initial statement ≠ []) {queries : ℕ}
    (queryBounded : ∀ statement, Typed.QueryBound absorb (validator statement) queries)
    (verifierCalls : ℕ) (callBudget : Stmt → ℕ)
    (callBounded : ∀ statement, CallBound absorb (validator statement) (callBudget statement))
    (within : ∀ statement, (initial statement).length + callBudget statement ≤ verifierCalls)
    (event : Stmt × (PIR.Outcome A × List P) → Prop) :
    Provider.Simulation (Primitive E S X) (fun _ => ()) (Raw E S width)
      (α := Stmt × List P) (ExecBound := Unit)
      (concreteEvent absorb validator initial event) (idealEvent absorb validator initial event) where
  Tape budget := Fin (budget ()) → S
  tapeSampleable _ := inferInstance
  simulator budget := chainSimulator width (budget ())
  charged _ := True
  chargedDecidable _ := instDecidableTrue
  carries _ _ _ _ _ := trivial
  queryCost :=
    { cost := fun budget => budget ()
      monotone := fun _ _ le => le ()
      expansion := fun _ => verifierCalls
      loss := fun budget calls =>
        (((budget () + calls) * (budget () + calls) : ℕ) : ENNReal) / Fintype.card S }
  covers budget := by simp [Provider.chargedBudget]
  bound adversary budget _ bounded := by
    have total : IsTotalQueryBound adversary (budget ()) := by
      simpa using Provider.FamilyQueryBound.isTotalQueryBound (fun _ => ()) adversary budget bounded
    refine (concrete_le_simulated absorb validator initial nonempty adversary total callBudget
      callBounded within event).trans (le_of_eq ?_)
    congr 1
    have same := ZkcSecurity.VCVio.Deferral.prEvent_eq_of_evalSPMF_eq
      (simulatedExperiment_eq_translated positive absorb validator initial queryBounded adversary
        total) event
    simp only [bind_assoc] at same
    simp only [idealEvent, bind_assoc, pure_bind]
    exact same

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [Inhabited S] [SampleableType S]
  [Fintype S] in
/-- A total bound on the primitive calls is a bound on the single family. -/
theorem familyQueryBound_of_total {α : Type} :
    ∀ (adversary : OracleComp (Primitive E S X) α) (calls : ℕ),
      IsTotalQueryBound adversary calls →
        Provider.FamilyQueryBound (fun _ => ()) adversary (fun _ => calls) := by
  intro adversary
  induction adversary using OracleComp.inductionOn with
  | pure value => intro _ _; trivial
  | query_bind query next ih =>
      intro calls bounded
      obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bounded
      refine (Provider.familyQueryBound_query_bind_iff _).mpr ⟨positive, fun reply => ?_⟩
      have same : Function.update (fun _ : Unit => calls) () (calls - 1) = fun _ => calls - 1 := by
        funext point
        cases point
        simp
      rw [same]
      exact ih reply (calls - 1) (rest reply)

/-- Fiat–Shamir soundness of the hash-chain construction: an adversary with at
most `q` primitive calls makes the validator of a false statement accept with
probability at most `(q + queries) * bound + (q + V)² / |S|`, where every site
error of the typed certificate is at most `bound`, the validators make at most
`queries` TranscriptQueries and at most `V` primitive calls with the chain. -/
theorem concrete_soundness (positive : 0 < width) {absorb : Typed.Interface I E P (Raw E S width)}
    {accepts : A → Prop} {error : E → ENNReal} (certificate : Typed.Certificate absorb accepts error)
    {bound : ENNReal} (bounded : ∀ event, error event ≤ bound) (validator : Stmt → PIR.Proc I A)
    (initial : Stmt → List E) (determined : Typed.Determined initial)
    (nonempty : ∀ statement, initial statement ≠ []) (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    {queries : ℕ} (queryBounded : ∀ statement, Typed.QueryBound absorb (validator statement) queries)
    (verifierCalls : ℕ) (callBudget : Stmt → ℕ)
    (callBounded : ∀ statement, CallBound absorb (validator statement) (callBudget statement))
    (within : ∀ statement, (initial statement).length + callBudget statement ≤ verifierCalls)
    (adversary : OracleComp (Primitive E S X) (Stmt × List P)) {calls : ℕ}
    (adversaryBound : IsTotalQueryBound adversary calls) :
    Pr{let result ← (simulateQ randomOracle (experiment absorb validator initial adversary)).run'
        ∅}[falseStatement result.1 ∧ Accepted accepts result.2.1] ≤
      (calls + queries) * bound +
        (((calls + verifierCalls) * (calls + verifierCalls) : ℕ) : ENNReal) / Fintype.card S :=
  (simulation positive absorb validator initial nonempty queryBounded verifierCalls callBudget
      callBounded within fun result => falseStatement result.1 ∧ Accepted accepts result.2.1).concrete_le
    (idealBound := fun proverQueries _ => (proverQueries + queries) * bound)
    (fun _ proverQueries _ proverBound =>
      prEvent_bind_le_of_forall_le_of_support _ _ _ fun prover member =>
        Typed.adaptive_soundness certificate bounded validator initial determined falseStatement
          doomedValidator queries queryBounded prover proverQueries (proverBound prover member))
    adversary (fun _ => calls) () (familyQueryBound_of_total adversary calls adversaryBound)

/-- Fiat–Shamir soundness of the hash-chain construction with an error per site:
the translated adversary's TranscriptQueries charge at most `q * bound` on every
path (`ZkcSecurity.FiatShamir.Provider.Simulation.weightedBudget`), so an
adversary with at most `q` primitive calls makes the validator of a false
statement accept with probability at most
`q * bound + validatorCost + (q + V)² / |S|`. -/
theorem concrete_soundness_weighted (positive : 0 < width)
    {absorb : Typed.Interface I E P (Raw E S width)} {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Typed.Certificate absorb accepts error) {bound : ENNReal}
    (bounded : ∀ event, error event ≤ bound) (validator : Stmt → PIR.Proc I A)
    (initial : Stmt → List E) (determined : Typed.Determined initial)
    (nonempty : ∀ statement, initial statement ≠ []) (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    {queries : ℕ} (queryBounded : ∀ statement, Typed.QueryBound absorb (validator statement) queries)
    (validatorCost : ENNReal)
    (validatorBound : ∀ statement, Typed.CostBound absorb error (validator statement) validatorCost)
    (verifierCalls : ℕ) (callBudget : Stmt → ℕ)
    (callBounded : ∀ statement, CallBound absorb (validator statement) (callBudget statement))
    (within : ∀ statement, (initial statement).length + callBudget statement ≤ verifierCalls)
    (adversary : OracleComp (Primitive E S X) (Stmt × List P)) {calls : ℕ}
    (adversaryBound : IsTotalQueryBound adversary calls) :
    Pr{let result ← (simulateQ randomOracle (experiment absorb validator initial adversary)).run'
        ∅}[falseStatement result.1 ∧ Accepted accepts result.2.1] ≤
      calls * bound + validatorCost +
        (((calls + verifierCalls) * (calls + verifierCalls) : ℕ) : ENNReal) / Fintype.card S := by
  let instance_ := simulation (X := X) positive absorb validator initial nonempty queryBounded
    verifierCalls callBudget callBounded within
    fun result => falseStatement result.1 ∧ Accepted accepts result.2.1
  have keyBounded : ∀ key, Typed.keyError error key ≤ bound := by
    intro key
    unfold Typed.keyError
    split
    · exact bounded _
    · exact zero_le
  have within' := familyQueryBound_of_total adversary calls adversaryBound
  refine (instance_.bound_translate adversary (fun _ => calls) () within').trans
    (add_le_add_left ?_ _)
  exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun prover member =>
    Typed.adaptive_soundness_weighted certificate validator initial determined falseStatement
      doomedValidator validatorCost validatorBound prover (calls * bound)
      (instance_.weightedBudget (Typed.keyError error) keyBounded adversary (fun _ => calls)
        within' prover member)

end ZkcSecurity.HashChain
