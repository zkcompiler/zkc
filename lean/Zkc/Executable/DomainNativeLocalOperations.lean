module

public import Zkc.Executable.DomainNativeHelperCosts
public import Zkc.Executable.DomainNativeUpdates

@[expose] public section

/-! Native transparent local operation boundaries. These are CPS laws for
actual native instructions against actual Domain.step, at every budget. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem native_calculate_metered
    (program : Structured.Program) (context : Context) (key : Origin → Origin)
    (initial : History F G) (challenge : History F G → m F)
    (vocabulary : Vocabulary) (validator : Validator) (budget : Nat)
    (cost : String → List (Value F G) → Nat)
    (call : String × String) (site binding : String) (parameters : List Parameter)
    (inputs outputs : List String) (calculation : Calculation)
    (resolved : validator.binding? binding >>= (vocabulary.resolve · parameters) = some (.calculate calculation))
    (eligible : calculation.op.results.all dataType = true)
    (named : Env F G) (state : State F G) (scalar : List (Value F G))
    (lookups : lookupAll named inputs = some scalar)
    (outputCount : outputs.length = calculation.op.results.length)
    (env nominal : Environment F G) (references : List Nat)
    (read : Domain.read env references = some nominal)
    (embedded : DomainAdapter.embedValues scalar = some nominal)
    (proof : Proof F G)
    (next : Env F G → State F G → m (Run F G))
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G))
    (continues : ∀ results values,
      Construction.calculate calculation scalar = .returned results →
      DomainAdapter.embedValues results = some values →
      values.map Domain.Value.sort = calculation.op.results.map ValueSort.data →
      Run.observe <$> next (outputs.zip results ++ named) state.charge =
        nativeObservation context.suite key initial <$>
          continuation (env ++ values) proof (state.used + 1)) :
    Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
      (.operation site binding parameters inputs outputs) named state next exit =
      nativeObservation context.suite key initial <$>
        meteredStep program context key initial challenge cost budget
          (.step ⟨.calculate calculation, references, calculation.op.results.map ValueSort.data, []⟩ 1)
          env proof state.used continuation := by
  simp only [Executable.localStep, meteredStep]
  by_cases tick : state.used < budget
  · have fits : state.used + 1 ≤ budget := by omega
    simp only [tick, fits, ite_true, resolved, lookups, Resolved.apply, pure_bind]
    rw [step_calculate_native program context key initial challenge calculation references env nominal scalar read embedded eligible]
    cases computed : Construction.calculate calculation scalar with
    | stopped reason => simp [nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
    | returned results =>
      obtain ⟨values, resultEmbedding, schema⟩ := calculate_returns_embeds calculation eligible computed
      have count : outputs.length = results.length := outputCount.trans (Uniform.calculate_length calculation computed).symm
      simp only [resultEmbedding, count, ite_true, Nat.add_zero]
      exact continues results values computed resultEmbedding schema
  · have short : ¬ state.used + 1 ≤ budget := by omega
    simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]

theorem native_indicesEmpty_metered
    (program : Structured.Program) (context : Context) (key : Origin → Origin)
    (initial : History F G) (challenge : History F G → m F)
    (vocabulary : Vocabulary) (validator : Validator) (budget : Nat)
    (cost : String → List (Value F G) → Nat)
    (call : String × String) (site binding : String) (parameters : List Parameter) (outputs : List String)
    (resolved : validator.binding? binding >>= (vocabulary.resolve · parameters) = some .indicesEmpty)
    (outputCount : outputs.length = 1) (named : Env F G) (state : State F G)
    (env : Environment F G) (proof : Proof F G)
    (next : Env F G → State F G → m (Run F G))
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G))
    (continues : Run.observe <$> next (outputs.zip [.indices []] ++ named) state.charge =
      nativeObservation context.suite key initial <$>
        continuation (env ++ [.indices []]) proof (state.used + 1)) :
    Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
      (.operation site binding parameters [] outputs) named state next exit =
      nativeObservation context.suite key initial <$>
        meteredStep program context key initial challenge cost budget
          (.step ⟨.indicesEmpty, [], [.indices], []⟩ 1) env proof state.used continuation := by
  simp only [Executable.localStep, meteredStep]
  by_cases tick : state.used < budget
  · have fits : state.used + 1 ≤ budget := by omega
    simp only [tick, fits, ite_true, resolved, lookupAll, List.mapM_nil, Option.pure_def,
      Resolved.apply, pure_bind, outputCount, List.length_singleton, Nat.add_zero]
    rw [Domain.Correspondence.indicesEmpty]
    simpa [Domain.View.indicesEmpty, Domain.View.append, Domain.sortsMatch, DomainAdapter.runK,
      Domain.Value.sort, State.charge] using continues
  · have short : ¬ state.used + 1 ≤ budget := by omega
    simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]

theorem native_indicesAppend_metered
    (program : Structured.Program) (context : Context) (key : Origin → Origin)
    (initial : History F G) (challenge : History F G → m F)
    (vocabulary : Vocabulary) (validator : Validator) (budget : Nat)
    (cost : String → List (Value F G) → Nat)
    (call : String × String) (site binding : String) (parameters : List Parameter)
    (inputs outputs : List String)
    (resolved : validator.binding? binding >>= (vocabulary.resolve · parameters) = some .indicesAppend)
    (outputCount : outputs.length = 1) (named : Env F G) (state : State F G)
    (env : Environment F G) (coordinates index : Nat) (path : List Nat) (value : Nat)
    (pathFound : env[coordinates]? = some (.indices path))
    (indexFound : env[index]? = some (.data (.index value)))
    (lookups : lookupAll named inputs = some [.indices path, .index value])
    (proof : Proof F G)
    (next : Env F G → State F G → m (Run F G))
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G))
    (continues : Run.observe <$> next (outputs.zip [.indices (path ++ [value])] ++ named) state.charge =
      nativeObservation context.suite key initial <$>
        continuation (env ++ [.indices (path ++ [value])]) proof (state.used + 1)) :
    Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
      (.operation site binding parameters inputs outputs) named state next exit =
      nativeObservation context.suite key initial <$>
        meteredStep program context key initial challenge cost budget
          (.step ⟨.indicesAppend, [coordinates, index], [.indices], []⟩ 1) env proof state.used continuation := by
  simp only [Executable.localStep, meteredStep]
  by_cases tick : state.used < budget
  · have fits : state.used + 1 ≤ budget := by omega
    simp only [tick, fits, ite_true, resolved, lookups, Resolved.apply, pure_bind,
      outputCount, List.length_singleton, Nat.add_zero]
    rw [Domain.Correspondence.indicesAppend,
      Domain.View.indicesAppend_eq coordinates index env path value pathFound indexFound]
    exact continues
  · have short : ¬ state.used + 1 ≤ budget := by omega
    simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]

theorem native_constant_metered
    (program : Structured.Program) (context : Context) (key : Origin → Origin)
    (initial : History F G) (challenge : History F G → m F)
    (vocabulary : Vocabulary) (validator : Validator) (budget : Nat)
    (cost : String → List (Value F G) → Nat)
    (call : String × String) (site output : String) (value : Bool)
    (named : Env F G) (state : State F G) (env : Environment F G) (proof : Proof F G)
    (next : Env F G → State F G → m (Run F G))
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G))
    (continues : Run.observe <$> next ((output, .data (.boolean value)) :: named) state.charge =
      nativeObservation context.suite key initial <$>
        continuation (env ++ [.data (.boolean value)]) proof (state.used + 1)) :
    Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
      (.constant site output value) named state next exit =
      nativeObservation context.suite key initial <$>
        meteredStep program context key initial challenge cost budget
          (.step ⟨.calculate (.booleanConstant value), [], [.data .boolean], []⟩ 1)
          env proof state.used continuation := by
  simp only [Executable.localStep, meteredStep]
  by_cases tick : state.used < budget
  · have fits : state.used + 1 ≤ budget := by omega
    simp only [tick, fits, ite_true]
    change Run.observe <$> _ = nativeObservation context.suite key initial <$>
      DomainAdapter.runK key initial challenge
        (Domain.step (Structured.ringModel F G) program context
          ⟨.calculate (.booleanConstant value), [], (Calculation.booleanConstant value).op.results.map ValueSort.data, []⟩ env)
        proof (fun final unread => continuation final unread (state.used + 1))
    rw [step_calculate_native program context key initial challenge (.booleanConstant value) [] env [] [] rfl rfl (by rfl)]
    exact continues
  · have short : ¬ state.used + 1 ≤ budget := by omega
    simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]

theorem native_guard_metered
    (program : Structured.Program) (context : Context) (key : Origin → Origin)
    (initial : History F G) (challenge : History F G → m F)
    (vocabulary : Vocabulary) (validator : Validator) (budget : Nat)
    (cost : String → List (Value F G) → Nat)
    (call : String × String) (site stopSite condition : String) (value : Bool)
    (named : Env F G) (state : State F G) (env : Environment F G) (reference : Nat)
    (lookup : List.lookup condition named = some (.data (.boolean value)))
    (found : env[reference]? = some (.data (.boolean value))) (proof : Proof F G)
    (next : Env F G → State F G → m (Run F G))
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G))
    (continues : Run.observe <$> next named state.charge.charge =
      nativeObservation context.suite key initial <$> continuation env proof (state.used + 2)) :
    Run.observe <$> Executable.localStep vocabulary validator context challenge budget call true none
      (.cond site condition [] [.yield []] [.stop stopSite "reject"] []) named state next exit =
      nativeObservation context.suite key initial <$>
        meteredStep program context key initial challenge cost budget
          (.step ⟨.guard stopSite, [reference], [], []⟩ 2) env proof state.used continuation := by
  simp only [Executable.localStep, meteredStep]
  rw [Domain.Correspondence.guard, Domain.View.guard_eq reference env value found]
  by_cases tick : state.used < budget
  · by_cases second : state.used + 1 < budget
    · have fits : state.used + 2 ≤ budget := by omega
      cases value with
      | true =>
        simp only [tick, fits, ite_true, lookup, lookupAll, List.mapM_nil, Option.pure_def,
          List.zip_nil_left, Executable.localK, Executable.localStep, List.nil_append,
          State.charge, second, List.length_nil, DomainAdapter.runK]
        simpa [State.charge, Nat.add_assoc] using continues
      | false =>
        simp [tick, second, fits, lookup, lookupAll, Executable.localK, Executable.localStep,
          State.charge, stopReason?, DomainAdapter.runK, nativeObservation,
          DomainAdapter.readbackOutcome, Executable.observation]
    · have short : ¬ state.used + 2 ≤ budget := by omega
      cases value <;> simp [tick, second, short, lookup, lookupAll, Executable.localK, Executable.localStep,
        State.charge, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
  · have short : ¬ state.used + 2 ≤ budget := by omega
    simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]

end Zkc.Executable.DomainVM
