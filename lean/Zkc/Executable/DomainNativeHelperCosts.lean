module

public import Zkc.Executable.DomainNativeCalculations
public import Zkc.Executable.DomainNativeBytes
public import Zkc.Executable.Evaluation

@[expose] public section

/-! Actual native helper evaluation and dynamic charges at the canonical
Domain boundary. Prepared is the existing checked helper implementation law;
the finite signature check separately supplies stopped-path metadata. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

theorem arguments_embed : ∀ {scalar : List (Value F G)} {nominal : Environment F G},
    DomainAdapter.embedValues scalar = some nominal → arguments nominal = some scalar
  | [], nominal, embedded => by cases embedded; rfl
  | value :: values, nominal, embedded => by
    simp only [DomainAdapter.embedValues_cons] at embedded
    cases head : DomainAdapter.embedData value with
    | none => simp [head] at embedded
    | some first =>
      cases tail : DomainAdapter.embedValues values with
      | none => simp [head, tail] at embedded
      | some rest =>
        simp only [head, tail, bind, Option.bind, Option.pure_def, Option.some.injEq] at embedded
        subst nominal
        simp only [arguments, List.mapM_cons, DomainAdapter.readback_embed head]
        change (do let tail ← arguments rest; pure (value :: tail)) = some (value :: values)
        rw [arguments_embed tail]
        rfl

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- One native participant helper call, including call-entry work, the actual
helper's dynamic body charge, all stop classes, and the continuation after its
frame is popped. The continuation premise is suitable for induction over the
remaining native actions; it imposes no condition on numerical arguments. -/
theorem native_helper_metered
    (program : Structured.Program) (context : Context) (key : Origin → Origin)
    (initial : History F G) (challenge : History F G → m F)
    (vocabulary : Vocabulary) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (site name : String) (inputs outputs : List String)
    (helper : Structured.Helper)
    (checked : (nativeHelperSignatures program).find? (fun found => found.name == name) = some helper)
    (eligible : helper.outputs.all dataType = true)
    (callee : Function) (calleeEq : validator.function? name = some callee)
    (free : transcriptFree vocabulary validator callee.body = true)
    (prepared : Prepared vocabulary validator (Domain.helperTable (Structured.ringModel F G) program) name)
    (state : State F G) (top : Frame F G) (rest : List (Frame F G))
    (frames : state.frames = top :: rest)
    (scalar : List (Value F G)) (lookups : lookupAll top.env inputs = some scalar)
    (arity : callee.inputs.length = scalar.length)
    (sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort), scalar[index]? = some value →
      (callee.inputs.map (·.2.sort))[index]? = some sort → HasSort value sort)
    (outputCount : outputs.length = callee.results.length)
    (env nominal : Environment F G) (references : List Nat)
    (read : Domain.read env references = some nominal)
    (embedded : DomainAdapter.embedValues scalar = some nominal)
    (proof : Proof F G)
    (next : State F G → m (Run F G))
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G))
    (continues : ∀ results charge values,
      evalSteps vocabulary validator callee.body ((callee.inputs.map (·.1)).zip scalar) = .values results charge →
      Construction.callHelper (Domain.helperTable (Structured.ringModel F G) program) name scalar = .returned results →
      DomainAdapter.embedValues results = some values →
      values.map Domain.Value.sort = helper.outputs.map ValueSort.data →
      Run.observe <$> next
        { state with
          used := state.used + 1 + charge
          frames := ⟨top.id, outputs.zip results ++ top.env⟩ :: rest
          events := state.events ++ [.enter (.call site name)] ++ [.leave (.call site name) .returned] } =
        nativeObservation context.suite key initial <$>
          continuation (env ++ values) proof (state.used + 1 + charge)) :
    Run.observe <$> Executable.runStep vocabulary validator context challenge decode budget
      (.call site name inputs outputs) state next exit =
      nativeObservation context.suite key initial <$>
        meteredStep program context key initial challenge (helperCost vocabulary validator) budget
          (.helper ⟨.call name, references, helper.outputs.map ValueSort.data, []⟩) env proof state.used continuation := by
  have scalarRead : arguments nominal = some scalar := arguments_embed embedded
  have costEq : helperCost vocabulary validator name scalar =
      (evalSteps vocabulary validator callee.body ((callee.inputs.map (·.1)).zip scalar)).cost := by
    simp [helperCost, Validator.evaluateCall, calleeEq, arity]
  have prep := prepared callee calleeEq scalar arity sorted
  simp only [Executable.runStep, meteredStep]
  by_cases tick : state.used < budget
  · have fits : state.used + 1 ≤ budget := by omega
    simp only [tick, fits, ite_true, frames, calleeEq, lookups, arity, read, scalarRead, costEq]
    rw [localK_evaluates vocabulary validator context challenge budget _ true none callee.body _ _ _ free (by simp; omega)]
    revert prep
    cases evaluated : evalSteps vocabulary validator callee.body ((callee.inputs.map (·.1)).zip scalar) with
    | values results charge =>
      cases called : Construction.callHelper (Domain.helperTable (Structured.ringModel F G) program) name scalar with
      | stopped reason => intro prep; exact prep.elim
      | returned actual =>
        intro prep
        obtain ⟨same, count, _⟩ := prep
        subst actual
        obtain ⟨values, resultEmbedding, schema⟩ := helper_returns_embeds program name helper checked eligible scalar results called
        have resultSorts : Domain.sortsMatch (helper.outputs.map ValueSort.data) values = true := by
          simp [Domain.sortsMatch, schema]
        have counts : outputs.length = results.length := outputCount.trans count.symm
        simp only [cutoff, Evaluated.cost]
        by_cases enough : state.used + 1 + charge ≤ budget
        · simp only [enough, ite_true]
          rw [step_helper_native program context key initial challenge name helper checked references env nominal scalar read embedded eligible]
          simp only [called, DomainAdapter.embedOutcome, resultEmbedding, resultSorts, ite_true, counts]
          exact continues results charge values evaluated called resultEmbedding schema
        · simp [enough, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
    | stopped cause charge =>
      cases called : Construction.callHelper (Domain.helperTable (Structured.ringModel F G) program) name scalar with
      | returned actual => intro prep; exact prep.elim
      | stopped reason =>
        intro prep
        simp only at prep
        simp only [cutoff, Evaluated.cost]
        by_cases enough : state.used + 1 + charge ≤ budget
        · simp only [enough, ite_true]
          rw [step_helper_native program context key initial challenge name helper checked references env nominal scalar read embedded eligible]
          simp only [called, DomainAdapter.embedOutcome, map_pure, nativeObservation_stopped]
          rw [prep]
        · simp [enough, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]
  · have short : ¬ state.used + 1 ≤ budget := by omega
    simp [tick, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]

end Zkc.Executable.DomainVM
