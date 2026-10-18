module

public import Zkc.Executable.Relation

@[expose] public section

/-! Local bodies without transcript operations are their unbounded evaluation,
cut off by the budget.

`localK` charges a local body one instruction at a time and stops at the
budget. On a body that applies no transcript operation it neither queries the
challenge function nor touches the live transcript, so what it observes is
determined by `evalSteps`: the values the body hands back, or the cause it
stops for, after the instructions it charges until then. If those charges fit
within the budget the run continues as the evaluation says; otherwise it stops
by exhaustion (`localK_evaluates`). This is how a helper call's work is
accounted for, whatever control its body has.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

variable {F G : Type}
variable {m : Type → Type} [Monad m]

/-- What a run observes when an evaluation is cut off by the budget, after which
`exit` receives the values handed back. -/
def cutoff (budget : Nat) (s : State F G) (exit : List (Value F G) → State F G → m (Run F G)) :
    Evaluated F G → m (PIR.Outcome (List (Value F G)) × Bool)
  | .values results cost =>
      if s.used + cost ≤ budget then Run.observe <$> exit results { s with used := s.used + cost }
      else pure (.stopped .exhausted, true)
  | .stopped cause cost =>
      if s.used + cost ≤ budget then pure (.stopped cause.outcome, true)
      else pure (.stopped .exhausted, true)

theorem cutoff_after (budget : Nat) (s : State F G) (exit : List (Value F G) → State F G → m (Run F G))
    (extra : Nat) (result : Evaluated F G) :
    cutoff budget s exit (result.after extra) =
      if s.used + extra ≤ budget then cutoff budget { s with used := s.used + extra } exit result
      else pure (.stopped .exhausted, true) := by
  cases result with
  | values results cost =>
      by_cases fits : s.used + extra ≤ budget
      · simp only [Evaluated.after, cutoff, fits, ite_true, Nat.add_assoc]
      · have : ¬ s.used + (extra + cost) ≤ budget := by omega
        simp only [Evaluated.after, cutoff, fits, this, ite_false]
  | stopped cause cost =>
      by_cases fits : s.used + extra ≤ budget
      · simp only [Evaluated.after, cutoff, fits, ite_true, Nat.add_assoc]
      · have : ¬ s.used + (extra + cost) ≤ budget := by omega
        simp only [Evaluated.after, cutoff, fits, this, ite_false]

theorem State.charge_used (s : State F G) (count : Nat) :
    ({ s.charge with used := s.charge.used + count } : State F G) = { s with used := s.used + (1 + count) } := by
  simp [State.charge, Nat.add_assoc]

section Local
variable [LawfulMonad m] (budget : Nat)

/-- Iterating a region that is its evaluation cut off by the budget is the
iteration's evaluation cut off by the budget. -/
theorem forK_evaluates
    (run : Env F G → State F G → (List (Value F G) → State F G → m (Run F G)) → m (Run F G))
    (evaluate : Env F G → Evaluated F G)
    (evaluates : ∀ env (s : State F G) exit, s.used ≤ budget →
      Run.observe <$> run env s exit = cutoff budget s exit (evaluate env))
    (site induction : String) (carried : List String) (captured : Env F G) (call : String × String) :
    ∀ (indices : List Nat) (values : List (Value F G)) (s : State F G)
      (done : List (Value F G) → State F G → m (Run F G)), s.used ≤ budget →
      Run.observe <$> forK run site induction carried captured call indices values s done =
        cutoff budget s done (evalFor evaluate induction carried captured indices values)
  | [], values, s, done, within => by simp [forK, evalFor, cutoff, within]
  | index :: rest, values, s, done, within => by
      simp only [forK, evalFor]
      rw [evaluates _ s _ within]
      cases evaluate ((induction, .index index) :: carried.zip values ++ captured) with
      | values yielded cost =>
          by_cases lengths : yielded.length = carried.length
          · simp only [lengths, ite_true, cutoff_after]
            simp only [cutoff]
            by_cases fits : s.used + cost ≤ budget
            · simp only [fits, ite_true, lengths]
              exact forK_evaluates run evaluate evaluates site induction carried captured call rest yielded
                _ done fits
            · simp [fits]
          · simp [lengths, cutoff, Cause.outcome]
      | stopped cause cost => simp [cutoff]

end Local

section Field
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A resolved operation without a transcript leaves the live transcript and
the challenge function alone. -/
theorem Resolved.apply_evaluate (context : Context) (challenge : History F G → m F)
    (live : History F G) {resolved : Resolved}
    (free : (resolved matches .observe _ _ _) = false ∧ (resolved matches .challenge _ _ _) = false)
    (arguments : List (Value F G)) :
    resolved.apply context challenge live arguments =
      pure (match resolved.evaluate arguments with
        | .returned results => .returned (results, live, 0)
        | .stopped reason => .stopped reason) := by
  cases resolved with
  | indicesEmpty =>
      rcases arguments with _ | ⟨a, rest⟩
      · rfl
      · simp [Resolved.apply, Resolved.evaluate]
  | indicesAppend =>
      rcases arguments with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · rfl
      · cases a <;> rfl
      · cases a <;> cases b <;> rfl
      · cases a <;> cases b <;> rfl
  | observe => simp at free
  | challenge => simp at free
  | calculate calculation =>
      simp only [Resolved.apply, Resolved.evaluate]
      cases Zkc.Construction.calculate calculation arguments <;> rfl
  | compute operation =>
      simp only [Resolved.apply, Resolved.evaluate]
      cases operation.apply arguments <;> rfl


section Bodies
variable [LawfulMonad m] (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (budget : Nat)

mutual
/-- A local body without transcript operations is its evaluation cut off by the
budget. -/
theorem localK_evaluates (call : String × String) (top : Bool) (region : Option String) :
    ∀ (steps : List Step) (env : Env F G) (s : State F G)
      (exit : List (Value F G) → State F G → m (Run F G)),
      transcriptFree vocabulary validator steps = true → s.used ≤ budget →
      Run.observe <$> localK vocabulary validator context challenge budget call top region steps env s exit =
        cutoff budget s exit (evalSteps vocabulary validator steps env)
  | [], env, s, exit, _, within => by
      simp [localK, evalSteps, cutoff, within, Cause.outcome]
  | step :: rest, env, s, exit, free, within => by
      simp only [transcriptFree, Bool.and_eq_true] at free
      simp only [localK, evalSteps]
      rw [localStep_evaluates call top region step env s _ exit free.1 within]
      cases evalStep vocabulary validator step env with
      | next env' cost =>
          simp only
          rw [cutoff_after]
          by_cases fits : s.used + cost ≤ budget
          · simp only [fits, ite_true]
            exact localK_evaluates call top region rest env' _ exit free.2 fits
          · simp [fits]
      | done result => rfl

/-- One step of a local body without transcript operations is its evaluation
cut off by the budget. -/
theorem localStep_evaluates (call : String × String) (top : Bool) (region : Option String) :
    ∀ (step : Step) (env : Env F G) (s : State F G) (next : Env F G → State F G → m (Run F G))
      (exit : List (Value F G) → State F G → m (Run F G)),
      transcriptFreeStep vocabulary validator step = true → s.used ≤ budget →
      Run.observe <$> localStep vocabulary validator context challenge budget call top region step env s next exit =
        match evalStep vocabulary validator step env with
        | .next env' cost =>
            if s.used + cost ≤ budget then Run.observe <$> next env' { s with used := s.used + cost }
            else pure (.stopped .exhausted, true)
        | .done result => cutoff budget s exit result
  | .operation site binding parameters inputs outputs, env, s, next, exit, free, within => by
      simp only [transcriptFreeStep] at free
      simp only [localStep, evalStep]
      cases resolvedEq : validator.binding? binding >>= (vocabulary.resolve · parameters) with
      | none =>
          by_cases tick : s.used < budget
          · cases lookupAll env inputs <;> simp [tick, cutoff, State.charge, Cause.outcome] <;> omega
          · cases lookupAll env inputs <;> simp [tick, cutoff, Cause.outcome] <;> omega
      | some resolved =>
          rw [resolvedEq] at free
          cases argumentsEq : lookupAll env inputs with
          | none =>
              by_cases tick : s.used < budget
              · simp [tick, cutoff, State.charge, Cause.outcome]; omega
              · simp [tick, cutoff, Cause.outcome]; omega
          | some arguments =>
              simp only
              rw [Resolved.apply_evaluate context challenge s.live
                (by cases resolved <;> simp_all) arguments, pure_bind]
              cases evaluated : resolved.evaluate arguments with
              | returned results =>
                  by_cases lengths : outputs.length = results.length
                  · by_cases tick : s.used < budget
                    · simp [tick, lengths, State.charge]; omega
                    · simp [tick, lengths]; omega
                  · by_cases tick : s.used < budget
                    · simp [tick, lengths, cutoff, State.charge, Cause.outcome]; omega
                    · simp [tick, lengths, cutoff, Cause.outcome]; omega
              | stopped reason =>
                  by_cases tick : s.used < budget
                  · simp [tick, cutoff, State.charge, Cause.outcome]; omega
                  · simp [tick, cutoff, Cause.outcome]; omega
  | .constant site output value, env, s, next, exit, _, within => by
      simp only [localStep, evalStep]
      by_cases tick : s.used < budget
      · have fits : s.used + 1 ≤ budget := by omega
        simp [tick, fits, State.charge]
      · have short : ¬ s.used + 1 ≤ budget := by omega
        simp [tick, short]
  | .cond site condition captures yes no outputs, env, s, next, exit, free, within => by
      simp only [transcriptFreeStep, Bool.and_eq_true] at free
      simp only [localStep, evalStep]
      by_cases tick : s.used < budget
      · have fits : s.charge.used ≤ budget := by simp [State.charge]; omega
        simp only [tick, ite_true]
        cases conditionEq : List.lookup condition env with
        | none => simp [cutoff, State.charge]; omega
        | some value =>
            cases capturedEq : lookupAll env captures with
            | none =>
                rcases value with ((_ | _) | _ | _) | _ | _ | _ | _ <;>
                  simp [cutoff, State.charge] <;> omega
            | some captured =>
                rcases value with (((_ | _) | _ | _) | _ | _ | _ | _)
                · simp only
                  rw [localK_evaluates call false (some site) no _ _ _ free.2 fits]
                  cases evalSteps vocabulary validator no (captures.zip captured) with
                  | values results cost =>
                      by_cases lengths : outputs.length = results.length
                      · simp only [cutoff, lengths, ite_true, State.charge_used]
                        simp [State.charge, Nat.add_assoc]
                      · simp only [cutoff, lengths, ite_false]
                        simp [State.charge, Nat.add_assoc]
                  | stopped cause cost =>
                      simp [cutoff, State.charge, Nat.add_assoc]
                · simp only
                  rw [localK_evaluates call false (some site) yes _ _ _ free.1 fits]
                  cases evalSteps vocabulary validator yes (captures.zip captured) with
                  | values results cost =>
                      by_cases lengths : outputs.length = results.length
                      · simp only [cutoff, lengths, ite_true, State.charge_used]
                        simp [State.charge, Nat.add_assoc]
                      · simp only [cutoff, lengths, ite_false]
                        simp [State.charge, Nat.add_assoc]
                  | stopped cause cost =>
                      simp [cutoff, State.charge, Nat.add_assoc]
                all_goals simp [cutoff, State.charge]; omega
      · simp only [tick, ite_false]
        cases conditionEq : List.lookup condition env with
        | none => simp [cutoff]; omega
        | some value =>
            cases capturedEq : lookupAll env captures with
            | none =>
                rcases value with ((_ | _) | _ | _) | _ | _ | _ | _ <;> simp [cutoff] <;> omega
            | some captured =>
                rcases value with (((_ | _) | _ | _) | _ | _ | _ | _)
                · simp only
                  cases evalSteps vocabulary validator no (captures.zip captured) with
                  | values results cost =>
                      by_cases lengths : outputs.length = results.length <;> simp [cutoff, lengths] <;> omega
                  | stopped cause cost => simp [cutoff]; omega
                · simp only
                  cases evalSteps vocabulary validator yes (captures.zip captured) with
                  | values results cost =>
                      by_cases lengths : outputs.length = results.length <;> simp [cutoff, lengths] <;> omega
                  | stopped cause cost => simp [cutoff]; omega
                all_goals simp [cutoff]; omega
  | .iterate site induction lower upper carried captures body outputs, env, s, next, exit, free, within => by
      simp only [transcriptFreeStep] at free
      simp only [localStep, evalStep]
      cases lowerEq : List.lookup lower env with
      | none =>
          by_cases tick : s.used < budget
          · simp [tick, cutoff, State.charge]; omega
          · simp [tick, cutoff]; omega
      | some lowerValue =>
      cases upperEq : List.lookup upper env with
      | none =>
          by_cases tick : s.used < budget
          · cases lowerValue <;> simp [tick, cutoff, State.charge] <;> omega
          · cases lowerValue <;> simp [tick, cutoff] <;> omega
      | some upperValue =>
      cases initialEq : lookupAll env (carried.map (·.2)) with
      | none =>
          by_cases tick : s.used < budget
          · cases lowerValue <;> cases upperValue <;> simp [tick, cutoff, State.charge] <;> omega
          · cases lowerValue <;> cases upperValue <;> simp [tick, cutoff] <;> omega
      | some initial =>
      cases capturedEq : lookupAll env captures with
      | none =>
          by_cases tick : s.used < budget
          · cases lowerValue <;> cases upperValue <;> simp [tick, cutoff, State.charge] <;> omega
          · cases lowerValue <;> cases upperValue <;> simp [tick, cutoff] <;> omega
      | some captured =>
      cases lowerValue with
      | index first =>
          cases upperValue with
          | index last =>
              simp only
              by_cases bounds : first ≤ 1048576 ∧ last ≤ 1048576 ∧ last - first ≤ 1048576
              · simp only [bounds, and_self, ite_true]
                by_cases tick : s.used < budget
                · have fits : s.charge.used ≤ budget := by simp [State.charge]; omega
                  simp only [tick, ite_true]
                  rw [forK_evaluates budget _ (fun env' => evalSteps vocabulary validator body env')
                    (fun env' s' exit' within' =>
                      localK_evaluates call false (some site) body env' s' exit' free within')
                    site induction (carried.map (·.1)) (captures.zip captured) call _ initial _ _ fits]
                  cases evalFor (fun env' => evalSteps vocabulary validator body env') induction
                      (carried.map (·.1)) (captures.zip captured) (List.range' first (last - first))
                      initial with
                  | values final cost =>
                      by_cases lengths : outputs.length = final.length
                      · simp only [cutoff, lengths, ite_true, State.charge_used]
                        simp [State.charge, Nat.add_assoc]
                      · simp only [cutoff, lengths, ite_false]
                        simp [State.charge, Nat.add_assoc]
                  | stopped cause cost =>
                      simp [cutoff, State.charge, Nat.add_assoc]
                · simp only [tick, ite_false]
                  cases evalFor (fun env' => evalSteps vocabulary validator body env') induction
                      (carried.map (·.1)) (captures.zip captured) (List.range' first (last - first))
                      initial with
                  | values final cost =>
                      by_cases lengths : outputs.length = final.length <;> simp [cutoff, lengths] <;> omega
                  | stopped cause cost => simp [cutoff]; omega
              · simp only [bounds, ite_false]
                by_cases tick : s.used < budget
                · simp [tick, cutoff, State.charge]
                · simp [tick, cutoff]
          | _ =>
              by_cases tick : s.used < budget
              · simp [tick, cutoff, State.charge]; omega
              · simp [tick, cutoff]; omega
      | _ =>
          by_cases tick : s.used < budget
          · cases upperValue <;> simp [tick, cutoff, State.charge] <;> omega
          · cases upperValue <;> simp [tick, cutoff] <;> omega
  | .stop site reason, env, s, next, exit, _, within => by
      simp only [localStep, evalStep]
      by_cases tick : s.used < budget
      · have fits : s.used + 1 ≤ budget := by omega
        simp only [tick, ite_true]
        cases stopReason? reason <;> simp [cutoff, fits, State.charge, Cause.outcome]
      · have short : ¬ s.used + 1 ≤ budget := by omega
        simp only [tick, ite_false]
        cases stopReason? reason <;> simp [cutoff, short]
  | .yield values, env, s, next, exit, _, within => by
      simp only [localStep, evalStep]
      by_cases tick : s.used < budget
      · have fits : s.used + 1 ≤ budget := by omega
        simp only [tick, ite_true]
        cases lookupAll env values <;> simp [cutoff, fits, State.charge, Cause.outcome]
      · have short : ¬ s.used + 1 ≤ budget := by omega
        simp only [tick, ite_false]
        cases lookupAll env values <;> simp [cutoff, short]
  | .ret values, env, s, next, exit, _, within => by
      simp only [localStep, evalStep]
      by_cases tick : s.used < budget
      · have fits : s.used + 1 ≤ budget := by omega
        simp only [tick, ite_true]
        cases lookupAll env values <;> simp [cutoff, fits, State.charge, Cause.outcome]
      · have short : ¬ s.used + 1 ≤ budget := by omega
        simp only [tick, ite_false]
        cases lookupAll env values <;> simp [cutoff, short]
  | .unsupported name, env, s, next, exit, _, within => by
      simp [localStep, evalStep, cutoff, within, Cause.outcome]
end

end Bodies

/-! ## Evaluation equations

One equation per step form, for evaluating a concrete body on symbolic
arguments one step at a time. -/

section Equations
variable (vocabulary : Vocabulary) (validator : Validator)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
@[simp] theorem Evaluated.after_values (extra : Nat) (results : List (Value F G)) (cost : Nat) :
    (Evaluated.values results cost).after extra = .values results (extra + cost) := rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
@[simp] theorem Evaluated.after_stopped (extra : Nat) (cause : Cause) (cost : Nat) :
    (Evaluated.stopped cause cost : Evaluated F G).after extra = .stopped cause (extra + cost) := rfl

theorem evalSteps_operation {site binding : String} {parameters : List Parameter}
    {inputs outputs : List String} {rest : List Step} {env : Env F G} {resolved : Resolved}
    {arguments results : List (Value F G)}
    (resolves : validator.binding? binding >>= (vocabulary.resolve · parameters) = some resolved)
    (looked : lookupAll env inputs = some arguments)
    (evaluates : resolved.evaluate arguments = .returned results)
    (length : outputs.length = results.length) :
    evalSteps vocabulary validator (.operation site binding parameters inputs outputs :: rest) env =
      (evalSteps vocabulary validator rest (outputs.zip results ++ env)).after 1 := by
  simp only [evalSteps, evalStep, resolves, looked, evaluates, length, ite_true]

theorem evalSteps_operation_stopped {site binding : String} {parameters : List Parameter}
    {inputs outputs : List String} {rest : List Step} {env : Env F G} {resolved : Resolved}
    {arguments : List (Value F G)} {reason : PIR.Stop}
    (resolves : validator.binding? binding >>= (vocabulary.resolve · parameters) = some resolved)
    (looked : lookupAll env inputs = some arguments)
    (evaluates : resolved.evaluate arguments = .stopped reason) :
    evalSteps vocabulary validator (.operation site binding parameters inputs outputs :: rest) env =
      .stopped (.kernel reason) 1 := by
  simp only [evalSteps, evalStep, resolves, looked, evaluates]

theorem evalSteps_constant {site output : String} {value : Bool} {rest : List Step} {env : Env F G} :
    evalSteps vocabulary validator (.constant site output value :: rest) env =
      (evalSteps vocabulary validator rest ((output, .data (.boolean value)) :: env)).after 1 := by
  simp only [evalSteps, evalStep]

theorem evalSteps_cond {site condition : String} {captures : List String} {yes no : List Step}
    {outputs : List String} {rest : List Step} {env : Env F G} {decision : Bool}
    {captured results : List (Value F G)} {cost : Nat}
    (conditionEq : List.lookup condition env = some (.data (.boolean decision)))
    (looked : lookupAll env captures = some captured)
    (branch : evalSteps vocabulary validator (if decision then yes else no) (captures.zip captured) =
      .values results cost)
    (length : outputs.length = results.length) :
    evalSteps vocabulary validator (.cond site condition captures yes no outputs :: rest) env =
      (evalSteps vocabulary validator rest (outputs.zip results ++ env)).after (1 + cost) := by
  cases decision <;> simp only [evalSteps, evalStep, conditionEq, looked] <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] at branch <;> simp [branch, length]

theorem evalSteps_cond_stopped {site condition : String} {captures : List String} {yes no : List Step}
    {outputs : List String} {rest : List Step} {env : Env F G} {decision : Bool}
    {captured : List (Value F G)} {cause : Cause} {cost : Nat}
    (conditionEq : List.lookup condition env = some (.data (.boolean decision)))
    (looked : lookupAll env captures = some captured)
    (branch : evalSteps vocabulary validator (if decision then yes else no) (captures.zip captured) =
      .stopped cause cost) :
    evalSteps vocabulary validator (.cond site condition captures yes no outputs :: rest) env =
      .stopped cause (1 + cost) := by
  cases decision <;> simp only [evalSteps, evalStep, conditionEq, looked] <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] at branch <;> simp [branch]

theorem evalSteps_iterate {site induction lower upper : String} {carried : List (String × String)}
    {captures : List String} {body : List Step} {outputs : List String} {rest : List Step}
    {env : Env F G} {first last : Nat} {initial captured final : List (Value F G)} {cost : Nat}
    (lowerEq : List.lookup lower env = some (.index first))
    (upperEq : List.lookup upper env = some (.index last))
    (initialEq : lookupAll env (carried.map (·.2)) = some initial)
    (capturedEq : lookupAll env captures = some captured)
    (bounded : first ≤ 1048576 ∧ last ≤ 1048576 ∧ last - first ≤ 1048576)
    (loop : evalFor (fun env' => evalSteps vocabulary validator body env') induction (carried.map (·.1))
      (captures.zip captured) (List.range' first (last - first)) initial = .values final cost)
    (length : outputs.length = final.length) :
    evalSteps vocabulary validator
        (.iterate site induction lower upper carried captures body outputs :: rest) env =
      (evalSteps vocabulary validator rest (outputs.zip final ++ env)).after (1 + cost) := by
  simp only [evalSteps, evalStep, lowerEq, upperEq, initialEq, capturedEq, bounded, and_self, ite_true,
    loop, length]

theorem evalSteps_yield {values : List String} {rest : List Step} {env : Env F G}
    {results : List (Value F G)} (looked : lookupAll env values = some results) :
    evalSteps vocabulary validator (.yield values :: rest) env = .values results 1 := by
  simp only [evalSteps, evalStep, looked]

theorem evalSteps_ret {values : List String} {rest : List Step} {env : Env F G}
    {results : List (Value F G)} (looked : lookupAll env values = some results) :
    evalSteps vocabulary validator (.ret values :: rest) env = .values results 1 := by
  simp only [evalSteps, evalStep, looked]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem evalFor_cons {run : Env F G → Evaluated F G} {induction : String} {carried : List String}
    {captured : Env F G} {index : Nat} {rest : List Nat} {values yielded : List (Value F G)} {cost : Nat}
    (step : run ((induction, .index index) :: carried.zip values ++ captured) = .values yielded cost)
    (length : yielded.length = carried.length) :
    evalFor run induction carried captured (index :: rest) values =
      (evalFor run induction carried captured rest yielded).after cost := by
  simp only [evalFor, step, length, ite_true]

/-- An evaluation hands back `results`, after some charge. -/
def Evaluated.Returns (result : Evaluated F G) (results : List (Value F G)) : Prop :=
  ∃ cost, result = .values results cost

/-- An evaluation stops for `cause`, after some charge. -/
def Evaluated.Stops (result : Evaluated F G) (cause : Cause) : Prop :=
  ∃ cost, result = .stopped cause cost

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Evaluated.Returns.after {result : Evaluated F G} {results : List (Value F G)}
    (returns : result.Returns results) (extra : Nat) : (result.after extra).Returns results := by
  obtain ⟨cost, rfl⟩ := returns
  exact ⟨extra + cost, rfl⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Evaluated.Stops.after {result : Evaluated F G} {cause : Cause} (stops : result.Stops cause)
    (extra : Nat) : (result.after extra).Stops cause := by
  obtain ⟨cost, rfl⟩ := stops
  exact ⟨extra + cost, rfl⟩

/-- The evaluation of a body of steps after a step that continues. -/
theorem Evaluated.Returns.operation {site binding : String} {parameters : List Parameter}
    {inputs outputs : List String} {rest : List Step} {env : Env F G} {resolved : Resolved}
    {arguments results final : List (Value F G)}
    (resolves : validator.binding? binding >>= (vocabulary.resolve · parameters) = some resolved)
    (looked : lookupAll env inputs = some arguments)
    (evaluates : resolved.evaluate arguments = .returned results)
    (length : outputs.length = results.length)
    (continues : (evalSteps vocabulary validator rest (outputs.zip results ++ env)).Returns final) :
    (evalSteps vocabulary validator (.operation site binding parameters inputs outputs :: rest) env).Returns
      final := by
  rw [evalSteps_operation vocabulary validator resolves looked evaluates length]
  exact continues.after 1

theorem Evaluated.Stops.operation {site binding : String} {parameters : List Parameter}
    {inputs outputs : List String} {rest : List Step} {env : Env F G} {resolved : Resolved}
    {arguments results : List (Value F G)} {cause : Cause}
    (resolves : validator.binding? binding >>= (vocabulary.resolve · parameters) = some resolved)
    (looked : lookupAll env inputs = some arguments)
    (evaluates : resolved.evaluate arguments = .returned results)
    (length : outputs.length = results.length)
    (continues : (evalSteps vocabulary validator rest (outputs.zip results ++ env)).Stops cause) :
    (evalSteps vocabulary validator (.operation site binding parameters inputs outputs :: rest) env).Stops
      cause := by
  rw [evalSteps_operation vocabulary validator resolves looked evaluates length]
  exact continues.after 1

theorem Evaluated.Stops.operation_stops {site binding : String} {parameters : List Parameter}
    {inputs outputs : List String} {rest : List Step} {env : Env F G} {resolved : Resolved}
    {arguments : List (Value F G)} {reason : PIR.Stop}
    (resolves : validator.binding? binding >>= (vocabulary.resolve · parameters) = some resolved)
    (looked : lookupAll env inputs = some arguments)
    (evaluates : resolved.evaluate arguments = .stopped reason) :
    (evalSteps vocabulary validator (.operation site binding parameters inputs outputs :: rest) env).Stops
      (.kernel reason) :=
  ⟨1, evalSteps_operation_stopped vocabulary validator resolves looked evaluates⟩

theorem Evaluated.Returns.constant {site output : String} {value : Bool} {rest : List Step}
    {env : Env F G} {final : List (Value F G)}
    (continues : (evalSteps vocabulary validator rest ((output, .data (.boolean value)) :: env)).Returns final) :
    (evalSteps vocabulary validator (.constant site output value :: rest) env).Returns final := by
  rw [evalSteps_constant]
  exact continues.after 1

theorem Evaluated.Returns.cond_true {site condition : String} {captures : List String}
    {yes no : List Step} {outputs : List String} {rest : List Step} {env : Env F G}
    {captured results final : List (Value F G)}
    (conditionEq : List.lookup condition env = some (.data (.boolean true)))
    (looked : lookupAll env captures = some captured)
    (branch : (evalSteps vocabulary validator yes (captures.zip captured)).Returns results)
    (length : outputs.length = results.length)
    (continues : (evalSteps vocabulary validator rest (outputs.zip results ++ env)).Returns final) :
    (evalSteps vocabulary validator (.cond site condition captures yes no outputs :: rest) env).Returns final := by
  obtain ⟨cost, branchEq⟩ := branch
  rw [evalSteps_cond vocabulary validator (decision := true) conditionEq looked branchEq length]
  exact continues.after _

theorem Evaluated.Returns.cond_false {site condition : String} {captures : List String}
    {yes no : List Step} {outputs : List String} {rest : List Step} {env : Env F G}
    {captured results final : List (Value F G)}
    (conditionEq : List.lookup condition env = some (.data (.boolean false)))
    (looked : lookupAll env captures = some captured)
    (branch : (evalSteps vocabulary validator no (captures.zip captured)).Returns results)
    (length : outputs.length = results.length)
    (continues : (evalSteps vocabulary validator rest (outputs.zip results ++ env)).Returns final) :
    (evalSteps vocabulary validator (.cond site condition captures yes no outputs :: rest) env).Returns final := by
  obtain ⟨cost, branchEq⟩ := branch
  rw [evalSteps_cond vocabulary validator (decision := false) conditionEq looked branchEq length]
  exact continues.after _

theorem Evaluated.Stops.cond_true {site condition : String} {captures : List String}
    {yes no : List Step} {outputs : List String} {rest : List Step} {env : Env F G}
    {captured results : List (Value F G)} {cause : Cause}
    (conditionEq : List.lookup condition env = some (.data (.boolean true)))
    (looked : lookupAll env captures = some captured)
    (branch : (evalSteps vocabulary validator yes (captures.zip captured)).Returns results)
    (length : outputs.length = results.length)
    (continues : (evalSteps vocabulary validator rest (outputs.zip results ++ env)).Stops cause) :
    (evalSteps vocabulary validator (.cond site condition captures yes no outputs :: rest) env).Stops cause := by
  obtain ⟨cost, branchEq⟩ := branch
  rw [evalSteps_cond vocabulary validator (decision := true) conditionEq looked branchEq length]
  exact continues.after _

theorem Evaluated.Stops.cond_stops {site condition : String} {captures : List String}
    {yes no : List Step} {outputs : List String} {rest : List Step} {env : Env F G}
    {captured : List (Value F G)} {cause : Cause}
    (conditionEq : List.lookup condition env = some (.data (.boolean true)))
    (looked : lookupAll env captures = some captured)
    (branch : (evalSteps vocabulary validator yes (captures.zip captured)).Stops cause) :
    (evalSteps vocabulary validator (.cond site condition captures yes no outputs :: rest) env).Stops cause := by
  obtain ⟨cost, branchEq⟩ := branch
  exact ⟨1 + cost, evalSteps_cond_stopped vocabulary validator (decision := true) conditionEq looked branchEq⟩

theorem Evaluated.Returns.iterate {site induction lower upper : String} {carried : List (String × String)}
    {captures : List String} {body : List Step} {outputs : List String} {rest : List Step}
    {env : Env F G} {first last : Nat} {initial captured results final : List (Value F G)}
    (lowerEq : List.lookup lower env = some (.index first))
    (upperEq : List.lookup upper env = some (.index last))
    (initialEq : lookupAll env (carried.map (·.2)) = some initial)
    (capturedEq : lookupAll env captures = some captured)
    (bounded : first ≤ 1048576 ∧ last ≤ 1048576 ∧ last - first ≤ 1048576)
    (loop : (evalFor (fun env' => evalSteps vocabulary validator body env') induction (carried.map (·.1))
      (captures.zip captured) (List.range' first (last - first)) initial).Returns results)
    (length : outputs.length = results.length)
    (continues : (evalSteps vocabulary validator rest (outputs.zip results ++ env)).Returns final) :
    (evalSteps vocabulary validator
        (.iterate site induction lower upper carried captures body outputs :: rest) env).Returns final := by
  obtain ⟨cost, loopEq⟩ := loop
  rw [evalSteps_iterate vocabulary validator lowerEq upperEq initialEq capturedEq bounded loopEq length]
  exact continues.after _

theorem Evaluated.Returns.yield {values : List String} {rest : List Step} {env : Env F G}
    {results : List (Value F G)} (looked : lookupAll env values = some results) :
    (evalSteps vocabulary validator (.yield values :: rest) env).Returns results :=
  ⟨1, evalSteps_yield vocabulary validator looked⟩

theorem Evaluated.Returns.ret {values : List String} {rest : List Step} {env : Env F G}
    {results : List (Value F G)} (looked : lookupAll env values = some results) :
    (evalSteps vocabulary validator (.ret values :: rest) env).Returns results :=
  ⟨1, evalSteps_ret vocabulary validator looked⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Evaluated.Returns.for_nil {run : Env F G → Evaluated F G} {induction : String}
    {carried : List String} {captured : Env F G} {values : List (Value F G)} :
    (evalFor run induction carried captured [] values).Returns values :=
  ⟨0, rfl⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Evaluated.Returns.for_cons {run : Env F G → Evaluated F G} {induction : String}
    {carried : List String} {captured : Env F G} {index : Nat} {rest : List Nat}
    {values yielded final : List (Value F G)}
    (step : (run ((induction, .index index) :: carried.zip values ++ captured)).Returns yielded)
    (length : yielded.length = carried.length)
    (continues : (evalFor run induction carried captured rest yielded).Returns final) :
    (evalFor run induction carried captured (index :: rest) values).Returns final := by
  obtain ⟨cost, stepEq⟩ := step
  rw [evalFor_cons stepEq length]
  exact continues.after cost

/-! ### Evaluation with its charge

The same equations with the exact charge, for bodies whose charge a bound
depends on. -/

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- An evaluation hands back `results` after charging exactly `cost`
instructions. -/
def Evaluated.ReturnsAfter (result : Evaluated F G) (results : List (Value F G)) (cost : Nat) : Prop :=
  result = .values results cost

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Evaluated.ReturnsAfter.of_eq {result : Evaluated F G} {results : List (Value F G)} {cost cost' : Nat}
    (returns : result.ReturnsAfter results cost) (same : cost = cost') : result.ReturnsAfter results cost' := by
  rw [← same]
  exact returns

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Evaluated.ReturnsAfter.returns {result : Evaluated F G} {results : List (Value F G)} {cost : Nat}
    (returns : result.ReturnsAfter results cost) : result.Returns results :=
  ⟨cost, returns⟩

theorem Evaluated.ReturnsAfter.operation {site binding : String} {parameters : List Parameter}
    {inputs outputs : List String} {rest : List Step} {env : Env F G} {resolved : Resolved}
    {arguments results final : List (Value F G)} {cost : Nat}
    (resolves : validator.binding? binding >>= (vocabulary.resolve · parameters) = some resolved)
    (looked : lookupAll env inputs = some arguments)
    (evaluates : resolved.evaluate arguments = .returned results)
    (length : outputs.length = results.length)
    (continues : (evalSteps vocabulary validator rest (outputs.zip results ++ env)).ReturnsAfter final cost) :
    (evalSteps vocabulary validator (.operation site binding parameters inputs outputs :: rest) env).ReturnsAfter
      final (1 + cost) := by
  rw [evalSteps_operation vocabulary validator resolves looked evaluates length, continues]
  rfl

theorem Evaluated.ReturnsAfter.constant {site output : String} {value : Bool} {rest : List Step}
    {env : Env F G} {final : List (Value F G)} {cost : Nat}
    (continues : (evalSteps vocabulary validator rest ((output, .data (.boolean value)) :: env)).ReturnsAfter
      final cost) :
    (evalSteps vocabulary validator (.constant site output value :: rest) env).ReturnsAfter final (1 + cost) := by
  rw [evalSteps_constant, continues]
  rfl

theorem Evaluated.ReturnsAfter.cond {site condition : String} {captures : List String}
    {yes no : List Step} {outputs : List String} {rest : List Step} {env : Env F G} {decision : Bool}
    {captured results final : List (Value F G)} {branchCost cost : Nat}
    (conditionEq : List.lookup condition env = some (.data (.boolean decision)))
    (looked : lookupAll env captures = some captured)
    (branch : (evalSteps vocabulary validator (if decision then yes else no) (captures.zip captured)).ReturnsAfter
      results branchCost)
    (length : outputs.length = results.length)
    (continues : (evalSteps vocabulary validator rest (outputs.zip results ++ env)).ReturnsAfter final cost) :
    (evalSteps vocabulary validator (.cond site condition captures yes no outputs :: rest) env).ReturnsAfter final
      (1 + branchCost + cost) := by
  rw [evalSteps_cond vocabulary validator conditionEq looked branch length, continues]
  rfl

theorem Evaluated.ReturnsAfter.iterate {site induction lower upper : String} {carried : List (String × String)}
    {captures : List String} {body : List Step} {outputs : List String} {rest : List Step}
    {env : Env F G} {first last : Nat} {initial captured results final : List (Value F G)}
    {loopCost cost : Nat}
    (lowerEq : List.lookup lower env = some (.index first))
    (upperEq : List.lookup upper env = some (.index last))
    (initialEq : lookupAll env (carried.map (·.2)) = some initial)
    (capturedEq : lookupAll env captures = some captured)
    (bounded : first ≤ 1048576 ∧ last ≤ 1048576 ∧ last - first ≤ 1048576)
    (loop : (evalFor (fun env' => evalSteps vocabulary validator body env') induction (carried.map (·.1))
      (captures.zip captured) (List.range' first (last - first)) initial).ReturnsAfter results loopCost)
    (length : outputs.length = results.length)
    (continues : (evalSteps vocabulary validator rest (outputs.zip results ++ env)).ReturnsAfter final cost) :
    (evalSteps vocabulary validator
        (.iterate site induction lower upper carried captures body outputs :: rest) env).ReturnsAfter final
      (1 + loopCost + cost) := by
  rw [evalSteps_iterate vocabulary validator lowerEq upperEq initialEq capturedEq bounded loop length, continues]
  rfl

theorem Evaluated.ReturnsAfter.yield {values : List String} {rest : List Step} {env : Env F G}
    {results : List (Value F G)} (looked : lookupAll env values = some results) :
    (evalSteps vocabulary validator (.yield values :: rest) env).ReturnsAfter results 1 :=
  evalSteps_yield vocabulary validator looked

theorem Evaluated.ReturnsAfter.ret {values : List String} {rest : List Step} {env : Env F G}
    {results : List (Value F G)} (looked : lookupAll env values = some results) :
    (evalSteps vocabulary validator (.ret values :: rest) env).ReturnsAfter results 1 :=
  evalSteps_ret vocabulary validator looked

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Evaluated.ReturnsAfter.for_nil {run : Env F G → Evaluated F G} {induction : String}
    {carried : List String} {captured : Env F G} {values : List (Value F G)} :
    (evalFor run induction carried captured [] values).ReturnsAfter values 0 :=
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Evaluated.ReturnsAfter.for_cons {run : Env F G → Evaluated F G} {induction : String}
    {carried : List String} {captured : Env F G} {index : Nat} {rest : List Nat}
    {values yielded final : List (Value F G)} {stepCost cost : Nat}
    (step : (run ((induction, .index index) :: carried.zip values ++ captured)).ReturnsAfter yielded stepCost)
    (length : yielded.length = carried.length)
    (continues : (evalFor run induction carried captured rest yielded).ReturnsAfter final cost) :
    (evalFor run induction carried captured (index :: rest) values).ReturnsAfter final (stepCost + cost) := by
  rw [evalFor_cons step length, continues]
  rfl

end Equations

end Field

end Zkc.Executable
