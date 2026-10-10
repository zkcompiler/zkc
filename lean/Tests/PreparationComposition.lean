import Tests.BilinearInstallation
import Zkc.Polynomial.Bilinear.Compilation

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Tests.PreparationComposition
open PIR
open Zkc.Modules.Factor Zkc.Modules.FactorBinding
open Zkc.Polynomial.Bilinear.Execution

inductive Mutation where
  | challenge (id value : Nat) (success : Bool)
  | view (handle value : Nat) (success : Bool)
  deriving DecidableEq, Repr

def mutationWrites : Mutation → Zkc.Modules.FactorState.Writes
  | .challenge id _ _ => ⟨[],[],[id]⟩
  | .view id _ _ => ⟨[],[id],[]⟩

def mutationSummary (m : Mutation) : Zkc.Modules.FactorState.Summary :=
  ⟨some (mutationWrites m),[],[],match m with | .challenge id _ _ => [id] | .view _ _ _ => []⟩

def mutate (m : Mutation) : Zkc.Modules.FactorState.Implementation Nat Nat := fun s =>
  match m with
  | .challenge id value ok =>
    ⟨ok,⟨{s.values with challenge := fun i => if i = id then value else s.values.challenge i},
      id :: s.known⟩,[value]⟩
  | .view id value ok =>
    ⟨ok,⟨overwrite s.values id (fun _ => value),s.known⟩,[value]⟩

def mutationContract (m : Mutation) : Zkc.Modules.FactorState.Spec Nat := ⟨fun _ => True,fun _ => mutationSummary m⟩

/-- A failed external call can mutate just as a successful one can. Both
    branches expose the actual footprint to the old fact-transfer analysis. -/
theorem mutation_satisfies (m : Mutation) : Zkc.Modules.FactorState.Satisfies (mutationContract m) (mutate m) := by
  intro s _
  cases m with
  | challenge id value ok =>
    refine ⟨?_,?_,?_,?_⟩
    · constructor
      · intro k _; rfl
      · intro h _; rfl
      · intro i hi
        have hn : i ≠ id := by simpa [mutationContract,mutationSummary,mutationWrites] using hi
        simp [mutate,hn]
    · simp [mutationContract,mutationSummary, Zkc.Modules.Factor.Valid]
    · intro i hi
      have hm : i ∈ s.known := (List.mem_filter.mp hi).1
      exact List.mem_cons_of_mem id hm
    · intro i hi
      have he : i = id := by simpa [mutationContract,mutationSummary] using hi
      subst i; exact List.mem_cons_self
  | view id value ok =>
    refine ⟨?_,?_,?_,?_⟩
    · constructor
      · intro k _; rfl
      · intro h hh
        have hn : h ≠ id := by simpa [mutationContract,mutationSummary,mutationWrites] using hh
        simp [mutate,overwrite,hn]
      · intro i _; rfl
    · simp [mutationContract,mutationSummary,Zkc.Modules.Factor.Valid]
    · intro i hi
      exact (List.mem_filter.mp hi).1
    · simp [Zkc.Modules.FactorState.Known,mutationContract,mutationSummary]

def n0 : Zkc.Modules.FactorBinding.Namespace := ⟨0,0⟩
def n1 : Zkc.Modules.FactorBinding.Namespace := ⟨1,0⟩
def input : Input := ⟨100,1,2,3,4,2,3⟩
def external (id : Nat) : Zkc.Modules.FactorState.Implementation Nat Nat :=
  mutate (if id = 0 then .challenge (addr n0 0) 4 false else .view (addr n0 0) 999 true)
def contracts (id : Nat) : Zkc.Modules.FactorState.Spec Nat :=
  mutationContract (if id = 0 then .challenge (addr n0 0) 4 false else .view (addr n0 0) 999 true)
theorem external_laws (id : Nat) : Zkc.Modules.FactorState.Satisfies (contracts id) (external id) := mutation_satisfies _

def calls : Nat → Call
  | 0 => .prepare input n0 2
  | 1 => .external 0
  | 2 => .prepare {input with x := 4} n0 2
  | 3 => .external 1
  | 4 => .prepare input n0 2
  | 5 => .prepare {input with y := 5} n1 2
  | _ => .prepare {input with x := 9} n0 1

def q (n : Zkc.Modules.FactorBinding.Namespace) : Query := query n ⟨Zkc.Polynomial.Bilinear.Factor.originKey 100,[0,1]⟩

def source : Zkc.Compiler.FactorProgram.Source :=
  .call 0
    (.demand (q n0)
      (.call 1 .stop
        (.demand (q n0)
          (.call 2
            (.demand (q n0)
              (.call 3
                (.demand (q n0)
                  (.call 4
                    (.demand (q n0)
                      (.call 5
                        (.demand (q n0) (.demand (q n1)
                          (.call 6 .stop (.demand (q n0) .stop))))
                        .stop))
                    .stop))
                .stop))
            .stop))))
    .stop

def initial : Zkc.Modules.FactorState.World Nat := Tests.BilinearInstallation.initial
def code := Zkc.Compiler.FactorProgram.compile (fun id => (spec contracts (calls id)).post) [] [] source
def run (optimized : Bool) :=
  (Zkc.Compiler.FactorExecution.embed (if optimized then code else Zkc.Compiler.FactorProgram.direct source)).run
    (Zkc.Polynomial.Bilinear.Compilation.mixedHandler (if optimized then .memo else .direct) external calls) (initial,Zkc.Modules.Preparation.empty)

/-- Decidability of the existing finite-instance legality predicate. This is
    evaluation of a fixed reference instance, not a static admission algorithm. -/
def legalDecision {E : Type} (specs : Nat → Zkc.Modules.FactorState.Spec Nat) (impl : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (pre : ∀ id s, Decidable ((specs id).pre s)) (available : List Nat) :
    (src : Zkc.Compiler.FactorProgram.Source) → (s : Zkc.Modules.FactorState.World Nat) →
      Decidable (Zkc.Compiler.FactorProgram.Legal specs impl available src s)
  | .stop, _ => isTrue trivial
  | .demand q next, s =>
    letI := legalDecision specs impl pre available next s
    inferInstanceAs (Decidable (Zkc.Modules.FactorState.Ready available q ∧ _))
  | .call id yes no, s => by
    letI := pre id s
    letI := legalDecision specs impl pre (Zkc.Modules.FactorState.nextKnown ((specs id).post (impl id s).success) available) yes (impl id s).world
    letI := legalDecision specs impl pre (Zkc.Modules.FactorState.nextKnown ((specs id).post (impl id s).success) available) no (impl id s).world
    unfold Zkc.Compiler.FactorProgram.Legal
    infer_instance

def preDecision (id : Nat) (s : Zkc.Modules.FactorState.World Nat) : Decidable ((spec contracts (calls id)).pre s) := by
  cases h : calls id with
  | prepare i n cap => exact isTrue trivial
  | external k => exact isTrue trivial

def legalCheck := @decide _ (legalDecision (fun id => spec contracts (calls id))
  (fun id => reference external (calls id)) preDecision [] source initial)

def row (optimized : Bool) : Outcome (List Nat) × Nat × Nat × Nat :=
  let r := run optimized
  (r.outcome,Preparation.work r.events,Preparation.saved r.events,Preparation.overhead r.events)

theorem source_legal : Zkc.Compiler.FactorProgram.Legal (fun id => spec contracts (calls id))
    (fun id => reference external (calls id)) [] source initial := by
  let := legalDecision (fun id => spec contracts (calls id))
    (fun id => reference external (calls id)) preDecision [] source initial
  exact of_decide_eq_true (show legalCheck = true from rfl)

/-- The example discharges the generic theorem's premises from an empty state;
    no initial prepared fact or cache validity certificate is supplied by a user. -/
theorem source_correct : Related SameWorld Preparation.view Preparation.view (run true) (run false) := by
  exact Zkc.Polynomial.Bilinear.Compilation.compile_with_guards contracts external external_laws calls source initial Zkc.Modules.Preparation.empty [] []
    (Zkc.Modules.ImmutableCache.empty_valid _) (by simp [Zkc.Modules.Factor.Valid]) (by simp [Zkc.Modules.FactorState.Known]) source_legal

theorem actual_outputs_and_costs :
    row false = (.returned [38,66,66,66,38,38,60,38],16,0,0) ∧
    row true = (.returned [38,66,66,66,38,38,60,38],8,8,6) := by
  decide +kernel

def f (n : Zkc.Modules.FactorBinding.Namespace) : Fact := (input.request n).exported
def afterInstall : Zkc.Modules.FactorState.World Nat := (reference external (calls 0) initial).world
def afterChallenge : Zkc.Modules.FactorState.World Nat := (external 0 afterInstall).world
def afterClobber : Zkc.Modules.FactorState.World Nat := (external 1 afterChallenge).world

theorem changed_capture_changes_key : input.prepKey ≠ ({input with x := 4} : Input).prepKey := by decide
theorem separate_namespace_can_share_preparation :
    input.prepKey = ({input with y := 5} : Input).prepKey ∧
    (input.request n0).namespaceId ≠ (input.request n1).namespaceId := by decide

theorem ignored_failure_write_is_wrong :
    (external 0 afterInstall).success = false ∧
    runPlan afterChallenge.values (q n0) (.reuse (f n0) [addr n0 1]) = 38 ∧
    runQuery afterChallenge.values (q n0) = 66 ∧
    Zkc.Modules.FactorState.nextFacts (mutationSummary (.challenge (addr n0 0) 4 false)) [f n0] = [] := by decide

theorem ignored_alias_write_is_wrong :
    runPlan afterClobber.values (q n0) (.reuse (f n0) [addr n0 1]) = 999 ∧
    runQuery afterClobber.values (q n0) = 66 ∧
    Zkc.Modules.FactorState.nextFacts (mutationSummary (.view (addr n0 0) 999 true)) [f n0] = [] := by decide

def reuse (n : Zkc.Modules.FactorBinding.Namespace) (tail : Zkc.Compiler.FactorProgram.Code) : Zkc.Compiler.FactorProgram.Code :=
  .demand (q n) (.reuse (f n) [addr n 1]) tail
def direct (n : Zkc.Modules.FactorBinding.Namespace) (tail : Zkc.Compiler.FactorProgram.Code) : Zkc.Compiler.FactorProgram.Code :=
  .demand (q n) .direct tail

/-- An equally capable library chooses the same legal plans by hand, using the
    same source calls, preparation interpreter, cache and contracts. -/
def libraryCode : Zkc.Compiler.FactorProgram.Code :=
  .call 0
    (reuse n0
      (.call 1 .stop
        (direct n0
          (.call 2
            (reuse n0
              (.call 3
                (direct n0
                  (.call 4
                    (reuse n0
                      (.call 5
                        (reuse n0 (reuse n1
                          (.call 6 .stop (reuse n0 .stop))))
                        .stop))
                    .stop))
                .stop))
            .stop))))
    .stop

theorem library_has_same_plans : libraryCode = code := by rfl

def libraryRun := (Zkc.Compiler.FactorExecution.embed libraryCode).run (Zkc.Polynomial.Bilinear.Compilation.mixedHandler .memo external calls) (initial,Zkc.Modules.Preparation.empty)

theorem library_has_same_execution : libraryRun = run true := by
  change (Zkc.Compiler.FactorExecution.embed libraryCode).run _ _ = _
  rw [library_has_same_plans]
  rfl

/-- A stale manual plan that ignores writes is unsound even with a valid cache. -/
def stale (src : Zkc.Compiler.FactorProgram.Source) : Zkc.Compiler.FactorProgram.Code :=
  match src with
  | .stop => .stop
  | .demand query next => .demand query
      (.reuse (f (if query = q n1 then n1 else n0))
        [addr (if query = q n1 then n1 else n0) 1]) (stale next)
  | .call id yes no => .call id (stale yes) (stale no)

def firstFour : Outcome (List Nat) → Outcome (List Nat)
  | .returned values => .returned (values.take 4)
  | .stopped why => .stopped why

theorem stale_plan_counterexample :
    firstFour ((Zkc.Compiler.FactorExecution.embed (stale source)).run (Zkc.Polynomial.Bilinear.Compilation.mixedHandler .memo external calls)
      (initial,Zkc.Modules.Preparation.empty)).outcome = .returned [38,38,66,999] := by rfl

theorem stale_execution_differs :
    ((Zkc.Compiler.FactorExecution.embed (stale source)).run (Zkc.Polynomial.Bilinear.Compilation.mixedHandler .memo external calls)
      (initial,Zkc.Modules.Preparation.empty)).outcome ≠ (run false).outcome := by
  intro h
  have bad := congrArg firstFour h
  rw [stale_plan_counterexample] at bad
  have good : firstFour (run false).outcome = .returned [38,66,66,66] := rfl
  rw [good] at bad
  contradiction

theorem rejected_install_has_no_preparation :
    let first := call .memo external (calls 0) (initial,Zkc.Modules.Preparation.empty)
    let refused := call .memo external (calls 6) (first.returned.world,first.cache)
    refused.returned.success = false ∧ refused.work = 0 ∧ refused.overhead = 0 ∧
    refused.cache = first.cache ∧ refused.returned.world = first.returned.world := by
  refine ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem unavailable_demand_refused :
    (Zkc.Compiler.FactorExecution.embed (.demand (q n0) .direct .stop)).run
      (Zkc.Polynomial.Bilinear.Compilation.mixedHandler .memo external calls) (initial,Zkc.Modules.Preparation.empty) =
      ⟨.stopped .refused,(initial,Zkc.Modules.Preparation.empty),[]⟩ := rfl

def afterRefusal : Zkc.Compiler.FactorProgram.Code := .call 0 .stop (.demand (q n0) .direct .stop)
def failCalls (_ : Nat) : Call := .prepare input n0 1

theorem failed_install_then_missing_input :
    (Zkc.Compiler.FactorExecution.embed afterRefusal).run (Zkc.Polynomial.Bilinear.Compilation.mixedHandler .memo external failCalls)
      (initial,Zkc.Modules.Preparation.empty) =
      ⟨.stopped .refused,(initial,Zkc.Modules.Preparation.empty),
        [.visible (.inl (.rejected n0)),.charge 0 0 0]⟩ := rfl


end Tests.PreparationComposition
