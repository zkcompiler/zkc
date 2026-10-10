import Zkc.Compiler.Analysis.FactorReuse
import Zkc.Modules.FactorContract


set_option autoImplicit false
namespace Zkc.Compiler.FactorProgram
open Zkc.Modules.Factor Zkc.Compiler.FactorReuse
open Zkc.Modules.FactorState

/-- Finite caller trees with returned success/failure branches. Queries export
    pure values; they do not themselves choose the next command in this fragment. -/
inductive Source where
  | stop
  | demand (q : Query) (next : Source)
  | call (id : Nat) (success failure : Source)

inductive Code where
  | stop
  | demand (q : Query) (p : Plan) (next : Code)
  | call (id : Nat) (success failure : Code)

def direct : Source → Code
  | .stop => .stop
  | .demand q next => .demand q .direct (direct next)
  | .call id yes no => .call id (direct yes) (direct no)

def compile (summaries : Nat → Bool → Summary) (facts : List Fact) (available : List Nat) :
    Source → Code
  | .stop => .stop
  | .demand q next => .demand q (infer facts available q) (compile summaries facts available next)
  | .call id yes no =>
    .call id
      (compile summaries (nextFacts (summaries id true) facts)
        (nextKnown (summaries id true) available) yes)
      (compile summaries (nextFacts (summaries id false) facts)
        (nextKnown (summaries id false) available) no)

variable {K E : Type}

structure Result (K E : Type) where
  world : World K
  values : List K
  events : List E

def run (impl : Nat → Implementation K E) : Code → World K → Result K E
  | .stop, s => ⟨s,[],[]⟩
  | .demand q p next, s =>
    let out := run impl next s
    {out with values := runPlan s.values q p :: out.values}
  | .call id yes no, s =>
    let out := impl id s
    let next := if out.success then run impl yes out.world else run impl no out.world
    {next with events := out.events ++ next.events}

/-- Legality at every reached source call; no assumption of atomic failure.
    Branch availability follows the declared summary, whose interpretation is
    separately required by Satisfies and Known. -/
def Legal (spec : Nat → Spec K) (impl : Nat → Implementation K E)
    (available : List Nat) : Source → World K → Prop
  | .stop, _ => True
  | .demand q next, s => Ready available q ∧ Legal spec impl available next s
  | .call id yes no, s =>
    (spec id).pre s ∧
      let out := impl id s
      if out.success then
        Legal spec impl (nextKnown ((spec id).post out.success) available) yes out.world
      else Legal spec impl (nextKnown ((spec id).post out.success) available) no out.world

def Enabled (spec : Nat → Spec K) (impl : Nat → Implementation K E) : Code → World K → Prop
  | .stop, _ => True
  | .demand q _ next, s => Ready s.known q ∧ Enabled spec impl next s
  | .call id yes no, s =>
    (spec id).pre s ∧
      let out := impl id s
      if out.success then Enabled spec impl yes out.world else Enabled spec impl no out.world

theorem compile_correct (spec : Nat → Spec K) (impl : Nat → Implementation K E)
    (laws : ∀ id, Satisfies (spec id) (impl id))
    (src : Source) (s : World K) (facts : List Fact) (available : List Nat)
    (valid : Valid s.values facts) (known : Known s available)
    (legal : Legal spec impl available src s) :
    run impl (compile (fun id => (spec id).post) facts available src) s =
      run impl (direct src) s := by
  induction src generalizing s facts available with
  | stop => rfl
  | demand q next ih =>
    simp only [compile,direct,run]
    rw [ih s facts available valid known legal.2,
      inferred_value s.values facts available q valid]
    rfl
  | call id yes no ihYes ihNo =>
    have transfer := call_transfer (spec id) (impl id) (laws id) s facts available legal.1 valid known
    cases h : (impl id s).success with
    | false =>
      have branch := legal.2
      simp only [h,Bool.false_eq_true,↓reduceIte] at branch transfer
      simp only [compile,direct,run,h,Bool.false_eq_true,↓reduceIte]
      rw [ihNo _ _ _ transfer.1 transfer.2 branch]
    | true =>
      have branch := legal.2
      simp only [h,↓reduceIte] at branch transfer
      simp only [compile,direct,run,h,↓reduceIte]
      rw [ihYes _ _ _ transfer.1 transfer.2 branch]

theorem compile_enabled (spec : Nat → Spec K) (impl : Nat → Implementation K E)
    (laws : ∀ id, Satisfies (spec id) (impl id))
    (src : Source) (s : World K) (facts : List Fact) (available : List Nat)
    (known : Known s available) (legal : Legal spec impl available src s) :
    Enabled spec impl (compile (fun id => (spec id).post) facts available src) s := by
  induction src generalizing s facts available with
  | stop => trivial
  | demand q next ih =>
    exact ⟨ready_actual s available q known legal.1, ih s facts available known legal.2⟩
  | call id yes no ihYes ihNo =>
    have postKnown := nextKnown_sound _ _ _ _ (laws id s legal.1) known
    refine ⟨legal.1,?_⟩
    cases h : (impl id s).success with
    | false =>
      have branch := legal.2
      simp only [h,Bool.false_eq_true,↓reduceIte] at branch postKnown ⊢
      exact ihNo _ _ _ postKnown branch
    | true =>
      have branch := legal.2
      simp only [h,↓reduceIte] at branch postKnown ⊢
      exact ihYes _ _ _ postKnown branch

end Zkc.Compiler.FactorProgram
