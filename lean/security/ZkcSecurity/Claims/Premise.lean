module

public import ZkcSecurity.Claims.Model

@[expose] public section

/-! Closed premise schemas for request receipts. These are deliberately small:
no proposition, predicate, callback or target can be supplied as an argument.
The search game below concerns finite equality-query decision trees only; it
makes no claim about general efficient discrete-log algorithms. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims

/-- A finite equality-query algorithm. Leaves return scalar guesses; internal
nodes compare a scalar multiple of the supplied base with the supplied target. -/
inductive DLogSearch (F : Type) where
  | guess (scalar : F)
  | query (scalar : F) (yes no : DLogSearch F)

def DLogSearch.queries {F : Type} : DLogSearch F → Nat
  | .guess _ => 0
  | .query _ yes no => 1 + max yes.queries no.queries

def DLogSearch.run {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (base target : G) : DLogSearch F → F
  | .guess scalar => scalar
  | .query scalar yes no => if scalar • base = target then yes.run base target else no.run base target

/-- Worst-case search hardness at the request's fixed query limit. Algorithms
are chosen before the base and secret; the schema cannot assume target truth,
a local probability estimate or an implementation correspondence. -/
def DLogSearchHard {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (limit : Nat) : Prop :=
  ¬ ∃ algorithm : DLogSearch F, algorithm.queries ≤ limit ∧
    ∀ (base : G), base ≠ 0 → ∀ secret : F, algorithm.run base (secret • base) = secret

/-- The zero-query condition is satisfiable on nontrivial groups: a constant
leaf cannot recover both zero and one. This is a search-game control, not a
computational lower bound for a richer algorithm model. -/
theorem dlogSearchHard_zero {F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq G] [Nontrivial G] : DLogSearchHard (F := F) (G := G) 0 := by
  rintro ⟨algorithm, bounded, solves⟩
  cases algorithm with
  | guess scalar =>
    obtain ⟨base, nonzero⟩ := exists_ne (0 : G)
    have zero : scalar = 0 := solves base nonzero 0
    have one : scalar = 1 := solves base nonzero 1
    exact zero_ne_one (zero.symm.trans one)
  | query scalar yes no => simp [DLogSearch.queries] at bounded

/-- A model law on the actual selected scalar and group carriers. -/
def FaithfulScalarAction (F G : Type) [Field F] [AddCommGroup G] [Module F G] : Prop :=
  ∀ base : G, base ≠ 0 → Function.Injective (fun scalar : F => scalar • base)

inductive PremiseKey where
  | faithfulScalarAction | dlogSearch
  deriving DecidableEq, Repr

def PremiseKey.identifier : PremiseKey → Identifier
  | .faithfulScalarAction => ⟨"assumptions.faithful_scalar_action", 0⟩
  | .dlogSearch => ⟨"assumptions.dlog_search", 0⟩

/-- Authorization has a closed wire shape. Arguments are derived from the
selected carriers and model, never supplied by the author as Lean expressions. -/
@[simp] def premiseKeys (application : Wire.Application) : Except ResolutionError (List PremiseKey) := do
  match (application.arguments.find? (fun pair => pair.1 == some "assumptions")).map Prod.snd with
  | none => return []
  | some (.list entries) =>
    let keys ← entries.mapM fun expression => match expression with
      | .application "assumptions.faithful_scalar_action" (some 0) [] => pure .faithfulScalarAction
      | .application "assumptions.dlog_search" (some 0) [] => pure .dlogSearch
      | _ => throw (.schema "unsupported assumption authorization or arguments")
    if keys.Nodup then return keys else throw (.schema "duplicate assumption authorization")
  | _ => throw (.schema "assumptions must be a list of closed versioned schemas")

/-- Separate recognition from permission. Being a registered schema does not
make it available to a request that has not explicitly selected it. -/
def premiseAuthorized (application : Wire.Application) (key : PremiseKey) : Bool :=
  match premiseKeys application with
  | .ok keys => key ∈ keys
  | .error _ => false

end ZkcSecurity.Claims
