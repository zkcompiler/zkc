import Zkc.Source.RegionTotality
import Zkc.Source.RegionInterpretation

/-! Positive and negative controls for generic laws, independent of protocol names. -/
set_option autoImplicit false
namespace Tests.RegionLaws
open Zkc.Source PIR

inductive Operation where
  | constant (value : Nat)
  | add | run | inspect | ask
  | choose (condition : Bool)

abbrev dialect : Dialect where
  Ty := Unit
  Op := Operation
  arguments
    | .add => [(), ()]
    | .choose _ => [()]
    | _ => []
  results _ := [()]
  regions
    | .run | .inspect => [([], [()])]
    | .choose _ => [([()], [()]), ([()], [()])]
    | _ => []

abbrev calls : Signature := ⟨Unit, fun _ => Nat⟩
abbrev closed : Signature := ⟨Empty, Empty.elim⟩
abbrev value (_ : Unit) := Nat

def singleton (n : Nat) : Values value [()] := .cons n .nil

/-- Both meanings deliberately inspect the callback process shape. -/
def observed {I : Signature} (process : Proc I (Values value [()])) : Proc I (Values value [()]) :=
  match process with
  | .call _ _ => .done (singleton 1)
  | _ => .done (singleton 0)

def meaning : RegionMeaning dialect calls where
  Value := value
  operation
    | .constant n, .nil, .nil => .done (singleton n)
    | .add, .cons x (.cons y .nil), .nil => .done (singleton (x + y))
    | .run, .nil, .cons body .nil => body .nil
    | .inspect, .nil, .cons body .nil => observed (body .nil)
    | .ask, .nil, .nil => .call () fun n => .done (singleton n)
    | .choose condition, args, .cons yes (.cons no .nil) =>
        if condition then yes args else no args

def lower : OperationInterpretation calls closed := fun _ => .done 7

def target : RegionMeaning dialect closed where
  Value := value
  operation
    | .constant n, .nil, .nil => .done (singleton n)
    | .add, .cons x (.cons y .nil), .nil => .done (singleton (x + y))
    | .run, .nil, .cons body .nil => body .nil
    | .inspect, .nil, .cons body .nil => observed (body .nil)
    | .ask, .nil, .nil => .done (singleton 7)
    | .choose condition, args, .cons yes (.cons no .nil) =>
        if condition then yes args else no args

def ask : Region dialect [] [()] := .letOp .ask .nil .nil (.ret (.cons .here .nil))
def inspected : Region dialect [] [()] :=
  .letOp .inspect .nil (.cons ask .nil) (.ret (.cons .here .nil))

-- Handler translation changes the inspected callback shape. An unconditional
-- higher-order translation theorem would identify these different results.
example : (inspected.denote meaning (fun reference => nomatch reference)).interpret lower =
    .done (singleton 1) := rfl
example : inspected.denote target (fun reference => nomatch reference) = .done (singleton 0) := rfl
example : (inspected.denote meaning (fun reference => nomatch reference)).interpret lower ≠
    inspected.denote target (fun reference => nomatch reference) := by
  intro contradiction
  cases contradiction

example : meaning.TotalOperation (.constant 9) := by
  intro args bodies _
  cases args
  cases bodies
  exact ⟨_, rfl⟩

example : meaning.TotalOperation .run := by
  intro args bodies total
  cases args
  cases bodies with
  | cons body tail =>
    cases tail
    exact total _ .here .nil

-- Even a leaf operation is not pure merely because it has no region bodies.
example : ¬ meaning.TotalOperation .ask := by
  intro total
  obtain ⟨result, impossible⟩ := total .nil .nil (fun _ reference => nomatch reference)
  cases impossible

/-- A pure term uses the same carrier and receives a totality proof. -/
def addition : Region dialect [(), ()] [()] :=
  .letOp .add (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))

example : addition.Total meaning := by
  refine ⟨?_, trivial, trivial⟩
  intro args bodies _
  cases args with
  | cons x rest => cases rest with
    | cons y tail =>
      cases tail
      cases bodies
      exact ⟨_, rfl⟩

example (env : Environment value [(), ()]) (total : addition.Total meaning) :
    Returns (addition.denote meaning env) := Region.returns_of_total meaning addition total env

-- A concrete operation result can be substituted even in an arbitrary suffix.
example {Γ out} (next : Region dialect (() :: Γ) out) (env : Environment value Γ) :
    (Region.letOp (dialect := dialect) (.constant 9) .nil .nil next).denote meaning env =
      next.denote meaning (env.prepend (singleton 9)) :=
  Region.letOp_return meaning (.constant 9) .nil .nil next env (singleton 9) rfl

/-- Each branch has closed explicit inputs; the suffix is stored once. -/
def branch {Γ : List Unit} (input : Var Γ ()) : Region dialect Γ [()] :=
  .letOp (.choose true) (.cons input .nil)
    (.cons (.ret (.cons .here .nil)) (.cons (.ret (.cons .here .nil)) .nil))
    (.ret (.cons .here .nil))

def chain {Γ : List Unit} (input : Var Γ ()) : Nat → Region dialect Γ [()]
  | 0 => .ret (.cons input .nil)
  | n + 1 => .bind (branch input) (chain .here n)

-- A universal structural bound, rather than a small timing measurement.
example {Γ : List Unit} (input : Var Γ ()) (n : Nat) :
    (chain input n).nodeCount = 5 * n + 1 := by
  induction n generalizing Γ with
  | zero => rfl
  | succ n ih =>
    simp only [chain, branch, Region.nodeCount, Regions.nodeCount, ih]
    omega

end Tests.RegionLaws
