import Zkc.Source.RegionBounds

/-! Runtime-selected local control is a family of existing finite typed regions.
Bounds are admitted before selecting a natural count. No unbounded source
constructor or native refinement premise is introduced. The executable adapters
instantiate these combinators after independent raw formation. -/

set_option autoImplicit false
namespace Zkc.Source.FiniteControl

structure Bounds where
  lower : Nat
  upper : Nat
  ceiling : Nat
  lower_le : lower ≤ ceiling
  upper_le : upper ≤ ceiling

def Bounds.admit (lower upper ceiling : Nat) : Option Bounds :=
  if hLower : lower ≤ ceiling then
    if hUpper : upper ≤ ceiling then some ⟨lower, upper, ceiling, hLower, hUpper⟩ else none
  else none

def Bounds.count (bounds : Bounds) : Nat := bounds.upper - bounds.lower

theorem Bounds.count_le (bounds : Bounds) : bounds.count ≤ bounds.ceiling :=
  Nat.le_trans (Nat.sub_le _ _) bounds.upper_le

theorem Bounds.zero (bounds : Bounds) (h : bounds.upper ≤ bounds.lower) : bounds.count = 0 :=
  Nat.sub_eq_zero_of_le h

theorem Bounds.upper_eq (bounds : Bounds) (h : bounds.lower ≤ bounds.upper) :
    bounds.upper = bounds.lower + bounds.count := by
  simp only [Bounds.count]
  omega

theorem Bounds.index_lt (bounds : Bounds) (i : Nat) (h : i < bounds.count) :
    bounds.lower + i < bounds.upper := by
  have := bounds.lower_le
  have := bounds.upper_le
  simp only [Bounds.count] at h
  omega

/-- A selected finite count reuses the existing iterate denotation, including
its complete early-stop behavior and the shared continuation. -/
theorem selected_iterate {language : Language} {interface : PIR.Signature}
    (meaning : Interpretation language interface) {Γ : List language.Ty} {acc ty : language.Ty}
    (select : Environment meaning.Value Γ → Bounds) (env : Environment meaning.Value Γ)
    (initial : Var Γ acc) (body : Region language (acc :: Γ) acc)
    (next : Region language (acc :: Γ) ty) :
    (Region.iterate (select env).count initial body next).denote meaning env =
      (PIR.repeatN (select env).count (fun value => body.denote meaning (env.push value))
        (env initial)).bind (fun value => next.denote meaning (env.push value)) := rfl

theorem selected_iterate_zero {language : Language} {interface : PIR.Signature}
    (meaning : Interpretation language interface) {Γ : List language.Ty} {acc ty : language.Ty}
    (bounds : Bounds) (h : bounds.upper ≤ bounds.lower) (env : Environment meaning.Value Γ)
    (initial : Var Γ acc) (body : Region language (acc :: Γ) acc)
    (next : Region language (acc :: Γ) ty) :
    (Region.iterate bounds.count initial body next).denote meaning env =
      next.denote meaning (env.push (env initial)) := by
  rw [bounds.zero h]
  rfl

/-- Input selection inherits a uniform finite semantic call bound. This counts
interface calls, independently of executable storage/instruction admission. -/
theorem selected_iterate_within {language : Language} {interface : PIR.Signature}
    (meaning : Interpretation language interface) (operationBound : language.Op → Nat)
    (operations : ∀ op args, PIR.Within (operationBound op) (meaning.operation op args))
    {Γ : List language.Ty} {acc ty : language.Ty}
    (bounds : Bounds) (env : Environment meaning.Value Γ) (initial : Var Γ acc)
    (body : Region language (acc :: Γ) acc) (next : Region language (acc :: Γ) ty) :
    PIR.Within (bounds.ceiling * body.callBound operationBound + next.callBound operationBound)
      ((Region.iterate bounds.count initial body next).denote meaning env) := by
  apply PIR.Boundary.within_mono _ _ _ _
    ((Region.iterate bounds.count initial body next).denote_within meaning operationBound operations env)
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ bounds.count_le) _

/-- Execute finite semantic requests in an outer monad. A failure in a stateful
ExceptT handler follows that handler's state-retention policy. -/
def execute {I : PIR.Signature} {m : Type → Type} [Monad m]
    (operation : (op : I.Op) → m (I.Reply op))
    (stop : {α : Type} → PIR.Stop → m α) {α : Type} : PIR.Proc I α → m α
  | .done value => pure value
  | .halt reason => stop reason
  | .call op next => do execute operation stop (next (← operation op))

namespace Iteration
abbrev language : Language where
  Ty := Unit
  Op := Unit
  arguments _ := [()]
  result _ := ()
  condition := ()

abbrev interface (α : Type) : PIR.Signature where
  Op := α
  Reply _ := α

abbrev meaning (α : Type) : Interpretation language (interface α) where
  Value _ := α
  condition _ := false
  operation _ values := .call (values.get .here) .done

def region (count : Nat) : Region language [()] () :=
  .iterate count .here (.letOp () (.cons .here .nil) (.ret .here)) (.ret .here)

def proc {α : Type} (count : Nat) (initial : α) : PIR.Proc (interface α) α :=
  (region count).denote (meaning α) (Values.cons initial .nil).get

theorem proc_eq_repeat {α : Type} (count : Nat) (initial : α) :
    proc count initial = PIR.repeatN count (fun a => .call a .done) initial := by
  change (PIR.repeatN (I := interface α) count (fun a => .call a .done) initial).bind PIR.Proc.done = _
  exact PIR.Proc.bind_done _

end Iteration

namespace Selection
inductive Ty where | condition | result
abbrev language : Language where
  Ty := Ty
  Op := Bool
  arguments _ := []
  result _ := .result
  condition := .condition
abbrev interface (α : Type) : PIR.Signature where
  Op := Bool
  Reply _ := α
abbrev value (α : Type) : Ty → Type | .condition => Bool | .result => α
abbrev meaning (α : Type) : Interpretation language (interface α) where
  Value := value α
  condition b := b
  operation b _ := .call b .done

def region : Region language [.condition] .result :=
  .branch .here (.letOp true .nil (.ret .here)) (.letOp false .nil (.ret .here))

def proc {α : Type} (selected : Bool) : PIR.Proc (interface α) α :=
  region.denote (meaning α) (Values.cons selected .nil).get

theorem proc_eq {α : Type} (selected : Bool) :
    proc (α := α) selected = .call selected .done := by
  cases selected <;> rfl
end Selection

def iterateM {m : Type → Type} [Monad m] {α : Type}
    (stop : {β : Type} → PIR.Stop → m β) (count : Nat) (initial : α) (step : α → m α) : m α :=
  execute (m := m) (I := Iteration.interface α) step (fun {α} why => stop (β := α) why) (Iteration.proc count initial)

def branchM {m : Type → Type} [Monad m] {α : Type}
    (stop : {β : Type} → PIR.Stop → m β) (selected : Bool) (yes no : Unit → m α) : m α :=
  execute (m := m) (I := Selection.interface α) (fun b => if b then yes () else no ())
    (fun {α} why => stop (β := α) why) (Selection.proc selected)

end Zkc.Source.FiniteControl
