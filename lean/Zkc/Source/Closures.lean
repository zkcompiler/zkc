import Zkc.Source.Inputs
import Zkc.Source.Expressions
import Zkc.Semantics.Execution

set_option autoImplicit false

namespace PIR.Source
open Zkc.Source.Expressions Zkc.Source.Availability

variable {F Role H : Type}

/-- Check every declared capture, including captures not used by the body.
    Expanding the body alone would erase those input obligations. -/
def captureDeps (c : Closure Nat) : List Nat :=
  (List.ofFn c.captures).flatMap Expr.deps

theorem capture_mem (c : Closure Nat) (i : Fin c.size) (j : Nat)
    (used : j ∈ (c.captures i).deps) : j ∈ captureDeps c :=
  List.mem_flatMap.mpr ⟨c.captures i, List.mem_ofFn.mpr ⟨i, rfl⟩, used⟩

/-- An immutable mathematical code/value pair, not an authorization token.
    Invocation has no access to the environment that supplied the captures. -/
structure Bound (n : Nat) (F : Type) where
  body : Expr (Fin n)
  values : Fin n → F

variable [Ring F] [DecidableEq F]

def capture (c : Closure Nat) (s : Env F) : Bound c.size F :=
  ⟨c.body, fun i => (c.captures i).eval (total s)⟩

def issue (scope : List Nat) (s : Env F) (c : Closure Nat) : Option (Bound c.size F) :=
  if ready scope s (captureDeps c) then some (capture c s) else none

def Bound.value {n : Nat} (b : Bound n F) : F := b.body.eval b.values

theorem capture_agreement (c : Closure Nat) (s t : Env F)
    (agree : ∀ j ∈ captureDeps c, s j = t j) : capture c s = capture c t := by
  unfold capture
  congr 1
  funext i
  apply eval_agreement
  intro j used
  exact congrArg (fun x : Option F => x.getD 0) (agree j (capture_mem c i j used))

theorem issue_agreement (scope : List Nat) (s t : Env F) (c : Closure Nat)
    (agree : Agree scope s t) : issue scope s c = issue scope t c := by
  have hr := ready_agreement scope s t (captureDeps c) agree
  by_cases hs : ready scope s (captureDeps c) = true
  · have hc := capture_agreement c s t (fun j used =>
      agree j (((ready_iff scope s (captureDeps c)).mp hs j used).1))
    simp [issue, ← hr, hs, hc]
  · simp [issue, ← hr, hs]

theorem issued_reads (scope : List Nat) (s : Env F) (c : Closure Nat)
    (b : Bound c.size F) (accepted : issue scope s c = some b)
    (j : Nat) (used : j ∈ captureDeps c) : j ∈ scope ∧ ∃ value, s j = some value := by
  unfold issue at accepted
  split at accepted
  · rename_i hr
    have hj := (ready_iff scope s (captureDeps c)).mp hr j used
    exact ⟨hj.1, Option.isSome_iff_exists.mp hj.2⟩
  · contradiction

/-- Successful admission makes evaluation independent of the default used to
    totalize unavailable slots. It still does not admit an unavailable read. -/
theorem capture_default_irrelevant (scope : List Nat) (s : Env F) (c : Closure Nat)
    (b : Bound c.size F) (accepted : issue scope s c = some b)
    (fallback : F) (i : Fin c.size) :
    (c.captures i).eval (total s) =
      (c.captures i).eval (fun j => (s j).getD fallback) := by
  apply eval_agreement
  intro j hj
  obtain ⟨_, value, present⟩ := issued_reads scope s c b accepted j (capture_mem c i j hj)
  simp [total, present]

theorem issued_value (scope : List Nat) (s : Env F) (c : Closure Nat)
    (b : Bound c.size F) (accepted : issue scope s c = some b) :
    b.value = c.expand.eval (total s) := by
  unfold issue at accepted
  split at accepted
  · have hb : capture c s = b := Option.some.inj accepted
    rw [← hb]
    exact (eval_bind c.body c.captures (total s)).symm
  · contradiction

variable [DecidableEq Role]

def admit (actor : Role) (bindings : List (SourceView.Slot Role))
    (w : SourceView.World Role F H) (c : Closure Nat) : Option (Bound c.size F) :=
  issue (List.range bindings.length) (SourceView.env actor bindings w) c

theorem admission_same_view (actor : Role) (bindings : List (SourceView.Slot Role))
    (w v : SourceView.World Role F H) (c : Closure Nat)
    (agree : SourceView.SameView actor w v) :
    admit actor bindings w c = admit actor bindings v c := by
  apply issue_agreement
  intro j _
  simp only [SourceView.env]
  cases bindings[j]? with
  | none => rfl
  | some slot => exact SourceView.read_agrees actor w v agree slot

theorem admitted_reads (actor : Role) (bindings : List (SourceView.Slot Role))
    (w : SourceView.World Role F H) (c : Closure Nat) (b : Bound c.size F)
    (accepted : admit actor bindings w c = some b)
    (j : Nat) (used : j ∈ captureDeps c) :
    ∃ slot value, bindings[j]? = some slot ∧ SourceView.permitted actor slot ∧
      SourceView.read actor w slot = some value := by
  obtain ⟨_, value, present⟩ := issued_reads _ _ c b accepted j used
  simp only [SourceView.env] at present
  cases hs : bindings[j]? with
  | none => simp [hs] at present
  | some slot =>
    simp only [hs, Option.bind_some] at present
    exact ⟨slot, value, rfl, SourceView.read_permitted actor w slot value present, present⟩

end PIR.Source
