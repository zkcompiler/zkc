import Mathlib.Algebra.Ring.Defs
import Aesop

set_option autoImplicit false
namespace Zkc.Source.Expressions

/-- A total pure fragment, with branch guards included in its dependencies.
    Literals belong to fixed code, not a trusted channel for runtime secrets. -/
inductive Expr (A : Type) where
  | var : A → Expr A
  | lit : Nat → Expr A
  | add : Expr A → Expr A → Expr A
  | mul : Expr A → Expr A → Expr A
  | sub : Expr A → Expr A → Expr A
  | ifz : Expr A → Expr A → Expr A → Expr A
  deriving DecidableEq, Repr

variable {A B F : Type}

def Expr.deps : Expr A → List A
  | .var a => [a]
  | .lit _ => []
  | .add x y | .mul x y | .sub x y => x.deps ++ y.deps
  | .ifz c x y => c.deps ++ x.deps ++ y.deps

def Expr.eval [Ring F] [DecidableEq F] (env : A → F) : Expr A → F
  | .var a => env a
  | .lit n => n
  | .add x y => x.eval env + y.eval env
  | .mul x y => x.eval env * y.eval env
  | .sub x y => x.eval env - y.eval env
  | .ifz c x y => if c.eval env = 0 then x.eval env else y.eval env

def Expr.bind (env : A → Expr B) : Expr A → Expr B
  | .var a => env a
  | .lit n => .lit n
  | .add x y => .add (x.bind env) (y.bind env)
  | .mul x y => .mul (x.bind env) (y.bind env)
  | .sub x y => .sub (x.bind env) (y.bind env)
  | .ifz c x y => .ifz (c.bind env) (x.bind env) (y.bind env)

theorem eval_bind [Ring F] [DecidableEq F] (e : Expr A)
    (captures : A → Expr B) (env : B → F) :
    (e.bind captures).eval env = e.eval (fun a => (captures a).eval env) := by
  induction e <;> simp_all [Expr.bind,Expr.eval]

theorem eval_agreement [Ring F] [DecidableEq F] (e : Expr A) (s t : A → F)
    (agree : ∀ a ∈ e.deps, s a = t a) : e.eval s = e.eval t := by
  induction e with
  | var a => exact agree a (by simp [Expr.deps])
  | lit n => rfl
  | add x y ihx ihy | mul x y ihx ihy | sub x y ihx ihy =>
    have hx := ihx (fun a ha => agree a (by simp [Expr.deps,ha]))
    have hy := ihy (fun a ha => agree a (by simp [Expr.deps,ha]))
    simp [Expr.eval,hx,hy]
  | ifz c x y ihc ihx ihy =>
    have hc := ihc (fun a ha => agree a (by simp [Expr.deps,ha]))
    have hx := ihx (fun a ha => agree a (by simp [Expr.deps,ha]))
    have hy := ihy (fun a ha => agree a (by simp [Expr.deps,ha]))
    simp [Expr.eval,hc,hx,hy]

def Allowed (scope : List A) (e : Expr A) : Prop := ∀ a ∈ e.deps, a ∈ scope

def check [DecidableEq A] (scope : List A) (e : Expr A) : Bool :=
  e.deps.all (fun a => decide (a ∈ scope))

theorem check_iff [DecidableEq A] (scope : List A) (e : Expr A) :
    check scope e = true ↔ Allowed scope e := by
  simp [check,Allowed,List.all_eq_true]

theorem checked_agreement [DecidableEq A] [Ring F] [DecidableEq F]
    (scope : List A) (e : Expr A) (s t : A → F)
    (accepted : check scope e = true) (agree : ∀ a ∈ scope, s a = t a) :
    e.eval s = e.eval t :=
  eval_agreement e s t (fun a ha => agree a ((check_iff scope e).mp accepted a ha))

/-- Scope is enforced at every variable constructor, not a proof wrapper around
    a complete untyped program. Arithmetic and branching preserve the scope. -/
abbrev Scoped (scope : List A) := Expr {a : A // a ∈ scope}

def erase {scope : List A} (e : Scoped scope) : Expr A := e.bind (fun a => .var a.val)

theorem erase_allowed {scope : List A} (e : Scoped scope) : Allowed scope (erase e) := by
  induction e <;> simp_all [Allowed,erase,Expr.bind,Expr.deps] <;> aesop

def restrict (scope : List A) (e : Expr A) (h : Allowed scope e) : Scoped scope :=
  match e with
  | .var a => .var ⟨a,h a (by simp [Expr.deps])⟩
  | .lit n => .lit n
  | .add x y => .add (restrict scope x (fun a ha => h a (by simp [Expr.deps,ha])))
      (restrict scope y (fun a ha => h a (by simp [Expr.deps,ha])))
  | .mul x y => .mul (restrict scope x (fun a ha => h a (by simp [Expr.deps,ha])))
      (restrict scope y (fun a ha => h a (by simp [Expr.deps,ha])))
  | .sub x y => .sub (restrict scope x (fun a ha => h a (by simp [Expr.deps,ha])))
      (restrict scope y (fun a ha => h a (by simp [Expr.deps,ha])))
  | .ifz c x y => .ifz (restrict scope c (fun a ha => h a (by simp [Expr.deps,ha])))
      (restrict scope x (fun a ha => h a (by simp [Expr.deps,ha])))
      (restrict scope y (fun a ha => h a (by simp [Expr.deps,ha])))

theorem erase_restrict (scope : List A) (e : Expr A) (h : Allowed scope e) :
    erase (restrict scope e h) = e := by
  induction e <;> simp_all [restrict,erase,Expr.bind] <;> aesop

theorem checked_iff_intrinsic [DecidableEq A] (scope : List A) (e : Expr A) :
    check scope e = true ↔ ∃ t : Scoped scope, erase t = e := by
  constructor
  · intro h
    exact ⟨restrict scope e ((check_iff scope e).mp h),erase_restrict _ _ _⟩
  · rintro ⟨t,rfl⟩
    exact (check_iff scope _).mpr (erase_allowed t)

theorem erase_eval [Ring F] [DecidableEq F] {scope : List A}
    (e : Scoped scope) (env : A → F) :
    (erase e).eval env = e.eval (fun a => env a.val) := eval_bind e _ env

/-- Finite explicit closure. All captures are pure syntax; there is no host
    callback hidden inside the object-language term. -/
structure Closure (A : Type) where
  size : Nat
  body : Expr (Fin size)
  captures : Fin size → Expr A

def Closure.expand (c : Closure A) : Expr A := c.body.bind c.captures

theorem closure_agreement [DecidableEq A] [Ring F] [DecidableEq F]
    (scope : List A) (c : Closure A) (s t : A → F)
    (accepted : check scope c.expand = true) (agree : ∀ a ∈ scope, s a = t a) :
    c.body.eval (fun i => (c.captures i).eval s) =
      c.body.eval (fun i => (c.captures i).eval t) := by
  simpa [Closure.expand,eval_bind] using checked_agreement scope c.expand s t accepted agree

end Zkc.Source.Expressions
