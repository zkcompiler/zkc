import Zkc.Relation.AIR

/-! Transport a finite AIR through an injective ring homomorphism. In
particular, checking a base-field trace in an extension preserves its relation.
The statement concerns embedded traces, not arbitrary extension-valued witnesses.
-/

set_option autoImplicit false

namespace Zkc.Relation.AIR

variable {F G : Type} {p c height : Nat}

def Expr.map (f : F → G) : Expr F p c → Expr G p c
  | .constant a => .constant (f a)
  | .publicInput i => .publicInput i
  | .read offset column => .read offset column
  | .add a b => .add (a.map f) (b.map f)
  | .mul a b => .mul (a.map f) (b.map f)

@[simp] theorem Expr.map_reads (e : Expr F p c) (f : F → G) :
    (e.map f).reads = e.reads := by
  induction e <;> simp [map, reads, *]

@[simp] theorem Expr.map_maxOffset (e : Expr F p c) (f : F → G) :
    (e.map f).maxOffset = e.maxOffset := by
  induction e <;> simp [map, maxOffset, *]

@[simp] theorem Expr.map_degree (e : Expr F p c) (f : F → G) :
    (e.map f).degree = e.degree := by
  induction e <;> simp [map, degree, *]

variable [CommRing F] [CommRing G]

theorem Expr.map_eval (e : Expr F p c) (f : F →+* G)
    (statement : Fin p → F) (read : Nat × Fin c → F) :
    (e.map f).eval (fun i => f (statement i)) (fun r => f (read r)) =
      f (e.eval statement read) := by
  induction e <;> simp [map, eval, *]

theorem Expr.map_evaluateAt (e : Expr F p c) (f : F →+* G)
    (statement : Fin p → F) (trace : Fin height → Fin c → F) (row : Fin height) :
    (e.map f).evaluateAt (fun i => f (statement i))
      (fun r i => f (trace r i)) row = (e.evaluateAt statement trace row).map f := by
  have reads : traceRead (fun r i => f (trace r i)) row =
      fun r => f (traceRead trace row r) := by
    funext r
    simp only [traceRead]
    split <;> simp
  simp only [evaluateAt, map_maxOffset]
  split <;> simp [reads, map_eval]

def Constraint.map (constraint : Constraint F p c) (f : F → G) : Constraint G p c :=
  ⟨constraint.scope, constraint.expression.map f⟩

/-- Extension checking is equivalent for the *same embedded witness*. This does
not allow a prover to replace a base-field trace with any extension-field trace.
-/
theorem Constraint.map_holds_iff (constraint : Constraint F p c) (f : F →+* G)
    (injective : Function.Injective f) (statement : Fin p → F)
    (trace : Fin height → Fin c → F) :
    (constraint.map f).Holds (fun i => f (statement i)) (fun r i => f (trace r i)) ↔
      constraint.Holds statement trace := by
  simp only [Holds, Constraint.map, Expr.map_evaluateAt]
  constructor
  · intro holds row active
    have h := holds row active
    cases hvalue : constraint.expression.evaluateAt statement trace row with
    | none => simp [hvalue] at h
    | some value =>
        have hz : f value = f 0 := by simpa [hvalue] using h
        simp [injective hz]
  · intro holds row active
    simp [holds row active]

end Zkc.Relation.AIR
