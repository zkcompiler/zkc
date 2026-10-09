import ZkcClean.Export
import Zkc.Relation.AIR

/-! Import of an exported artifact into the independent zkc finite AIR, and the
expression translation theorem.

Import admission checks the field presentation size, that every serialized
constant is canonical and that every column is below the declared width. It
decodes constants with Clean's `FiniteField.fromNat`, which is `Nat.cast` on
prime fields `F p`. Every column becomes a current-row read (`offset = 0`), so
`evaluateAt` is defined on every row. There are no public inputs.
-/

set_option autoImplicit false

namespace ZkcClean

open Zkc.Relation

variable {F : Type} [FiniteField F]

def Term.decode (F : Type) [FiniteField F] (width : Nat) : Term → Option (AIR.Expr F 0 width)
  | .constant value =>
      if value < FiniteField.size F then some (.constant (FiniteField.fromNat value)) else none
  | .column index => if h : index < width then some (.read 0 ⟨index, h⟩) else none
  | .add left right =>
      match left.decode F width, right.decode F width with
      | some l, some r => some (.add l r)
      | _, _ => none
  | .mul left right =>
      match left.decode F width, right.decode F width with
      | some l, some r => some (.mul l r)
      | _, _ => none

/-- Every imported assertion applies to every row. -/
def decodeAssertions (F : Type) [FiniteField F] (width : Nat) :
    List Term → Option (List (AIR.Constraint F 0 width))
  | [] => some []
  | t :: ts =>
      match t.decode F width, decodeAssertions F width ts with
      | some e, some cs => some (⟨.every, e⟩ :: cs)
      | _, _ => none

/-- Import admission of an artifact for the field `F`. -/
def Artifact.decode (F : Type) [FiniteField F] (artifact : Artifact) :
    Option (List (AIR.Constraint F 0 artifact.width)) :=
  if artifact.fieldSize = FiniteField.size F then
    decodeAssertions F artifact.width artifact.assertions
  else none

/-- The clean-row environment of a current-row read function. -/
abbrev rowEnvironment {width : Nat} (read : Fin width → F) (data : ProverData F) : Environment F :=
  Environment.fromArray (Array.ofFn read) data

theorem decode_maxOffset {width : Nat} :
    ∀ {t : Term} {x : AIR.Expr F 0 width}, t.decode F width = some x → x.maxOffset = 0
  | .constant value, x, h => by
      unfold Term.decode at h
      split at h
      · cases h; rfl
      · cases h
  | .column index, x, h => by
      unfold Term.decode at h
      split at h
      · cases h; rfl
      · cases h
  | .add left right, x, h => by
      unfold Term.decode at h
      split at h
      · rename_i l r hl hr
        cases h
        simp [AIR.Expr.maxOffset, decode_maxOffset hl, decode_maxOffset hr]
      · cases h
  | .mul left right, x, h => by
      unfold Term.decode at h
      split at h
      · rename_i l r hl hr
        cases h
        simp [AIR.Expr.maxOffset, decode_maxOffset hl, decode_maxOffset hr]
      · cases h

/-- An imported encoding evaluates exactly as Clean evaluates the source
expression on the row read at offset zero, for every public statement (there are
none), read function and `Environment.data`. -/
theorem eval_decode {width : Nat} :
    ∀ {e : Expression F} {x : AIR.Expr F 0 width}, (encode e).decode F width = some x →
      ∀ (statement : Fin 0 → F) (read : Nat × Fin width → F) (data : ProverData F),
        x.eval statement read =
          Expression.eval (rowEnvironment (fun column => read (0, column)) data) e
  | .var v, x, h, statement, read, data => by
      simp only [encode, Term.decode] at h
      split at h
      · rename_i hv
        cases h
        simp [AIR.Expr.eval, Expression.eval, hv]
      · cases h
  | .const c, x, h, statement, read, data => by
      simp only [encode, Term.decode, if_pos (FiniteField.val_lt c)] at h
      cases h
      simp [AIR.Expr.eval, Expression.eval, FiniteField.fromNat_val]
  | .add left right, x, h, statement, read, data => by
      simp only [encode, Term.decode] at h
      split at h
      · rename_i l r hl hr
        cases h
        simp only [AIR.Expr.eval, Expression.eval]
        rw [eval_decode hl statement read data, eval_decode hr statement read data]
      · cases h
  | .mul left right, x, h, statement, read, data => by
      simp only [encode, Term.decode] at h
      split at h
      · rename_i l r hl hr
        cases h
        simp only [AIR.Expr.eval, Expression.eval]
        rw [eval_decode hl statement read data, eval_decode hr statement read data]
      · cases h

/-- Import admission succeeds on every expression whose variables are in range. -/
theorem decode_encode {width : Nat} :
    ∀ {e : Expression F}, Bounded width e → ∃ x, (encode e).decode F width = some x
  | .var v, h => ⟨.read 0 ⟨v.index, h⟩, by simp [encode, Term.decode, show v.index < width from h]⟩
  | .const c, _ => ⟨.constant c, by
      simp [encode, Term.decode, FiniteField.val_lt c, FiniteField.fromNat_val]⟩
  | .add left right, h => by
      obtain ⟨l, hl⟩ := decode_encode h.1
      obtain ⟨r, hr⟩ := decode_encode h.2
      exact ⟨.add l r, by simp [encode, Term.decode, hl, hr]⟩
  | .mul left right, h => by
      obtain ⟨l, hl⟩ := decode_encode h.1
      obtain ⟨r, hr⟩ := decode_encode h.2
      exact ⟨.mul l r, by simp [encode, Term.decode, hl, hr]⟩

/-- Expression translation for a trace row. -/
theorem evaluateAt_decode {width height : Nat} {e : Expression F} {x : AIR.Expr F 0 width}
    (h : (encode e).decode F width = some x) (statement : Fin 0 → F)
    (trace : Fin height → Fin width → F) (row : Fin height) (data : ProverData F) :
    x.evaluateAt statement trace row =
      some (Expression.eval (rowEnvironment (trace row) data) e) := by
  have fits : row.val + x.maxOffset < height := by simp [decode_maxOffset h]
  have reads : (fun column => AIR.Expr.traceRead trace row (0, column)) = trace row := by
    funext column
    simp [AIR.Expr.traceRead]
  simp only [AIR.Expr.evaluateAt, if_pos fits]
  rw [eval_decode h statement _ data]
  simp only [reads]

/-- Obligation (1): a successful export of `e` imports to a zkc expression whose
evaluation equals Clean's `Expression.eval` on the corresponding row
environment. -/
theorem export_expression {width : Nat} {e : Expression F} {t : Term}
    (exported : exportExpression width e = .ok t) :
    ∃ x, t.decode F width = some x ∧
      ∀ (statement : Fin 0 → F) (read : Nat × Fin width → F) (data : ProverData F),
        x.eval statement read =
          Expression.eval (rowEnvironment (fun column => read (0, column)) data) e := by
  obtain ⟨bounded, rfl⟩ := exportExpression_ok exported
  obtain ⟨x, hx⟩ := decode_encode bounded
  exact ⟨x, hx, eval_decode hx⟩

end ZkcClean
