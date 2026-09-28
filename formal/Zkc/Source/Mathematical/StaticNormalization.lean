import Zkc.Source.Mathematical.StaticPolynomial

/-! Bounded static normalization with a semantic certificate.

Natural addition/multiplication use sparse polynomials; a nonconstant power of
two becomes an atom whose exponent is normalized. Successful equality carries
a proof for every natural assignment. Work refusal grants no inequality fact.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Static

inductive NormalizationError where
  | resource | overflow
  deriving DecidableEq, Repr

private structure Atom (arity : Nat) where
  key : String
  expression : Expression arity
  deriving DecidableEq

private abbrev Terms (arity : Nat) := Polynomial.Terms (Atom arity)
variable {arity : Nat}

private def atomValue (parameters : Fin arity → Nat) (atom : Atom arity) := atom.expression.eval parameters
private def atomLess (a b : Atom arity) := decide (a.key < b.key)
private def monomialLess (a b : List (Atom arity)) := decide (List.Lex (fun a b => a.key < b.key) a b)

private def monomialExpression : List (Atom arity) → Expression arity
  | [] => .literal ⟨1, by decide⟩
  | [atom] => atom.expression
  | atom :: next :: rest => .multiply atom.expression (monomialExpression (next :: rest))

private theorem monomialExpression_value (atoms : List (Atom arity)) (parameters : Fin arity → Nat) :
    (monomialExpression atoms).eval parameters = Polynomial.monomialValue (atomValue parameters) atoms := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      cases rest <;> simp_all [monomialExpression, Expression.eval, Polynomial.monomialValue, atomValue]

private def termExpression (coefficient : Word) (atoms : List (Atom arity)) : Expression arity :=
  match atoms with
  | [] => .literal coefficient
  | _ :: _ => if coefficient.val = 1 then monomialExpression atoms
      else .multiply (.literal coefficient) (monomialExpression atoms)

private theorem termExpression_value (coefficient : Word) (atoms : List (Atom arity)) (parameters : Fin arity → Nat) :
    (termExpression coefficient atoms).eval parameters = coefficient.val * Polynomial.monomialValue (atomValue parameters) atoms := by
  cases atoms with
  | nil => simp [termExpression, Expression.eval, Polynomial.monomialValue]
  | cons first rest =>
      by_cases one : coefficient.val = 1 <;>
        simp [termExpression, one, Expression.eval, monomialExpression_value]

private def reify : (terms : Terms arity) → Except NormalizationError
    { expression : Expression arity // ∀ parameters,
      expression.eval parameters = Polynomial.evaluate (atomValue parameters) terms }
  | [] => return ⟨.literal ⟨0, by decide⟩, fun _ => rfl⟩
  | (coefficient, atoms) :: rest => do
      if bound : coefficient < limit then
        let term := termExpression ⟨coefficient, bound⟩ atoms
        match hrest : rest with
        | [] => return ⟨term, fun parameters => by simp [term, termExpression_value, Polynomial.evaluate, hrest]⟩
        | next :: rest =>
            let tail ← reify (next :: rest)
            return ⟨.add term tail.val,
              fun parameters => by simp [term, Expression.eval, termExpression_value, tail.property,
                Polynomial.evaluate, hrest]⟩
      else throw (if atoms.isEmpty then .overflow else .resource)

private def key (terms : Terms arity) : String :=
  String.join (terms.map fun (coefficient, atoms) => toString coefficient ++ "[" ++
    String.join (atoms.map fun atom => toString atom.key.utf8ByteSize ++ ":" ++ atom.key) ++ "]")

private def cost (terms : Terms arity) : Nat :=
  terms.foldl (fun total term => total + 1 + term.2.foldl (fun n atom => n + 1 + atom.key.utf8ByteSize) 0) 0

private def consume (amount : Nat) : StateT Nat (Except NormalizationError) Unit := do
  let available ← get
  if amount > available then throw .resource
  set (available - amount)

private structure PolynomialCertificate (expression : Expression arity) where
  terms : Terms arity
  sound : ∀ parameters, Polynomial.evaluate (atomValue parameters) terms = expression.eval parameters

private def constant (terms : Terms arity) : Option
    { value : Nat // ∀ parameters, Polynomial.evaluate (atomValue parameters) terms = value } :=
  match terms with
  | [] => some ⟨0, fun _ => rfl⟩
  | [(n, [])] => some ⟨n, fun _ => by simp [Polynomial.evaluate, Polynomial.monomialValue]⟩
  | _ => none

private def normalized : (expression : Expression arity) →
    StateT Nat (Except NormalizationError) (PolynomialCertificate expression)
  | .literal value => do
      consume 1
      if zero : value.val = 0 then
        return ⟨[], fun _ => by simp [Polynomial.evaluate, Expression.eval, zero]⟩
      else return ⟨[(value.val, [])], fun _ => by simp [Polynomial.evaluate, Polynomial.monomialValue, Expression.eval]⟩
  | .parameter index => do
      consume 1
      return ⟨[(1, [⟨"p" ++ toString index.val, .parameter index⟩])],
        fun _ => by simp [Polynomial.evaluate, Polynomial.monomialValue, atomValue, Expression.eval]⟩
  | .add left right => do
      let a ← normalized left
      let b ← normalized right
      consume ((1 + cost a.terms + cost b.terms) ^ 2)
      let terms := Polynomial.add monomialLess a.terms b.terms
      let _ ← reify terms
      return ⟨terms, fun parameters => by
        simpa [terms, Expression.eval, a.sound, b.sound] using
          Polynomial.add_value monomialLess (atomValue parameters) a.terms b.terms⟩
  | .multiply left right => do
      let a ← normalized left
      let b ← normalized right
      -- Charge the worst intermediate insertion/copy work before distributing.
      -- This conservative consumer budget may refuse earlier than the native
      -- implementation; it never executes an unbounded expansion first.
      consume ((1 + cost a.terms) ^ 2 * (1 + cost b.terms) ^ 2)
      let terms := Polynomial.multiply atomLess monomialLess a.terms b.terms
      let _ ← reify terms
      return ⟨terms, fun parameters => by
        simpa [terms, Expression.eval, a.sound, b.sound] using
          Polynomial.multiply_value atomLess monomialLess (atomValue parameters) a.terms b.terms⟩
  | .pow2 exponent => do
      let a ← normalized exponent
      consume (1 + cost a.terms)
      match constant a.terms with
      | some n =>
          if n.val ≥ 64 then throw .overflow
          let value := 2 ^ n.val
          if bound : value < limit then
            return ⟨[(value, [])], fun parameters => by
              simp only [Polynomial.evaluate, Polynomial.monomialValue, Nat.mul_one, Nat.add_zero, Expression.eval]
              rw [← a.sound parameters, n.property parameters]⟩
          else throw .overflow
      | none =>
          let expression ← reify a.terms
          return ⟨[(1, [⟨"e" ++ key a.terms, .pow2 expression.val⟩])], fun parameters => by
            simp only [Polynomial.evaluate, Polynomial.monomialValue, atomValue, Expression.eval,
              Nat.mul_one, Nat.one_mul, Nat.add_zero]
            rw [expression.property parameters, a.sound parameters]⟩

structure Normalized (source : Expression arity) where
  expression : Expression arity
  key : String
  sound : ∀ parameters, expression.eval parameters = source.eval parameters
  closed : arity = 0 → ∃ value : Word, expression = .literal value

private def checkExpression : Nat → Expression arity → StateT Nat (Except NormalizationError) Nat
  | 0, _ => throw .resource
  | fuel + 1, expression => do
      consume 1
      match expression with
      | .literal _ | .parameter _ => pure 1
      | .add left right | .multiply left right =>
          let left ← checkExpression fuel left
          let right ← checkExpression fuel right
          pure (1 + left + right)
      | .pow2 exponent => return 1 + (← checkExpression fuel exponent)

def normalizeM (source : Expression arity) :
    StateT Nat (Except NormalizationError) (Normalized source) := do
  let size ← checkExpression 65 source
  if closed : arity = 0 then
    -- The first traversal charged itself; precharge the second, checked
    -- traversal before evaluating. Every intermediate
    -- remains a word; powers check the exponent before allocating the result.
    consume size
    let parameters : Fin arity → Word := fun index => Fin.elim0 (closed ▸ index)
    let value ← (source.checked parameters).mapError (fun _ => NormalizationError.overflow)
    let terms : Terms arity := if value.val.val = 0 then [] else [(value.val.val, [])]
    return ⟨.literal value.val, key terms, fun values => by
      have same : (fun index => (parameters index).val) = values :=
        funext fun index => Fin.elim0 (closed ▸ index)
      simpa only [Expression.eval, same] using value.property,
      fun _ => ⟨value.val, rfl⟩⟩
  else
    let result ← normalized source
    consume (cost result.terms)
    let expression ← reify result.terms
    return ⟨expression.val, key result.terms,
      fun parameters => (expression.property parameters).trans (result.sound parameters),
      fun same => False.elim (closed same)⟩

/-- Every successful closed normalization has literal syntax with exactly the
mathematical value. This is carried by admission, independently of test cases. -/
theorem Normalized.closed_literal {source : Expression 0} (result : Normalized source) :
    result.expression.erase = .literal (source.eval Fin.elim0) := by
  obtain ⟨value, literal⟩ := result.closed rfl
  have sound := result.sound Fin.elim0
  rw [literal] at sound
  simpa only [literal, Expression.erase, Expression.eval] using congrArg Raw.literal sound

/-- Standalone normalization caps its allowance. Larger admission actions use
`normalizeM` so different expressions consume one shared allowance. -/
def normalize (source : Expression arity) (budget : Nat := 1000000) :
    Except NormalizationError (Normalized source) :=
  (normalizeM source).run' (min budget 1000000)

structure Equality (left right : Expression arity) : Type where
  sound : ∀ parameters, left.eval parameters = right.eval parameters

/-- A capacity refusal and a different normal form are distinct results. The
positive result is an equality for every natural assignment, not a hash match. -/
def equality (left right : Expression arity) (budget : Nat := 1000000) :
    Except NormalizationError (Option (Equality left right)) := do
  let a ← normalize left budget
  let b ← normalize right budget
  if same : a.expression = b.expression then
    return some ⟨fun parameters => (a.sound parameters).symm.trans
      ((congrArg (fun expression => expression.eval parameters) same).trans (b.sound parameters))⟩
  else return none

end Zkc.Source.Mathematical.Static
