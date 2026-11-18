module

public import Zkc.Core.Meaning.Assertions
public import Zkc.Core.Value.Expressions

@[expose] public section

/-!
The seam of the analysis on the term in steps, part 2: assertions and annotations.

An assertion is an expression over positions built from written operations (`Expr`): a
position, or one result of a written operation applied to expressions. It names a value when
its operands do and the operation gives that result (`Expr.Denotes`), and it holds when it
names a value that reads as true (`Expr.Holds`). A summary is assertions about the inputs and
about the inputs followed by the results (`Contract`).

A definition carries annotations, keyed by lexical occurrence (`Annotation`, `Annotations`): the
invariant of a loop, a step by a proved lemma (`Lemma`), a fact given by another producer.
They are no part of the term.

Which operations may appear in an assertion (shared, with no requirement of their own) is a
condition of a dialect's rules, in part 3.
-/

namespace Zkc.Core.BodyAnalysis

/-! ## Lemmas and annotations -/

/-- Each actual argument has the corresponding formal type. The constructors also enforce
the arity of the application. -/
inductive ArgumentsMatch {T Val : Type} (typed : Val → T → Prop) : List Val → List T → Prop where
  | nil : ArgumentsMatch typed [] []
  | cons {v t vs ts} (head : typed v t) (tail : ArgumentsMatch typed vs ts) :
      ArgumentsMatch typed (v :: vs) (t :: ts)

/-- A lemma holds on valid arguments of its declared types. The typed relation includes
validity; elaboration separately checks that an application has exactly this context. -/
def Lemma.Valid {T Raw Val : Type} (Run : Raw → List Val → List Val → Prop) (R : Reading Val)
    (Typed : Val → T → Prop) (l : Lemma T Raw) : Prop :=
  ∀ args : List Val, ArgumentsMatch Typed args l.parameters →
    (∀ p, p ∈ l.premises → p.Holds Run R args) → l.conclusion.Holds Run R args

/-- Resolve an application against its lexical context before analysing reachability. -/
def Lemma.resolve? {T Raw : Type} [DecidableEq T] (lemmas : List (Lemma T Raw))
    (Γ : Ctx T) (number : Nat) (names : List Name) : Option (Lemma T Raw) := do
  let lemma ← lemmas[number]?
  let actual ← names.mapM Γ.find?
  if actual = lemma.parameters then some lemma else none

theorem Lemma.resolve?_eq_some {T Raw : Type} [DecidableEq T] (lemmas : List (Lemma T Raw))
    (Γ : Ctx T) (number : Nat) (names : List Name) (lemma : Lemma T Raw) :
    resolve? lemmas Γ number names = some lemma ↔
      lemmas[number]? = some lemma ∧ names.mapM Γ.find? = some lemma.parameters := by
  unfold resolve?
  cases found : lemmas[number]? with
  | none => simp
  | some registered =>
      cases actual : names.mapM Γ.find? with
      | none => simp
      | some types =>
          by_cases equal : types = registered.parameters
          · subst types
            simp +contextual
          · simp [equal]
            rintro rfl
            exact equal

def Instr.site (cursor : StaticCursor) (key : Key) {D : Dialect} {Γ : Ctx D.Ty}
    {mid : List D.Ty} : Instr D Γ mid → AnnotationSite
  | .block n _ => .block cursor key n
  | _ => .instruction cursor key

end Zkc.Core.BodyAnalysis
