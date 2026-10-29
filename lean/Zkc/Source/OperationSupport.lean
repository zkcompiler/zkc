module

public import Zkc.Semantics.OperationSupport
public import Zkc.Source.Structure
public import Zkc.Source.Finite

@[expose] public section

/-! Finite structural support certificates for typed bodies, callbacks and
iteration. The check proves a fact about the existing denotation; it is not a
second evaluator. Runtime iteration counts are never unrolled by the check. -/
set_option autoImplicit false
namespace PIR.OperationSupport
open Zkc.Source
variable {I : PIR.Signature} {S : Type} {allowed : I.Op → Prop}

theorem finite {T : Type} (items : List T) (step : S → T → PIR.Process I S)
    (law : ∀ state item, OperationSupport allowed (step state item)) (state : S) :
    OperationSupport allowed (Finite.fold step items state) := by
  induction items generalizing state with
  | nil => trivial
  | cons item rest ih => exact (law state item).bind _ ih

end PIR.OperationSupport

namespace Zkc.Source
open PIR
variable {I : PIR.Signature}

namespace SourceSupport
variable {dialect : Dialect}

mutual
  /-- Finite body check; callbacks are inspected once, independently of loop bounds. -/
  def region (allowed : dialect.Op → Bool) {Γ out} : Region dialect Γ out → Bool
    | .ret _ | .stop _ => true
    | .letOp operation _ bodies next => allowed operation && regions allowed bodies && region allowed next
    | .bind body next => region allowed body && region allowed next
  def regions (allowed : dialect.Op → Bool) {signatures} : Regions dialect signatures → Bool
    | .nil => true
    | .cons body rest => region allowed body && regions allowed rest
end

/-- One installed operation law composes through the actual shared body denotation. -/
theorem denote (allowed : dialect.Op → Bool) (effects : I.Op → Prop)
    (meaning : RegionMeaning dialect I)
    (laws : ∀ operation arguments callbacks, allowed operation = true →
      (∀ {signature} (ref : Var (dialect.regions operation) signature) arguments,
        OperationSupport effects (callbacks.get ref arguments)) →
      OperationSupport effects (meaning.operation operation arguments callbacks))
    {Γ out} (body : Region dialect Γ out) (checked : region allowed body = true)
    (environment : Environment meaning.Value Γ) :
    OperationSupport effects (body.denote meaning environment) := by
  induction body using Region.rec
    (motive_2 := fun signatures bodies => regions allowed bodies = true →
      ∀ {signature} (ref : Var signatures signature) arguments,
        OperationSupport effects ((bodies.denote meaning).get ref arguments)) with
  | ret => trivial
  | stop => trivial
  | letOp operation arguments bodies next bodiesIH nextIH =>
    simp only [region, Bool.and_eq_true] at checked
    exact (laws operation _ _ checked.1.1 (bodiesIH checked.1.2)).bind _ (fun _ => nextIH checked.2 _)
  | bind body next bodyIH nextIH =>
    simp only [region, Bool.and_eq_true] at checked
    exact (bodyIH checked.1 _).bind _ (fun _ => nextIH checked.2 _)
  | nil => exact nomatch ‹Var [] _›
  | cons body rest bodyIH restIH =>
    rename_i checked signature ref arguments
    simp only [regions, Bool.and_eq_true] at checked
    cases ref with
    | here => exact bodyIH checked.1 arguments.get
    | there ref => exact restIH checked.2 ref arguments

end SourceSupport
end Zkc.Source
