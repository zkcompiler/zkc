import Zkc.Polynomial.Bilinear.Preparation
import Zkc.Source.FactorInputs

set_option autoImplicit false

namespace Zkc.Polynomial.Bilinear.Factor
open Zkc.Modules.Preparation Zkc.Source.TablePreparation

open Zkc.Modules.Factor

def originKey (o : Nat) : Zkc.Modules.Factor.Key := ⟨o,[0,1]⟩
def source (o : Nat) : Zkc.Source.FactorInputs.Source := .fix (.base (originKey o)) 0

def world (a b c d x : Nat) (t : List Nat) : Zkc.Modules.Factor.State Nat where
  base := fun _ xs =>
    a+b*(xs[0]?.getD 0)+(c+d*(xs[0]?.getD 0))*(xs[1]?.getD 0)
  view := fun _ ys => Zkc.Polynomial.Bilinear.consume t (ys[0]?.getD 0)
  challenge := fun i => if i = 0 then x else i

def materialized (o a b c d x : Nat) : Zkc.Modules.Factor.State Nat :=
  world a b c d x (provider (Zkc.Polynomial.Bilinear.key o a b c d x)).1

/-- Concrete interpreted coefficients implement the actual Zkc.Source.Expressions source evaluator;
    the new Means assertion is derived, rather than supplied by a caller. -/
theorem source_evaluator_join (o a b c d x : Nat) (tail : List Nat) :
    (materialized o a b c d x).view 0 tail =
    (source o).eval (materialized o a b c d x) tail := by
  simp [materialized,world,source,Zkc.Source.FactorInputs.Source.eval,Zkc.Polynomial.Bilinear.table_exact,Zkc.Polynomial.Bilinear.consume]

theorem prepared_means (o a b c d x : Nat) :
    Means (materialized o a b c d x) (Zkc.Source.FactorInputs.fact (source o) 0) := by
  intro tail _
  simp only [Zkc.Source.FactorInputs.fact]
  rw [← Zkc.Source.FactorInputs.source_meaning]
  exact source_evaluator_join o a b c d x tail

/-- A single shared-handler request produces the value used in the factor view. -/
def request (o a b c d x : Nat) : Program Zkc.Source.TablePreparation.Key (List Nat) Unit (List Nat) :=
  .request (Zkc.Polynomial.Bilinear.key o a b c d x) .done

theorem memo_produces_means (o a b c d x : Nat) :
    Means (world a b c d x
      (run provider prices .memo (request o a b c d x) empty).value)
      (Zkc.Source.FactorInputs.fact (source o) 0) := by
  rw [(simulation provider prices .memo _ empty
    (Zkc.Modules.ImmutableCache.empty_valid provider)).1]
  exact prepared_means o a b c d x

end Zkc.Polynomial.Bilinear.Factor
