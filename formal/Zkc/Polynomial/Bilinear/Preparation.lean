import Zkc.Source.TablePreparation

set_option autoImplicit false

namespace Zkc.Polynomial.Bilinear
open Zkc.Source.TablePreparation

/-- f(x,y)=a+b*x+c*y+d*x*y; fix x and materialize the
    residual coefficients [a+b*x,c+d*x]. Captures are in the exact key. -/
def key (origin a b c d x : Nat) : Key :=
  ⟨1,origin,[a,b,c,d,x],
    [.add (.reg 0) (.mul (.reg 1) (.reg 4)),
     .add (.reg 2) (.mul (.reg 3) (.reg 4))]⟩
def consume (t : List Nat) (y : Nat) := t[5]?.getD 0 + t[6]?.getD 0 * y

theorem table_exact (o a b c d x : Nat) :
    provider (key o a b c d x) = ([a,b,c,d,x,a+b*x,c+d*x],4) := by
  simp [provider,key,exec,Expr.eval]

theorem consume_exact (o a b c d x y : Nat) :
    consume (provider (key o a b c d x)).1 y = a+b*x+(c+d*x)*y := by
  rw [table_exact]; rfl

theorem evaluate_exact (o a b c d x y : Nat) :
    consume (provider (key o a b c d x)).1 y = a+b*x+c*y+d*x*y := by
  rw [consume_exact]
  simp [Nat.add_mul,Nat.add_assoc,Nat.mul_assoc]

end Zkc.Polynomial.Bilinear
