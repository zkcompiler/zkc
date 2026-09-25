import Zkc.Modules.PolynomialPreparation
import Zkc.Compiler.FactorOptimization

set_option autoImplicit false
namespace Zkc.Compiler.PolynomialPreparation
open Zkc.Modules.PolynomialPreparation
variable {F : Type} [CommSemiring F] {n m : Nat}

theorem laws (binding : Binding F (n + m)) (calls : Nat → Call F m) :
    Compiler.FactorOptimization.Laws (Bound binding)
      (fun name => summary binding (calls name)) (fun name => execute binding (calls name)) where
  summary name := justifies binding (calls name)
  preserves name := preserves_binding binding (calls name)

end Zkc.Compiler.PolynomialPreparation
