import Zkc.Modules.FactorExecution
import Zkc.Compiler.FactorProgram

set_option autoImplicit false
namespace Zkc.Compiler.FactorExecution
open PIR Zkc.Modules.Factor Zkc.Modules.FactorExecution
variable {K E : Type}

def embed : Zkc.Compiler.FactorProgram.Code → Proc (signature K) (List K)
  | .stop => .done []
  | .demand q plan next => .call (.demand q plan) (fun v =>
      (embed next).bind (fun values => .done (v :: values)))
  | .call id yes no => .call (.external id) (fun b =>
      match (show Bool from b) with
      | true => embed yes
      | false => embed no)

/-- Both interpreters execute the same source calls and retain their actual emissions. -/
theorem embedding_exact (impl : Nat → Zkc.Modules.FactorState.Implementation K E)
    (code : Zkc.Compiler.FactorProgram.Code) (s : Zkc.Modules.FactorState.World K) :
    (embed code).run (handler impl) s =
      let old := Zkc.Compiler.FactorProgram.run impl code s
      ⟨.returned old.values, old.world, old.events⟩ := by
  induction code generalizing s with
  | stop => rfl
  | demand q plan next ih =>
    simp [embed, Proc.run, handler, Execution.follow, run_bind, ih, Zkc.Compiler.FactorProgram.run]
    rfl
  | call id yes no ihYes ihNo =>
    cases h : (impl id s).success <;>
      simp [embed, Proc.run, handler, returned, Execution.follow, h, ihYes, ihNo, Zkc.Compiler.FactorProgram.run]

/-- The existing inference+framing compiler theorem now has the common execution type. -/
theorem compiled_execution (spec : Nat → Zkc.Modules.FactorState.Spec K) (impl : Nat → Zkc.Modules.FactorState.Implementation K E)
    (laws : ∀ id, Zkc.Modules.FactorState.Satisfies (spec id) (impl id))
    (src : Zkc.Compiler.FactorProgram.Source) (s : Zkc.Modules.FactorState.World K) (facts : List Fact) (available : List Nat)
    (valid : Valid s.values facts) (known : Zkc.Modules.FactorState.Known s available)
    (legal : Zkc.Compiler.FactorProgram.Legal spec impl available src s) :
    (embed (Zkc.Compiler.FactorProgram.compile (fun id => (spec id).post) facts available src)).run (handler impl) s =
      (embed (Zkc.Compiler.FactorProgram.direct src)).run (handler impl) s := by
  rw [embedding_exact,embedding_exact,
    Zkc.Compiler.FactorProgram.compile_correct spec impl laws src s facts available valid known legal]

end Zkc.Compiler.FactorExecution
