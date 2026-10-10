import Zkc.Modules.Installation
import Zkc.Compiler.FactorProgram

set_option autoImplicit false
namespace Zkc.Compiler.FactorBinding
open Zkc.Modules.FactorBinding Zkc.Modules.FactorState
variable {K E : Type}

/-- Whole finite caller join from the actual returned instance, with no
    separately supplied initial Valid/Known premise. Call contracts remain explicit. -/
theorem instantiated_caller (n : Namespace) (l outer : World K)
    (e : Zkc.Source.FactorInputs.Source) (handle : Nat) (p : Prepared K)
    (accepted : instantiate n l outer e handle = some p)
    (spec : Nat → Spec K) (impl : Nat → Implementation K E)
    (laws : ∀ i, Satisfies (spec i) (impl i)) (caller : Zkc.Compiler.FactorProgram.Source)
    (legal : Zkc.Compiler.FactorProgram.Legal spec impl p.available caller p.world) :
    Zkc.Compiler.FactorProgram.run impl (Zkc.Compiler.FactorProgram.compile (fun i => (spec i).post)
      [p.exported] p.available caller) p.world =
    Zkc.Compiler.FactorProgram.run impl (Zkc.Compiler.FactorProgram.direct caller) p.world ∧
    Zkc.Compiler.FactorProgram.Enabled spec impl (Zkc.Compiler.FactorProgram.compile (fun i => (spec i).post)
      [p.exported] p.available caller) p.world := by
  have ok := instantiated_valid n l outer e handle p accepted
  exact ⟨Zkc.Compiler.FactorProgram.compile_correct spec impl laws caller p.world [p.exported]
    p.available ok.1 ok.2.1 legal,
    Zkc.Compiler.FactorProgram.compile_enabled spec impl laws caller p.world [p.exported]
    p.available ok.2.1 legal⟩

open Zkc.Modules.Installation Zkc.Modules.Factor in
/-- Initialization now occurs inside the caller. Validity of existing facts is
    still required; validity of newly installed facts is derived by execute. -/
theorem caller_from_before (capacity : Nat) (requests : Nat → Request K)
    (src : Zkc.Compiler.FactorProgram.Source) (s : World K) (facts : List Fact) (available : List Nat)
    (valid : Valid s.values facts) (known : Known s available)
    (legal : Zkc.Compiler.FactorProgram.Legal (fun i => contract (requests i))
      (fun i => execute capacity (requests i)) available src s) :
    Zkc.Compiler.FactorProgram.run (fun i => execute capacity (requests i))
      (Zkc.Compiler.FactorProgram.compile (fun i => (contract (requests i)).post) facts available src) s =
    Zkc.Compiler.FactorProgram.run (fun i => execute capacity (requests i)) (Zkc.Compiler.FactorProgram.direct src) s :=
  Zkc.Compiler.FactorProgram.compile_correct _ _ (fun i => execute_satisfies capacity (requests i))
    src s facts available valid known legal

end Zkc.Compiler.FactorBinding
