import Zkc.Source.TablePreparation
import Zkc.Protocols.CommitmentSessions.Execution

set_option autoImplicit false

namespace Zkc.Protocols.CommitmentSessions.Modular
open Zkc.Source.TablePreparation

/-- Repeated addition in the additive cyclic group Z/7Z. The seed 0 is
    captured; six instructions materialize 1*h through 6*h modulo 7. -/
def key (h : Nat) : Key :=
  ⟨1,700,[0],(List.range 6).map (fun i => .mod (.add (.reg i) (.lit h)) 7)⟩
def consume (t : List Nat) (m r : Nat) := (m + t[r % 7]?.getD 0) % 7

theorem table_exact : ∀ h : Fin 7,
    (Zkc.Source.TablePreparation.provider (key h.val)).1 = (List.range 7).map (fun r => h.val*r % 7) := by decide

theorem consume_exact : ∀ h m r : Fin 7,
    consume (Zkc.Source.TablePreparation.provider (key h.val)).1 m.val r.val = (m.val+h.val*r.val)%7 := by decide

/-- Concrete additive group control; key is h, q=7 and g=1. No binding claim. -/
def table (h : Nat) : List Nat := (List.range 7).map (fun r => h*r % 7)
def provider : Provider (List Nat) where
  prepare := table
  commit := fun _ t m r => (m + t[r % 7]!) % 7
  verify := fun h c m r => c == (m + h * (r % 7)) % 7

end Zkc.Protocols.CommitmentSessions.Modular
