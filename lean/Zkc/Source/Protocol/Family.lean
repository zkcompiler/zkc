import Zkc.Source.Protocol.Counts
import Zkc.Source.PublicDimensions

/-! Compact public-dimension families use the same typed protocol grammar.
Resolution changes counts without unrolling or introducing a second source AST. -/

set_option autoImplicit false
namespace Zkc.Source.Protocol
open PublicDimensions
variable {n m : Nat} {Role Binding Schema : Type} {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {scope : List (Signature Role language.Ty)}
  {Γ results : List (Port Role language.Ty)}

def Program.instantiate (program : Program (Dim n) Role Binding Schema language locals scope Γ results)
    (environment : Fin n → Nat) : Program Nat Role Binding Schema language locals scope Γ results :=
  program.mapCounts (Dim.eval environment)

theorem Program.instantiate_subst
    (program : Program (Dim n) Role Binding Schema language locals scope Γ results)
    (substitution : Fin n → Dim m) (environment : Fin m → Nat) :
    (program.mapCounts (Dim.subst substitution)).instantiate environment =
      program.instantiate (fun i => (substitution i).eval environment) := by
  unfold instantiate
  rw [mapCounts_comp]
  congr 1
  funext expression
  exact eval_subst expression substitution environment

/-- Literal counts are an exact embedding of the old resolved syntax. -/
theorem Program.instantiate_literals
    (program : Program Nat Role Binding Schema language locals scope Γ results)
    (environment : Fin n → Nat) :
    (program.mapCounts Dim.lit).instantiate environment = program := by
  unfold instantiate
  rw [mapCounts_comp]
  exact program.mapCounts_id

end Zkc.Source.Protocol
