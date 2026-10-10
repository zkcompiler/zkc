import Zkc.Protocols.Sumcheck.LocalProver.Code
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.ProbCompLift

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.LocalProver
open OracleComp ENNReal Zkc.Protocols.Sumcheck.LocalProver

/-- Operational interpretation with an effect handler only at the terminal boundary. -/
def exec {F A : Type} [Ring F] [DecidableEq F] (k : Cut F → ProbComp A) :
    Code → State F → ProbComp A
  | .abort, st => k (.stopped st)
  | .assign i e p, st => exec k p (write st i (eval st e))
  | .random n i p, st => do
      let x ← $ᵗ (Fin (n+1))
      exec k p (coin st n i x)
  | .ifz e p q, st => if eval st e = 0 then exec k p (branch st true)
      else exec k q (branch st false)
  | .commit s a b c, st => k (.committed (boundary st s a b c))
def pre {F : Type} [Ring F] [DecidableEq F] (p : Code) (st : State F) : ProbComp (Cut F) :=
  exec pure p st

/-- Causal normalization is proved over source constructors, not assumed about a sampler. -/
theorem normalize {F A : Type} [Ring F] [DecidableEq F]
    (p : Code) (st : State F) (k : Cut F → ProbComp A) :
    exec k p st = (pre p st >>= k) := by
  induction p generalizing st with
  | abort => simp [pre, exec]
  | assign i e p ih => simpa [pre, exec] using ih (write st i (eval st e))
  | random n i p ih => simp only [pre, exec, bind_assoc]; congr 1; funext x; exact ih _
  | ifz e p q ihp ihq =>
      by_cases h : eval st e = 0 <;> simp [pre, exec, h, ihp, ihq]
  | commit s a b c => simp [pre, exec]

theorem support_iff_reaches {F : Type} [Ring F] [DecidableEq F]
    (p : Code) (st : State F) (out : Cut F) :
    out ∈ support (pre p st) ↔ Reaches p st out := by
  induction p generalizing st with
  | abort => simp only [pre, exec, mem_support_pure_iff]; constructor <;> intro h
             · subst out; exact .abort st
             · cases h; rfl
  | assign i e p ih =>
      simp only [pre, exec]
      rw [show exec pure p (write st i (eval st e)) = pre p (write st i (eval st e)) from rfl, ih]
      constructor
      · exact Reaches.assign i e p st out
      · intro h; cases h; assumption
  | random n i p ih =>
      simp only [pre, exec, mem_support_bind_iff]
      constructor
      · rintro ⟨x, _, hx⟩; exact .random n i p st out x ((ih _).mp hx)
      · intro h; cases h with
        | random _ _ _ _ _ x hx => exact ⟨x, by simp, (ih _).mpr hx⟩
  | ifz e p q ihp ihq =>
      by_cases h : eval st e = 0
      · simp only [pre, exec, if_pos h]
        constructor
        · intro hx; exact .yes e p q st out h ((ihp _).mp hx)
        · intro hx; cases hx with
          | yes _ _ _ _ _ _ hx => exact (ihp _).mpr hx
          | no _ _ _ _ _ hn _ => exact False.elim (hn h)
      · simp only [pre, exec, if_neg h]
        constructor
        · intro hx; exact .no e p q st out h ((ihq _).mp hx)
        · intro hx; cases hx with
          | yes _ _ _ _ _ hy _ => exact False.elim (h hy)
          | no _ _ _ _ _ _ hx => exact (ihq _).mpr hx
  | commit s a b c =>
      simp only [pre, exec, mem_support_pure_iff]
      constructor
      · intro h; subst out; exact .commit s a b c st
      · intro h; cases h; rfl


end ZkcArkLib.LocalProver
