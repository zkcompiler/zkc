import Zkc.Protocols.CapturedPrograms.Installation
import ZkcArkLib.CapturedPrograms.Inputs

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.CapturedPrograms.Installation
open Zkc.Protocols.CapturedPrograms Zkc.Protocols.CapturedPrograms.Installation ZkcArkLib.CapturedPrograms Zkc.Modules.Installation Zkc.Modules.FactorState
variable {F : Type} [CommRing F] [DecidableEq F]
theorem installed_no_default {A : Type} (capacity : Nat) (r : Request F) (tree : Tree)
    (s : World F) (x : Issued F) (hx : afterInstall capacity r tree s = some x)
    (fallback : Nat → F) (k : Zkc.Protocols.Sumcheck.LocalProver.Cut F → ProbComp A) :
    ZkcArkLib.LocalProver.execFallback fallback k x.code.causal (Zkc.Protocols.Sumcheck.LocalProver.initial x.inputs) =
      ZkcArkLib.LocalProver.exec k x.code.causal (Zkc.Protocols.Sumcheck.LocalProver.initial x.inputs) :=
  issued_no_default _ _ tree x (afterInstall_accepted capacity r tree s x hx).2 fallback k

def initializedExperiment {D : Type} (capacity : Nat) (r : Request F) (tree : Tree)
    (s : World F) (embed : D → F) (draw : Zkc.Protocols.Sumcheck.LocalProver.Boundary F → ProbComp D) :
    ProbComp (Option Unit) :=
  match afterInstall capacity r tree s with
  | none => pure none
  | some x => actual embed draw x

end ZkcArkLib.CapturedPrograms.Installation

namespace ZkcArkLib.CapturedPrograms.Installation
open Zkc.Protocols.CapturedPrograms.Installation ZkcArkLib.CapturedPrograms
open Zkc.Modules.FactorState Zkc.Modules.Installation Zkc.Protocols.CapturedPrograms OracleComp ENNReal Zkc.Protocols.Sumcheck.LocalProver ZkcArkLib.LocalProver
open Zkc.Source.Availability

/-- The false-claim/provider law is still explicit; no native or FS security is
    inferred. Both installer rejection and issuer rejection are non-acceptance. -/
theorem initialized_experiment_bound {F D : Type} [Field F] [DecidableEq F] [Fintype D]
    (capacity : Nat) (r : Request F) (tree : Tree) (s : World F)
    (embed : D → F) (inj : Function.Injective embed) (draw : Boundary F → ProbComp D)
    (ε : ℝ≥0∞)
    (cap : ∀ x, afterInstall capacity r tree s = some x → ∀ b,
      Reaches x.code.causal (initial x.inputs) (.committed b) → ∀ d, Pr[= d | draw b] ≤ ε)
    (false_claim : ∀ x, afterInstall capacity r tree s = some x → ∀ b,
      Reaches x.code.causal (initial x.inputs) (.committed b) → b.claim ≠ 2) :
    Pr[= some () | initializedExperiment capacity r tree s embed draw] ≤ 2 * ε := by
  cases h : afterInstall capacity r tree s with
  | none => simp [initializedExperiment,h]
  | some x =>
    simpa [initializedExperiment,h] using issued_acceptance_cap embed inj draw x ε (cap x h) (false_claim x h)

end ZkcArkLib.CapturedPrograms.Installation
