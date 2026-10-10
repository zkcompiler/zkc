import Zkc.Semantics.ExecutionPath
import Mathlib.Logic.Function.Basic

/-! Session-indexed interfaces and phase framing. Resource state remains shared. -/

set_option autoImplicit false

namespace PIR.Sessions
variable {Session : Type} [DecidableEq Session] (I : Session → Signature)

/-- Session tags select interfaces; they do not assert resource independence. -/
def sig : Signature := ⟨(s : Session) × (I s).Op, fun o => (I o.1).Reply o.2⟩

def interaction (P : (s : Session) → Interaction (I s)) : Interaction (sig I) where
  Role := (s : Session) × (P s).Role
  Phase := (s : Session) → (P s).Phase
  owner := fun o => ⟨o.1,(P o.1).owner o.2⟩
  enabled := fun phases o => (P o.1).enabled (phases o.1) o.2
  advance := fun phases o a => Function.update phases o.1 ((P o.1).advance (phases o.1) o.2 a)

theorem selected_phase (P : (s : Session) → Interaction (I s))
    (phases : (s : Session) → (P s).Phase) (o : (sig I).Op) (a : (sig I).Reply o) :
    ((interaction I P).advance phases o a) o.1 = (P o.1).advance (phases o.1) o.2 a := by
  simp [interaction]

theorem other_phase (P : (s : Session) → Interaction (I s))
    (phases : (s : Session) → (P s).Phase) (o : (sig I).Op) (a : (sig I).Reply o)
    (other : Session) (different : other ≠ o.1) :
    ((interaction I P).advance phases o a) other = phases other := by
  simp [interaction, different]

/-- This is an actual handler execution. A shared provider can remain in S;
    session-local phase framing does not reset or commute that provider. -/
theorem actual_calls {A S E : Type} (P : (s : Session) → Interaction (I s))
    (p : Proc (sig I) A) (h : Handler (sig I) S E)
    (phases : (s : Session) → (P s).Phase) (state : S)
    (formed : Conforms (interaction I P) p phases) :
    ∀ before o, Sum.inl (before,o) ∈
      (p.run (ExecutionPath.handler (interaction I P) h) (phases,state)).events →
      (P o.1).enabled (before o.1) o.2 :=
  ExecutionPath.calls_permitted (interaction I P) h p phases state formed

end PIR.Sessions
