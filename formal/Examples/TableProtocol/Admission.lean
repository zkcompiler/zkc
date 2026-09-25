import Examples.TableProtocol.Format
import Zkc.Compiler.Admission
import Zkc.Source.PhaseAdmissionFormat

/-! Consumer-installed send/draw discipline for the finite table trace profile.
The summary law covers every typed reply, including a false send reply. It does
not assert a cryptographic challenge law or participant projection. -/

set_option autoImplicit false

namespace TableProtocol.Admission
open Zkc.Source Zkc.Compiler PhaseAdmission Protocol

inductive Phase where | ready | sent deriving DecidableEq, Repr

def profile : String := "table-round/1"

def interaction : PIR.Interaction protocolInterface where
  Role := Unit
  Phase := Phase
  owner := fun _ => ()
  enabled
    | _, .base _ => True
    | .ready, .send _ _ => True
    | .sent, .draw => True
    | _, _ => False
  advance := fun phase call _ => match call with
    | .base _ => phase
    | .send _ _ => .sent
    | .draw => .ready

def policy : Policy Protocol.language Phase where
  step
    | .send, .ready => some [.sent]
    | .draw, .sent => some [.ready]
    | .send, .sent | .draw, .ready => none
    | _, phase => some [phase]

private theorem lift_sound {A : Type} (body : PIR.Proc TableProtocol.interface A)
    (phase : Phase) :
    PIR.Conforms interaction (lift body) phase ∧
    PIR.Boundary.Returns interaction (fun _ finish => finish = phase) (lift body) phase := by
  induction body with
  | done value => exact ⟨trivial, rfl⟩
  | halt reason => exact ⟨trivial, trivial⟩
  | call op next ih => exact ⟨⟨trivial, fun reply => (ih reply).1⟩, fun reply => (ih reply).2⟩

def summaryLaws : Realizes policy Protocol.meaning interaction where
  relates := Eq
  operation := by
    intro op before exits accepted args phase related
    cases related
    cases op with
    | base op =>
      simp [policy] at accepted
      subst exits
      have law := lift_sound (TableProtocol.meaning.operation op args) before
      exact ⟨law.1, PIR.Boundary.returns_mono interaction _ _ _ before law.2
        (fun _ _ same => ⟨before, by simp, same.symm⟩)⟩
    | send =>
      cases before <;> simp [policy] at accepted
      subst exits
      cases args
      rename_i a rest
      cases rest
      rename_i b rest
      cases rest
      exact ⟨⟨trivial, fun _ => trivial⟩, fun _ => ⟨.sent, by simp, rfl⟩⟩
    | draw =>
      cases before <;> simp [policy] at accepted
      subst exits
      cases args
      exact ⟨⟨trivial, fun _ => trivial⟩, fun _ => ⟨.ready, by simp, rfl⟩⟩
    | linear =>
      simp [policy] at accepted
      subst exits
      cases args
      rename_i a rest
      cases rest
      rename_i b rest
      cases rest
      rename_i r rest
      cases rest
      exact ⟨trivial, ⟨before, by simp, rfl⟩⟩
    | point =>
      simp [policy] at accepted
      subst exits
      cases args
      rename_i r rest
      cases rest
      exact ⟨trivial, ⟨before, by simp, rfl⟩⟩
    | endpointPoint one =>
      simp [policy] at accepted
      subst exits
      cases args
      exact ⟨trivial, ⟨before, by simp, rfl⟩⟩
    | equal | parent _ | digestEqual =>
      simp [policy] at accepted
      subst exits
      cases args
      rename_i a rest
      cases rest
      rename_i b rest
      cases rest
      exact ⟨trivial, ⟨before, by simp, rfl⟩⟩

def phases : Format.Codec Phase where
  encode | .ready => .str "ready" | .sent => .str "sent"
  decode
    | .str "ready" => .ok .ready
    | .str "sent" => .ok .sent
    | _ => .error .shape

def certificateCodec := PhaseAdmission.certificateCodec phases 256

end TableProtocol.Admission
