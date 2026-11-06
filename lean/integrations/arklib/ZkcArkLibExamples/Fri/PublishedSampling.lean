module

public import ZkcArkLibExamples.Fri.RetainedSampling

@[expose] public section

/-! The immutable publication experiment installs the scalar sampler at the
qualified source site. A draw reads the reached word table; all changes to
that table still come from successful publications. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.PublishedSampling
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriScalarLoop RetainedSampling Phases OracleComp
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {Aux E : Type}

abbrev Network (model : DomainModel) (Aux E : Type) :=
  PublishedWords.Table model → PIR.MonadHandler ProbComp (participantInterfaceOn model.toCarriers) Aux E

/-- Index draws belong to the verifier. Other ordinary capabilities keep their
own service implementation and may abort. Every scalar draw records its audit
events against the pre-existing table without exposing another sample. -/
noncomputable def withScalar (network : Network model Aux E) (service : Nat)
    (audit : PublishedWords.Table model → Fin 32 → List E) : Network model Aux E :=
  fun words op state ↦ match op with
  | .query location (.sampleIndex name) (.cons handle (.cons bound .nil)) =>
      if location = site drawSites.draw ∧ name = contract ∧ handle = service ∧ bound = 32 then do
        let i ← $ᵗ (Fin 32)
        pure ⟨.returned i.val, state, audit words i⟩
      else pure ⟨.stopped .refused, state, []⟩
  | .query _ (.sampleIndices _) _ => pure ⟨.stopped .refused, state, []⟩
  | .send (ty := ty) loc peer v => network words (.send (ty := ty) loc peer v) state
  | .receive ty loc peer => network words (.receive ty loc peer) state
  | .query loc (.draw domain) args => network words (.query loc (.draw domain) args) state

theorem configured (network : Network model Aux E) (service : Nat)
    (audit : PublishedWords.Table model → Fin 32 → List E) (words : PublishedWords.Table model) (state : Aux) :
    withScalar network service audit words (.query (site drawSites.draw) (.sampleIndex contract)
      (.cons service (.cons 32 .nil))) state = (do
      let i ← $ᵗ (Fin 32)
      pure ⟨.returned i.val, state, audit words i⟩) := by
  change (if site drawSites.draw = site drawSites.draw ∧ contract = contract ∧ service = service ∧ (32 : Nat) = 32 then _
    else _) = _
  simp only [and_self, ↓reduceIte]

noncomputable def fresh (oracles : List (CheckedOracle snapshot domains math))
    (network : Network model Aux E) (service : Nat) (audit : PublishedWords.Table model → Fin 32 → List E)
    (choose : PublishedWords.Chooser ProbComp model Aux E) :
    Fresh (PublishedWords.actionM oracles (withScalar network service audit) choose) service where
  afterDraw i s := pure ⟨.returned (), s,
    (audit s.oracle.provider.words i).map OracleProtocol.Event.ordinary⟩
  sample state := by
    have bound : 0 < 32 ∧ 32 < indexLimit := by decide
    simp [OracleProtocol.finiteIndex, bound, PIR.Process.runM, PublishedWords.actionM_ordinary,
      configured, PIR.Execution.followM, repack, PIR.Execution.follow]

end ZkcSecurity.ArkLib.Fri.PublishedSampling
