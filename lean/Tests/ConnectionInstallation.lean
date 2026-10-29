import Zkc.Construction.ConnectionInstallation

/-! The common return assembler uses source scopes and the selected profile.
These metadata fixtures isolate schema checks from source admission. Full
readback below quantifies the nominal model, residual and reached history. -/
set_option autoImplicit false
namespace Tests.ConnectionInstallation
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionInstallation

private def signature : ProtocolSignature :=
  ⟨"Root", ["P", "V"], [], [.boolean, .field "f", .index], [], [[1], [0, 1], [0]]⟩
private def plain : Context := .plain "Root" ["P", "V"] 0 1
private def fs : Context := .fiatShamir "Root" ["P", "V"] 0 1 0
  "random.f/0" (some (.draw "f")) "suite" []
private def artifact (outputs : List ValueSort) (returned : List Nat) : Participant where
  source := "metadata-fixture"
  candidate := "metadata-fixture"
  symbol := "validator"
  policy := ⟨"Root", "P", "V", 0, "", [], [], [], "fixture", "fixture"⟩
  inputs := []
  outputs := outputs
  instructions := []
  returned := returned
private def plainArtifact := artifact [.data .boolean, .data (.field "f")] [0, 1]
private def fsArtifact := artifact [.data .boolean, .data (.field "f"), .transcript "suite"] [0, 1, 2]
private def plainLayout : ReturnLayout signature plain 1 plainArtifact :=
  (ReturnLayout.build signature plain 1 plainArtifact).toOption.get (by decide +kernel)
private def fsLayout : ReturnLayout signature fs 1 fsArtifact :=
  (ReturnLayout.build signature fs 1 fsArtifact).toOption.get (by decide +kernel)

example : plainLayout.locations = [.data 0, .data 1, .absent] := rfl
example : fsLayout.locations = [.data 0, .data 1, .absent] := rfl
example : fsLayout.historyReference = some 2 := rfl
example : returnLocations 1 signature.outputScopes [0] = none := rfl
example : returnLocations 1 signature.outputScopes [0, 1, 2] = none := rfl

-- A hidden output does not consume a physical selector. The other role has a
-- different complete row; the assembler cannot reuse the validator's policy.
example : returnLocations 0 signature.outputScopes [5, 9] =
    some [.absent, .data 5, .data 9] := rfl
example : (ReturnLayout.build signature plain 0 plainArtifact).toOption = none := by decide +kernel

-- Sort checks keep nominal fields distinct and the transcript profile exact.
example : (ReturnLayout.build signature plain 1
    (artifact [.data .boolean, .data (.field "other")] [0, 1])).toOption = none := by decide +kernel
example : (ReturnLayout.build signature fs 1 plainArtifact).toOption = none := by decide +kernel
example : (ReturnLayout.build signature plain 1 fsArtifact).toOption = none := by decide +kernel
example : (ReturnLayout.build signature fs 1
    (artifact [.data .boolean, .data (.field "f"), .transcript "other"] [0, 1, 2])).toOption = none := by decide +kernel
-- Schema alone is insufficient: missing and surplus return selectors refuse.
example : (ReturnLayout.build signature fs 1 { fsArtifact with returned := [0, 1] }).toOption = none := by decide +kernel
example : (ReturnLayout.build signature plain 1 { plainArtifact with returned := [0, 1, 2] }).toOption = none := by decide +kernel
example : (ReturnLayout.build { signature with outputs := [.boolean, .service "random.f/0", .index] }
    plain 1 plainArtifact).toOption = none := by decide +kernel

example (model : DomainModel) (accepted : Bool) (residual : model.Field "f")
    (history : Domain.History model.toCarriers) :
    ∃ output,
      Domain.read [.data (.boolean accepted), .data (.field "f" residual), .transcript "suite" history]
        fsArtifact.returned = some output ∧
      Domain.sortsMatch fsArtifact.outputs output = true ∧
      Original.CompleteReturns signature fs 1 fsArtifact
        ⟨.cons (some accepted) (.cons (some residual) (.cons none .nil)), ⟨[], history⟩⟩
        ⟨output, [.data (.boolean accepted), .data (.field "f" residual), .transcript "suite" history]⟩ := by
  apply fsLayout.finish (captured := [])
  refine ⟨?_, rfl, rfl, ?_⟩
  · exact ⟨⟨accepted, rfl, rfl⟩, ⟨residual, rfl, rfl⟩, rfl, trivial⟩
  · exact ArtifactBinding.captures_append [] _

-- Replacing the final transcript by a stale one cannot discharge readback,
-- even when all data and the acceptance bit agree.
example (model : DomainModel) (accepted : Bool) (residual : model.Field "f")
    (before reached : Domain.History model.toCarriers) (changed : before ≠ reached) :
    ¬ fsLayout.BodyReturns []
      ⟨.cons (some accepted) (.cons (some residual) (.cons none .nil)), ⟨[], reached⟩⟩
      [.data (.boolean accepted), .data (.field "f" residual), .transcript "suite" before] := by
  intro related
  have same : some (Domain.Value.transcript (carriers := model.toCarriers) "suite" before) =
      some (.transcript "suite" reached) := related.2.1
  exact changed (Domain.Value.transcript.inj (Option.some.inj same)).2

end Tests.ConnectionInstallation
