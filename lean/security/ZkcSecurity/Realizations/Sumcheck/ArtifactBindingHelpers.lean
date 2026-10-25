module

public import ZkcSecurity.Realizations.Sumcheck.ArtifactBindingLoop

@[expose] public section

/-! Pure helper construction uses the same closed dependency fold on both
sides. It preserves every stopped outcome, including index exhaustion. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Compose a physical suffix when the original participant has already
returned. The source return itself is retained, including its full ABI. -/
def finish {A B C : Type}
    {relation : A → B → Prop} {result : A → C → Prop}
    {live : PIR.Process (Domain.effects (uniformCarriers F G)) A →
      Domain.Environment (uniformCarriers F G) → Prop}
    {nextLive : PIR.Process (Domain.effects (uniformCarriers F G)) A →
      Domain.Environment (uniformCarriers F G) → Prop}
    {source : PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {target : PIR.Process (Domain.effects (uniformCarriers F G)) B}
    {next : B → PIR.Process (Domain.effects (uniformCarriers F G)) C}
    (head : Original.Simulation relation live source target)
    (frames : ∀ process frame, live process frame → nextLive process frame)
    (tail : ∀ a b, relation a b → Original.Simulation result nextLive (.done a) (next b)) :
    Original.Simulation result nextLive source (target.bind next) := by
  simpa only [PIR.Process.bind_done] using
    head.bind (fun process frame related => by
      simpa only [PIR.Process.bind_done] using frames process frame related) tail

theorem helper_stopped (program : Structured.Program) (helper : Helper)
    (arguments : Values (assignment F G) helper.inputs)
    (present : helper ∈ program.payload.definitions.map CheckedDefinition.helper)
    (encoded : Domain.Environment (uniformCarriers F G))
    (encoding : Domain.encodeValues arguments = some encoded) (reason : PIR.Stop)
    (law : invoke (closedMeanings program.payload.definitions) helper arguments = .halt reason) :
    Domain.callHelper (ringModel F G) program helper.name
      (helper.outputs.map ValueSort.data) encoded = .stopped reason := by
  obtain ⟨entry, found, signature⟩ := Evaluation.linked_lookup (F := F) (G := G)
    SiteObservations.closed program.payload.linked helper present
  rw [← Domain.Binding.helperTable_ringModel] at found
  subst helper
  simp only [closedMeanings, ← Domain.Binding.helperTable_ringModel, invoke,
    found, ↓reduceDIte] at law
  rw [Domain.Binding.callHelper_of_lookup (ringModel F G) program entry found arguments encoded encoding, law]
  rfl

def BooleanReturns (initial : Original.State (uniformCarriers F G))
    (environment : Domain.Environment (uniformCarriers F G))
    (source : Values (Component (assignment F G)) [.boolean] × Original.State (uniformCarriers F G))
    (final : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ result : Bool, source = (.cons (some result) .nil, initial) ∧
    final = environment ++ [.data (.boolean result)]

/-- The actual original checker and actual compiled helper have identical
closed outcomes on every raw table, point, and scalar. No shape or success
premise is needed. The helper lookup and full nominal encodings are checked. -/
def terminal (program : Structured.Program)
    (bodies : ZkcSecurity.Realizations.Sumcheck.DomainHelpers.Bodies program) (routing : Original.Routing)
    (state : Original.State (uniformCarriers F G)) (self : Nat)
    (entries point : List F) (scalar : F)
    (environment : Domain.Environment (uniformCarriers F G)) (references : List Nat)
    (read : Domain.read environment references = some
      [.data (.vector "bls12-381.fr" entries), .data (.vector "bls12-381.fr" point),
        .data (.field "bls12-381.fr" scalar)]) :
    Original.Simulation (BooleanReturns state environment)
      (fun _ frame => frame = environment)
      (Original.fold routing
        (Participant.owned self self
          (invoke (OriginalSumcheckLibrary.helpers program.payload).closed SumcheckHelperBodies.checkHelper)
          (.cons (some entries) (.cons (some point) (.cons (some scalar) .nil)))) state)
      (Domain.View.helper (ringModel F G) program SumcheckHelperBodies.checkHelper.name
        references [.data .boolean] environment) := by
  simp only [Participant.owned, ↓reduceIte, RoleFamily.sequence,
    Bind.bind, Pure.pure, Option.bind]
  rw [← (OriginalSumcheckLibrary.helpers_lift program.payload).closed,
    SumcheckVerifierHelpers.closed_invoke_plain]
  simp only []
  cases computed : invoke (closedMeanings (F := F) (G := G) program.payload.definitions)
      SumcheckHelperBodies.checkHelper (SumcheckHelperLaws.checkInputs entries point scalar) with
  | done result =>
    simp only [SumcheckHelperLaws.checkInputs] at computed
    cases result with
    | cons value rest =>
      cases rest
      have nominal := ZkcSecurity.Realizations.Sumcheck.DomainHelpers.call_return program
        SumcheckHelperBodies.checkHelper (SumcheckHelperLaws.checkInputs entries point scalar)
        (.cons value .nil) computed _ _ rfl rfl
      simp only [List.map_cons, List.map_nil] at nominal
      simp only [Domain.View.helper, read]
      rw [nominal]
      simp only [computed, PIR.Process.interpret, PIR.Process.bind, Values.present,
        Original.fold, PIR.Process.interpretState, Domain.View.append, Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty,
        List.map_cons, List.map_nil, beq_self_eq_true, ↓reduceIte]
      exact .done ⟨value, rfl, rfl⟩
  | halt reason =>
    simp only [SumcheckHelperLaws.checkInputs] at computed
    have present : SumcheckHelperBodies.checkHelper ∈
        program.payload.definitions.map CheckedDefinition.helper := by
      obtain ⟨definition, member, signature, _⟩ := bodies.check
      exact List.mem_map.mpr ⟨definition, member, signature⟩
    have nominal := helper_stopped program SumcheckHelperBodies.checkHelper
      (SumcheckHelperLaws.checkInputs entries point scalar) present _ rfl reason computed
    simp only [List.map_cons, List.map_nil] at nominal
    simp only [Domain.View.helper, read]
    rw [nominal]
    simp only [computed, PIR.Process.interpret, PIR.Process.bind, Original.fold,
      PIR.Process.interpretState]
    exact .halt reason
  | call operation _ => exact nomatch operation

end ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
