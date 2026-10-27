module

public import ZkcExamples.Construction.GkrDomainHelpers

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrDomainHelperCalls
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol GkrDomainHelpers
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Compose the singleton field ABI with every helper outcome and every
continued result, without inverting a projected transcript. -/
def bind_field {A B : Type} {env : Domain.Environment (uniformCarriers F G)}
    {suffix : Domain.History (uniformCarriers F G)}
    {source : PIR.Process (Domain.effects (uniformCarriers F G))
      (Values (assignment F G) [.field "bls12-381.fr"] × Domain.History (uniformCarriers F G))}
    {target : PIR.Process (Domain.effects (uniformCarriers F G)) (Domain.Environment (uniformCarriers F G))}
    {sourceNext : (Values (assignment F G) [.field "bls12-381.fr"] × Domain.History (uniformCarriers F G)) →
      PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {targetNext : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G)) B}
    {relation : A → B → Prop}
    (head : Original.Simulation (HelperReturns fieldResult env suffix) (fun _ _ => True) source target)
    (next : ∀ result : F, Original.Simulation relation (fun _ _ => True)
      (sourceNext (.cons result .nil, suffix))
      (targetNext (env ++ [.data (.field "bls12-381.fr" result)]))) :
    Original.Simulation relation (fun _ _ => True) (source.bind sourceNext) (target.bind targetNext) := by
  apply Original.Simulation.bind head (by intros; trivial)
  intro original actual related
  apply Classical.choice
  obtain ⟨result, rfl, rfl⟩ := related
  cases result with
  | cons result rest => cases rest; exact ⟨next result⟩

/-- Compose the singleton vector ABI with every helper outcome and every
continued result, without inverting a projected transcript. -/
def bind_vector {A B : Type} {env : Domain.Environment (uniformCarriers F G)}
    {suffix : Domain.History (uniformCarriers F G)}
    {source : PIR.Process (Domain.effects (uniformCarriers F G))
      (Values (assignment F G) [.vector "bls12-381.fr"] × Domain.History (uniformCarriers F G))}
    {target : PIR.Process (Domain.effects (uniformCarriers F G)) (Domain.Environment (uniformCarriers F G))}
    {sourceNext : (Values (assignment F G) [.vector "bls12-381.fr"] × Domain.History (uniformCarriers F G)) →
      PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {targetNext : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G)) B}
    {relation : A → B → Prop}
    (head : Original.Simulation (HelperReturns vectorResult env suffix) (fun _ _ => True) source target)
    (next : ∀ result : List F, Original.Simulation relation (fun _ _ => True)
      (sourceNext (.cons result .nil, suffix))
      (targetNext (env ++ [.data (.vector "bls12-381.fr" result)]))) :
    Original.Simulation relation (fun _ _ => True) (source.bind sourceNext) (target.bind targetNext) := by
  apply Original.Simulation.bind head (by intros; trivial)
  intro original actual related
  apply Classical.choice
  obtain ⟨result, rfl, rfl⟩ := related
  cases result with
  | cons result rest => cases rest; exact ⟨next result⟩

/-- The two total structural helpers reduce through their checked closed
source equations; other helper calls stay as certificate boundaries. -/
theorem empty_view (env : Domain.Environment (uniformCarriers F G)) :
    Domain.View.helper (ringModel F G) program
      "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f" []
      [.data (.vector "bls12-381.fr")] env =
        .done (env ++ [.data (.vector "bls12-381.fr" [])]) := by
  simp only [Domain.View.helper, Domain.read, List.mapM_nil, Option.pure_def]
  erw [GkrDomainHelpers.empty (F := F) (G := G)]
  rfl

theorem append_view (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (point : List F) (scalar : F)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" point),
      .data (.field "bls12-381.fr" scalar)]) :
    Domain.View.helper (ringModel F G) program
      "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d" refs
      [.data (.vector "bls12-381.fr")] env =
        .done (env ++ [.data (.vector "bls12-381.fr" (point ++ [scalar]))]) := by
  simp only [Domain.View.helper, read]
  erw [GkrDomainHelpers.append (F := F) (G := G)]
  rfl

/-- Unfold only the checked append helper view, leaving unrelated helper
calls available for their source simulation certificates. -/
theorem append_view_read (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat) :
    Domain.View.helper (ringModel F G) program
      "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d" refs
      [.data (.vector "bls12-381.fr")] env =
    match Domain.read env refs with
    | some arguments =>
      match Domain.callHelper (ringModel F G) program
        "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d"
        [.data (.vector "bls12-381.fr")] arguments with
      | .returned outputs => Domain.View.append [.data (.vector "bls12-381.fr")] env outputs
      | .stopped reason => .halt reason
    | none => .halt .refused := by kernel_rfl

/-- Exact sum call, retaining every closed-source outcome. -/
def sum (xs : List F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" xs)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns fieldResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.sumHelper (.cons xs .nil)) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.sumHelper.name refs
        [.data (.field "bls12-381.fr")] env).interpret operations) := by
  have present : GkrSourceBodies.sumHelper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := GkrSourceLaws.sum_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.sumHelper present (.cons xs .nil) _ rfl fieldResult
    fieldEncoding fieldSorts env refs read suffix

/-- Exact evaluate call, retaining every closed-source outcome. -/
def evaluate (xs point : List F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" xs), .data (.vector "bls12-381.fr" point)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns fieldResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.evaluateHelper (.cons xs (.cons point .nil))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.evaluateHelper.name refs
        [.data (.field "bls12-381.fr")] env).interpret operations) := by
  have present : GkrSourceBodies.evaluateHelper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := GkrSourceLaws.evaluate_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.evaluateHelper present (.cons xs (.cons point .nil)) _ rfl fieldResult
    fieldEncoding fieldSorts env refs read suffix

/-- Exact selectBlock call, retaining every closed-source outcome. -/
def selectBlock (xs : List F) (index selector : Nat) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" xs), .data (.index index), .data (.index selector)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns vectorResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.selectBlockHelper (.cons xs (.cons index (.cons selector .nil)))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.selectBlockHelper.name refs
        [.data (.vector "bls12-381.fr")] env).interpret operations) := by
  have present : GkrSourceBodies.selectBlockHelper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := GkrSourceLaws.selectBlock_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.selectBlockHelper present (.cons xs (.cons index (.cons selector .nil))) _ rfl vectorResult
    vectorEncoding vectorSorts env refs read suffix

/-- Exact evaluateWiring call, retaining every closed-source outcome. -/
def evaluateWiring (xs point left right : List F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" xs), .data (.vector "bls12-381.fr" point), .data (.vector "bls12-381.fr" left), .data (.vector "bls12-381.fr" right)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns fieldResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.evaluateWiringHelper (.cons xs (.cons point (.cons left (.cons right .nil))))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.evaluateWiringHelper.name refs
        [.data (.field "bls12-381.fr")] env).interpret operations) := by
  have present : GkrSourceBodies.evaluateWiringHelper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := GkrSourceLaws.evaluateWiring_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.evaluateWiringHelper present (.cons xs (.cons point (.cons left (.cons right .nil)))) _ rfl fieldResult
    fieldEncoding fieldSorts env refs read suffix

/-- Exact evaluateCoefficients call, retaining every closed-source outcome. -/
def evaluateCoefficients (xs : List F) (challenge : F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" xs), .data (.field "bls12-381.fr" challenge)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns fieldResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.evaluateCoefficientsHelper (.cons xs (.cons challenge .nil))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.evaluateCoefficientsHelper.name refs
        [.data (.field "bls12-381.fr")] env).interpret operations) := by
  have present : GkrSourceBodies.evaluateCoefficientsHelper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := GkrSourceLaws.evaluateCoefficients_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.evaluateCoefficientsHelper present (.cons xs (.cons challenge .nil)) _ rfl fieldResult
    fieldEncoding fieldSorts env refs read suffix

/-- Exact linePoint call, retaining every closed-source outcome. -/
def linePoint (left right : List F) (challenge : F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" left), .data (.vector "bls12-381.fr" right), .data (.field "bls12-381.fr" challenge)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns vectorResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.linePointHelper (.cons left (.cons right (.cons challenge .nil)))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.linePointHelper.name refs
        [.data (.vector "bls12-381.fr")] env).interpret operations) := by
  have present : GkrSourceBodies.linePointHelper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := GkrSourceLaws.linePoint_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.linePointHelper present (.cons left (.cons right (.cons challenge .nil))) _ rfl vectorResult
    vectorEncoding vectorSorts env refs read suffix

end ZkcExamples.Construction.GkrDomainHelperCalls
