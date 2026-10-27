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
structured_associations GkrSourceViews
  [sourceHelper20 := GkrSourceBodies.sourceHelper20,
    sourceHelper37 := GkrSourceBodies.sourceHelper37,
    sourceHelper40 := GkrSourceBodies.sourceHelper40,
    sourceHelper50 := GkrSourceBodies.sourceHelper50,
    sourceHelper19 := GkrSourceBodies.sourceHelper19,
    sourceHelper84 := GkrSourceBodies.sourceHelper84,
    sourceHelper4 := GkrSourceBodies.sourceHelper4]

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

def booleanResult (result : Values (assignment F G) [.boolean]) : Domain.Environment (uniformCarriers F G) :=
  [.data (.boolean (result.get .here))]
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem booleanEncoding (result : Values (assignment F G) [.boolean]) :
    Domain.encodeValues result = some (booleanResult result) := by cases result with | cons value rest => cases rest; rfl
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem booleanSorts (result : Values (assignment F G) [.boolean]) :
    Domain.sortsMatch [.data (.boolean)] (booleanResult result) = true := rfl

def bind_boolean {A B : Type} {env : Domain.Environment (uniformCarriers F G)}
    {suffix : Domain.History (uniformCarriers F G)}
    {source : PIR.Process (Domain.effects (uniformCarriers F G))
      (Values (assignment F G) [.boolean] × Domain.History (uniformCarriers F G))}
    {target : PIR.Process (Domain.effects (uniformCarriers F G)) (Domain.Environment (uniformCarriers F G))}
    {sourceNext : (Values (assignment F G) [.boolean] × Domain.History (uniformCarriers F G)) →
      PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {targetNext : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G)) B}
    {relation : A → B → Prop}
    (head : Original.Simulation (HelperReturns booleanResult env suffix) (fun _ _ => True) source target)
    (next : ∀ (result0 : Bool), Original.Simulation relation (fun _ _ => True)
      (sourceNext ((.cons result0 .nil), suffix)) (targetNext (env ++ [.data (.boolean result0)]))) :
    Original.Simulation relation (fun _ _ => True) (source.bind sourceNext) (target.bind targetNext) := by
  apply Original.Simulation.bind head (by intros; trivial)
  intro original actual related
  apply Classical.choice
  obtain ⟨result, rfl, rfl⟩ := related
  cases result with | cons result0 rest =>
    cases rest; exact ⟨next result0⟩

def indexResult (result : Values (assignment F G) [.index]) : Domain.Environment (uniformCarriers F G) :=
  [.data (.index (result.get .here))]
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem indexEncoding (result : Values (assignment F G) [.index]) :
    Domain.encodeValues result = some (indexResult result) := by cases result with | cons value rest => cases rest; rfl
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem indexSorts (result : Values (assignment F G) [.index]) :
    Domain.sortsMatch [.data (.index)] (indexResult result) = true := rfl

def bind_index {A B : Type} {env : Domain.Environment (uniformCarriers F G)}
    {suffix : Domain.History (uniformCarriers F G)}
    {source : PIR.Process (Domain.effects (uniformCarriers F G))
      (Values (assignment F G) [.index] × Domain.History (uniformCarriers F G))}
    {target : PIR.Process (Domain.effects (uniformCarriers F G)) (Domain.Environment (uniformCarriers F G))}
    {sourceNext : (Values (assignment F G) [.index] × Domain.History (uniformCarriers F G)) →
      PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {targetNext : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G)) B}
    {relation : A → B → Prop}
    (head : Original.Simulation (HelperReturns indexResult env suffix) (fun _ _ => True) source target)
    (next : ∀ (result0 : Nat), Original.Simulation relation (fun _ _ => True)
      (sourceNext ((.cons result0 .nil), suffix)) (targetNext (env ++ [.data (.index result0)]))) :
    Original.Simulation relation (fun _ _ => True) (source.bind sourceNext) (target.bind targetNext) := by
  apply Original.Simulation.bind head (by intros; trivial)
  intro original actual related
  apply Classical.choice
  obtain ⟨result, rfl, rfl⟩ := related
  cases result with | cons result0 rest =>
    cases rest; exact ⟨next result0⟩

def vectorsResult (result : Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"]) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" (result.get .here)), .data (.vector "bls12-381.fr" (result.get (.there .here)))]
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem vectorsEncoding (result : Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"]) :
    Domain.encodeValues result = some (vectorsResult result) := by cases result with | cons value rest => cases rest with | cons other rest => cases rest; rfl
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem vectorsSorts (result : Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"]) :
    Domain.sortsMatch [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr")] (vectorsResult result) = true := rfl

def bind_vectors {A B : Type} {env : Domain.Environment (uniformCarriers F G)}
    {suffix : Domain.History (uniformCarriers F G)}
    {source : PIR.Process (Domain.effects (uniformCarriers F G))
      (Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"] × Domain.History (uniformCarriers F G))}
    {target : PIR.Process (Domain.effects (uniformCarriers F G)) (Domain.Environment (uniformCarriers F G))}
    {sourceNext : (Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"] × Domain.History (uniformCarriers F G)) →
      PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {targetNext : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G)) B}
    {relation : A → B → Prop}
    (head : Original.Simulation (HelperReturns vectorsResult env suffix) (fun _ _ => True) source target)
    (next : ∀ (result0 : List F) (result1 : List F), Original.Simulation relation (fun _ _ => True)
      (sourceNext ((.cons result0 (.cons result1 .nil)), suffix)) (targetNext (env ++ [.data (.vector "bls12-381.fr" result0), .data (.vector "bls12-381.fr" result1)]))) :
    Original.Simulation relation (fun _ _ => True) (source.bind sourceNext) (target.bind targetNext) := by
  apply Original.Simulation.bind head (by intros; trivial)
  intro original actual related
  apply Classical.choice
  obtain ⟨result, rfl, rfl⟩ := related
  cases result with | cons result0 rest =>
    cases rest with | cons result1 rest =>
      cases rest; exact ⟨next result0 result1⟩

def stateResult (result : Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr"]) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" (result.get .here)), .data (.field "bls12-381.fr" (result.get (.there .here)))]
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem stateEncoding (result : Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr"]) :
    Domain.encodeValues result = some (stateResult result) := by cases result with | cons value rest => cases rest with | cons other rest => cases rest; rfl
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem stateSorts (result : Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr"]) :
    Domain.sortsMatch [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")] (stateResult result) = true := rfl

def bind_state {A B : Type} {env : Domain.Environment (uniformCarriers F G)}
    {suffix : Domain.History (uniformCarriers F G)}
    {source : PIR.Process (Domain.effects (uniformCarriers F G))
      (Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr"] × Domain.History (uniformCarriers F G))}
    {target : PIR.Process (Domain.effects (uniformCarriers F G)) (Domain.Environment (uniformCarriers F G))}
    {sourceNext : (Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr"] × Domain.History (uniformCarriers F G)) →
      PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {targetNext : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G)) B}
    {relation : A → B → Prop}
    (head : Original.Simulation (HelperReturns stateResult env suffix) (fun _ _ => True) source target)
    (next : ∀ (result0 : List F) (result1 : F), Original.Simulation relation (fun _ _ => True)
      (sourceNext ((.cons result0 (.cons result1 .nil)), suffix)) (targetNext (env ++ [.data (.vector "bls12-381.fr" result0), .data (.field "bls12-381.fr" result1)]))) :
    Original.Simulation relation (fun _ _ => True) (source.bind sourceNext) (target.bind targetNext) := by
  apply Original.Simulation.bind head (by intros; trivial)
  intro original actual related
  apply Classical.choice
  obtain ⟨result, rfl, rfl⟩ := related
  cases result with | cons result0 rest =>
    cases rest with | cons result1 rest =>
      cases rest; exact ⟨next result0 result1⟩

/-- Exact current closed helper call, including every stopped outcome. -/
def unpackState (point : List F) (claim : F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" claim)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns stateResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.sourceHelper20Helper (.cons point (.cons claim .nil))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.sourceHelper20Helper.name refs
        (GkrSourceBodies.sourceHelper20Helper.outputs.map ValueSort.data) env).interpret operations) := by
  have present : GkrSourceBodies.sourceHelper20Helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := sourceHelper20_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.sourceHelper20Helper present (.cons point (.cons claim .nil)) _ rfl stateResult
    stateEncoding stateSorts env refs read suffix

/-- Exact current closed helper call, including every stopped outcome. -/
def pending (claim : F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.field "bls12-381.fr" claim)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns stateResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.sourceHelper37Helper (.cons claim .nil)) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.sourceHelper37Helper.name refs
        (GkrSourceBodies.sourceHelper37Helper.outputs.map ValueSort.data) env).interpret operations) := by
  have present : GkrSourceBodies.sourceHelper37Helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := sourceHelper37_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.sourceHelper37Helper present (.cons claim .nil) _ rfl stateResult
    stateEncoding stateSorts env refs read suffix

/-- Exact current closed helper call, including every stopped outcome. -/
def openPending (point : List F) (claim : F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" claim)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns stateResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.sourceHelper40Helper (.cons point (.cons claim .nil))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.sourceHelper40Helper.name refs
        (GkrSourceBodies.sourceHelper40Helper.outputs.map ValueSort.data) env).interpret operations) := by
  have present : GkrSourceBodies.sourceHelper40Helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := sourceHelper40_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.sourceHelper40Helper present (.cons point (.cons claim .nil)) _ rfl stateResult
    stateEncoding stateSorts env refs read suffix

/-- Exact current closed helper call, including every stopped outcome. -/
def split (point : List F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" point)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns vectorsResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.sourceHelper50Helper (.cons point .nil)) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.sourceHelper50Helper.name refs
        (GkrSourceBodies.sourceHelper50Helper.outputs.map ValueSort.data) env).interpret operations) := by
  have present : GkrSourceBodies.sourceHelper50Helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := sourceHelper50_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.sourceHelper50Helper present (.cons point .nil) _ rfl vectorsResult
    vectorsEncoding vectorsSorts env refs read suffix

/-- Exact current closed helper call, including every stopped outcome. -/
def packState (point : List F) (claim : F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" claim)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns stateResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.sourceHelper19Helper (.cons point (.cons claim .nil))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.sourceHelper19Helper.name refs
        (GkrSourceBodies.sourceHelper19Helper.outputs.map ValueSort.data) env).interpret operations) := by
  have present : GkrSourceBodies.sourceHelper19Helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := sourceHelper19_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.sourceHelper19Helper present (.cons point (.cons claim .nil)) _ rfl stateResult
    stateEncoding stateSorts env refs read suffix

/-- Exact current closed helper call, including every stopped outcome. -/
def terminal (inputs : List F) (point : List F) (claim : F) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" inputs), .data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" claim)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns booleanResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.sourceHelper84Helper (.cons inputs (.cons point (.cons claim .nil)))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.sourceHelper84Helper.name refs
        (GkrSourceBodies.sourceHelper84Helper.outputs.map ValueSort.data) env).interpret operations) := by
  have present : GkrSourceBodies.sourceHelper84Helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := sourceHelper84_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.sourceHelper84Helper present (.cons inputs (.cons point (.cons claim .nil))) _ rfl booleanResult
    booleanEncoding booleanSorts env refs read suffix

/-- Exact current closed helper call, including every stopped outcome. -/
def less (left : Nat) (right : Nat) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.index left), .data (.index right)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns booleanResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.helper2Helper (.cons left (.cons right .nil))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.helper2Helper.name refs
        (GkrSourceBodies.helper2Helper.outputs.map ValueSort.data) env).interpret operations) := by
  have present : GkrSourceBodies.helper2Helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := GkrSourceLaws.helper2_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.helper2Helper present (.cons left (.cons right .nil)) _ rfl booleanResult
    booleanEncoding booleanSorts env refs read suffix

/-- Exact current closed helper call, including every stopped outcome. -/
def shape (values : List F) (dimension : Nat) (arity : Nat) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.vector "bls12-381.fr" values), .data (.index dimension), .data (.index arity)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns booleanResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.helper4Helper (.cons values (.cons dimension (.cons arity .nil)))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.helper4Helper.name refs
        (GkrSourceBodies.helper4Helper.outputs.map ValueSort.data) env).interpret operations) := by
  have present : GkrSourceBodies.helper4Helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := GkrSourceLaws.helper4_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.helper4Helper present (.cons values (.cons dimension (.cons arity .nil))) _ rfl booleanResult
    booleanEncoding booleanSorts env refs read suffix

/-- Exact current closed helper call, including every stopped outcome. -/
def indexAdd (left : Nat) (right : Nat) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.index left), .data (.index right)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns indexResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.sourceHelper4Helper (.cons left (.cons right .nil))) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.sourceHelper4Helper.name refs
        (GkrSourceBodies.sourceHelper4Helper.outputs.map ValueSort.data) env).interpret operations) := by
  have present : GkrSourceBodies.sourceHelper4Helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := sourceHelper4_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.sourceHelper4Helper present (.cons left (.cons right .nil)) _ rfl indexResult
    indexEncoding indexSorts env refs read suffix

/-- Exact current closed helper call, including every stopped outcome. -/
def power (exponent : Nat) (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat)
    (read : Domain.read env refs = some [.data (.index exponent)]) (suffix : Domain.History (uniformCarriers F G)) :
    Original.Simulation (HelperReturns indexResult env suffix) (fun _ _ => True)
      (SourceProcess.sourceView context (helper GkrSourceBodies.helper18Helper (.cons exponent .nil)) suffix)
      ((Domain.View.helper (ringModel F G) program GkrSourceBodies.helper18Helper.name refs
        (GkrSourceBodies.helper18Helper.outputs.map ValueSort.data) env).interpret operations) := by
  have present : GkrSourceBodies.helper18Helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := GkrSourceLaws.helper18_association
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  exact helper_binding GkrSourceBodies.helper18Helper present (.cons exponent .nil) _ rfl indexResult
    indexEncoding indexSorts env refs read suffix

theorem tuple40_source (point : List F) (claim : F) :
    helper (F := F) (G := G) GkrSourceBodies.sourceHelper40Helper (.cons point (.cons claim .nil)) =
      .done (.cons point (.cons claim .nil)) := by
  unfold helper
  rw [GkrRoundsReading.invoke_law _ _ _ (by
    rw [sourceHelper40_association.invoke GkrSourceViews.unit.linked]
    rfl)]
  rfl

theorem tuple40 (point : List F) (claim : F) :
    Domain.callHelper (ringModel F G) program "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825" [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")] [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" claim)] = .returned [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" claim)] :=
  ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.call_return program GkrSourceBodies.sourceHelper40Helper
    (.cons point (.cons claim .nil)) (.cons point (.cons claim .nil))
    (by kernel_rfl) _ _ rfl rfl

theorem tuple40_view (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat) :
    Domain.View.helper (ringModel F G) program "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825" refs [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")] env =
    match Domain.read env refs with
    | some arguments =>
      match Domain.callHelper (ringModel F G) program "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825" [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")] arguments with
      | .returned outputs => Domain.View.append [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")] env outputs
      | .stopped reason => .halt reason
    | none => .halt .refused := by kernel_rfl

theorem tuple49 (point : List F) (claim : F) :
    Domain.callHelper (ringModel F G) program "zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3" [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")] [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" claim)] = .returned [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" claim)] :=
  ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.call_return program GkrSourceBodies.sourceHelper49Helper
    (.cons point (.cons claim .nil)) (.cons point (.cons claim .nil))
    (by kernel_rfl) _ _ rfl rfl

theorem tuple49_view (env : Domain.Environment (uniformCarriers F G)) (refs : List Nat) :
    Domain.View.helper (ringModel F G) program "zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3" refs [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")] env =
    match Domain.read env refs with
    | some arguments =>
      match Domain.callHelper (ringModel F G) program "zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3" [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")] arguments with
      | .returned outputs => Domain.View.append [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")] env outputs
      | .stopped reason => .halt reason
    | none => .halt .refused := by kernel_rfl

end ZkcExamples.Construction.GkrDomainHelperCalls
