module

public import Zkc.Realization.RecordAllocator

@[expose] public section

/-! Ordered backend index requirements. These rules retain checked index ingress,
the exact SSA operands and every checkpoint, including the first failing requirement.
They do not identify a request or authorize a continuation on their own. -/
set_option autoImplicit false
namespace Zkc.Realization.RequiredIndices
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Check where
  left : Nat
  right : Nat
  site : String
  deriving DecidableEq, Repr

def instructions (start : Nat) : List Check → List Construction.Instruction
  | [] => []
  | requirement :: rest =>
      ⟨.execute .indexEqual, [requirement.left, requirement.right], [.data .boolean], []⟩ ::
      ⟨.require requirement.site, [start], [], []⟩ :: instructions (start + 1) rest

def spine (start : Nat) : List Check → ConnectionTargetPrefix.Prefix
  | [] => .empty
  | requirement :: rest =>
      .step (fun model ↦ Domain.View.execute model .indexEqual
        [requirement.left, requirement.right] [.data .boolean])
      (.step (fun _ ↦ Domain.View.require start []) (spine (start + 1) rest))

theorem correspondence (model : DomainModel) (program : Program) (context : Context)
    (start : Nat) (checks : List Check) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (instructions start checks) ((spine start checks).block model) := by
  induction checks generalizing start with
  | nil => exact Domain.Correspondence.empty
  | cons requirement rest ih =>
      exact Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
        (Domain.Correspondence.sequence (Domain.Correspondence.require _ _ _) (ih _))

/-- The actual two index operands, before any requirement has run. -/
inductive Readback {carriers : Carriers} (environment : Domain.Environment carriers) :
    List Check → List (Nat × Nat) → Prop where
  | nil : Readback environment [] []
  | cons {requirement : Check} {rest : List Check} {left right : Nat} {values : List (Nat × Nat)}
      (first : environment[requirement.left]? = some (.data (.index left)))
      (second : environment[requirement.right]? = some (.data (.index right)))
      (tail : Readback environment rest values) :
      Readback environment (requirement :: rest) ((left, right) :: values)

theorem Readback.extended {carriers : Carriers} {environment : Domain.Environment carriers}
    {checks : List Check} {values : List (Nat × Nat)}
    (readback : Readback environment checks values) (suffix : Domain.Environment carriers) :
    Readback (environment ++ suffix) checks values := by
  induction readback with
  | nil => exact .nil
  | cons first second tail ih =>
      exact .cons (Original.read_append first suffix) (Original.read_append second suffix) ih

def Accepted (values : List (Nat × Nat)) : Prop :=
  ∀ pair ∈ values, pair.1 < indexLimit ∧ pair.2 < indexLimit ∧ pair.1 = pair.2

instance (values : List (Nat × Nat)) : Decidable (Accepted values) :=
  inferInstanceAs (Decidable (∀ pair ∈ values,
    pair.1 < indexLimit ∧ pair.2 < indexLimit ∧ pair.1 = pair.2))

def results {carriers : Carriers} (count : Nat) : Domain.Environment carriers :=
  List.replicate count (.data (.boolean true))

private theorem comparison (model : DomainModel)
    (environment : Domain.Environment model.toCarriers) (requirement : Check) (left right : Nat)
    (first : environment[requirement.left]? = some (.data (.index left)))
    (second : environment[requirement.right]? = some (.data (.index right))) :
    Domain.View.execute model .indexEqual [requirement.left, requirement.right]
      [.data .boolean] environment =
      if left < indexLimit ∧ right < indexLimit then
        .done (environment ++ [.data (.boolean (decide (left = right)))])
      else .halt .refused := by
  have read : Domain.read environment [requirement.left, requirement.right] =
      Domain.encodeValues (tys := [.index, .index]) (.cons left (.cons right .nil)) := by
    simp [Domain.read, first, second, Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle]
  have law := ConnectionPrimitives.view_execute model .indexEqual
    (.cons left (.cons right .nil)) rfl rfl environment _ read
  by_cases bounds : left < indexLimit ∧ right < indexLimit <;>
    simpa [Primitive.results, Primitive.evaluateOn, checkedIndices, bounds,
      primitiveOutcome, PIR.Process.bind, Original.encodeHelperResult,
      Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
      Domain.Payload.ofValue, Ty.isHandle] using law

/-- The first failed requirement stops before every later requirement. Even a
reflexive comparison refuses an index outside the installed machine range. -/
theorem simulation (model : DomainModel)
    {environment : Domain.Environment model.toCarriers} {checks : List Check}
    {values : List (Nat × Nat)} (readback : Readback environment checks values)
    (captured : Domain.Environment model.toCarriers) (preserved : captured <+: environment) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ captured <+: frame)
      (if Accepted values then .done (environment ++ results checks.length) else .halt .refused)
      ((spine environment.length checks).block model environment)) := by
  induction checks generalizing environment values with
  | nil =>
      cases readback
      refine ⟨?_⟩
      simpa [Accepted, results, spine, ConnectionTargetPrefix.Prefix.block,
        ConnectionTargetPrefix.Prefix.plug, Domain.View.empty] using
        (Original.Simulation.done (returns := Eq) (live := fun _ frame ↦ captured <+: frame)
          (a := environment) rfl)
  | cons requirement rest ih =>
      cases readback with
      | @cons _ _ left right remaining first second tail =>
        obtain ⟨continued⟩ := ih (tail.extended [.data (.boolean true)])
          (preserved.trans (List.prefix_append _ _))
        refine ⟨?_⟩
        have compare := comparison model environment requirement left right first second
        change Original.Simulation _ _ _ (Domain.View.sequence _ _ environment)
        by_cases bounds : left < indexLimit ∧ right < indexLimit
        · simp only [bounds, and_self, ↓reduceIte] at compare
          by_cases equal : left = right
          · simp only [equal, decide_true] at compare
            let next := environment ++ [.data (.boolean true)]
            have guard : Domain.View.require environment.length [] next = .done next := by
              simp [Domain.View.require, next]
            have accepted : Accepted ((left, right) :: remaining) ↔ Accepted remaining := by
              simp [Accepted, bounds.2, equal]
            rw [Domain.View.sequence_return _ _ _ _ compare]
            refine .checkpoint _ preserved (.checkpoint _
              (preserved.trans (List.prefix_append _ _)) ?_)
            dsimp only [ConnectionTargetPrefix.Prefix.plug]
            rw [Domain.View.sequence_return _ _ _ _ guard]
            refine .checkpoint _ (preserved.trans (List.prefix_append _ _))
              (.checkpoint _ (preserved.trans (List.prefix_append _ _)) ?_)
            simp only [accepted]
            change Original.Simulation _ _
              (if Accepted remaining then .done
                (environment ++ (.data (.boolean true) :: results rest.length)) else .halt .refused)
              ((spine (environment.length + 1) rest).block model next)
            simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
              List.append_assoc, List.cons_append, List.nil_append] using continued
          · have rejected : ¬ Accepted ((left, right) :: remaining) := by
              intro accepted
              exact equal (accepted (left, right) (by simp)).2.2
            simp only [equal, decide_false] at compare
            simp only [rejected, ↓reduceIte]
            rw [Domain.View.sequence_return _ _ _ _ compare]
            refine .checkpoint _ preserved (.checkpoint _
              (preserved.trans (List.prefix_append _ _)) ?_)
            have guard : Domain.View.require environment.length []
                (environment ++ [.data (.boolean false)]) = .halt .refused := by
              simp [Domain.View.require]
            dsimp only [ConnectionTargetPrefix.Prefix.plug]
            rw [Domain.View.sequence_stop _ _ _ _ guard]
            exact .checkpoint _ (preserved.trans (List.prefix_append _ _)) (.halt .refused)
        · have rejected : ¬ Accepted ((left, right) :: remaining) := by
            intro accepted
            have both := accepted (left, right) (by simp)
            exact bounds ⟨both.1, both.2.1⟩
          simp only [bounds, ↓reduceIte] at compare
          simp only [rejected, ↓reduceIte]
          rw [Domain.View.sequence_stop _ _ _ _ compare]
          exact .checkpoint _ preserved (.halt .refused)

def constantInstructions (start left expected : Nat) (site : String) :
    List Construction.Instruction :=
  ⟨.execute (.indexConstant expected), [], [.data .index], []⟩ ::
    instructions (start + 1) [⟨left, start, site⟩]

def constantSpine (start left expected : Nat) (site : String) : ConnectionTargetPrefix.Prefix :=
  .step (fun model ↦ Domain.View.execute model (.indexConstant expected) [] [.data .index])
    (spine (start + 1) [⟨left, start, site⟩])

theorem constantCorrespondence (model : DomainModel) (program : Program) (context : Context)
    (start left expected : Nat) (site : String) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (constantInstructions start left expected site)
      ((constantSpine start left expected site).block model) :=
  Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
    (correspondence model program context _ _)

/-- The constant is checked before comparing the actual operand. The static
bound belongs to the installed controller layout, not to its dynamic state. -/
theorem constant (model : DomainModel)
    (environment captured : Domain.Environment model.toCarriers)
    (preserved : captured <+: environment)
    (left expected value : Nat) (site : String) (bounded : expected < indexLimit)
    (read : environment[left]? = some (.data (.index value))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ captured <+: frame)
      (if Accepted [(value, expected)] then
        .done (environment ++ [.data (.index expected), .data (.boolean true)]) else .halt .refused)
      ((constantSpine environment.length left expected site).block model environment)) := by
  let tag : Domain.Value model.toCarriers := .data (.index expected)
  have step : Domain.View.execute model (.indexConstant expected) [] [.data .index] environment =
      .done (environment ++ [tag]) := by
    have law := ConnectionPrimitives.view_execute model (.indexConstant expected)
      .nil rfl rfl environment [] rfl
    simpa [Primitive.results, Primitive.evaluateOn, bounded, primitiveOutcome,
      Original.encodeHelperResult, Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, tag, PIR.Process.bind] using law
  have decoded : Readback (environment ++ [tag]) [⟨left, environment.length, site⟩]
      [(value, expected)] :=
    .cons (Original.read_append read [tag]) (by simp [tag]) .nil
  obtain ⟨rest⟩ := simulation model decoded captured (preserved.trans (List.prefix_append _ _))
  refine ⟨?_⟩
  change Original.Simulation _ _ _ (Domain.View.sequence _ _ environment)
  rw [Domain.View.sequence_return _ _ _ _ step]
  refine .checkpoint _ preserved (.checkpoint _ (preserved.trans (List.prefix_append _ _)) ?_)
  simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
    Nat.zero_add, results, List.replicate_one, List.append_assoc, List.cons_append, List.nil_append,
    ConnectionTargetPrefix.Prefix.block, tag] using rest

end Zkc.Realization.RequiredIndices
