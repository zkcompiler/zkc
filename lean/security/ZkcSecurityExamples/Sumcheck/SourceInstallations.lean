module

public import ZkcSecurityExamples.Sumcheck.SourceRootProperties
public import Zkc.Source.Structured.ComponentClosure

@[expose] public section

/-! Actual SmallSumcheck and TwoSums mathematical consumers. Instance work is
source/input/context selection; both uses share the library, round mathematics,
symbolic reduction and family Representation. This does not construct a receipt. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceInstallations
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration SourceRootProperties
open SumcheckSourceSelections hiding field
attribute [local implicit_reducible] NormalForm.InputPattern.scope SourceRootReference.pattern

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame E P : Type} {Raw : E → Type}

/-- Data selection installs the shared conditional sampling theorem. The result
still requires the actual reached-history collision law and query cuts. -/
def selected_sampled (selection : Selection) :=
  sampled_contract model (Frame := Frame) (E := E) (P := P) (Raw := Raw)
    (source selection).payload.definitions (source selection).payload.linked (roundBodies selection)
    (Occurrence.table model (source selection).payload)

/-- Conditional validator-handler execution uses the installed body laws.
This supplies no producer/validator pair alignment. Full source-pair results
are owned by `SourcePairInstallations`. -/
abbrev selected_honest {H : Type} (selection : Selection) :=
  honest_contract model (Frame := Frame) (E := E) (H := H)
    (source selection).payload.definitions (source selection).payload.linked (roundBodies selection)
    (Occurrence.table model (source selection).payload)

def returned (selection : Selection) (accepted : Option Bool) :
    Values (Component model.Value) (source selection).payload.entry.outputs :=
  match selection with
  | .small => .cons accepted .nil
  | .twoSums => .cons accepted .nil

omit fieldLaw in
/-- The optional-component invocation of the actual shared Boolean helper. -/
theorem both_return (a b : Bool) :
    (invoke (tables model (source .twoSums).payload.definitions).components
      Generated.Bindings.TwoSumsInputs.helper25Helper (.cons (some a) (.cons (some b) .nil))).bind
      (fun accepted => .done (.cons (accepted.get .here) .nil : Values (Component model.Value) [.boolean])) =
      .done (.cons (some (a && b)) .nil) := by
  have adequate := Evaluation.ComponentTablesOn.adequate_fold model
    (.silent (Occurrence.signature model.toCarriers)) ⟨[],[]⟩
    (Evaluation.ComponentTablesOn.adequate_empty model) (source .twoSums).payload.definitions
  have invoked := adequate Generated.Bindings.TwoSumsInputs.helper25Helper (.cons a (.cons b .nil))
  change invoke (tables model (source .twoSums).payload.definitions).components
    Generated.Bindings.TwoSumsInputs.helper25Helper (.cons (some a) (.cons (some b) .nil)) = _ at invoked
  rw [invoked, (Sum.both model).invokeOn (model := model)
    (helper := Generated.Bindings.TwoSumsInputs.helper25Helper)
    _ (source .twoSums).payload.linked (bothBody model) (.cons a (.cons b .nil)) trivial]
  rfl

section Small
variable (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
  (callerFrame : Frame) (shape : original.length = 2^count) (bounded : count ≤ maximum .small)
  (small : count < 64) (finite : original.length < indexLimit)
include callerFrame shape bounded small finite

/-- Full actual admitted SmallSumcheck source, at arbitrary incoming history. -/
def small_no (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw)
    (steps : RepeatedComponent.NoContract
      (component model (source .small).payload.definitions (Occurrence.table model (source .small).payload)
        (context "label_726564756365") handle) absorb escape (no model original callerFrame))
    (wrong : scalar ≠ original.sum) (history : List E) :
    Derivation absorb escape (fun _ out => out = returned model .small (some false)) history
      (Occurrence.participant model (source .small) 1
        (SourceRootReference.rootInputs model .small
          (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil)))))) := by
  let args : NormalForm.Binders model (SourceRootReference.pattern .small).scope :=
    .cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil)))
  change Derivation absorb escape _ history
    (Occurrence.participant model (source .small) 1 (SourceRootReference.rootInputs model .small args))
  rw [SourceRootReference.actual_reference model .small args]
  change Derivation absorb escape (fun _ (out : Values (Component model.Value) [.boolean]) =>
    out = .cons (some false) .nil) history _
  exact (one_no model .small "label_726564756365" original count handle scalar callerFrame shape bounded small finite
    absorb escape steps wrong history).bind _ (by
      intro reached out rejected
      apply Derivation.done
      rw [rejected])

/-- Successful validator execution conditional on the supplied handler contract;
the actual honest pair is proved separately in `SourcePairInstallations.small`. -/
theorem small_honest {H : Type}
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (good : List E → Runtime model Frame → H → Prop)
    (steps : RepeatedComponent.HonestContract
      (component model (source .small).payload.definitions (Occurrence.table model (source .small).payload)
        (context "label_726564756365") handle) handler (honest model good original callerFrame))
    (history : List E) (h : H)
    (initial : honest model good original callerFrame history count
      (encode model 0 (PrefixState.initial original count scalar callerFrame shape)) h) :
    PIR.WeakestPrecondition.satisfies
      ((Occurrence.participant model (source .small) 1
        (SourceRootReference.rootInputs model .small
          (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil)))))).run handler h)
      (fun out _ _ => out = returned model .small (some true)) (fun _ _ _ => False) history := by
  let args : NormalForm.Binders model (SourceRootReference.pattern .small).scope :=
    .cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil)))
  change PIR.WeakestPrecondition.satisfies
    ((Occurrence.participant model (source .small) 1 (SourceRootReference.rootInputs model .small args)).run handler h)
    _ _ history
  rw [SourceRootReference.actual_reference model .small args]
  change PIR.WeakestPrecondition.satisfies
    (_ : PIR.Execution H E (Values (Component model.Value) [.boolean]))
    (fun out _ _ => out = .cons (some true) .nil) (fun _ _ _ => False) history
  exact PIR.WeakestPrecondition.successful_bind _ _ _ _ _ _ _
    (one_honest model .small "label_726564756365" original count handle scalar callerFrame shape bounded small finite
      handler good steps history h initial) (by
        intro out final reached accepted
        change Values.cons out Values.nil = Values.cons (some true) Values.nil
        rw [accepted])
end Small

section Pair
variable (left right : List (model.Field field)) (count handle : Nat) (a b : model.Field field)
  (callerFrame : Frame) (leftShape : left.length = 2^count) (rightShape : right.length = 2^count)
  (bounded : count ≤ maximum .twoSums) (small : count < 64)
  (leftFinite : left.length < indexLimit) (rightFinite : right.length < indexLimit)
include callerFrame leftShape rightShape bounded small leftFinite rightFinite

/-- No for a conjunction needs only one false conjunct. The other invocation
uses an independent all-replies frame and an explicit empty-event escape law;
no independence between the two discoveries or the sampling metadata is assumed. -/
def two_no (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw) (empty : ∀ reached event, escape reached event (fun _ => False))
    (leftSteps : RepeatedComponent.NoContract
      (component model (source .twoSums).payload.definitions (Occurrence.table model (source .twoSums).payload)
        (context "label_6c656674") handle) absorb escape (no model left callerFrame))
    (rightSteps : RepeatedComponent.NoContract
      (component model (source .twoSums).payload.definitions (Occurrence.table model (source .twoSums).payload)
        (context "label_7269676874") handle) absorb escape (no model right callerFrame))
    (wrong : ¬ (a = left.sum ∧ b = right.sum)) (history : List E) :
    Derivation absorb escape (fun _ out => out = returned model .twoSums (some false)) history
      (Occurrence.participant model (source .twoSums) 1
        (SourceRootReference.rootInputs model .twoSums
          (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
            (.cons (some count) (.cons (some handle) .nil)))))))) := by
  let args : NormalForm.Binders model (SourceRootReference.pattern .twoSums).scope :=
    .cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
      (.cons (some count) (.cons (some handle) .nil)))))
  change Derivation absorb escape _ history
    (Occurrence.participant model (source .twoSums) 1 (SourceRootReference.rootInputs model .twoSums args))
  rw [SourceRootReference.actual_reference model .twoSums args]
  change Derivation absorb escape (fun _ (out : Values (Component model.Value) [.boolean]) =>
    out = .cons (some false) .nil) history _
  by_cases leftWrong : a ≠ left.sum
  · exact (one_no model .twoSums "label_6c656674" left count handle a callerFrame leftShape bounded small leftFinite
      absorb escape leftSteps leftWrong history).bind _ (by
        intro reached first rejected
        rw [rejected]
        exact (Derivation.ofYields empty
          (one_present model .twoSums "label_7269676874" right count handle b callerFrame rightShape bounded small rightFinite)
          reached).bind _ (by
            intro final second present
            let accepted := Classical.choose present
            have same : second = some accepted := Classical.choose_spec present
            rw [same]
            exact Eq.mpr (congrArg (fun process => Derivation absorb escape
              (fun _ out => out = Values.cons (some false) Values.nil) final process)
                (both_return model false accepted)) (.done rfl)))
  · have rightWrong : b ≠ right.sum := fun rightTrue => wrong ⟨by simpa using leftWrong, rightTrue⟩
    exact (Derivation.ofYields empty
      (one_present model .twoSums "label_6c656674" left count handle a callerFrame leftShape bounded small leftFinite)
      history).bind _ (by
        intro reached first present
        let accepted := Classical.choose present
        have same : first = some accepted := Classical.choose_spec present
        rw [same]
        exact (one_no model .twoSums "label_7269676874" right count handle b callerFrame rightShape bounded small rightFinite
          absorb escape rightSteps rightWrong reached).bind _ (by
            intro final second rejected
            rw [rejected]
            exact Eq.mpr (congrArg (fun process => Derivation absorb escape
              (fun _ out => out = Values.cons (some false) Values.nil) final process)
                (both_return model accepted false)) (.done (by cases accepted <;> rfl))))

/-- Conditional validator execution and synchronization, rather than a pair
completeness claim. `SourcePairInstallations.two` supplies the actual pair. -/
theorem two_honest {H : Type}
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (leftGood rightGood : List E → Runtime model Frame → H → Prop)
    (leftSteps : RepeatedComponent.HonestContract
      (component model (source .twoSums).payload.definitions (Occurrence.table model (source .twoSums).payload)
        (context "label_6c656674") handle) handler (honest model leftGood left callerFrame))
    (rightSteps : RepeatedComponent.HonestContract
      (component model (source .twoSums).payload.definitions (Occurrence.table model (source .twoSums).payload)
        (context "label_7269676874") handle) handler (honest model rightGood right callerFrame))
    (history : List E) (h : H)
    (initial : honest model leftGood left callerFrame history count
      (encode model 0 (PrefixState.initial left count a callerFrame leftShape)) h)
    (synchronize : ∀ reached runtime final, honest model leftGood left callerFrame reached 0 runtime final →
      honest model rightGood right callerFrame reached count
        (encode model 0 (PrefixState.initial right count b callerFrame rightShape)) final) :
    PIR.WeakestPrecondition.satisfies
      ((Occurrence.participant model (source .twoSums) 1
        (SourceRootReference.rootInputs model .twoSums
          (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
            (.cons (some count) (.cons (some handle) .nil)))))))).run handler h)
      (fun out _ _ => out = returned model .twoSums (some true)) (fun _ _ _ => False) history := by
  let args : NormalForm.Binders model (SourceRootReference.pattern .twoSums).scope :=
    .cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
      (.cons (some count) (.cons (some handle) .nil)))))
  change PIR.WeakestPrecondition.satisfies
    ((Occurrence.participant model (source .twoSums) 1 (SourceRootReference.rootInputs model .twoSums args)).run handler h)
    _ _ history
  rw [SourceRootReference.actual_reference model .twoSums args]
  change PIR.WeakestPrecondition.satisfies
    (_ : PIR.Execution H E (Values (Component model.Value) [.boolean]))
    (fun out _ _ => out = .cons (some true) .nil) (fun _ _ _ => False) history
  have first := one_honest_preserving model .twoSums "label_6c656674" left count handle a callerFrame
    leftShape bounded small leftFinite handler leftGood leftSteps history h initial
    (fun final reached => honest model rightGood right callerFrame reached count
      (encode model 0 (PrefixState.initial right count b callerFrame rightShape)) final) synchronize
  apply PIR.WeakestPrecondition.successful_bind _ _ _ _ _ _ _ first
  intro leftAccepted final reached valid
  rw [valid.1]
  have second := one_honest model .twoSums "label_7269676874" right count handle b callerFrame
    rightShape bounded small rightFinite handler rightGood rightSteps reached final valid.2
  apply PIR.WeakestPrecondition.successful_bind _ _ _ _ _ _ _ second
  intro rightAccepted final reached accepted
  rw [accepted]
  exact Eq.mpr (congrArg (fun process => PIR.WeakestPrecondition.satisfies (process.run handler final)
    (fun out _ _ => out = Values.cons (some true) Values.nil) (fun _ _ _ => False) reached)
      (both_return model true true)) rfl
end Pair

#print axioms small_no
#print axioms small_honest
#print axioms two_no
#print axioms two_honest
end ZkcSecurity.Realizations.Sumcheck.SourceInstallations
