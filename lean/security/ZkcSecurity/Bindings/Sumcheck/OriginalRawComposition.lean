module

public import ZkcSecurity.Bindings.Sumcheck.RootContract

@[expose] public section

/-! Finite source-order composition over the existing Process.bind. The spine
threads the actual construction state; the pure terminal tree records checked
caller dataflow. Neither structure interprets protocol operations. -/
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.FiatShamir ZkcSecurity.Obligations
open ZkcSecurity.Families.Sumcheck TableComponent
variable {F G : Type} [Field F] [DecidableEq F]

abbrev Verdicts := List (Option Bool)
inductive Conjunction where
  | leaf (index : Nat)
  | and (left right : Conjunction)
  deriving Repr, BEq

namespace Conjunction
@[simp] def leaves : Conjunction → List Nat
  | .leaf index => [index]
  | .and left right => left.leaves ++ right.leaves
@[simp] def evaluate : Conjunction → Verdicts → Option Bool
  | .leaf index, values => (values[index]?).join
  | .and left right, values =>
      (left.evaluate values).bind fun a => (right.evaluate values).map fun b => a && b

theorem evaluate_true (tree : Conjunction) (values : Verdicts)
    (accepted : tree.evaluate values = some true) :
    ∀ index ∈ tree.leaves, values[index]? = some (some true) := by
  induction tree with
  | leaf index =>
    intro selected member
    simp only [leaves, List.mem_singleton] at member
    subst selected
    cases found : values[index]? with
    | none => simp [evaluate, found] at accepted
    | some value => simpa only [evaluate, found, Option.join_some] using congrArg some accepted
  | and left right ihLeft ihRight =>
    have both : left.evaluate values = some true ∧ right.evaluate values = some true := by
      cases a : left.evaluate values <;> cases b : right.evaluate values <;>
        simp_all [evaluate]
    intro index member
    rcases List.mem_append.mp member with inside | inside
    · exact ihLeft both.1 index inside
    · exact ihRight both.2 index inside
end Conjunction

structure Call (F : Type) where
  statement : RootStatement F
  context : Realizations.Sumcheck.Original.Context
  schedule : Nominal.Schedule "bls12-381.fr"

noncomputable def sourceSequence (maximum : Nat) : List (Call F) →
    PIR.Process (ZkcExamples.Structured.OriginalSumcheckLibrary.signature (F := F) (G := G)) Verdicts
  | [] => .done []
  | call :: rest =>
      (sourceRoot maximum call.context call.statement.table call.statement.claim call.statement.rounds).bind fun result =>
      (sourceSequence maximum rest).bind fun tail => .done (result.get .here :: tail)

noncomputable def sequence (maximum : Nat) : List (Call F) → ConstructionState (F := F) (G := G) →
    PIR.Process (NominalField.signature F "bls12-381.fr") (Verdicts × ConstructionState (F := F) (G := G))
  | [], construction => .done ([], construction)
  | call :: rest, construction =>
      (root maximum call.schedule call.statement.table call.statement.claim call.statement.rounds construction).bind fun result =>
      (sequence maximum rest result.2).bind fun tail => .done (acceptance result :: tail.1, tail.2)

noncomputable def sourceComposition (maximum : Nat) (calls : List (Call F)) (tree : Conjunction) :
    PIR.Process (ZkcExamples.Structured.OriginalSumcheckLibrary.signature (F := F) (G := G))
      (Values (Component (assignment F G)) [.boolean]) :=
  (sourceSequence (G := G) maximum calls).bind fun values =>
    .done (Values.cons (tree.evaluate values) .nil)
noncomputable def composition (maximum : Nat) (calls : List (Call F)) (tree : Conjunction)
    (construction : ConstructionState (F := F) (G := G)) :
    PIR.Process (NominalField.signature F "bls12-381.fr") (Result (F := F) (G := G)) :=
  (sequence maximum calls construction).bind fun result =>
    .done (Values.cons (tree.evaluate result.1) .nil, result.2)

/-- Exact optional Boolean operation selected by checked helper equations. -/
def both {I : PIR.Signature} (left right : Values (Component (assignment F G)) [.boolean]) :
    PIR.Process I (Values (Component (assignment F G)) [.boolean]) :=
  .done (.cons ((left.get .here).bind fun a => (right.get .here).map fun b => a && b) .nil)

omit [Field F] [DecidableEq F] in
theorem verdict_value (result : Result (F := F) (G := G)) : result.1.get .here = acceptance result := by
  rcases result with ⟨values, state⟩
  cases values with | cons value rest => cases rest; rfl

theorem sequence_bridge (routing : Zkc.Construction.Original.Routing) (maximum : Nat)
    (calls : List (Call F)) (construction : ConstructionState (F := F) (G := G))
    (routes : ∀ call ∈ calls, OriginalSecurity.Routes routing call.context call.schedule construction.frames) :
    DomainReduction.Bridge (NominalField.interface (G := G) "bls12-381.fr")
      (fun reached result => result.2.history = reached ∧ result.2.frames = construction.frames)
      construction.history
      (Zkc.Construction.Original.fold routing (sourceSequence maximum calls) construction)
      (sequence maximum calls construction) := by
  induction calls generalizing construction with
  | nil => exact .done _ _ ⟨rfl, rfl⟩
  | cons call rest ih =>
    simp only [sourceSequence, sequence, Zkc.Construction.Original.fold_bind]
    apply (root_bridge routing call.context call.schedule maximum call.statement.table
      call.statement.claim call.statement.rounds construction (routes call (by simp))).bind
    intro reached first preserved
    have tail := ih first.2 (fun next member => preserved.2 ▸ routes next (by simp [member]))
    rw [preserved.1] at tail
    apply tail.bind
    intro final second holds
    rw [verdict_value first]
    exact .done _ _ ⟨holds.1, holds.2.trans preserved.2⟩

theorem composition_bridge (routing : Zkc.Construction.Original.Routing) (maximum : Nat)
    (calls : List (Call F)) (tree : Conjunction) (construction : ConstructionState (F := F) (G := G))
    (routes : ∀ call ∈ calls, OriginalSecurity.Routes routing call.context call.schedule construction.frames) :
    DomainReduction.Bridge (NominalField.interface (G := G) "bls12-381.fr")
      (fun reached (result : Result (F := F) (G := G)) =>
        result.2.history = reached ∧ result.2.frames = construction.frames)
      construction.history
      (Zkc.Construction.Original.fold routing (sourceComposition maximum calls tree) construction)
      (composition maximum calls tree construction) := by
  unfold sourceComposition composition
  rw [Zkc.Construction.Original.fold_bind]
  apply (sequence_bridge routing maximum calls construction routes).bind
  intro reached result preserved
  exact .done _ _ preserved

/-- Independent preservation covers true, false and gap prefixes. -/
theorem sequence_returns (interaction : PIR.Interaction (NominalField.signature F "bls12-381.fr"))
    (phase : interaction.Phase) (maximum : Nat) (calls : List (Call F))
    (construction : ConstructionState (F := F) (G := G)) :
    PIR.Boundary.Returns interaction (fun result _ => result.2.frames = construction.frames)
      (sequence maximum calls construction) phase := by
  induction calls generalizing construction phase with
  | nil => rfl
  | cons call rest ih =>
    apply PIR.Boundary.returns_bind interaction _ _
      (fun result _ => result.2.frames = construction.frames) _ phase
      (root_returns interaction phase maximum ⟨call.statement, call.schedule, construction⟩)
    intro first reached preserved
    apply PIR.Boundary.returns_bind interaction _ _
      (fun result _ => result.2.frames = first.2.frames) _ reached (ih reached first.2)
    intro tail _ holds
    exact holds.trans preserved

variable {charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal}
variable [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)]

/-- Correct prefixes remain arbitrary executions. Only a false component uses
its soundness contract, including every malformed raw input case. -/
noncomputable def sequence_rejected
    (sampling : (Nominal.queriesWithFrame (G := G) "bls12-381.fr"
      (TableComponent.Execution.frameUpdate (F := F) (G := G) "bls12-381.fr")).ConditionalBound
      (Nominal.layoutWithFrame "bls12-381.fr"
        (TableComponent.Execution.frameUpdate (F := F) (G := G) "bls12-381.fr")).representation 1 1 charge)
    (maximum : Nat) (calls : List (Call F)) (construction : ConstructionState (F := F) (G := G))
    (history : Domain.History (uniformCarriers F G)) :
    Derivation (NominalField.interface (G := G) "bls12-381.fr") (boundedEscape charge)
      (fun _ result => (∀ call ∈ calls, Correct call.statement.table call.statement.claim call.statement.rounds) ∨
        ∃ index, index < calls.length ∧ result.1[index]? ≠ some (some true))
      history (sequence maximum calls construction) := by
  induction calls generalizing construction history with
  | nil => exact .done (Or.inl (by simp))
  | cons call rest ih =>
    unfold sequence
    by_cases correct : Correct call.statement.table call.statement.claim call.statement.rounds
    · apply (unrestricted (root maximum call.schedule call.statement.table call.statement.claim
        call.statement.rounds construction) history).bind
      intro reached first _
      apply (ih first.2 reached).bind
      intro final tail outcome
      apply Derivation.done
      rcases outcome with all | ⟨index, inside, wrong⟩
      · exact Or.inl (by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro correct all)
      · exact Or.inr ⟨index + 1, by simpa using Nat.succ_lt_succ inside, by simpa using wrong⟩
    · have rejected := root_soundness sampling maximum ()
        ⟨call.statement, call.schedule, construction⟩ history trivial
        (by exact ⟨call.statement, rfl, by rintro ⟨_, holds⟩; exact correct holds⟩)
      apply rejected.bind
      intro reached first wrong
      apply (unrestricted (sequence maximum rest first.2) reached).bind
      intro final tail _
      apply Derivation.done
      exact Or.inr ⟨0, by simp, by
        simp only [List.getElem?_cons_zero]
        intro accepted
        have no := ReadbackHolds.some.mp wrong
        exact no ⟨(), Option.some.inj accepted⟩⟩

noncomputable def composition_rejected
    (sampling : (Nominal.queriesWithFrame (G := G) "bls12-381.fr"
      (TableComponent.Execution.frameUpdate (F := F) (G := G) "bls12-381.fr")).ConditionalBound
      (Nominal.layoutWithFrame "bls12-381.fr"
        (TableComponent.Execution.frameUpdate (F := F) (G := G) "bls12-381.fr")).representation 1 1 charge)
    (maximum : Nat) (calls : List (Call F)) (tree : Conjunction)
    (coverage : ∀ index < calls.length, index ∈ tree.leaves)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G))
    (wrong : ¬ ∀ call ∈ calls, Correct call.statement.table call.statement.claim call.statement.rounds) :
    Derivation (NominalField.interface (G := G) "bls12-381.fr") (boundedEscape charge)
      (fun _ result => acceptance result ≠ some true) history
      (composition maximum calls tree construction) := by
  apply (sequence_rejected sampling maximum calls construction history).bind
  intro reached result outcome
  apply Derivation.done
  intro accepted
  rcases outcome with all | ⟨index, inside, refused⟩
  · exact wrong all
  · exact refused (tree.evaluate_true result.1 accepted index (coverage index inside))

omit [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)] in
theorem sequence_cost (price : ENNReal)
    (priced : ∀ history origin, charge history (.challenge origin) ≤ price)
    (maximum : Nat) (calls : List (Call F)) (construction : ConstructionState (F := F) (G := G))
    (history : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (NominalField.interface (G := G) "bls12-381.fr") charge
      (sequence maximum calls construction) history ((calls.length * maximum) • price) := by
  induction calls generalizing construction history with
  | nil => trivial
  | cons call rest ih =>
    simp only [sequence, List.length_cons, Nat.add_mul, one_mul, add_nsmul]
    rw [add_comm]
    apply CostComposition.bind _ _ (maximum • price) ((rest.length * maximum) • price)
      (root_cost price priced maximum call.schedule call.statement.table call.statement.claim call.statement.rounds construction history)
    intro first reached
    have tail := CostComposition.bind _ (fun tail => .done (acceptance first :: tail.1, tail.2)) ((rest.length * maximum) • price) 0
      (ih first.2 reached) (fun _ _ => CostComposition.done _)
    simpa only [add_zero] using tail

omit [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)] in
theorem composition_cost (price : ENNReal)
    (priced : ∀ history origin, charge history (.challenge origin) ≤ price)
    (maximum : Nat) (calls : List (Call F)) (tree : Conjunction)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (NominalField.interface (G := G) "bls12-381.fr") charge
      (composition maximum calls tree construction) history ((calls.length * maximum) • price) := by
  have bound := CostComposition.bind (sequence maximum calls construction)
    (fun result => .done (Values.cons (tree.evaluate result.1) .nil, result.2) :
      _ → PIR.Process (NominalField.signature F "bls12-381.fr") (Result (F := F) (G := G)))
    ((calls.length * maximum) • price) 0 (sequence_cost price priced maximum calls construction history)
    (fun _ _ => CostComposition.done _)
  simpa only [composition, add_zero] using bound

end ZkcSecurity.Realizations.Sumcheck.OriginalRaw
