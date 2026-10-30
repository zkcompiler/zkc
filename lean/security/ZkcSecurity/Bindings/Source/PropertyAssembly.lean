module

public import ZkcSecurity.Bindings.Source.Pair
public import Zkc.Obligations.FrameComposition
public import ZkcSecurity.ProgramLogic.Transcript.CostComposition

@[expose] public section

/-! Application seams over the existing property judgments. The returned
relation, the all-replies presence law and the No law are independent inputs.
In particular an unrelated application's refusal cannot prove honest success.
No probability independence is used by sequential composition. -/
set_option autoImplicit false
namespace ZkcSecurity.Source.PropertyAssembly
open Zkc.Source Zkc.Source.Structured Zkc.Transcript Zkc.Obligations
open ZkcSecurity.FiatShamir

variable {I : PIR.Signature} {E P A B C : Type} {Raw : E → Type}
  {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}

/-- Reduce pure returns without unfolding a component's execution tree. -/
theorem done_bind (value : A) (next : A → PIR.Process I B) :
    (PIR.Process.done value).bind next = next value := rfl

def map (project : A → B) {Post : List E → A → Prop} {Final : List E → B → Prop}
    {source : PIR.Process I A} {history : List E}
    (proof : Derivation absorb escape Post history source)
    (finish : ∀ reached value, Post reached value → Final reached (project value)) :
    Derivation absorb escape Final history (source.bind fun value => .done (project value)) :=
  proof.bind _ (fun reached value holds => .done (finish reached value holds))

/-- A mathematical seam for two optional Boolean results. This contract is
about the actual selected helper, including its complete output representation. -/
structure Conjunction (combine : Option Bool → Option Bool → PIR.Process I C)
    (returned : Bool → C) : Prop where
  equation : ∀ a b, combine (some a) (some b) = .done (returned (a && b))

/-- One false conjunct suffices, while the other application must independently
return a present Boolean for every typed reply. Its actual reached history is
passed to the next proof. Neither valid input nor honest messages are assumed. -/
noncomputable def conjunction
    (left right : PIR.Process I (Option Bool)) (leftValid rightValid : Prop)
    (leftPresent : PIR.Yields (fun out => ∃ b, out = some b) left)
    (rightPresent : PIR.Yields (fun out => ∃ b, out = some b) right)
    (empty : ∀ reached event, escape reached event (fun _ => False))
    (leftNo : ¬ leftValid → ∀ reached,
      Derivation absorb escape (fun _ out => out = some false) reached left)
    (rightNo : ¬ rightValid → ∀ reached,
      Derivation absorb escape (fun _ out => out = some false) reached right)
    (combine : Option Bool → Option Bool → PIR.Process I C) (returned : Bool → C)
    (seam : Conjunction combine returned) (wrong : ¬ (leftValid ∧ rightValid)) (history : List E) :
    Derivation absorb escape (fun _ out => out = returned false) history
      (left.bind fun a => right.bind fun b => combine a b) := by
  classical
  by_cases first : leftValid
  · exact (Derivation.ofYields empty leftPresent history).bind _ (by
      intro reached a present
      let value := Classical.choose present
      have same : a = some value := Classical.choose_spec present
      rw [same]
      exact (rightNo (fun second => wrong ⟨first, second⟩) reached).bind _ (by
        intro final b rejected
        rw [rejected, seam.equation]
        exact .done (by cases value <;> rfl)))
  · exact (leftNo first history).bind _ (by
      intro reached a rejected
      rw [rejected]
      exact (Derivation.ofYields empty rightPresent reached).bind _ (by
        intro final b present
        let value := Classical.choose present
        have same : b = some value := Classical.choose_spec present
        rw [same, seam.equation]
        exact .done rfl))

/-- The additive rule is proved by the existing charged walk composition
theorem. The terminal helper is required to have zero cost at every reached
history and every returned value, independently of either No predicate. -/
theorem sequence_cost (charge : List E → E → ENNReal)
    (left : PIR.Process I A) (right : PIR.Process I B)
    (finish : A → B → PIR.Process I C) (first second : ENNReal)
    (leftCost : ∀ reached, Typed.ChargedCostBound absorb charge left reached first)
    (rightCost : ∀ reached, Typed.ChargedCostBound absorb charge right reached second)
    (finishCost : ∀ a b reached, Typed.ChargedCostBound absorb charge (finish a b) reached 0)
    (history : List E) :
    Typed.ChargedCostBound absorb charge
      (left.bind fun a => right.bind fun b => finish a b) history (first + second) := by
  apply CostComposition.bind _ _ first second (leftCost history)
  intro a reached
  simpa only [add_zero] using
    CostComposition.bind right (finish a) second 0 (rightCost reached) (finishCost a)

variable {carriers : Carriers} {scope : PairScope}

/-- Pure source returns are installed once, including producer outputs that
the source discards. No equality of complete root processes is a premise. -/
theorem pair_map {D : Type} {Post : A → B → Prop} {Final : C → D → Prop}
    {left : PIR.Process (Structured.Occurrence.signature carriers) A}
    {right : PIR.Process (Structured.Occurrence.signature carriers) B}
    (paired : Pair scope Post left right) (projectLeft : A → C) (projectRight : B → D)
    (finish : ∀ a b, Post a b → Final (projectLeft a) (projectRight b)) :
    Pair scope Final (left.bind fun a => .done (projectLeft a))
      (right.bind fun b => .done (projectRight b)) :=
  paired.bind _ _ (fun a b holds => .done (finish a b holds))

end ZkcSecurity.Source.PropertyAssembly
