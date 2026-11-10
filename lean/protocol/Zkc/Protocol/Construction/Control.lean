module

public import Zkc.Protocol.Construction.Region
public import Zkc.Program.Source.ScalarRegion
public import Zkc.Program.Source.Finite

/-! Callback and finite-control rules for the existing scalar reference profile.

This profile is a client of the shared Region. Native integration is a separate admission
boundary. A remaining-iteration invariant is mathematical input; the rule never unrolls a
runtime bound in the client's proof and never resets operation state or observations.
-/

@[expose] public section
open PIR Zkc.Source Std.WP

namespace ProtocolProof.Construction

@[spec_invariant_type]
def RemainingInvariant (A Pred : Type) := Nat → A → Pred

variable {I : Signature} {Pred EPred : Type}
  [Assertion Pred] [Assertion EPred] [WPMonad (Process I) Pred EPred]

@[spec] theorem finiteRepeat {A : Type} (count : Nat) (body : A → Process I A)
    (initial : A) (inv : RemainingInvariant A Pred) (post : A → Pred) (stopped : EPred)
    (step : ∀ remaining, remaining < count → ∀ value,
      ⦃inv (remaining + 1) value⦄ body value ⦃inv remaining; stopped⦄)
    (terminal : ∀ value, Lean.Order.PartialOrder.rel (inv 0 value) (post value)) :
    ⦃inv count initial⦄ repeatN count body initial ⦃post; stopped⦄ := by
  induction count generalizing initial with
  | zero =>
    simpa only [repeatN, pure] using
      (Triple.pure (m := Process I) (epost := stopped) initial (terminal initial))
  | succ count ih =>
    simpa only [repeatN, bind] using
      (Triple.bind (m := Process I) (body initial) (repeatN count body) (inv count)
        (step count (Nat.lt_succ_self count) initial)
        (fun value => ih value (fun remaining h => step remaining (Nat.lt_succ_of_lt h))))

/-- Mathematical state assertions indexed by the remaining ordered input suffix. -/
@[spec_invariant_type]
abbrev SequenceInvariant (Item State Pred : Type) := List Item → State → Pred

/-- The same structural fold rule covers runtime bounds and admitted finite domains.
A step law is required only for actual suffixes; no independent-state assumption is made. -/
@[spec] theorem finiteFold {Item State : Type} (step : State → Item → Process I State)
    (items : List Item) (initial : State) (inv : SequenceInvariant Item State Pred)
    (post : State → Pred) (stopped : EPred)
    (each : ∀ before item rest, items = before ++ item :: rest → ∀ state,
      ⦃inv (item :: rest) state⦄ step state item ⦃inv rest; stopped⦄)
    (terminal : ∀ state, Lean.Order.PartialOrder.rel (inv [] state) (post state)) :
    ⦃inv items initial⦄ Finite.fold step items initial ⦃post; stopped⦄ := by
  induction items generalizing initial with
  | nil => exact ⟨(processDone initial post stopped).entails_wp_of_pre (terminal initial)⟩
  | cons item rest ih =>
    exact Triple.bind (m := Process I) (step initial item) (Finite.fold step rest) (inv rest)
      (each [] item rest rfl initial)
      (fun state => ih state (fun before next suffix split =>
        each (item :: before) next suffix (by simp only [List.cons_append, split])))

variable {language : Language} (meaning : Interpretation language I)

@[spec] theorem ordinaryOperation (op : language.Op)
    (arguments : Values meaning.Value (language.arguments op))
    (post : Values meaning.Value [language.result op] → Pred) (stopped : EPred) :
    ⦃wp (meaning.operation op arguments) (fun value => post (.singleton value)) stopped⦄
      meaning.regionMeaning.operation (.ordinary op) arguments .nil ⦃post; stopped⦄ := by
  simpa only [Interpretation.regionMeaning, bind, pure] using
    (Triple.bind (m := Process I) (meaning.operation op arguments)
      (fun value => pure (Values.singleton value)) (fun value => post (.singleton value))
      ⟨Lean.Order.PartialOrder.rel_refl⟩ (fun value =>
        Spec.pure (m := Process I) (post := post) (epost := stopped) (Values.singleton value)))

@[spec] theorem selectedOperation {captures : List language.Ty} {result : language.Ty}
    (condition : meaning.Value language.condition) (values : Values meaning.Value captures)
    (yes no : RegionFunction meaning.Value I (captures, [result]))
    (post : Values meaning.Value [result] → Pred) (stopped : EPred) :
    ⦃if meaning.condition condition then wp (yes values) post stopped
        else wp (no values) post stopped⦄
      meaning.regionMeaning.operation (.branch captures result) (.cons condition values)
        (.cons yes (.cons no .nil)) ⦃post; stopped⦄ := by
  change Triple (if meaning.condition condition then yes values else no values)
    (if meaning.condition condition then wp (yes values) post stopped
      else wp (no values) post stopped) post stopped
  split <;> exact ⟨Lean.Order.PartialOrder.rel_refl⟩

@[spec] theorem repeatedOperation (count : Nat) {captures : List language.Ty}
    {accumulator : language.Ty} (initial : meaning.Value accumulator)
    (values : Values meaning.Value captures)
    (body : RegionFunction meaning.Value I (accumulator :: captures, [accumulator]))
    (post : Values meaning.Value [accumulator] → Pred) (stopped : EPred) :
    ⦃wp (repeatN count
      (fun value => (body (.cons value values)).bind fun out => .done (out.get .here)) initial)
      (fun value => post (.singleton value)) stopped⦄
      meaning.regionMeaning.operation (.repeat count captures accumulator) (.cons initial values)
        (.cons body .nil) ⦃post; stopped⦄ := by
  simpa only [Interpretation.regionMeaning, bind, pure] using
    (Triple.bind (m := Process I)
      (repeatN count
        (fun value => (body (.cons value values)).bind fun out => .done (out.get .here)) initial)
      (fun value => pure (Values.singleton value)) (fun value => post (.singleton value))
      ⟨Lean.Order.PartialOrder.rel_refl⟩ (fun value =>
        Spec.pure (m := Process I) (post := post) (epost := stopped) (Values.singleton value)))

end ProtocolProof.Construction
