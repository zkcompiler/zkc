module

public import Zkc.Protocol.Construction.WP

/-! Upstream specifications for every primitive Process constructor, including stops. -/

@[expose] public section
open PIR Std.WP

namespace ProtocolProof.Construction

@[spec] theorem processDone {I : Signature} {Pred EPred A : Type}
    [Assertion Pred] [Assertion EPred] [WPMonad (Process I) Pred EPred]
    (value : A) (post : A → Pred) (stopped : EPred) :
    ⦃post value⦄ Process.done (I := I) value ⦃post; stopped⦄ := by
  simpa only [pure] using
    (Spec.pure (m := Process I) (post := post) (epost := stopped) value)

@[spec] theorem processBind {I : Signature} {A B : Type}
    (body : Process I A) (next : A → Process I B) : body.bind next = body >>= next := rfl

variable {I : Signature} {S L A : Type} (spec : OperationSpec I S L) (mono : spec.Monotone)
  (post : A → Potential S L) (stopped : Stop → Potential S L)

@[spec] theorem processHaltLower (reason : Stop) :
    @Triple _ _ _ _ _ _ (.halt reason : Process I A) ((spec.toWPMonad mono).toWP A)
      (stopped reason) post stopped := by
  let := spec.toWPMonad mono
  exact ⟨Lean.Order.PartialOrder.rel_refl⟩

@[spec] theorem processHaltUpper
    (post : A → (Potential S L)ᵒᵈ) (stopped : (Stop → Potential S L)ᵒᵈ) (reason : Stop) :
    @Triple _ _ _ _ _ _ (.halt reason : Process I A) ((spec.toUpperWPMonad mono).toWP A)
      (OrderDual.toDual (OrderDual.ofDual stopped reason)) post stopped := by
  let := spec.toUpperWPMonad mono
  exact ⟨Lean.Order.PartialOrder.rel_refl⟩

/-- Expose a primitive operation's continuation through the ordinary bind rule. -/
theorem processCallBind (op : I.Op) (next : I.Reply op → Process I A) :
    Process.call op next = (Process.call op Process.done).bind next := rfl

@[spec] theorem processCallLower (op : I.Op)
    (post : I.Reply op → Potential S L) (stopped : Stop → Potential S L) :
    @Triple _ _ _ _ _ _ (.call op .done) ((spec.toWPMonad mono).toWP (I.Reply op))
      (spec op (OperationSpec.outcomePost post stopped)) post stopped := by
  let := spec.toWPMonad mono
  constructor
  change _ ≤ wpFold spec (.call op .done) (OperationSpec.outcomePost post stopped)
  rw [wpFold_operation]

@[spec] theorem processCallUpper (op : I.Op)
    (post : I.Reply op → (Potential S L)ᵒᵈ) (stopped : (Stop → Potential S L)ᵒᵈ) :
    @Triple _ _ _ _ _ _ (.call op .done) ((spec.toUpperWPMonad mono).toWP (I.Reply op))
      (OrderDual.toDual (spec op (OperationSpec.outcomePost
        (fun value => OrderDual.ofDual (post value)) (OrderDual.ofDual stopped)))) post stopped := by
  let := spec.toUpperWPMonad mono
  constructor
  change wpFold spec (.call op .done) _ ≤ _
  rw [wpFold_operation]
  exact le_rfl

end ProtocolProof.Construction
