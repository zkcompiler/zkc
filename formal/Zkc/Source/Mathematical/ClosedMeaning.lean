import Zkc.Source.Mathematical.ClosedAssembly

/-! Semantic induction over the actual source-certified execution table.

A property proved for each retained Prepared body transfers to any selected
entry. No re-elaboration or independently supplied intrinsic body is involved.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.ClosedAssembly
open Protocol

variable {Payload : ManifestAdmission.Category → Type} {contracts : RegistryAdmission.Contracts Payload}
  {source : Raw.Subject} (header : DeclarationAdmission.Header contracts source)

private theorem reference_cast_index {vocabulary : Protocol.Vocabulary}
    {first second : List (Target Nat vocabulary)} {ty : Protocol.Signature Nat vocabulary}
    (same : first = second) (reference : Var (first.map Target.signature) ty) :
    (same ▸ reference).index = reference.index := by cases same; rfl

private theorem reference_bound {α : Type} {values : List α} {ty : α}
    (reference : Var values ty) : reference.index < values.length := by
  induction reference <;> simp_all [Var.index]

/-- Prove a semantic property at a source key from the bodies certified by
assembly. The earlier-call meaning is explicit, so this rule introduces no
assumption about opaque calls or external providers. -/
theorem History.denote_satisfies
    (meaning : Graph.Interpretation (Vocabulary header).toAlgebra) (self : Nat)
    (path : List LocatedExecution.Frame)
    (property : ClosedInstances.Key → (signature : Protocol.Signature Nat (Vocabulary header)) →
      Values (Component meaning.Value self) signature.arguments →
      PIR.Proc (Protocol.interface self (Vocabulary header) meaning.Value)
        (Values (Component meaning.Value self) signature.results) → Prop)
    (body_case : ∀ {records key node} (prepared : Prepared header records key node)
      (earlier : StoredMeanings meaning self (recordTargets header records))
      (arguments : Values (Component meaning.Value self) prepared.target.arguments),
      property key prepared.target.signature arguments
        (prepared.bound.body.checked.program.denoteChecked meaning self earlier path
          ((prepared.bound.body.checked.program.callsMatch_iff targetRoots).mp prepared.calls)
          (fun ref => arguments.get ref)))
    {records} (history : History header records) {signature}
    (reference : Var (scope header records) signature) (key : ClosedInstances.Key)
    (selected : (recordKeys header records)[reference.index]? = some key)
    {capabilities} (bindings : CapabilityBindings capabilities signature.capabilities)
    (roots : bindings.roots = targetRoots reference)
    (arguments : Values (Component meaning.Value self) signature.arguments) :
    property key signature arguments
      (history.definitions.denote meaning self reference bindings roots path arguments) := by
  induction history generalizing signature key with
  | nil => nomatch reference
  | @snoc records lastKey node previous prepared ih =>
    let moved : Var ((recordTargets header records ++ [prepared.target]).map Target.signature) signature :=
      (recordTargets_snoc header records prepared.record) ▸ reference
    have index : moved.index = reference.index :=
      reference_cast_index (recordTargets_snoc header records prepared.record) reference
    rw [History.definitions]
    erw [Protocol.Definitions.denote_reindex]
    change property key signature arguments
      ((Protocol.Definitions.snoc previous.definitions prepared.target prepared.bound.body.checked.program
        _ _ _).denote meaning self moved bindings _ path arguments)
    have selected' : (recordKeys header records ++ [lastKey])[moved.index]? = some key := by
      simpa [recordKeys, index, Prepared.record] using selected
    suffices claim : ∀ (bindings : CapabilityBindings capabilities signature.capabilities)
        (roots : bindings.roots = targetRoots moved)
        (arguments : Values (Component meaning.Value self) signature.arguments),
        property key signature arguments
          ((Protocol.Definitions.snoc previous.definitions prepared.target prepared.bound.body.checked.program
            _ _ _).denote meaning self moved bindings roots path arguments) by
      exact claim bindings _ arguments
    generalize moved = chosen at selected' ⊢
    rcases reference_append_cases chosen with ⟨same, equal⟩ | ⟨earlier, equal⟩
    · cases same
      subst chosen
      have length : (recordTargets header records).length = (recordKeys header records).length := by
        simp [recordTargets, recordKeys]
      simp only [lastReference_index, length, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at selected'
      subst key
      intro bindings roots arguments
      erw [Protocol.Definitions.denote, appendMeaning_last]
      exact body_case prepared (previous.definitions.denote meaning self) arguments
    · subst chosen
      have bound : earlier.index < (recordKeys header records).length := by
        simpa [scope, recordTargets, recordKeys] using reference_bound earlier
      rw [prefixReference_index, List.getElem?_append_left bound] at selected'
      intro bindings roots arguments
      erw [Protocol.Definitions.denote, appendMeaning_prefix]
      exact ih earlier key selected' bindings _ arguments

/-- The selected entry has the authored entry key, independent of the table's
callee-first ordering. -/
theorem Result.denote_satisfies (result : Result header)
    (meaning : Graph.Interpretation (Vocabulary header).toAlgebra) (self : Nat)
    (property : ClosedInstances.Key → (signature : Protocol.Signature Nat (Vocabulary header)) →
      Values (Component meaning.Value self) signature.arguments →
      PIR.Proc (Protocol.interface self (Vocabulary header) meaning.Value)
        (Values (Component meaning.Value self) signature.results) → Prop)
    (body_case : ∀ {records key node} (prepared : Prepared header records key node)
      (earlier : StoredMeanings meaning self (recordTargets header records))
      (arguments : Values (Component meaning.Value self) prepared.target.arguments),
      property key prepared.target.signature arguments
        (prepared.bound.body.checked.program.denoteChecked meaning self earlier []
          ((prepared.bound.body.checked.program.callsMatch_iff targetRoots).mp prepared.calls)
          (fun ref => arguments.get ref)))
    (arguments : Values (Component meaning.Value self) result.entry.signature.arguments) :
    property (ClosedInstances.entryKey source) result.entry.signature arguments
      ((result.closed).denote meaning self arguments) := by
  apply History.denote_satisfies header meaning self [] property body_case result.table.history
  change (recordKeys header result.table.records)[result.entry.target.index]? = some _
  rw [result.entry.targetIndex]
  exact result.entryPosition.property

end Zkc.Source.Mathematical.ClosedAssembly
