import Zkc.Source.Mathematical.BlsInstallation
import Zkc.Source.Mathematical.RegisteredVocabulary

/-! Meanings selected from an admitted BLS mathematical vocabulary.

The operation key keeps its authored declaration index. Re-reading that
declaration through the admitted manifest recovers its installed payload;
signature equality alone never selects an operation's meaning.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.BlsMeaning
open BlsInstallation
open Zkc.Algebra.Bls12381

private def selected {α : Type} (values : List α) (index : Nat)
    (present : ∃ value, values[index]? = some value) : SignatureAdmission.Selected values index := by
  have bound : index < values.length := by
    obtain ⟨value, same⟩ := present
    exact (List.getElem?_eq_some_iff.mp same).1
  exact ⟨values[index], by simp⟩

section Selection
variable {Group : Type} {source : Raw.Subject}
  (header : DeclarationAdmission.Header (contracts Group) source) {arity : Nat}

def declaration (operation : RegisteredVocabulary.Operation header arity) :
    SignatureAdmission.Selected source.module.operations operation.val.declaration :=
  selected _ _ (by
    obtain ⟨_, _, raw, signature, _, _, _, same⟩ := operation.property
    rw [same]
    exact ⟨signature.declaration.value, signature.declaration.selected⟩)

def identity (operation : RegisteredVocabulary.Operation header arity) :
    SignatureAdmission.Selected source.manifest.operations (declaration header operation).value.identity.index :=
  selected _ _ (by
    obtain ⟨_, _, raw, signature, _, _, _, same⟩ := operation.property
    have index : operation.val.declaration = raw.operation.index := congrArg (·.declaration) same
    have decl : (declaration header operation).value = signature.declaration.value := by
      apply Option.some.inj
      have lookup := (declaration header operation).selected
      exact lookup.symm.trans ((congrArg (fun i => source.module.operations[i]?) index).trans
        signature.declaration.selected)
    rw [decl]
    exact ⟨signature.identity.value, signature.identity.selected⟩)

def package (operation : RegisteredVocabulary.Operation header arity) :=
  header.context.selected .operation (identity header operation)

def payload (operation : RegisteredVocabulary.Operation header arity) : Operation :=
  (package header operation).package.interpretation

private theorem selected_unique {Payload category installation manifest firstId secondId}
    (first : ManifestAdmission.Selected (Payload := Payload) installation manifest category firstId)
    (second : ManifestAdmission.Selected (Payload := Payload) installation manifest category secondId)
    (same : firstId = secondId) :
    first.package = second.package :=
  List.inj_on_of_nodup_map (installation category).unique first.registered second.registered
    (congrArg ManifestAdmission.key (first.exactIdentity.trans (same.trans second.exactIdentity.symm)))

/-- This equation ties the recovered function selector to the package whose
contract admitted this exact occurrence. -/
theorem payload_agrees (operation : RegisteredVocabulary.Operation header arity)
    {count : Nat} {parameters : Fin count → Static.Expression arity}
    {raw : GraphResolution.OperationUse}
    (signature : SignatureAdmission.Operation header.context.meaning header.types parameters
      source.module source.manifest raw.operation.index raw.statics)
    (registered : RegistryAdmission.Operation header.context header.types signature)
    (same : operation.val = ⟨raw.operation.index, signature.signature, registered.facts, raw.attributes⟩) :
    payload header operation = registered.selected.package.interpretation := by
  have index : operation.val.declaration = raw.operation.index := congrArg (·.declaration) same
  have decl : (declaration header operation).value = signature.declaration.value := by
    apply Option.some.inj
    have lookup := (declaration header operation).selected
    exact lookup.symm.trans ((congrArg (fun i => source.module.operations[i]?) index).trans
      signature.declaration.selected)
  have id : (identity header operation).value = signature.identity.value := by
    apply Option.some.inj
    exact (identity header operation).selected.symm.trans
      (congrArg (fun value => source.manifest.operations[value.identity.index]?) decl |>.trans signature.identity.selected)
  unfold payload package
  exact congrArg (·.interpretation) (selected_unique
    (header.context.selected .operation (identity header operation)) registered.selected id)

theorem payload_signature (operation : RegisteredVocabulary.Operation header arity) :
    operation.val.signature.arguments.mapM (classify source.manifest) = some (payload header operation).arguments ∧
      classify source.manifest operation.val.signature.result = some (payload header operation).result := by
  obtain ⟨_, _, _, signature, registered, _, _, same⟩ := operation.property
  rw [payload_agrees header operation signature registered same]
  have accepted := operationCheck_signature source.manifest registered.selected.package.interpretation
    signature.signature registered.facts registered.accepted
  simpa [same] using accepted.2.2.2

theorem domain_payload (index : Fin source.manifest.domains.length) (domain : Domain)
    (same : source.manifest.domains[index.val]? = some domain.identity) :
    header.context.domain index = domain := by
  let picked := (header.context.manifest.selected .domain).get index
  have identity : picked.package.identity = domain.identity := by
    exact picked.exactIdentity.trans ((List.getElem?_eq_some_iff.mp same).2)
  have member := picked.registered
  change picked.package.interpretation = domain
  simp only [contracts, installation, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with first | second
  · rw [first] at identity ⊢
    cases domain <;> simp_all [domainPackage, Domain.identity]
    rfl
  · rw [second] at identity ⊢
    cases domain <;> simp_all [domainPackage, Domain.identity]
    rfl

/-- An occurrence retains the meaning selected by its exact registered
identity, independently of other operations with the same type signature. -/
theorem payload_of_identity (operation : RegisteredVocabulary.Operation header arity) (op : Operation)
    (same : source.manifest.operations[(declaration header operation).value.identity.index]? = some op.identity) :
    payload header operation = op := by
  let picked := header.context.selected .operation (identity header operation)
  have identityEq : picked.package.identity = op.identity :=
    picked.exactIdentity.trans (Option.some.inj ((identity header operation).selected.symm.trans same))
  have member := picked.registered
  change picked.package.interpretation = op
  simp only [contracts, installation, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same <;>
    (rw [same] at identityEq ⊢; cases op <;> simp_all [operationPackage, Operation.identity]) <;> rfl

end Selection

variable {model : GroupModel} {source : Raw.Subject}
  (header : DeclarationAdmission.Header (contracts model.Carrier) source) {arity : Nat}

/-- Classification agrees with the actual manifest-selected type carrier. -/
theorem classify_value (shape : TypeExpansion.Shape source.manifest.domains.length 0)
    (type : LogicalType) (valid : classify source.manifest shape = some type) :
    TypeExpansion.denote header.context.meaning shape Fin.elim0 = LogicalType.Value model type := by
  cases shape with
  | atom atom =>
      cases atom with
      | nominal index constructor arguments =>
          cases arguments with
          | cons _ _ => simp [classify] at valid
          | nil =>
              dsimp only [classify] at valid
              split at valid
              · rename_i scalar
                have payload := domain_payload header index .scalar scalar
                split at valid
                · rename_i constructorEq
                  cases Option.some.inj valid
                  subst constructor
                  change nominal model.Carrier (header.context.domain index) "field" [] = Scalar
                  rw [payload]
                  rfl
                · split at valid
                  · rename_i constructorEq
                    cases Option.some.inj valid
                    subst constructor
                    change nominal model.Carrier (header.context.domain index) "nonzero_field" [] = Challenge
                    rw [payload]
                    rfl
                  · contradiction
              · split at valid
                · rename_i group
                  have parts : source.manifest.domains[index.val]? = some Domain.group.identity ∧
                      constructor = "group" := by simpa using group
                  have payload := domain_payload header index .group parts.1
                  have constructorEq := parts.2
                  cases Option.some.inj valid
                  subst constructor
                  change nominal model.Carrier (header.context.domain index) "group" [] = model.Carrier
                  rw [payload]
                  rfl
                · contradiction
      | polynomial | residual => simp [classify] at valid
  | fin count =>
      cases count with
      | literal n =>
          simp only [classify] at valid
          split at valid
          · rename_i countEq
            cases Option.some.inj valid
            simp [TypeExpansion.denote, Data.Shape.Value, Static.Expression.eval, countEq]
          · contradiction
      | parameter index => exact Fin.elim0 index
      | add | multiply | pow2 => simp [classify] at valid
  | product | vector => simp [classify] at valid

private theorem classified_cons {domains target : Nat}
    {shape : TypeExpansion.Shape domains target} {shapes : List (TypeExpansion.Shape domains target)}
    {type : LogicalType} {types : List LogicalType}
    (valid : (shape :: shapes).mapM (classify source.manifest) = some (type :: types)) :
    classify source.manifest shape = some type ∧ shapes.mapM (classify source.manifest) = some types := by
  cases head : classify source.manifest shape with
  | none => simp [List.mapM_cons, head] at valid
  | some found =>
      cases tail : shapes.mapM (classify source.manifest) with
      | none => simp [List.mapM_cons, head, tail] at valid
      | some rest =>
          simp [List.mapM_cons, head, tail] at valid
          exact ⟨congrArg some valid.1, congrArg some valid.2⟩

abbrev Value (shape : TypeExpansion.Shape source.manifest.domains.length 0) : Type :=
  TypeExpansion.denote header.context.meaning shape Fin.elim0

private def castArguments : {shapes : List (TypeExpansion.Shape source.manifest.domains.length 0)} →
    {types : List LogicalType} → shapes.mapM (classify source.manifest) = some types →
    Values (Value header) shapes → Values (LogicalType.Value model) types
  | [], [], _, .nil => .nil
  | [], _ :: _, valid, _ => by simp at valid
  | shape :: shapes, [], valid, _ => by
      cases head : classify source.manifest shape with
      | none => simp [List.mapM_cons, head] at valid
      | some found =>
          cases tail : shapes.mapM (classify source.manifest) <;>
            simp [List.mapM_cons, head, tail] at valid
  | _ :: _, _ :: _, valid, .cons value rest =>
      let parts := classified_cons (source := source) valid
      .cons (cast (classify_value header _ _ parts.1) value) (castArguments parts.2 rest)

/-- The actual installed total operation, transported only across the admitted
type equalities. No operation is chosen from a matching signature. -/
def pure (operation : (RegisteredVocabulary.vocabulary header 0).Op)
    (arguments : Values (Value header) operation.val.val.signature.arguments) :
    Value header operation.val.val.signature.result :=
  let valid := payload_signature header operation.val
  cast (classify_value header _ _ valid.2).symm
    ((payload header operation.val).denote model (castArguments header valid.1 arguments))

def interpretation : Graph.Interpretation (RegisteredVocabulary.vocabulary header 0).toAlgebra where
  Value := Value header
  count count := count.eval Fin.elim0
  pure := pure header
  condition value := value.val == 1
  index index := index
  tuple := Data.product
  project := Data.project
  vector values := values
  element value index := value index

theorem lawful : (interpretation header).Lawful where
  project_tuple := Data.project_product
  tuple_project value := ⟨Data.unpack _ value, Data.product_unpack _ value⟩
  element_vector := fun _ _ => rfl
  vector_element := fun _ => rfl

end Zkc.Source.Mathematical.BlsMeaning
