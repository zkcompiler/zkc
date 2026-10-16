module

public import Zkc.Source.Structured.LogicalInstantiation
public import Zkc.Source.Structured.ContractObligations

@[expose] public section

/-! The existing contract layer as an instance of logical contexts.

Retained source relations become predicate codes beside a library vocabulary.
Their meaning is keyed by the relation's table position, so every retained
application of one relation reads one meaning. A retained clause lowers to an
atom whose `parameter`/`witness` arguments read the legacy keys and whose
remaining arguments observe the boundary, exactly as `readSelectors` routes
them. Existing statements are unchanged; these theorems relate them. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Logical
open Zkc.Source Zkc.Source.Structured

/-- Native lists inside a logical sort list. -/
def Values.toNative {Sorts : Type} {Value : Ty → Type} {meaning : Sorts → Type} :
    {types : List Ty} → Values Value types →
      Values (LogicalType.denote Value meaning) (types.map LogicalType.native)
  | [], .nil => .nil
  | _ :: _, .cons value rest => .cons value (Values.toNative rest)

def Values.ofNative {Sorts : Type} {Value : Ty → Type} {meaning : Sorts → Type} :
    {types : List Ty} → Values (LogicalType.denote Value meaning) (types.map LogicalType.native) →
      Values Value types
  | [], .nil => .nil
  | _ :: _, .cons value rest => .cons value (Values.ofNative rest)

theorem Values.ofNative_toNative {Sorts : Type} {Value : Ty → Type} {meaning : Sorts → Type}
    {types : List Ty} (values : Values Value types) :
    Values.ofNative (Sorts := Sorts) (meaning := meaning) (Values.toNative values) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih => exact congrArg (Values.cons value) ih

/-- A library vocabulary extended by the retained relations of one snapshot. -/
abbrev Vocabulary.withRelations (V : Vocabulary) (snapshot : Snapshot) : Vocabulary where
  Sorts := V.Sorts
  Predicates := V.Predicates ⊕ Fin snapshot.relations.length
  Views := V.Views
  sortIdentity := V.sortIdentity
  predicateIdentity
    | .inl predicate => V.predicateIdentity predicate
    | .inr index => ⟨(snapshot.relations.get index).name, []⟩
  viewIdentity := V.viewIdentity
  arguments
    | .inl predicate => V.arguments predicate
    | .inr index => (snapshot.relations.get index).inputs.map LogicalType.native
  viewInput := V.viewInput
  viewOutput := V.viewOutput

/-- Interpret retained relations by one meaning per table position. -/
abbrev Interpretation.withRelations {V : Vocabulary} {Value : Ty → Type} {snapshot : Snapshot}
    (interpretation : Interpretation V Value)
    (relations : (index : Fin snapshot.relations.length) →
      Values Value (snapshot.relations.get index).inputs → Prop) :
    Interpretation (V.withRelations snapshot) Value where
  sorts := interpretation.sorts
  holds
    | .inl predicate, arguments => interpretation.holds predicate arguments
    | .inr index, arguments => relations index (Values.ofNative arguments)
  view := interpretation.view

variable {snapshot : Snapshot} {imported : Imported snapshot}
  {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- One meaning per retained relation: a formula is its actual helper
invocation, otherwise the experiment's opaque meaning for that position. -/
def relationMeaning (environment : RelationEnvironment imported F G)
    (index : Fin snapshot.relations.length)
    (arguments : Values (assignment F G) (snapshot.relations.get index).inputs) : Prop :=
  match (snapshot.relations.get index).formula with
  | some name => ∃ boolean : (snapshot.relations.get index).outputs = [.boolean],
      invoke (closedMeanings imported.program.payload.definitions)
        ⟨name, .math, (snapshot.relations.get index).inputs, (snapshot.relations.get index).outputs⟩
        arguments = .done (boolean.symm ▸ Values.cons true .nil)
  | none => environment.meanings index arguments

/-- Every existing interpretation of an application reads the one meaning of
its relation position. Formula and opaque alternatives are both covered. -/
theorem _root_.Zkc.Source.Structured.RelationInterpretation.holds_iff_relationMeaning {application : RelationApplication}
    {relation : RelationBinding snapshot application} {environment : RelationEnvironment imported F G}
    (interpretation : RelationInterpretation imported relation F G environment)
    (arguments : Values (assignment F G) relation.declaration.inputs) :
    interpretation.Holds arguments ↔ relationMeaning environment relation.index arguments := by
  cases interpretation with
  | formula binding booleanOutput domain predicate decidablePredicate =>
    unfold relationMeaning
    change binding.invokeRelation arguments = .done (booleanOutput.symm ▸ Values.cons true .nil) ↔
      (match relation.declaration.formula with
        | some name => ∃ boolean : relation.declaration.outputs = [.boolean],
            invoke (closedMeanings imported.program.payload.definitions)
              ⟨name, .math, relation.declaration.inputs, relation.declaration.outputs⟩
              arguments = .done (boolean.symm ▸ Values.cons true .nil)
        | none => environment.meanings relation.index arguments)
    rw [binding.formula_eq]
    exact ⟨fun holds => ⟨booleanOutput, holds⟩, fun ⟨_, holds⟩ => holds⟩
  | «opaque» noFormula _ =>
    unfold relationMeaning
    change environment.meanings relation.index arguments ↔
      (match relation.declaration.formula with
        | some name => ∃ boolean : relation.declaration.outputs = [.boolean],
            invoke (closedMeanings imported.program.payload.definitions)
              ⟨name, .math, relation.declaration.inputs, relation.declaration.outputs⟩
              arguments = .done (boolean.symm ▸ Values.cons true .nil)
        | none => environment.meanings relation.index arguments)
    rw [noFormula]

/-- Two retained applications of the same relation have the same meaning,
whatever interpretation record each carries. -/
theorem _root_.Zkc.Source.Structured.RelationInterpretation.coherent {first second : RelationApplication}
    {left : RelationBinding snapshot first} {right : RelationBinding snapshot second}
    {environment : RelationEnvironment imported F G}
    (leftInterpretation : RelationInterpretation imported left F G environment)
    (rightInterpretation : RelationInterpretation imported right F G environment)
    (same : left.index = right.index)
    (arguments : Values (assignment F G) left.declaration.inputs) :
    leftInterpretation.Holds arguments ↔
      rightInterpretation.Holds (same ▸ arguments : Values (assignment F G) (snapshot.relations.get right.index).inputs) := by
  cases left with | mk leftIndex leftName =>
  cases right with | mk rightIndex rightName =>
  change leftIndex = rightIndex at same
  subst same
  exact (leftInterpretation.holds_iff_relationMeaning arguments).trans
    (rightInterpretation.holds_iff_relationMeaning arguments).symm

end Zkc.Source.Structured.Logical

namespace Zkc.Source.Structured.Logical
open Zkc.Source Zkc.Source.Structured

variable {snapshot : Snapshot} {imported : Imported snapshot}
  {V : Vocabulary} {Value : Ty → Type} {interpretation : Interpretation V Value}

/-- Route selectors exactly as `readSelectors`: `parameter` and `witness`
purposes read legacy keys; every other purpose observes the boundary. -/
def lowerSelectors {signature : ProtocolSignature} {context : List (LogicalType V.Sorts)}
    (purposes : List String) : {types : List Ty} → Values (BoundarySelector signature) types →
      Values (Term V Value signature context) (types.map LogicalType.native)
  | [], .nil => .nil
  | _ :: _, .cons selector rest =>
    .cons (match purposes.head? with
      | some "parameter" => .key (.parameter selector)
      | some "witness" => .key (.witness selector)
      | _ => .observed selector)
      (lowerSelectors purposes.tail rest)

/-- `readTerms` on a nonempty list is the ordered bind of its two reads. -/
theorem readTerms_cons_bind {owner : ContractBinding imported} {invocation : InvocationCoordinate}
    {context : List (LogicalType V.Sorts)} (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context) {type : LogicalType V.Sorts}
    {types : List (LogicalType V.Sorts)} (term : Term V Value owner.protocol.signature context type)
    (rest : Values (Term V Value owner.protocol.signature context) types) :
    readTerms interpretation protocolContext boundary store (.cons term rest) =
      (do
        let value ← term.read interpretation protocolContext boundary store
        let values ← readTerms interpretation protocolContext boundary store rest
        pure (.cons value values)) := by
  simp only [readTerms]
  generalize term.read interpretation protocolContext boundary store = first
  generalize readTerms interpretation protocolContext boundary store rest = others
  cases first <;> cases others <;> rfl

private theorem bind_toNative {type : Ty} {types : List Ty}
    (first : Option (Value type)) (others : Option (Values Value types)) :
    (do
      let value ← first
      let values ← others.map (Values.toNative (Sorts := V.Sorts) (meaning := interpretation.sorts))
      pure (Values.cons (Value := interpretation.Denote) (ty := .native type) value values)) =
      (do
        let head ← first
        let tail ← others
        pure (Values.cons head tail)).map Values.toNative := by
  cases first <;> cases others <;> rfl

theorem lowerSelectors_read {owner : ContractBinding imported} {invocation : InvocationCoordinate}
    {context : List (LogicalType V.Sorts)} (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context) (purposes : List String)
    {types : List Ty} (selectors : Values (BoundarySelector owner.protocol.signature) types) :
    readTerms interpretation protocolContext boundary store (lowerSelectors purposes selectors) =
      (RoleFamily.sequence (readSelectors protocolContext boundary store.legacy purposes selectors)).map
        Values.toNative := by
  induction selectors generalizing purposes with
  | nil => rfl
  | cons selector rest ih =>
    simp only [lowerSelectors]
    rw [readTerms_cons_bind, ih purposes.tail]
    simp only [readSelectors, RoleFamily.sequence]
    generalize RoleFamily.sequence (readSelectors protocolContext boundary store.legacy purposes.tail rest) = others
    generalize purposes.head? = purpose
    split <;> (try split) <;> first | exact bind_toNative _ _ | simp_all

/-- A retained clause application as an atom of the extended vocabulary. -/
def lowerApplication {owner : ContractBinding imported} {application : RelationApplication}
    {context : List (LogicalType V.Sorts)} (binding : ApplicationBinding owner application) :
    Atom (V.withRelations snapshot) Value owner.protocol.signature context :=
  ⟨.inr binding.relation.index,
    lowerSelectors binding.relation.declaration.purposes binding.selectors⟩

end Zkc.Source.Structured.Logical

namespace Zkc.Source.Structured.Logical
open Zkc.Source Zkc.Source.Structured

private theorem sequence_toNative_some {Sorts : Type} {Value : Ty → Type} {meaning : Sorts → Type}
    {types : List Ty} (read : Option (Values Value types)) (arguments : Values Value types) :
    read.map (Values.toNative (Sorts := Sorts) (meaning := meaning)) = some (Values.toNative arguments) ↔
      read = some arguments := by
  constructor
  · intro mapped
    cases read with
    | none => cases mapped
    | some value =>
      have same := Option.some.inj mapped
      have back := congrArg (Values.ofNative (Sorts := Sorts) (meaning := meaning)) same
      simp only [Values.ofNative_toNative] at back
      rw [back]
  · intro present
    rw [present]
    rfl

variable {snapshot : Snapshot} {imported : Imported snapshot} {V : Vocabulary}
  {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
  {interpretation : Interpretation V (assignment F G)}
  {environment : RelationEnvironment imported F G}
  {owner : ContractBinding imported} {invocation : InvocationCoordinate}
  {context : List (LogicalType V.Sorts)}

/-- Translation of the existing clause semantics. The legacy reading of a
store's selector-named slots gives the same truth as the lowered atom, whose
meaning is the relation's one coherent meaning. -/
theorem _root_.Zkc.Source.Structured.InterpretedApplication.holds_iff_lowered {application : RelationApplication}
    (interpreted : InterpretedApplication owner application F G environment)
    (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (store : Store (interpretation.withRelations (relationMeaning environment)) owner invocation context) :
    interpreted.Holds protocolContext boundary store.legacy ↔
      (lowerApplication interpreted.binding).Holds (interpretation.withRelations (relationMeaning environment))
        protocolContext boundary store := by
  have read := lowerSelectors_read (interpretation := interpretation.withRelations (relationMeaning environment))
    protocolContext boundary store interpreted.binding.relation.declaration.purposes interpreted.binding.selectors
  constructor
  · rintro ⟨arguments, present, holds⟩
    refine ⟨Values.toNative arguments, ?_, ?_⟩
    · change readTerms _ protocolContext boundary store
        (lowerSelectors interpreted.binding.relation.declaration.purposes interpreted.binding.selectors) = _
      rw [read]
      change Option.map Values.toNative (interpreted.binding.read protocolContext boundary store.legacy) = _
      rw [present]
      rfl
    · change relationMeaning environment interpreted.binding.relation.index
        (Values.ofNative (Values.toNative arguments))
      erw [Values.ofNative_toNative]
      exact (interpreted.interpretation.holds_iff_relationMeaning arguments).mp holds
  · rintro ⟨lowered, present, holds⟩
    change readTerms _ protocolContext boundary store
      (lowerSelectors interpreted.binding.relation.declaration.purposes interpreted.binding.selectors) = _ at present
    rw [read] at present
    cases sequence : interpreted.binding.read protocolContext boundary store.legacy with
    | none =>
      change Option.map Values.toNative (interpreted.binding.read protocolContext boundary store.legacy) = _ at present
      rw [sequence] at present
      cases present
    | some arguments =>
      change Option.map Values.toNative (interpreted.binding.read protocolContext boundary store.legacy) = _ at present
      rw [sequence] at present
      cases Option.some.inj present
      refine ⟨arguments, sequence, ?_⟩
      apply (interpreted.interpretation.holds_iff_relationMeaning arguments).mpr
      change relationMeaning environment interpreted.binding.relation.index
        (Values.ofNative (Values.toNative arguments)) at holds
      erw [Values.ofNative_toNative] at holds
      exact holds

/-- Every retained subject clause is an instance of a lowered atom. -/
theorem _root_.Zkc.Source.Structured.ContractInterpretation.subject_iff_lowered
    (contract : ContractInterpretation owner F G environment) (protocolContext : ProtocolContext)
    (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (store : Store (interpretation.withRelations (relationMeaning environment)) owner invocation context) :
    contract.Subject protocolContext index boundary store.legacy ↔
      (lowerApplication (contract.subjects index).binding).Holds
        (interpretation.withRelations (relationMeaning environment)) protocolContext boundary store :=
  (contract.subjects index).holds_iff_lowered protocolContext boundary store

/-- Retained residual clauses lower in the same way; a missing residual stays missing. -/
theorem _root_.Zkc.Source.Structured.ContractInterpretation.residual_iff_lowered
    (contract : ContractInterpretation owner F G environment) (protocolContext : ProtocolContext)
    (index : Fin owner.contract.clauses.length)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (store : Store (interpretation.withRelations (relationMeaning environment)) owner invocation context) :
    contract.Residual protocolContext index boundary store.legacy ↔
      ∃ residual, ∃ selected : (owner.clause index).residual = some residual,
        (lowerApplication (contract.residuals index residual selected).binding).Holds
          (interpretation.withRelations (relationMeaning environment)) protocolContext boundary store := by
  unfold ContractInterpretation.Residual
  constructor
  · rintro ⟨residual, selected, holds⟩
    exact ⟨residual, selected, ((contract.residuals index residual selected).holds_iff_lowered
      protocolContext boundary store).mp holds⟩
  · rintro ⟨residual, selected, holds⟩
    exact ⟨residual, selected, ((contract.residuals index residual selected).holds_iff_lowered
      protocolContext boundary store).mpr holds⟩

/-- An external terminal's parameter sources and output selectors as terms. -/
def lowerParameters :
    {types : List Ty} → Values (AssignmentSource (assignment F G) owner) types →
      Values (Term V (assignment F G) owner.protocol.signature context) (types.map LogicalType.native)
  | [], .nil => .nil
  | _ :: _, .cons source rest => .cons (lowerSource source) (lowerParameters rest)

def lowerOutputs :
    {types : List Ty} → Values (fun type => { selector : BoundarySelector owner.protocol.signature type //
      selector.port.direction = .output }) types →
      Values (Term V (assignment F G) owner.protocol.signature context) (types.map LogicalType.native)
  | [], .nil => .nil
  | _ :: _, .cons selector rest => .cons (.observed selector.val) (lowerOutputs rest)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem lowerParameters_read (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context)
    {types : List Ty} (sources : Values (AssignmentSource (assignment F G) owner) types) :
    readTerms interpretation protocolContext boundary store (lowerParameters sources) =
      (RoleFamily.sequence (ExternalTerminal.readParameters protocolContext boundary store.legacy sources)).map
        Values.toNative := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
    simp only [lowerParameters, readTerms, ExternalTerminal.readParameters, lowerSource_read, ih,
      RoleFamily.sequence]
    generalize source.read protocolContext boundary store.legacy = first
    generalize RoleFamily.sequence (ExternalTerminal.readParameters protocolContext boundary store.legacy rest) = others
    cases first <;> cases others <;> rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem lowerOutputs_read (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context)
    {types : List Ty} (selectors : Values (fun type => { selector : BoundarySelector owner.protocol.signature type //
      selector.port.direction = .output }) types) :
    readTerms interpretation protocolContext boundary store (lowerOutputs (V := V) (context := context) selectors) =
      (RoleFamily.sequence (ExternalTerminal.readOutputs protocolContext boundary selectors)).map
        Values.toNative := by
  induction selectors with
  | nil => rfl
  | cons selector rest ih =>
    simp only [lowerOutputs, readTerms, Term.read, ExternalTerminal.readOutputs, ih, RoleFamily.sequence]
    generalize selector.val.read protocolContext boundary = first
    generalize RoleFamily.sequence (ExternalTerminal.readOutputs protocolContext boundary rest) = others
    cases first <;> cases others <;> rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- An existing external terminal reads lowered terms of the same store: its
parameter sources and output observations become terms in order, and its
experiment-authored meaning is applied to their values. -/
theorem _root_.Zkc.Source.Structured.ExternalTerminal.holds_iff_lowered (terminal : ExternalTerminal owner F G)
    (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context) :
    terminal.Holds protocolContext boundary store.legacy ↔
      ∃ parameters outputs,
        readTerms interpretation protocolContext boundary store (lowerParameters terminal.parameters) =
          some (Values.toNative parameters) ∧
        readTerms interpretation protocolContext boundary store
          (lowerOutputs (V := V) (context := context) terminal.outputs) = some (Values.toNative outputs) ∧
        terminal.meaning parameters outputs := by
  unfold ExternalTerminal.Holds
  simp only [lowerParameters_read, lowerOutputs_read, sequence_toNative_some]

end Zkc.Source.Structured.Logical
