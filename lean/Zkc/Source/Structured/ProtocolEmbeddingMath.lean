module

public import Zkc.Source.Structured.ProtocolEmbedding
public import Zkc.Source.Structured.ProtocolCalculation
public import Zkc.Source.Structured.Participant

@[expose] public section

/-! Concrete-input specialization of the actual lazy Math evaluator. The relation uses
immutable retained prefixes, not authored helper meanings, and retains partial outcomes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Zkc.Source.Structured.ProtocolEmbedding
open Zkc.Source
variable {carriers : Carriers} {I : PIR.Signature}

abbrev component (t : Ty) (value : Component carriers.Value t) :
    Component (ProtocolValue carriers) t := value.map (ProtocolValue.ofConcrete t)

@[simp] theorem map_components {ts : List Ty} (values : Values (Component carriers.Value) ts) :
    mapValues component values = ProtocolValue.embedComponents values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [mapValues, ProtocolValue.embedComponents, ih, component]

@[simp] theorem embed_append {ts us : List Ty}
    (values : Values (Component carriers.Value) ts) (rest : Values (Component carriers.Value) us) :
    ProtocolValue.embedComponents (values.append rest) =
      (ProtocolValue.embedComponents values).append (ProtocolValue.embedComponents rest) := by
  simpa only [map_components] using mapValues_append component values rest

@[simp] theorem embed_split (ts : List Ty) {us : List Ty}
    (values : Values (Component carriers.Value) (ts ++ us)) :
    (ProtocolValue.embedComponents values).split ts =
      (ProtocolValue.embedComponents (values.split ts).1,
        ProtocolValue.embedComponents (values.split ts).2) := by
  simpa only [map_components] using mapValues_split component ts values

@[simp] theorem embed_present {ts : List Ty} (values : Values carriers.Value ts) :
    ProtocolValue.embedComponents values.present = (ProtocolValue.embedValues values).present := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [ProtocolValue.embedComponents, ProtocolValue.embedValues,
      Values.present, Option.map_some, ih]

@[simp] theorem embed_absent (ts : List Ty) :
    ProtocolValue.embedComponents (Values.absent carriers.Value ts) =
      Values.absent (ProtocolValue carriers) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [ProtocolValue.embedComponents, Values.absent, Option.map_none, ih]

@[simp] theorem sequence_embed {ts : List Ty} (args : Values (Component carriers.Value) ts) :
    RoleFamily.sequence (ProtocolValue.embedComponents args) =
      (RoleFamily.sequence args).map ProtocolValue.embedValues := by
  induction args with
  | nil => rfl
  | cons value rest ih =>
    cases value <;> simp [ProtocolValue.embedComponents, RoleFamily.sequence, ih,
      ProtocolValue.embedValues, Option.map_bind, Option.bind_map]
    cases RoleFamily.sequence rest <;> rfl

theorem sequence_some {ts : List Ty} (args : Values (Component carriers.Value) ts)
    (values : Values carriers.Value ts) (present : RoleFamily.sequence args = some values) :
    args = values.present := by
  induction args with
  | nil => cases values; rfl
  | cons value rest ih =>
    cases value with
    | none => simp [RoleFamily.sequence] at present
    | some value =>
      cases found : RoleFamily.sequence rest with
      | none => simp [RoleFamily.sequence, found] at present
      | some tail =>
        simp only [RoleFamily.sequence, found, Option.bind_some, Option.map_some,
          Option.some.injEq] at present
        cases present
        simp only [Values.present, ih tail found]

@[simp] theorem present_append {ts us : List Ty} (values : Values carriers.Value ts)
    (rest : Values carriers.Value us) :
    (values.append rest).present = values.present.append rest.present := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [Values.append, Values.present, ih]

@[simp] theorem present_split (ts : List Ty) {us : List Ty}
    (values : Values carriers.Value (ts ++ us)) :
    values.present.split ts = ((values.split ts).1.present, (values.split ts).2.present) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases values with
    | cons value rest => simp only [Values.present, Values.split, ih]

@[simp] theorem component_toConcrete {carriers : Carriers} {t : Ty}
    (value : Component carriers.Value t) :
    (value.map (ProtocolValue.ofConcrete t)).bind ProtocolValue.toConcrete = value := by
  cases value <;> simp only [Option.map_none, Option.map_some, Option.bind_none,
    Option.bind_some, ProtocolValue.toConcrete_ofConcrete]

/-- Only Math entries are used by the lazy Math path. Local calls remain closed. -/
def MathTablesRelated (model : DomainModel)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers I)
    (lazy : ProtocolCalculation.Tables model.toCarriers I) : Prop :=
  ∀ helper, helper.kind = .math → ∀ args,
    invoke lazy helper (ProtocolValue.embedComponents args) =
      (invoke ordinary.components helper args).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result))

/-- The lazy fold's actual transition, named here only to expose its existing equation. -/
def lazyFoldStep (model : DomainModel) (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (spec : FoldSpec) (arguments : Values model.Value spec.domain.inputs)
    (captures : Values (Component (ProtocolValue model.toCarriers)) spec.captures)
    (state : Values (Component (ProtocolValue model.toCarriers)) spec.state)
    (item : Values model.Value spec.domain.items) :
    PIR.Process I (Values (Component (ProtocolValue model.toCarriers)) spec.state) :=
  let callbackArguments := (ProtocolValue.embedComponents item.present).append
    ((ProtocolValue.embedComponents arguments.present).append captures)
  let enabled : PIR.Process I (Option Bool) :=
    if spec.predicate.isEmpty then .done (some true)
    else (invoke helpers spec.predicateHelper callbackArguments).bind
      (fun result ↦ .done ((result.get .here).bind ProtocolValue.toConcrete))
  enabled.bind fun enabled ↦ match enabled with
    | none => .halt .incomplete
    | some false => .done state
    | some true => invoke helpers spec.stepHelper (state.append callbackArguments)

theorem fold_step_embed (model : DomainModel)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (related : MathTablesRelated model ordinary helpers) (adequate : ordinary.Adequate)
    (spec : FoldSpec) (math : spec.kind = .math)
    (arguments : Values model.Value spec.domain.inputs)
    (captures : Values model.Value spec.captures) (state : Values model.Value spec.state)
    (item : Values model.Value spec.domain.items) :
    lazyFoldStep model helpers spec arguments (ProtocolValue.embedComponents captures.present)
      (ProtocolValue.embedComponents state.present) item =
      (Evaluation.foldTransitionOn ordinary.closed spec arguments captures state item).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result.present)) := by
  have helper (helper : Helper) (kind : helper.kind = .math)
      (args : Values model.Value helper.inputs) :
      invoke helpers helper (ProtocolValue.embedComponents args.present) =
        (invoke ordinary.closed helper args).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result.present)) := by
    rw [related helper kind, adequate helper args]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  unfold lazyFoldStep Evaluation.foldTransitionOn
  simp only [← embed_append, ← present_append]
  have predicate := helper spec.predicateHelper math
    (item.append (arguments.append captures))
  have step := helper spec.stepHelper math (state.append (item.append (arguments.append captures)))
  dsimp only [FoldSpec.predicateHelper, FoldSpec.stepHelper] at *
  by_cases empty : spec.predicate.isEmpty = true
  · simp only [empty, ↓reduceIte, PIR.Process.bind]
    exact step
  · simp only [empty, Bool.false_eq_true, ↓reduceIte]
    erw [predicate]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind, ProtocolValue.embedComponents,
      Values.get, Values.get_present, Option.map_some, ProtocolValue.toConcrete_ofConcrete,
      Option.bind_some]
    congr 1
    funext result
    cases result with | cons enabled tail =>
      cases tail
      cases enabled <;>
        simp only [embed_present, ProtocolValue.embedValues, Values.present, Values.get,
          Option.map_some,
          ProtocolValue.toConcrete_ofConcrete, Option.bind_some, Bool.false_eq_true,
          ↓reduceIte, PIR.Process.bind]
      simpa only [embed_present] using step

theorem fold_embed_present (model : DomainModel)
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (related : MathTablesRelated model ordinary helpers) (adequate : ordinary.Adequate)
    (spec : FoldSpec) (math : spec.kind = .math) (args : Values model.Value spec.arguments) :
    ProtocolCalculation.fold model demand self helpers spec
      (ProtocolValue.embedComponents args.present) =
      (Evaluation.denoteFoldOn ordinary.closed spec args).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result.present)) := by
  unfold ProtocolCalculation.fold Evaluation.denoteFoldOn
  dsimp only [FoldSpec.arguments] at args ⊢
  simp only [sequence_embed, RoleFamily.sequence_present, Option.map_some, embed_split,
    present_split, ProtocolValue.materializeComponents_embedComponents, PIR.Process.bind,
    RoleFamily.sequence_present]
  change Finite.admitThen _ (fun items ↦ Finite.fold
      (lazyFoldStep model helpers spec (args.split spec.domain.inputs).1
        (ProtocolValue.embedComponents
          ((args.split spec.domain.inputs).2.split spec.state).2.present))
      items (ProtocolValue.embedComponents
        ((args.split spec.domain.inputs).2.split spec.state).1.present)) = _
  cases spec.domain.admit (args.split spec.domain.inputs).1 with
  | stopped reason => rfl
  | returned items =>
    exact fold_naturality (fun result ↦ ProtocolValue.embedComponents result.present) _ _
      (fun state item ↦
        fold_step_embed model ordinary helpers related adequate spec math _ _ state item)
      items _

end Zkc.Source.Structured.ProtocolEmbedding

namespace Zkc.Source.Structured.ProtocolEmbedding
open Zkc.Source
variable {I : PIR.Signature}

theorem fold_embed (model : DomainModel)
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (ordinary captured : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (related : MathTablesRelated model captured helpers) (adequate : captured.Adequate)
    (spec : FoldSpec) (math : spec.kind = .math)
    (args : Values (Component model.Value) spec.arguments) :
    ProtocolCalculation.operation model demand self ordinary helpers (.fold spec)
      (ProtocolValue.embedComponents args) =
      (Evaluation.componentOperationOn model (.silent _) captured (.fold spec) args .nil).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  simp only [ProtocolCalculation.operation, math, ↓reduceIte]
  dsimp only [Op.arguments, Op.results] at *
  cases sequenced : RoleFamily.sequence args with
  | none =>
    unfold ProtocolCalculation.fold
    erw [sequence_embed, sequenced]
    change PIR.Process.done (Values.absent (ProtocolValue model.toCarriers) spec.state) = _
    change _ = (strictComponent (Evaluation.meaningOn model (.silent _) captured.closed)
      (.fold spec) args .nil).bind _
    unfold strictComponent
    erw [sequenced]
    simp only [PIR.Process.bind, Op.results, embed_absent]
  | some values =>
    rw [sequence_some args values sequenced]
    erw [fold_embed_present model demand self captured helpers related adequate spec math]
    erw [Evaluation.componentOperationOn_adequate model (.silent _) captured adequate]
    dsimp only [Evaluation.meaningOn]
    erw [Evaluation.operationOn.eq_def]
    erw [PIR.Process.bind_assoc]
    rfl

theorem concrete_fields (carriers : Carriers) (fields : ProductFields)
    (args : Values carriers.Value fields.toList) :
    ProtocolValue.ofConcreteFields fields (fields.pack args) = ProtocolValue.embedValues args := by
  cases fields with
  | nil => cases args; rw [ProtocolValue.ofConcreteFields]; rfl
  | cons t fields => cases args with
    | cons value rest =>
      simp only [ProductFields.pack, ProtocolValue.ofConcreteFields,
        ProtocolValue.embedValues]
      rw [concrete_fields carriers fields rest]
termination_by fields

theorem concrete_product (carriers : Carriers) (identity constructor : String)
    (fields : ProductFields) (args : Values carriers.Value fields.toList) :
    ProtocolValue.ofConcrete (carriers := carriers) (.product identity constructor fields)
      (fields.pack args) =
      ProtocolValue.product identity constructor fields (ProtocolValue.embedValues args) := by
  rw [ProtocolValue.ofConcrete, concrete_fields]

/-- Every admitted calculation case is instantiated. The fallback delegates primitive
outcomes to the original evaluator, preserving bounded-read failure and execution of
zero-result operations. -/
theorem calculation_embed (model : DomainModel)
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (ordinary captured : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (related : MathTablesRelated model captured helpers) (adequate : captured.Adequate)
    (op : Op) (allowed : op.isCalculation = true)
    (args : Values (Component model.Value) op.arguments)
    (bodies : Values (RegionFunction model.Value I) op.regions) :
    ProtocolCalculation.operation model demand self ordinary helpers op
      (ProtocolValue.embedComponents args) =
      (Evaluation.componentOperationOn model (.silent _) captured op args bodies).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  cases op <;> try (simp [Op.isCalculation] at allowed)
  all_goals cases bodies
  all_goals dsimp only [Op.arguments, Op.results, Op.regions] at args ⊢
  case invoke helper =>
    have math : helper.kind = .math := by simpa only [Op.isCalculation, beq_iff_eq] using allowed
    change (if helper.kind = .math then invoke helpers helper (ProtocolValue.embedComponents args)
      else _) = _
    erw [ite_eq_left math]
    change _ = (if helper.kind = .math then invoke captured.components helper args else _).bind _
    erw [ite_eq_left math]
    exact related helper math args
  case fold spec =>
    exact fold_embed model demand self ordinary captured helpers related adequate spec
      (by simpa only [Op.isCalculation, beq_iff_eq] using allowed) args
  case makeProduct identity constructor fields =>
    change PIR.Process.done (Values.cons
      (Value := Component (ProtocolValue model.toCarriers))
      ((RoleFamily.sequence (ProtocolValue.embedComponents args)).map
        (ProtocolValue.product identity constructor fields)) .nil) = _
    cases sequenced : RoleFamily.sequence args with
    | none =>
      erw [sequence_embed, sequenced]
      change _ = (strictComponent (Evaluation.meaningOn model (.silent _) captured.closed)
        (.makeProduct identity constructor fields) args .nil).bind _
      unfold strictComponent
      erw [sequenced]
      rfl
    | some values =>
      rw [sequence_some args values sequenced]
      erw [Evaluation.componentOperationOn_adequate model (.silent _) captured adequate]
      simp only [Evaluation.meaningOn, Evaluation.operationOn, PIR.Process.bind,
        ProtocolValue.embedComponents, Values.present, Option.map_some, concrete_product]
      erw [sequence_embed, RoleFamily.sequence_present]
      simp only [Option.map_some]
      change _ = PIR.Process.done (Values.cons
        (Value := Component (ProtocolValue model.toCarriers))
        (some (ProtocolValue.ofConcrete (.product identity constructor fields)
          (fields.pack values))) .nil)
      rw [concrete_product]
  case getProduct identity constructor fields t field =>
    cases args with | cons value rest =>
      cases rest
      change PIR.Process.done (Values.cons
        (Value := Component (ProtocolValue model.toCarriers))
        ((value.map (ProtocolValue.ofConcrete _)).map (fun value ↦ value.project field)) .nil) = _
      change _ = (strictComponent (Evaluation.meaningOn model (.silent _) captured.closed)
        (.getProduct identity constructor fields t field) (.cons value .nil) .nil).bind _
      cases value with
      | none => rfl
      | some value =>
        change PIR.Process.done (Values.cons
          (Value := Component (ProtocolValue model.toCarriers))
          (some ((ProtocolValue.ofConcrete _ value).project field)) .nil) =
          PIR.Process.done (Values.cons (some (ProtocolValue.ofConcrete t
            ((fields.unpack value).get field))) .nil)
        rw [ProtocolValue.project_ofConcrete]
  case select t =>
    cases args with | cons condition rest =>
      cases rest with | cons yes rest =>
        cases rest with | cons no rest =>
          cases rest
          change PIR.Process.done (Values.cons
            (Value := Component (ProtocolValue model.toCarriers))
            (do
              let c ← (condition.map (ProtocolValue.ofConcrete .boolean)).bind
                ProtocolValue.toConcrete
              let y ← yes.map (ProtocolValue.ofConcrete t)
              let n ← no.map (ProtocolValue.ofConcrete t)
              pure (if c then y else n)) .nil) =
            (strictComponent (Evaluation.meaningOn model (.silent _) captured.closed)
            (.select t) (.cons condition (.cons yes (.cons no .nil))) .nil).bind _
          rw [component_toConcrete]
          cases condition with
          | none => rfl
          | some condition =>
            cases yes with
            | none => rfl
            | some yes =>
              cases no with
              | none => rfl
              | some no =>
                cases condition <;> rfl
  case vectorLength field =>
    cases args with | cons value rest =>
      cases rest
      change _ = (strictComponent (Evaluation.meaningOn model (.silent _) captured.closed)
        (.vectorLength field) (.cons value .nil) .nil).bind _
      cases value with
      | none => rfl
      | some value =>
        change PIR.Process.done (Values.cons
          (Value := Component (ProtocolValue model.toCarriers))
          (((some (ProtocolValue.ofConcrete (.vector field) value)).bind
            ProtocolValue.observedLength).map (ProtocolValue.ofConcrete .index)) .nil) =
          PIR.Process.done (Values.cons (some (ProtocolValue.ofConcrete .index value.length)) .nil)
        simp only [Option.bind_some, ProtocolValue.ofConcrete, ProtocolValue.observedLength,
          Option.map_some, ProtocolValue.toConcrete_concrete]
  case sequenceEmpty element =>
    cases args
    exact (ProtocolCalculation.strict_embed model demand self ordinary
      (.sequenceEmpty element) .nil rfl).trans rfl
  case sequenceAppend element =>
    cases args with | cons values rest =>
    cases rest with | cons value rest =>
    cases rest
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.sequenceAppend element) (.cons values (.cons value .nil)) rfl).trans ?_
    cases values <;> cases value <;> rfl
  case sequenceLength element =>
    cases args with | cons values rest =>
    cases rest
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.sequenceLength element) (.cons values .nil) rfl).trans ?_
    cases values <;> rfl
  case indexConstant value =>
    cases args
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.indexConstant value) .nil rfl).trans ?_
    rfl
  case indexEqual =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.indexEqual) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case indexLess =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.indexLess) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case indexPowerOfTwo =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.indexPowerOfTwo) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case indexWrappingAdd =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.indexWrappingAdd) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case indexWrappingSubtract =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.indexWrappingSubtract) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case indexBitAnd =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.indexBitAnd) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case indexLogicalShiftRight =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.indexLogicalShiftRight) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case multilinearRestrictPrefix field =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.multilinearRestrictPrefix field) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case fieldConstant field value =>
    cases args
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.fieldConstant field value) .nil rfl).trans ?_
    rfl
  case fieldAdd field =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.fieldAdd field) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case fieldSubtract field =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.fieldSubtract field) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case fieldMultiply field =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.fieldMultiply field) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case fieldEqual field =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.fieldEqual field) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case fieldEmbed extension base =>
    cases args with | cons v0 rest1 =>
    cases rest1
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.fieldEmbed extension base) (.cons v0 .nil) rfl).trans ?_
    cases v0 <;> rfl
  case groupIdentity group =>
    cases args
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.groupIdentity group) .nil rfl).trans ?_
    rfl
  case groupAdd group =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.groupAdd group) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case groupScale group field =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.groupScale group field) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case groupEqual group =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.groupEqual group) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case booleanConstant value =>
    cases args
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.booleanConstant value) .nil rfl).trans ?_
    rfl
  case booleanAnd =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.booleanAnd) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case booleanOr =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.booleanOr) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case booleanXor =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.booleanXor) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case booleanEqual =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.booleanEqual) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case booleanNotEqual =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.booleanNotEqual) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl
  case boundedAt field =>
    cases args with | cons v0 rest1 =>
    cases rest1 with | cons v1 rest2 =>
    cases rest2
    refine (ProtocolCalculation.strict_embed model demand self ordinary
      (.boundedAt field) (.cons v0 (.cons v1 .nil)) rfl).trans ?_
    cases v0 <;> cases v1 <;> rfl

end Zkc.Source.Structured.ProtocolEmbedding

namespace Zkc.Source.Structured.ProtocolEmbedding
open Zkc.Source
variable {I : PIR.Signature}

/-- A syntactic condition on the actual retained Math body, including lexical binds.
No helper equation, input presence or mathematical definedness is assumed here. -/
def MathLeaf (op : Op) : Prop := op.isCalculation = true ∨ ∃ site, op = .mark site

def MathOperation (op : Op) : Prop :=
  MathLeaf op ∨ ∃ captures outputs, op = .branch captures outputs

theorem math_no_regions (op : Op) (allowed : MathLeaf op) : op.regions = [] := by
  rcases allowed with calculation | ⟨site, rfl⟩
  · exact op.calculation_no_regions calculation
  · rfl

theorem math_operation_embed (model : DomainModel)
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (ordinary captured : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (related : MathTablesRelated model captured helpers) (adequate : captured.Adequate)
    (op : Op) (allowed : MathLeaf op)
    (args : Values (Component model.Value) op.arguments)
    (bodies : Values (RegionFunction model.Value I) op.regions) :
    ProtocolCalculation.operation model demand self ordinary helpers op
      (ProtocolValue.embedComponents args) =
      (Evaluation.componentOperationOn model (.silent _) captured op args bodies).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  rcases allowed with calculation | ⟨site, rfl⟩
  · exact calculation_embed model demand self ordinary captured helpers related adequate
      op calculation args bodies
  · cases args
    cases bodies
    rfl

/-- A nested Math region is invoked with present captures. Its original closed
process may return, stop, or request an interaction. -/
private def MathCallbacks (model : DomainModel) {ss : List (List Ty × List Ty)}
    (closed : Values (RegionFunction model.Value I) ss)
    (openMath : Values (RegionFunction (Component (ProtocolValue model.toCarriers)) I) ss) : Prop :=
  ∀ {signature} (ref : Var ss signature) args,
    (openMath.get ref) (ProtocolValue.embedComponents args.present) =
      ((closed.get ref) args).bind fun result ↦ .done (ProtocolValue.embedComponents result.present)

private theorem selected_missing (model : DomainModel) {ts us : List Ty}
    (args : Values (Component model.Value) (.boolean :: ts))
    (onYes onNo : RegionFunction (Component (ProtocolValue model.toCarriers)) I (ts, us))
    (missing : RoleFamily.sequence args = none) :
    ProtocolCalculation.selected model (ProtocolValue.embedComponents args) onYes onNo =
      .done (Values.absent _ us) := by
  unfold ProtocolCalculation.selected
  rw [sequence_embed args, missing]
  rfl

private theorem selected_present (model : DomainModel) {ts us : List Ty}
    (flag : Bool) (xs : Values model.Value ts)
    (onYes onNo : RegionFunction (Component (ProtocolValue model.toCarriers)) I (ts, us)) :
    ProtocolCalculation.selected model
        (ProtocolValue.embedComponents (.cons flag xs : Values model.Value (.boolean :: ts)).present) onYes onNo =
      (if flag then onYes else onNo) (ProtocolValue.embedComponents xs.present) := by
  unfold ProtocolCalculation.selected
  rw [embed_present, RoleFamily.sequence_present]
  simp only [ProtocolValue.embedValues, ProtocolValue.toConcrete_ofConcrete, embed_present]

private theorem math_region_embed (model : DomainModel)
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (ordinary captured : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (related : MathTablesRelated model captured helpers) (adequate : captured.Adequate)
    (op : Op) (allowed : MathOperation op) (args : Values (Component model.Value) op.arguments)
    (closed : Values (RegionFunction model.Value I) op.regions)
    (openMath : Values (RegionFunction (Component (ProtocolValue model.toCarriers)) I) op.regions)
    (callbacks : MathCallbacks model closed openMath) :
    ProtocolCalculation.regionOperation model demand self ordinary helpers op
      (ProtocolValue.embedComponents args) openMath =
      (Evaluation.componentOperationOn model (.silent _) captured op args closed).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  rcases allowed with leaf | ⟨ts, us, rfl⟩
  · rw [← math_operation_embed model demand self ordinary captured helpers related adequate
      op leaf args closed]
    have noRegions := math_no_regions op leaf
    cases op <;> first | rfl | contradiction
  · cases closed with | cons yes rest =>
    cases rest with | cons no rest =>
    cases rest
    cases openMath with | cons onYes rest =>
    cases rest with | cons onNo rest =>
    cases rest
    cases sequenced : RoleFamily.sequence args with
    | none =>
      change ProtocolCalculation.selected model (ProtocolValue.embedComponents args) onYes onNo =
        (strictComponent (Evaluation.meaningOn model (.silent _) captured.closed)
          (Op.branch ts us) args (.cons yes (.cons no .nil))).bind _
      rw [selected_missing model args onYes onNo sequenced]
      simp only [strictComponent, sequenced, PIR.Process.bind, embed_absent]
      rfl
    | some values =>
      have present := sequence_some args values sequenced
      subst args
      cases values with | cons flag xs =>
      erw [Evaluation.componentOperationOn_branch model (.silent _) captured ts us flag xs yes no, PIR.Process.bind_assoc]
      change ProtocolCalculation.selected model (ProtocolValue.embedComponents _) onYes onNo = _
      erw [selected_present model flag xs onYes onNo]
      cases flag
      · exact callbacks (.there .here) xs
      · exact callbacks .here xs

/-- Both sides execute the same Region. Optional Math inputs are never sequenced at
helper entry. Closed Local callback semantics is retained by the original component side. -/
theorem math_body_embed (model : DomainModel)
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (ordinary captured : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (related : MathTablesRelated model captured helpers) (adequate : captured.Adequate)
    {ts us} (body : Region dialect ts us) (fragment : Fragment MathOperation body)
    (env : Environment (Component model.Value) ts) :
    body.denote (ProtocolCalculation.meaning model demand self ordinary helpers)
      (fun {t} ref ↦ component t (env ref)) =
      (body.component (Evaluation.meaningOn model (.silent _) captured.closed)
        (Evaluation.componentOperationOn model (.silent _) captured) env).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  revert fragment env
  induction body using Region.rec (motive_2 := fun _ bodies ↦ Fragments MathOperation bodies →
    MathCallbacks model (bodies.denote (Evaluation.meaningOn model (.silent _) captured.closed))
      (bodies.denote (ProtocolCalculation.meaning model demand self ordinary helpers))) with
  | ret args =>
    intro _ env
    simp only [Region.denote, Region.component, mapValues_eval, map_components,
      PIR.Process.bind]
  | stop reason => intro _ _; rfl
  | letOp op args bodies next bodiesIH ih =>
    intro fragment env
    simp only [Region.denote, Region.component, mapValues_eval, map_components]
    rw [math_region_embed model demand self ordinary captured helpers related adequate
      op fragment.1 _ _ _ (bodiesIH fragment.2.1)]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    congr 1
    funext result
    have envEq := map_prepend component env result
    rw [map_components] at envEq
    rw [← envEq]
    exact ih fragment.2.2 _
  | bind body next ih nextIH =>
    intro fragment env
    simp only [Region.denote, Region.component, ih fragment.1,
      PIR.Process.bind_assoc, PIR.Process.bind]
    congr 1
    funext result
    have envEq := map_prepend component env result
    rw [map_components] at envEq
    rw [← envEq]
    exact nextIH fragment.2 _
  | nil => rename_i fragment; intro signature ref; cases ref
  | cons body rest bodyIH restIH =>
    rename_i fragment
    intro signature ref
    cases ref with
    | there ref => exact restIH fragment.2 ref
    | here =>
      intro args
      change body.denote (ProtocolCalculation.meaning model demand self ordinary helpers) (ProtocolValue.embedComponents args.present).get = _
      have converted : @Eq (Environment (Component (ProtocolValue model.toCarriers)) _)
          (ProtocolValue.embedComponents args.present).get
          (fun ref ↦ component _ (some (args.get ref))) := by
        funext ty ref
        rw [← map_components, mapValues_get, Values.get_present]
      rw [converted, bodyIH fragment.1]
      rw [body.component_present _ _ (Evaluation.componentOperationOn_adequate
        model (.silent _) captured adequate) args.get, PIR.Process.bind_assoc]
      rfl

/-- Each helper uses the immutable prefix captured by its actual source definition. -/
theorem math_tables_extend (model : DomainModel)
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (ordinary captured : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (related : MathTablesRelated model captured helpers) (adequate : captured.Adequate)
    (definition : CheckedDefinition)
    (fragment : definition.kind = .math → Fragment MathOperation definition.body) :
    MathTablesRelated model (captured.extend model (.silent _) definition)
      (ProtocolCalculation.extend model demand self ordinary helpers definition) := by
  intro helper math args
  by_cases name : definition.helper.name = helper.name
  · by_cases same : definition.helper = helper
    · subst helper
      simp only [Evaluation.ComponentTablesOn.extend, ProtocolCalculation.extend]
      erw [invoke_cons_same, invoke_cons_same]
      have kind : definition.kind = .math := math
      have envEq := mapValues_environment component args
      rw [map_components] at envEq
      dsimp only [HelperDefinition.invoke]
      erw [envEq]
      exact math_body_embed model demand self ordinary captured helpers related adequate
        definition.body (fragment kind) args.get
    · simp only [Evaluation.ComponentTablesOn.extend, ProtocolCalculation.extend]
      rw [invoke_cons_mismatch _ _ _ name same, invoke_cons_mismatch _ _ _ name same]
      rfl
  · simp only [Evaluation.ComponentTablesOn.extend, ProtocolCalculation.extend]
    rw [invoke_cons_other _ _ _ name, invoke_cons_other _ _ _ name]
    exact related helper math args

theorem math_tables_fold (model : DomainModel)
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (ordinary captured : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : ProtocolCalculation.Tables model.toCarriers I)
    (related : MathTablesRelated model captured helpers) (adequate : captured.Adequate)
    (definitions : List CheckedDefinition)
    (fragment : ∀ definition ∈ definitions, definition.kind = .math →
      Fragment MathOperation definition.body) :
    MathTablesRelated model
      (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) captured)
      (definitions.foldl (ProtocolCalculation.extend model demand self ordinary) helpers) := by
  induction definitions generalizing captured helpers with
  | nil => exact related
  | cons definition rest ih =>
    exact ih _ _
      (math_tables_extend model demand self ordinary captured helpers related adequate definition
        (fragment definition (by simp)))
      (Evaluation.ComponentTablesOn.adequate_extend model (.silent _) captured adequate definition)
      (fun definition member ↦ fragment definition (by simp [member]))

end Zkc.Source.Structured.ProtocolEmbedding
