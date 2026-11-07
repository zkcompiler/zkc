module

public import ZkcExamples.Structured.WordPower
public import ZkcExamples.Structured.FriSourceBodies
public import Zkc.Source.Structured.WordDerivation
public import Zkc.Source.Structured.DeterministicFold
public import Zkc.Source.Structured.LoopPresentation

@[expose] public section

/-! Complete ReferenceLaws for every original power dependency and its finite source fold.
Each Requires field names actual smaller helper calls; installation discharges them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Structured.FriPower
open Zkc.Source Zkc.Source.Structured FriSourceBodies WordPower

attribute [local implicit_reducible] Op.arguments Op.results Op.regions

private theorem getHead {V : Ty → Type} {ty : Ty} {rest : List Ty}
    (x : V ty) (xs : Values V rest) : (Values.cons x xs).get .here = x := rfl
private theorem getTail {V : Ty → Type} {ty out : Ty} {rest : List Ty}
    (x : V ty) (xs : Values V rest) (v : Var rest out) :
    (Values.cons x xs).get (.there v) = xs.get v := rfl
private theorem pushHead {V : Ty → Type} {ty : Ty} {rest : List Ty}
    (env : Environment V rest) (x : V ty) : env.push x .here = x := rfl
private theorem pushTail {V : Ty → Type} {ty out : Ty} {rest : List Ty}
    (env : Environment V rest) (x : V ty) (v : Var rest out) :
    env.push x (.there v) = env v := rfl

abbrev extension := "koala-bear.ext8-binomial3"
variable (model : DomainModel)

def rangeDomain : DomainSpec :=
  ⟨"finite_" ++ helper11Helper.name ++ "_s5_domain", [.index, .index], [.index],
    .letNode (.range .here (.there .here)) (.ret .here)⟩

def trips : FoldSpec :=
  ⟨rangeDomain, [.field extension, .field extension, .index], [], helper8Helper.name, "", .math⟩

def halfLaw : ReferenceLaw model helper9Helper.inputs helper9Helper.outputs where
  body := helper9Body
  Requires _ _ := True
  reference args :=
    let next := half (args.get .here) (args.get (.there .here))
      (args.get (.there (.there .here)))
    .returned (.cons next.1 (.cons next.2 .nil))
  valid _ args _ := by
    cases args with | cons value rest =>
    cases rest with | cons offset rest =>
    cases rest with | cons amount rest =>
    cases rest
    by_cases empty : logicalShiftRight value amount = 0 <;>
      simp only [helper9Body, Region.denote, Regions.denote, Operands.eval, Evaluation.meaningOn,
      Evaluation.operationOn, getHead, getTail, Environment.prepend, pushHead, pushTail,
      primitiveOutcome, PIR.Process.bind, half, empty, decide_true, decide_false,
        Bool.false_eq_true, ↓reduceIte]

def widthLaw : ReferenceLaw model helper10Helper.inputs helper10Helper.outputs where
  body := helper10Body
  Requires table _ := ∀ value offset amount,
    invoke table helper9Helper (.cons value (.cons offset (.cons amount .nil))) =
      .done (.cons (half value offset amount).1 (.cons (half value offset amount).2 .nil))
  reference args := .returned (.cons (width (args.get .here)) .nil)
  valid table args dependency := by
    cases args with | cons value rest =>
    cases rest
    let a := half (value, 0).1 (value, 0).2 32
    change (invoke table helper9Helper
      (.cons value (.cons 0 (.cons 32 .nil)))).bind _ = _
    rw [dependency]
    dsimp only [PIR.Process.bind]
    let b := half a.1 a.2 16
    change (invoke table helper9Helper
      (.cons a.1 (.cons a.2 (.cons 16 .nil)))).bind _ = _
    rw [dependency]
    dsimp only [PIR.Process.bind]
    let c := half b.1 b.2 8
    change (invoke table helper9Helper
      (.cons b.1 (.cons b.2 (.cons 8 .nil)))).bind _ = _
    rw [dependency]
    dsimp only [PIR.Process.bind]
    let fourth := half c.1 c.2 4
    change (invoke table helper9Helper
      (.cons c.1 (.cons c.2 (.cons 4 .nil)))).bind _ = _
    rw [dependency]
    dsimp only [PIR.Process.bind]
    let e := half fourth.1 fourth.2 2
    change (invoke table helper9Helper
      (.cons fourth.1 (.cons fourth.2 (.cons 2 .nil)))).bind _ = _
    rw [dependency]
    dsimp only [PIR.Process.bind]
    let f := half e.1 e.2 1
    change (invoke table helper9Helper
      (.cons e.1 (.cons e.2 (.cons 1 .nil)))).bind _ = _
    rw [dependency]
    dsimp only [PIR.Process.bind]
    simp only [Region.denote, Regions.denote, Operands.eval, Evaluation.meaningOn,
      Evaluation.operationOn, getHead, Environment.prepend, pushHead, pushTail, PIR.Process.bind,
      decide_eq_true_eq]
    rfl

def stepLaw : ReferenceLaw model helper7Helper.inputs helper7Helper.outputs where
  body := helper7Body
  Requires _ _ := True
  reference args := .returned (pack model extension (step
    ⟨args.get .here, args.get (.there .here), args.get (.there (.there .here))⟩))
  valid _ args _ := by
    cases args with | cons result rest =>
    cases rest with | cons factor rest =>
    cases rest with | cons remaining rest =>
    cases rest with | cons index rest =>
    cases rest
    simp only [helper7Body, Region.denote, Regions.denote, Operands.eval, Evaluation.meaningOn,
      Evaluation.operationOn, getHead, getTail, Environment.prepend, pushHead, pushTail,
      primitiveOutcome, PIR.Process.bind, step, pack, decide_eq_true_eq]

def callbackLaw : ReferenceLaw model helper8Helper.inputs helper8Helper.outputs where
  body := helper8Body
  Requires table _ := ∀ (state : State (model.Field extension)) index,
    invoke table helper7Helper ((pack model extension state).append (.cons index .nil)) =
      .done (pack model extension (step state))
  reference args := .returned (pack model extension (step
    ⟨args.get .here, args.get (.there .here), args.get (.there (.there .here))⟩))
  valid table args dependency := by
    cases args with | cons result rest =>
    cases rest with | cons factor rest =>
    cases rest with | cons remaining rest =>
    cases rest with | cons index rest =>
    cases rest with | cons lower rest =>
    cases rest with | cons upper rest =>
    cases rest
    change (invoke table helper7Helper
      ((pack model extension ⟨result, factor, remaining⟩).append (.cons index .nil))).bind _ = _
    rw [dependency]
    rfl

/-- The existing finite-fold presentation bridges the counted reference without unfolding trips. -/
theorem fold_run (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (count : Nat) (initial : State (model.Field extension))
    (admitted : 0 < indexLimit ∧ count < indexLimit)
    (callback : ∀ (state : State (model.Field extension)) index lower upper,
      invoke table helper8Helper ((pack model extension state).append
        (.cons index (.cons lower (.cons upper .nil)))) = .done (pack model extension (step state))) :
    Evaluation.denoteFoldOn table trips
      (.cons 0 (.cons count (pack model extension initial))) =
      .done (pack model extension (run count initial)) := by
  have domainAdmitted : trips.domain.admit (carriers := model.toCarriers)
      (.cons 0 (.cons count .nil)) =
      .returned ((List.range' 0 count).map (fun i ↦ Values.cons i Values.nil)) := by
    simp [trips, rangeDomain, DomainSpec.admit, DomainBody.admit, DomainNode.admit, admitted,
      Finite.continueWith]
  have encoded := Evaluation.denoteFoldOn_checked table trips
    (.cons 0 (.cons count .nil)) .nil (List.range' 0 count)
    (fun i ↦ .cons i .nil) (pack model extension) initial domainAdmitted
    (fun state _ ↦ .returned (step state)) (by
      intro state index
      simp only [Evaluation.foldTransitionOn,
        show trips.predicate.isEmpty = true from by
          change ("" : String).isEmpty = true
          decide, ↓reduceIte,
        PIR.Process.bind, getHead]
      exact callback state index 0 count)
  have counted := LoopPresentation.foldCounted
    (I := closedInterface) (fun (state : State (model.Field extension)) _ ↦ .done (step state))
    (fun _ count state ↦ .done (run count state))
    (by intros; rfl) (by intros; rfl) 0 count initial
  rw [← Finite.fold_checked] at encoded
  simp only [Finite.toProcess] at encoded
  rw [counted] at encoded
  simpa only [pack, Values.append, PIR.Process.bind] using encoded

def powerLaw : ReferenceLaw model helper11Helper.inputs helper11Helper.outputs where
  body := helper11Body
  Requires table _ :=
    (∀ exponent, invoke table helper10Helper (.cons exponent .nil) =
      .done (.cons (width exponent) .nil)) ∧
    (∀ (state : State (model.Field extension)) index lower upper,
      invoke table helper8Helper ((pack model extension state).append
        (.cons index (.cons lower (.cons upper .nil)))) = .done (pack model extension (step state)))
  reference args := outcome model extension (args.get .here) (args.get (.there .here))
  valid table args dependencies := by
    cases args with | cons base rest =>
    cases rest with | cons exponent rest =>
    cases rest
    obtain ⟨widthCall, callback⟩ := dependencies
    change (invoke table helper10Helper (.cons exponent .nil)).bind _ = _
    rw [widthCall]
    dsimp only [PIR.Process.bind]
    simp only [Region.denote, Regions.denote, Operands.eval, Evaluation.meaningOn,
      Evaluation.operationOn, getHead, getTail, Environment.prepend, pushHead, pushTail,
      Nat.cast_one]
    change (Evaluation.denoteFoldOn table trips
      (.cons 0 (.cons (width exponent) (pack model extension ⟨1, base, exponent⟩)))).bind _ = _
    by_cases admitted : 0 < indexLimit ∧ width exponent < indexLimit
    · rw [fold_run model table _ _ admitted callback]
      simp [outcome, admitted, pack, primitiveOutcome, PIR.Process.bind,
        Environment.prepend, pushHead]
    · simp [Evaluation.denoteFoldOn, trips, rangeDomain, DomainSpec.admit, DomainBody.admit,
        DomainNode.admit, admitted, Finite.admitThen, Finite.continueWith, outcome,
        primitiveOutcome, pack, Values.split, PIR.Process.bind]

/-- The public protocol and the virtual oracle link power into different
tables. Exact association with the four smaller helper bodies suffices for
either installation. -/
theorem dependencies (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (stepBody : BodyIn definitions helper7Helper (stepLaw model).body)
    (callbackBody : BodyIn definitions helper8Helper (callbackLaw model).body)
    (halfBody : BodyIn definitions helper9Helper (halfLaw model).body)
    (widthBody : BodyIn definitions helper10Helper (widthLaw model).body)
    (generator : model.Field extension) (exponent : Nat) :
    (powerLaw model).Requires (closedMeaningsOn model definitions)
      (.cons generator (.cons exponent .nil)) := by
  constructor
  · intro value
    apply (widthLaw model).invoke (helper := helper10Helper) definitions linked
      widthBody (.cons value .nil)
    intro value offset amount
    exact (halfLaw model).invoke (helper := helper9Helper) definitions linked
      halfBody
      (.cons value (.cons offset (.cons amount .nil))) trivial
  · intro state index lower upper
    cases state with | mk result factor remaining =>
    apply (callbackLaw model).invoke (helper := helper8Helper) definitions linked
      callbackBody
      ((WordPower.pack model extension ⟨result, factor, remaining⟩).append
        (.cons index (.cons lower (.cons upper .nil))))
    intro state index
    cases state with | mk result factor remaining =>
    exact (stepLaw model).invoke (helper := helper7Helper) definitions linked
      stepBody
      ((WordPower.pack model extension ⟨result, factor, remaining⟩).append (.cons index .nil)) trivial

end ZkcExamples.Structured.FriPower
