module

public import Zkc.Source.Structured.ReferenceLibrary
public import Zkc.Source.Structured.MultilinearBodies
public import Zkc.Source.Structured.CollectLaws

@[expose] public section

/-! Nominal mathematical laws for the exact multilinear library. The references
are independent of scalar claims. Applicability records complete dependencies,
including unused captured rows, and the logical index and collection bounds. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Zkc.Source.Structured.ReferenceLibrary.Multilinear
open Zkc.Source
open Zkc.Polynomial.Multilinear
open MultilinearBodies

attribute [local implicit_reducible] Op.arguments Op.results Op.regions DomainSpec.elements Collection.element

variable (model : DomainModel) (domain : String) (bindings : Bindings)

abbrev triple : List Ty := [.vector domain, .index, .index]
abbrev firstInputs : List Ty := [.vector domain, .index, .index, .field domain]

abbrev lessHelper : Helper := ⟨bindings.less, .local, [.index, .index], [.boolean]⟩
abbrev halvesHelper : Helper := ⟨bindings.halves, .local, triple domain, [.vector domain, .vector domain]⟩
abbrev mapHelper : Helper := ⟨bindings.collection, .local,
  [.vector domain, .vector domain, .field domain], [.vector domain]⟩
abbrev firstHelper : Helper := ⟨bindings.first, .local, firstInputs domain, triple domain⟩

def tableValues (xs : List (model.Field domain)) (dimension columns : Nat) :
    Values model.Value (triple domain) := .cons xs (.cons dimension (.cons columns .nil))

def less : ReferenceLaw model [.index, .index] [.boolean] where
  body := lessBody domain bindings
  Requires _ _ := True
  reference args := if args.get .here < indexLimit ∧ args.get (.there .here) < indexLimit then
    .returned (.cons (decide (args.get .here < args.get (.there .here))) .nil)
    else .stopped .refused
  valid _ args _ := by
    cases args with | cons a rest => cases rest with | cons b rest =>
      cases rest
      by_cases bound : a < indexLimit ∧ b < indexLimit <;>
        simp [lessBody, Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
          Operands.eval, Regions.denote, Values.get, Environment.prepend, Environment.push,
          SiteObservations.closed, SiteObservations.silent, Primitive.evaluateOn, checkedIndices,
          PIR.Process.bind, primitiveOutcome, bound]

def halvesOutcome (xs : List (model.Field domain)) (dimension : Nat) :
    PIR.Outcome (Values model.Value [.vector domain, .vector domain]) :=
  if dimension < indexLimit then
    if 0 < dimension then
      if 0 < xs.length ∧ xs.length % 2 = 0 then
        .returned (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
      else .stopped .refused
    else .stopped .reject
  else .stopped .refused

set_option backward.isDefEq.respectTransparency false in
def halves : ReferenceLaw model (triple domain) [.vector domain, .vector domain] where
  body := halvesBody domain bindings
  Requires table args := invoke table (lessHelper bindings)
    (.cons 0 (.cons (args.get (.there .here)) .nil)) =
      primitiveOutcome ((less model domain bindings).reference
        (.cons 0 (.cons (args.get (.there .here)) .nil)))
  reference args := halvesOutcome model domain (args.get .here) (args.get (.there .here))
  valid table args dependency := by
    cases args with | cons xs rest => cases rest with | cons dimension rest =>
      cases rest with | cons columns rest =>
        cases rest
        change invoke table (lessHelper bindings) (.cons 0 (.cons dimension .nil)) = _ at dependency
        simp only [less, Values.get, show 0 < indexLimit by decide +kernel, true_and] at dependency
        simp only [halvesBody, Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
          Operands.eval, Regions.denote, Values.get, Environment.prepend, Environment.push,
          SiteObservations.closed, SiteObservations.silent, Primitive.evaluateOn,
          show 0 < indexLimit by decide +kernel, ↓reduceIte, primitiveOutcome, PIR.Process.bind]
        change (invoke table (lessHelper bindings) (.cons 0 (.cons dimension .nil))).bind _ = _
        rw [dependency]
        by_cases bound : dimension < indexLimit <;>
          by_cases positive : 0 < dimension <;>
          by_cases shape : 0 < xs.length ∧ xs.length % 2 = 0 <;>
          simp [bound, positive, shape, halvesOutcome, primitiveOutcome, PIR.Process.bind,
            Evaluation.invokeCallbackOn, Values.get, Environment.prepend, Environment.push,
            Region.denote, Regions.denote, Evaluation.operationOn, Operands.eval,
            SiteObservations.closed, SiteObservations.silent, Primitive.evaluateOn]

/-- A scalar callback is a call with its complete captured source tuple. -/
def callback : ReferenceLaw model
    [.field domain, .field domain, .vector domain, .vector domain, .field domain] [.field domain] :=
  marked model "body" <| call model
    ⟨bindings.interpolation, .local, [.field domain, .field domain, .field domain], [.field domain]⟩
    (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil)))
    (.cons .here .nil) (interpolate model domain).reference

def interpolation : ReferenceLaw model [.field domain, .field domain, .field domain] [.field domain] :=
  call model ⟨bindings.interpolate, .math,
    [.field domain, .field domain, .field domain], [.field domain]⟩
    (Operands.identity _) (.cons .here .nil) (interpolate model domain).reference

/-- Strict zip admission observes both lengths before evaluating any callback. -/
theorem collect_admit (low high : List (model.Field domain))
    (small : low.length < indexLimit) (same : low.length = high.length) :
    (collectSpec domain bindings).domain.admit (carriers := model.toCarriers)
      (.cons low (.cons high .nil)) =
      .returned ((low.zip high).map fun pair => .cons pair.1 (.cons pair.2 .nil)) := by
  have highSmall : high.length < indexLimit := same ▸ small
  change Finite.continueWith
    (if low.length < indexLimit then
      .returned (low.map fun x => (Values.cons x .nil : Values model.Value [.field domain]))
    else .stopped .exhausted) (fun lows =>
      Finite.continueWith
        (if high.length < indexLimit then
          .returned (high.map fun x => (Values.cons x .nil : Values model.Value [.field domain]))
        else .stopped .exhausted) (fun highs =>
          Finite.continueWith (zipDomainRows (.cons lows (.cons highs .nil)))
            (fun rows => .returned rows))) = _
  simp only [highSmall, ↓reduceIte, Finite.continueWith, zipDomainRows,
    List.map_map, Values.append, List.length_map, same, List.zip_map,
    Function.comp_def, Prod.map_fst, Prod.map_snd]

def collect : ReferenceLaw model
    [.vector domain, .vector domain, .field domain] [.vector domain] where
  body := mapBody domain bindings
  Requires table args :=
    (args.get .here).length < indexLimit ∧
    (args.get .here).length = (args.get (.there .here)).length ∧
    ∀ lo hi, invoke table (collectSpec domain bindings).bodyHelper
      (.cons lo (.cons hi (.cons (args.get .here) (.cons (args.get (.there .here))
        (.cons (args.get (.there (.there .here))) .nil))))) =
      .done (.cons (lo + (hi - lo) * args.get (.there (.there .here))) .nil)
  reference args := .returned (.cons
    (List.zipWith (fun lo hi => lo + (hi - lo) * args.get (.there (.there .here)))
      (args.get .here) (args.get (.there .here))) .nil)
  valid table args premises := by
    cases args with | cons low rest => cases rest with | cons high rest =>
      cases rest with | cons r rest =>
        cases rest
        obtain ⟨small, same, callback⟩ := premises
        have collected := Evaluation.denoteCollect_reference table (collectSpec domain bindings)
          (.cons low (.cons high .nil)) (.cons r .nil) (low.zip high)
          (fun pair => .cons pair.1 (.cons pair.2 .nil))
          (collect_admit model domain bindings low high small same) rfl
          (fun pair => pair.1 + (pair.2 - pair.1) * r)
          (fun pair _ => callback pair.1 pair.2)
        change Evaluation.denoteCollect table (collectSpec domain bindings)
          (.cons low (.cons high (.cons r .nil))) =
          .done (.cons ((low.zip high).map fun pair => pair.1 + (pair.2 - pair.1) * r) .nil)
          at collected
        simp only [mapBody, Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
          Operands.eval, Regions.denote, Values.get, Environment.prepend]
        rw [collected]
        simp only [PIR.Process.bind, Values.get, Environment.prepend, List.map_zip_eq_zipWith,
          primitiveOutcome, Environment.push, Function.curry]
        rfl

def sums : ReferenceLaw model (triple domain) [.field domain, .field domain] where
  body := sumsBody domain bindings
  Requires table args := invoke table (halvesHelper domain bindings) args =
    primitiveOutcome ((halves model domain bindings).reference args)
  reference args := match (halves model domain bindings).reference args with
    | .returned values => .returned (.cons (values.get .here).sum
        (.cons (values.get (.there .here)).sum .nil))
    | .stopped reason => .stopped reason
  valid table args dependency := by
    cases args with | cons xs rest => cases rest with | cons n rest =>
      cases rest with | cons w rest =>
        cases rest
        simp only [sumsBody, Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
          Operands.eval, Regions.denote, Values.get, Environment.prepend, Environment.push,
          SiteObservations.closed, SiteObservations.silent, PIR.Process.bind]
        change (invoke table (halvesHelper domain bindings) (.cons xs (.cons n (.cons w .nil)))).bind _ = _
        rw [dependency]
        cases outcome : (halves model domain bindings).reference (.cons xs (.cons n (.cons w .nil))) with
        | stopped reason => rfl
        | returned values =>
          cases values with | cons low rest => cases rest with | cons high rest =>
            cases rest
            simp only [primitiveOutcome, PIR.Process.bind, Values.get, Environment.prepend,
              Environment.push, Primitive.evaluateOn, List.sum_eq_foldl]
            rfl

def firstOutcome (args : Values model.Value (firstInputs domain)) :
    PIR.Outcome (Values model.Value (triple domain)) :=
  if 0 < args.get (.there .here) then
    .returned (tableValues model domain
      (restrictValues (args.get .here) (args.get (.there (.there (.there .here)))))
      (args.get (.there .here) - 1) (args.get (.there (.there .here))))
  else .stopped .reject


set_option backward.isDefEq.respectTransparency false in
/-- The local restriction helper retains dimension and width as distinct outputs.
Its reference depends on the complete table and challenge, never on a claim. -/
def first : ReferenceLaw model (firstInputs domain) (triple domain) where
  body := firstBody domain bindings
  Requires table args :=
    (args.get .here).length < indexLimit ∧
    args.get (.there .here) < indexLimit ∧
    (0 < args.get (.there .here) →
      0 < (args.get .here).length ∧ (args.get .here).length % 2 = 0) ∧
    invoke table (halvesHelper domain bindings)
      (tableValues model domain (args.get .here) (args.get (.there .here))
        (args.get (.there (.there .here)))) =
      primitiveOutcome (halvesOutcome model domain (args.get .here) (args.get (.there .here))) ∧
    ∀ low high r, low.length < indexLimit → low.length = high.length →
      invoke table (mapHelper domain bindings) (.cons low (.cons high (.cons r .nil))) =
        .done (.cons (List.zipWith (fun lo hi => lo + (hi - lo) * r) low high) .nil)
  reference := firstOutcome model domain
  valid table args premises := by
    cases args with | cons xs rest => cases rest with | cons n rest =>
      cases rest with | cons w rest => cases rest with | cons r rest =>
        cases rest
        obtain ⟨lengthBound, bound, splitShape, halvesLaw, mapLaw⟩ := premises
        simp only [firstOutcome, Values.get] at lengthBound bound splitShape halvesLaw mapLaw ⊢
        simp only [firstBody, Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
          Operands.eval, Regions.denote, Values.get, Environment.prepend, Environment.push,
          SiteObservations.closed, SiteObservations.silent, PIR.Process.bind]
        change (invoke table (halvesHelper domain bindings) (tableValues model domain xs n w)).bind _ = _
        rw [halvesLaw]
        by_cases positive : 0 < n
        · obtain ⟨nonempty, even⟩ := splitShape positive
          have same : (xs.take (xs.length / 2)).length = (xs.drop (xs.length / 2)).length := by
            simp only [List.length_take, List.length_drop]
            omega
          -- Collection admission needs the original range as well as split shape.
          have lowBound : (xs.take (xs.length / 2)).length < indexLimit := by
            simp only [List.length_take]
            exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) lengthBound
          simp only [halvesOutcome, bound, positive, nonempty, even, and_self, ↓reduceIte,
            primitiveOutcome, PIR.Process.bind, Values.get, Environment.prepend, Environment.push]
          rw [mapLaw _ _ r lowBound same]
          have nPositive : 1 ≤ n := positive
          simp [Primitive.evaluateOn, checkedIndices, bound, show 1 < indexLimit by decide +kernel,
            nPositive, tableValues, primitiveOutcome, PIR.Process.bind,
            Values.get, Environment.prepend, Environment.push, restrictValues]
        · simp [halvesOutcome, bound, positive, primitiveOutcome, PIR.Process.bind]

/-- Pure size consequences used at every reached restriction, without unfolding
an actual iteration count or assuming anything about received messages. -/
theorem split_shape (xs : List (model.Field domain)) (n w : Nat)
    (positive : 0 < n) (width : 0 < w) (shape : xs.length = 2 ^ n * w) :
    0 < xs.length ∧ xs.length % 2 = 0 := by
  have nEq : n = n - 1 + 1 := by omega
  have size : xs.length = (2 ^ (n - 1) * w) * 2 := by
    rw [shape]
    conv_lhs => rw [nEq, Nat.pow_succ]
    ac_rfl
  constructor
  · rw [shape]
    exact Nat.mul_pos (Nat.pow_pos (by decide)) width
  · simp [size]

theorem restrict_size (xs : List (model.Field domain)) (n w : Nat) (r : model.Field domain)
    (positive : 0 < n) (shape : xs.length = 2 ^ n * w) :
    (restrictValues xs r).length = 2 ^ (n - 1) * w := by
  apply restrictValues_length
  have nEq : n = n - 1 + 1 := by omega
  rw [shape]
  conv_lhs => rw [nEq, Nat.pow_succ]
  ac_rfl

theorem restrict_bound (xs : List (model.Field domain)) (r : model.Field domain)
    (bound : xs.length < indexLimit) : (restrictValues xs r).length < indexLimit := by
  apply Nat.lt_of_le_of_lt _ bound
  simp only [restrictValues, List.length_zipWith, List.length_take, List.length_drop]
  exact le_trans (Nat.min_le_left _ _) (Nat.min_le_right _ _)


/-- Marked local step, shared by the finite restriction callback. -/
def step : ReferenceLaw model (firstInputs domain) (triple domain) :=
  marked model "s2" <| forward model (firstHelper domain bindings) (Operands.identity _)
    (firstOutcome model domain)

def foldStep : ReferenceLaw model
    [.vector domain, .index, .index, .field domain, .vector domain] (triple domain) :=
  marked model "body" <| forward model
    ⟨bindings.step, .local, firstInputs domain, triple domain⟩
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here))) .nil))))
    (firstOutcome model domain)

def prefixOutcome (xs point : List (model.Field domain)) (n w : Nat) :
    PIR.Outcome (Values model.Value (triple domain)) :=
  if point.length < indexLimit then
    if point.length ≤ n then
      .returned (tableValues model domain (restrictPrefixValues xs point) (n - point.length) w)
    else .stopped .reject
  else .stopped .exhausted

set_option backward.isDefEq.respectTransparency false in
/-- The existing finite fold consumes a reached-state law. All counts remain
symbolic, and the same body theorem is used at every index. -/
theorem fold_restriction
    (transition : Values model.Value (triple domain) → model.Field domain →
      PIR.Process closedInterface (Values model.Value (triple domain)))
    (law : ∀ xs n w r, xs.length < indexLimit → n < 64 → 0 < w → xs.length = 2 ^ n * w →
      transition (tableValues model domain xs n w) r =
        primitiveOutcome (firstOutcome model domain (.cons xs (.cons n (.cons w (.cons r .nil))))))
    (xs : List (model.Field domain)) (n w : Nat) (point : List (model.Field domain))
    (bound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2 ^ n * w) :
    Finite.fold transition point (tableValues model domain xs n w) =
      if point.length ≤ n then
        .done (tableValues model domain (restrictPrefixValues xs point) (n - point.length) w)
      else .halt .reject := by
  induction point generalizing xs n with
  | nil => rfl
  | cons r point ih =>
      rw [Finite.fold, law xs n w r bound small width shape]
      change (primitiveOutcome (if 0 < n then
        .returned (tableValues model domain (restrictValues xs r) (n - 1) w)
        else .stopped .reject)).bind _ = _
      by_cases positive : 0 < n
      · simp only [firstOutcome, Values.get, positive, ↓reduceIte, primitiveOutcome, PIR.Process.bind]
        rw [ih (restrictValues xs r) (n - 1) (restrict_bound model domain xs r bound)
          (by omega) (restrict_size model domain xs n w r positive shape)]
        have order : point.length ≤ n - 1 ↔ (r :: point).length ≤ n := by
          simp only [List.length_cons]; omega
        have remaining : n - 1 - point.length = n - (r :: point).length := by
          simp only [List.length_cons]; omega
        simp only [order, remaining, restrictPrefixValues, List.foldl_cons]
      · have tooLong : ¬ (r :: point).length ≤ n := by
          simp only [List.length_cons]; omega
        simp only [firstOutcome, Values.get, positive, tooLong, ↓reduceIte,
          primitiveOutcome, PIR.Process.bind]

set_option backward.isDefEq.respectTransparency false in
def fold : ReferenceLaw model [.vector domain, .vector domain, .index, .index] (triple domain) where
  body := foldBody domain bindings
  Requires table args :=
    (args.get (.there .here)).length < indexLimit ∧
    args.get (.there (.there .here)) < 64 ∧
    0 < args.get (.there (.there (.there .here))) ∧
    (args.get (.there .here)).length =
      2 ^ args.get (.there (.there .here)) * args.get (.there (.there (.there .here))) ∧
    ∀ xs n w r, xs.length < indexLimit → n < 64 → 0 < w → xs.length = 2 ^ n * w →
      invoke table (foldSpec domain bindings).stepHelper
        (.cons xs (.cons n (.cons w (.cons r (.cons (args.get .here) .nil))))) =
          primitiveOutcome (firstOutcome model domain (.cons xs (.cons n (.cons w (.cons r .nil)))))
  reference args := prefixOutcome model domain (args.get (.there .here)) (args.get .here)
    (args.get (.there (.there .here))) (args.get (.there (.there (.there .here))))
  valid table args premises := by
    cases args with | cons point rest => cases rest with | cons xs rest =>
      cases rest with | cons n rest => cases rest with | cons w rest =>
        cases rest
        obtain ⟨bound, small, width, shape, stepLaw⟩ := premises
        have expanded : (foldBody domain bindings).denote
            (Evaluation.meaningOn model SiteObservations.closed table)
            (Values.cons point (.cons xs (.cons n (.cons w .nil)))).get =
            Evaluation.denoteFoldOn table (foldSpec domain bindings)
              (.cons point (.cons xs (.cons n (.cons w .nil)))) := by
          simp only [foldBody, Region.denote, Evaluation.meaningOn, Evaluation.operationOn,
            Operands.eval, Regions.denote, Values.get]
          trans (Evaluation.denoteFoldOn table (foldSpec domain bindings)
            (.cons point (.cons xs (.cons n (.cons w .nil))))).bind .done
          · congr 1
            funext results
            cases results with | cons a rest => cases rest with | cons b rest =>
              cases rest with | cons c rest => cases rest; rfl
          · exact PIR.Process.bind_done _
        rw [expanded]
        change Finite.admitThen
          ((foldSpec domain bindings).domain.admit (carriers := model.toCarriers) (.cons point .nil))
          (fun items => Finite.fold
            (Evaluation.foldTransitionOn table (foldSpec domain bindings) (.cons point .nil) .nil)
            items (tableValues model domain xs n w)) = _
        have admitted : (foldSpec domain bindings).domain.admit
            (carriers := model.toCarriers) (.cons point .nil) =
            if point.length < indexLimit then .returned (point.map fun r => .cons r .nil)
            else .stopped .exhausted := by
          simp [foldSpec, DomainSpec.admit_elements, Collection.values, Values.get]
        rw [admitted]
        by_cases pointBound : point.length < indexLimit
        · simp only [pointBound, ↓reduceIte, Finite.admitThen, Finite.fold_map]
          have law : ∀ (ys : List (model.Field domain)) (dim cols : Nat) (r : model.Field domain),
              ys.length < indexLimit → dim < 64 →
              0 < cols → ys.length = 2 ^ dim * cols →
              Evaluation.foldTransitionOn table (foldSpec domain bindings) (.cons point .nil) .nil
                (tableValues model domain ys dim cols) (.cons r .nil) =
                primitiveOutcome (firstOutcome model domain
                  (.cons ys (.cons dim (.cons cols (.cons r .nil))))) := by
            intro ys dim cols r hlen hdim hcols hshape
            exact stepLaw ys dim cols r hlen hdim hcols hshape
          have computed := fold_restriction model domain
            (fun state r => Evaluation.foldTransitionOn table (foldSpec domain bindings)
              (.cons point .nil) .nil state (.cons r .nil))
            law xs n w point bound small width shape
          refine computed.trans ?_
          change (if point.length ≤ n then
            PIR.Process.done (tableValues model domain (restrictPrefixValues xs point) (n - point.length) w)
            else .halt .reject) = primitiveOutcome (prefixOutcome model domain xs point n w)
          simp only [prefixOutcome, pointBound, ↓reduceIte, primitiveOutcome]
          split <;> rfl
        · simp only [pointBound, ↓reduceIte, Finite.admitThen, prefixOutcome, Values.get,
            primitiveOutcome]

/-- Public wrappers preserve the complete table triple, including columns. -/
def foldWrapper : ReferenceLaw model
    [.vector domain, .index, .index, .vector domain] (triple domain) :=
  marked model "s0" <| forward model
    ⟨bindings.fold, .local, [.vector domain, .vector domain, .index, .index], triple domain⟩
    (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here)
      (.cons (.there (.there .here)) .nil))))
    (fun args => prefixOutcome model domain (args.get (.there .here)) (args.get .here)
      (args.get (.there (.there .here))) (args.get (.there (.there (.there .here)))))

def restrictionPrefix : ReferenceLaw model
    [.vector domain, .index, .index, .vector domain] (triple domain) :=
  marked model "s0" <| forward model
    ⟨bindings.foldWrapper, .local, [.vector domain, .index, .index, .vector domain], triple domain⟩
    (Operands.identity _)
    (fun args => prefixOutcome model domain (args.get .here)
      (args.get (.there (.there (.there .here)))) (args.get (.there .here))
      (args.get (.there (.there .here))))

def values : ReferenceLaw model (triple domain) [.vector domain] :=
  projection model (.cons .here .nil)

def valuesRealization : ReferenceLaw model (triple domain) [.vector domain] :=
  forward model ⟨bindings.values, .math, triple domain, [.vector domain]⟩
    (Operands.identity _) (values model domain).reference


end Zkc.Source.Structured.ReferenceLibrary.Multilinear
