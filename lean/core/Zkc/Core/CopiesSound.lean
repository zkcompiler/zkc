module

public import Zkc.Core.CopiesClasses
public import Zkc.Core.LocalEnds
public import Zkc.Core.ProtocolFactsSound

public section

/-! The check of copies is sound.

A protocol that passes the check of copies, run for a side that supports its requirements on
arguments of which the input agreements hold, never stops `incomplete`, and the output
agreements hold of what it returns.

The proof carries, through the denotation of a region, a value per class: every value in
scope whose support is inside the side is the value of its class. Nothing is carried of the
type of a class: an operation made is sound for every typed operation that has its key, and
the values that the valuation reads give the operands their types.

What the statement is, and is not. Its two premises are part of it: the side supports the
requirements that the check returns (of every requirement of which the side holds two copies,
it contains the support of each), and the input agreements hold of the arguments. A side is
any set of roles, so a statement for one side is not a statement about what a role outside it
may send: a value received from outside the side is any value. The conclusion excludes the one
stop `incomplete` and constrains what is returned; it says nothing of the other stops (the
check of facts excludes `undefined`; a guard may reject), of whether an honest run returns, of
probabilities, or of cost.

The statement is proved for every instruction of a protocol body, for a definition
(`ProtocolDefinition.copies_sound`) and for the protocols of a program
(`Protocols.table_agrees`).
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## Processes that never stop `incomplete` -/

/-- A process never stops `incomplete`, and every result it returns satisfies `post`,
through every reply of every effect. -/
@[expose] def Coheres {I : PIR.Signature} {A : Type} (post : A → Prop) : PIR.Process I A → Prop
  | .done value => post value
  | .halt why => why ≠ .incomplete
  | .call _ next => ∀ reply, Coheres post (next reply)

theorem Coheres.done {I : PIR.Signature} {A : Type} {post : A → Prop} {value : A}
    (holds : post value) : Coheres post (.done value : PIR.Process I A) := holds

theorem Coheres.halt {I : PIR.Signature} {A : Type} {post : A → Prop} {why : PIR.Stop}
    (other : why ≠ .incomplete) : Coheres post (.halt why : PIR.Process I A) := other

theorem Coheres.call {I : PIR.Signature} {A : Type} {post : A → Prop} {op : I.Op}
    {next : I.Reply op → PIR.Process I A} (continues : ∀ reply, Coheres post (next reply)) :
    Coheres post (.call op next) := continues

theorem Coheres.bind {I : PIR.Signature} {A B : Type} {post : A → Prop} {after : B → Prop}
    {source : PIR.Process I A} {next : A → PIR.Process I B} (coheres : Coheres post source)
    (continues : ∀ value, post value → Coheres after (next value)) :
    Coheres after (source.bind next) := by
  induction source with
  | done value => exact continues value coheres
  | halt why => exact coheres
  | call op tail ih => exact fun reply => ih reply (coheres reply)

theorem Coheres.weaken {I : PIR.Signature} {A : Type} {post wider : A → Prop}
    {source : PIR.Process I A} (coheres : Coheres post source)
    (implies : ∀ value, post value → wider value) : Coheres wider source := by
  induction source with
  | done value => exact implies value coheres
  | halt why => exact coheres
  | call op tail ih => exact fun reply => ih reply (coheres reply)

variable {model : Model}

/-- A process that ends agrees with what holds of the value it returns. -/
theorem Ends.coheres {A : Type} {post : A → Prop} {process : PIR.Process (Effects model) A}
    (ends : Ends process) (holds : ∀ value, process = .done value → post value) :
    Coheres post process := by
  rcases ends with ⟨value, returned⟩ | ⟨why, other, stopped⟩
  · rw [returned]
    exact holds value returned
  · rw [stopped]
    exact other

/-! ## The operands of a key -/

/-- The numbers of the operands of a raw local operation, in the order of the typed one. -/
@[expose] def Raw.LocalStep.operands : Raw.LocalStep → List Nat
  | .op _ operands => operands
  | .call _ operands => operands
  | .conditional condition captures _ _ _ => condition :: captures
  | .match _ value captures _ _ => value :: captures
  | .loop (.static _) carried captures _ _ => carried ++ captures
  | .loop (.runtime _ count) carried captures _ _ => count :: (carried ++ captures)
  | .guard _ condition => [condition]
  | .literal _ => []
  | .builtin _ operands => operands

section Keys

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- The operands of an unelaborated operation are the numbers it was given, when there is one
per argument. -/
theorem unelaborateLocalStep_operands (count : Nat) :
    ∀ (op : LocalOp operations functions deployed)
      (bodies : Regions (LocalDialect operations functions deployed) op.regions)
      (values : List Nat), values.length = op.arguments.length →
        (unelaborateLocalStep count op values (unelaborateLocalRegions count bodies)).operands =
          values
  | .op _ _, .nil, _, _ => rfl
  | .call _ _, .nil, _, _ => rfl
  | .conditional _ _, .cons _ (.cons _ .nil), _ :: _, _ => rfl
  | .match _ _ _ _, _, _ :: _, _ => rfl
  | .loop (.static _) carried _ _, .cons _ .nil, values, _ => by
      simp only [unelaborateLocalStep, unelaborateLocalRegions, Raw.LocalStep.operands,
        List.take_append_drop]
  | .loop (.runtime _) carried _ _, .cons _ .nil, _ :: values, _ => by
      simp only [unelaborateLocalStep, unelaborateLocalRegions, Raw.LocalStep.operands,
        List.take_append_drop]
  | .guard _, .nil, [_], _ => rfl
  | .literal _, .nil, [], _ => rfl
  | .builtin _, .nil, _, _ => rfl
  | .conditional _ _, _, [], counted => nomatch counted
  | .match _ _ _ _, _, [], counted => nomatch counted
  | .loop (.runtime _) _ _ _, _, [], counted => nomatch counted
  | .guard _, .nil, [], counted => nomatch counted
  | .guard _, .nil, _ :: _ :: _, counted => nomatch counted
  | .literal _, .nil, _ :: _, counted => nomatch counted

/-- Numbers that have the types of a list are as many as the types. -/
theorem NumbersHave.length {α : Type} {typeOf : Nat → Option α} :
    ∀ {values : List Nat} {types : List α}, NumbersHave typeOf values types →
      values.length = types.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, rest⟩ => congrArg (· + 1) rest.length
  | [], _ :: _, impossible => impossible.elim
  | _ :: _, [], impossible => impossible.elim

/-- Two typed operations with one key, whose operands have the types that one typing gives
their numbers, are one operation on the same numbers. -/
theorem LocalElaborated.eq_of_key (typeTable : TypeTable) (rows : Scope operations)
    (callees : Scope functions) (typeOf : Nat → Option Ty)
    {first second : LocalOp operations functions deployed}
    {firstBodies : Regions (LocalDialect operations functions deployed) first.regions}
    {secondBodies : Regions (LocalDialect operations functions deployed) second.regions}
    {firstValues secondValues : List Nat}
    (firstTyped : NumbersHave typeOf firstValues first.arguments)
    (secondTyped : NumbersHave typeOf secondValues second.arguments)
    (firstNamed : (Ty.allNamed typeTable first.arguments &&
      Ty.allNamed typeTable first.results) = true)
    (secondNamed : (Ty.allNamed typeTable second.arguments &&
      Ty.allNamed typeTable second.results) = true)
    (firstOk : LocalRegionsOk typeTable rows callees firstBodies)
    (secondOk : LocalRegionsOk typeTable rows callees secondBodies)
    (same : unelaborateLocalStep callees.depth first firstValues
        (unelaborateLocalRegions callees.depth firstBodies) =
      unelaborateLocalStep callees.depth second secondValues
        (unelaborateLocalRegions callees.depth secondBodies)) :
    (⟨first, firstBodies, firstValues⟩ : LocalElaborated operations functions deployed) =
      ⟨second, secondBodies, secondValues⟩ := by
  have one := elaborateLocalStep_unelaborate typeTable rows callees typeOf first firstBodies
    firstValues firstTyped firstNamed firstOk
  have two := elaborateLocalStep_unelaborate typeTable rows callees typeOf second secondBodies
    secondValues secondTyped secondNamed secondOk
  rw [same] at one
  exact Except.ok.inj (one.symm.trans two)

variable {model : Model}

/-- One operation on the same numbers, on arguments that one store reads at them, returns
the same results. -/
theorem localOperation_results_of_eq (table : FunctionTable model functions)
    {first second : LocalOp operations functions deployed}
    {firstBodies : Regions (LocalDialect operations functions deployed) first.regions}
    {secondBodies : Regions (LocalDialect operations functions deployed) second.regions}
    {firstValues secondValues : List Nat}
    (same : (⟨first, firstBodies, firstValues⟩ : LocalElaborated operations functions deployed) =
      ⟨second, secondBodies, secondValues⟩)
    {store : Store model} {firstArguments : Values model.Value first.arguments}
    {secondArguments : Values model.Value second.arguments}
    (firstReads : Reads store firstValues firstArguments)
    (secondReads : Reads store secondValues secondArguments)
    {firstResults : Values model.Value first.results}
    {secondResults : Values model.Value second.results}
    (firstDone : localOperation model table first firstArguments
      (firstBodies.denote (localMeaning model table)) = .done firstResults)
    (secondDone : localOperation model table second secondArguments
      (secondBodies.denote (localMeaning model table)) = .done secondResults) :
    entryOf firstResults = entryOf secondResults := by
  cases same
  have arguments := Reads.unique firstReads secondReads
  cases arguments
  cases firstDone.symm.trans secondDone
  rfl

end Keys

/-! ## The value of a class -/

namespace Copies

/-- The value of each class. A class without a value is a class of which no copy is known to
the side. -/
structure Valuation (model : Model) where
  value : Store model

/-- A valuation agrees with an earlier one on the classes below a number. -/
def Valuation.Extends {model : Model} (later earlier : Valuation model) (next : Nat) : Prop :=
  ∀ class_, class_ < next → later.value class_ = earlier.value class_

theorem Valuation.Extends.refl {model : Model} (valuation : Valuation model) (next : Nat) :
    valuation.Extends valuation next := fun _ _ => rfl

theorem Valuation.Extends.trans {model : Model} {first second third : Valuation model}
    {next later : Nat} (one : second.Extends first next) (two : third.Extends second later)
    (grows : next ≤ later) : third.Extends first next := fun class_ below =>
  (two class_ (Nat.lt_of_lt_of_le below grows)).trans (one class_ below)

end Copies

/-- The numbers at which a store reads values have the types of the values, by the types of
the store's entries. -/
theorem Reads.numbersHave {model : Model} {store : Store model} :
    ∀ {levels : List Nat} {types : List Ty} {values : Values model.Value types},
      Reads store levels values →
        NumbersHave (fun level => (store level).map (·.1)) levels types
  | [], _, .nil, _ => trivial
  | level :: _, _, .cons _ _, reads =>
      ⟨by
        show (store level).map (·.1) = _
        rw [reads.1]
        rfl, reads.2.numbersHave⟩
  | [], _, .cons _ _, reads => reads.elim
  | _ :: _, _, .nil, reads => reads.elim

/-- Values are read at the levels of a list by a store that agrees on them. -/
theorem Reads.congr {model : Model} {store other : Store model} :
    ∀ {levels : List Nat} {types : List Ty} {values : Values model.Value types},
      Reads store levels values → (∀ level ∈ levels, other level = store level) →
        Reads other levels values
  | [], _, .nil, _, _ => trivial
  | level :: _, _, .cons _ _, reads, same =>
      ⟨(same level (List.mem_cons_self ..)).trans reads.1,
        Reads.congr reads.2 fun other member => same other (List.mem_cons_of_mem _ member)⟩
  | [], _, .cons _ _, reads, _ => reads.elim
  | _ :: _, _, .nil, reads, _ => reads.elim

section Sound

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} (typeTable : TypeTable) (rows : Scope operations) (callees : Scope functions)
  (functionTable : FunctionTable model functions)

/-- An entry of the operations made is sound for a valuation: its operands and its results are
classes below `next`, and for every typed operation that has its key, whenever the valuation
reads arguments at the operands and the operation returns on them, the valuation has the
results at the classes of the entry. The operation is any that has the key: nothing is said of
the types of the classes, and an operation whose arguments the valuation does not read is not
constrained. -/
def Copies.MadeSound (valuation : Copies.Valuation model) (next : Nat)
    (entry : Raw.LocalStep × List Nat) : Prop :=
  (∀ class_ ∈ entry.1.operands, class_ < next) ∧ (∀ class_ ∈ entry.2, class_ < next) ∧
    ∀ (op : LocalOp operations functions deployed)
      (bodies : Regions (LocalDialect operations functions deployed) op.regions)
      (classes : List Nat),
      entry.1 = unelaborateLocalStep functions.length op classes
        (unelaborateLocalRegions functions.length bodies) →
      (Ty.allNamed typeTable op.arguments && Ty.allNamed typeTable op.results) = true →
      LocalRegionsOk typeTable rows callees bodies →
      ∀ (arguments : Values model.Value op.arguments) (results : Values model.Value op.results),
        Reads valuation.value classes arguments →
        localOperation model functionTable op arguments
          (bodies.denote (localMeaning model functionTable)) = .done results →
        ∀ (index class_ : Nat), entry.2[index]? = some class_ →
          valuation.value class_ = entryOf results index

/-- A sound entry stays sound under a valuation that extends the first from a later class. -/
theorem Copies.MadeSound.extend {valuation later : Copies.Valuation model} {next after : Nat}
    {entry : Raw.LocalStep × List Nat}
    (sound : Copies.MadeSound (deployed := deployed) typeTable rows callees functionTable
      valuation next entry)
    (extends_ : later.Extends valuation next) (grows : next ≤ after) :
    Copies.MadeSound (deployed := deployed) typeTable rows callees functionTable later after
      entry := by
  obtain ⟨below, resultsBelow, made⟩ := sound
  refine ⟨fun class_ member => Nat.lt_of_lt_of_le (below class_ member) grows,
    fun class_ member => Nat.lt_of_lt_of_le (resultsBelow class_ member) grows,
    fun op bodies classes key named ok arguments results read returned index class_ found => ?_⟩
  have operands : entry.1.operands = classes := by
    rw [key]
    exact unelaborateLocalStep_operands functions.length op bodies classes read.length
  have earlier : Reads valuation.value classes arguments :=
    Reads.congr read fun class_ member => (extends_ class_ (below class_ (operands ▸ member))).symm
  exact (extends_ class_ (resultsBelow class_ (List.mem_of_getElem? found))).trans
    (made op bodies classes key named ok arguments results earlier returned index class_ found)

/-- What the check knows at a point holds of the values of a side: the holder of every value
in scope is in its support, and when its support is inside the side the value is the value of
its class; every operation made is sound. -/
structure Copies.State.Sound (side : Side) (valuation : Copies.Valuation model)
    (state : Copies.State) {Γ : List Located} (env : Environment (SideValue model side) Γ) :
    Prop where
  depth : state.values.length = Γ.length
  copies : ∀ {located : Located} (reference : Var Γ located),
    (state.at_ (Scope.number Γ.length reference)).support.contains located.holder = true ∧
    (state.at_ (Scope.number Γ.length reference)).class_ < state.next ∧
    ((state.at_ (Scope.number Γ.length reference)).support.all side = true →
      valuation.value (state.at_ (Scope.number Γ.length reference)).class_ =
        storeOf (plainEnvironment side env) (Scope.number Γ.length reference))
  made : ∀ entry ∈ state.made,
    Copies.MadeSound (deployed := deployed) typeTable rows callees functionTable valuation
      state.next entry

end Sound

/-! ## Levels -/

/-- The entry at a level of a context with more values: an earlier level keeps its entry, and
a new level has the entry bound at it. -/
theorem atLevel?_bindAll_cases {β : Type} (added Δ : List β) {level : Nat} {entry : β}
    (found : atLevel? (bindAll Δ added) (Δ.length + added.length) level = some entry) :
    (level < Δ.length ∧ atLevel? Δ Δ.length level = some entry) ∨
      (Δ.length ≤ level ∧ added[level - Δ.length]? = some entry) := by
  unfold atLevel? at found
  split at found
  · rename_i below
    by_cases earlier : level < Δ.length
    · left
      refine ⟨earlier, ?_⟩
      have position : Δ.length + added.length - 1 - level =
          (Δ.length - 1 - level) + added.length := by omega
      rw [position, getElem?_bindAll_old] at found
      simp only [atLevel?, earlier, ↓reduceIte]
      exact found
    · right
      refine ⟨Nat.le_of_not_lt earlier, ?_⟩
      have inside : level - Δ.length < added.length := by omega
      have position : Δ.length + added.length - 1 - level =
          added.length - 1 - (level - Δ.length) := by omega
      rw [position, getElem?_bindAll_new added Δ _ inside] at found
      exact found
  · cases found

theorem atLevel?_lt {β : Type} {Δ : List β} {depth level : Nat} {entry : β}
    (found : atLevel? Δ depth level = some entry) : level < depth := by
  unfold atLevel? at found
  split at found
  · assumption
  · cases found

/-- The entry at the level of a reference is the type of the reference. -/
theorem atLevel?_number {β : Type} {Δ : List β} {entry : β} (reference : Var Δ entry) :
    atLevel? Δ Δ.length (Scope.number Δ.length reference) = some entry :=
  atLevel?_index reference

/-- The store of a side after more values: the earlier levels are unchanged, and the new
levels have the new values of the side, in order. -/
theorem storeOf_plain_bound {model : Model} (side : Side) {added Γ : List Located}
    (env : Environment (SideValue model side) Γ) (values : Values (SideValue model side) added)
    (level : Nat) :
    storeOf (plainEnvironment side (Environment.bindAll env values)) level =
      if level < Γ.length then storeOf (plainEnvironment side env) level
      else entryOf (plainValues side values) (level - Γ.length) := by
  rw [storeOf_plain_bindAll, storeOf_bindAll, List.length_map]

/-! ## Copies of values -/

section Copies

variable {model : Model}

/-- What the check says of a copy holds of a value of a side: the holder is in the support,
the class is below `next`, and when the support is inside the side the value is the value of
the class. -/
def Copies.Copy.Holds (side : Side) (valuation : Copies.Valuation model) (next : Nat)
    (copy : Copies.Copy) (located : Located) (entry : Option (Sigma model.Value)) : Prop :=
  copy.support.contains located.holder = true ∧ copy.class_ < next ∧
    (copy.support.all side = true → valuation.value copy.class_ = entry)

/-- The copies of a list are copies of the values of a tuple, in order. -/
def Copies.Hold (side : Side) (valuation : Copies.Valuation model) (next : Nat)
    (copies : List Copies.Copy) {types : List Located}
    (values : Values (SideValue model side) types) : Prop :=
  copies.length = types.length ∧
    ∀ (index : Nat) (located : Located), types[index]? = some located →
      (copies.getD index default).Holds side valuation next located
        (entryOf (plainValues side values) index)

theorem Copies.Copy.Holds.extend {side : Side} {valuation later : Copies.Valuation model}
    {next after : Nat} {copy : Copies.Copy} {located : Located}
    {entry : Option (Sigma model.Value)} (holds : copy.Holds side valuation next located entry)
    (extends_ : later.Extends valuation next) (grows : next ≤ after) :
    copy.Holds side later after located entry :=
  ⟨holds.1, Nat.lt_of_lt_of_le holds.2.1 grows,
    fun inside => (extends_ _ holds.2.1).trans (holds.2.2 inside)⟩

theorem Copies.Hold.extend {side : Side} {valuation later : Copies.Valuation model}
    {next after : Nat} {copies : List Copies.Copy} {types : List Located}
    {values : Values (SideValue model side) types} (hold : Copies.Hold side valuation next copies values)
    (extends_ : later.Extends valuation next) (grows : next ≤ after) :
    Copies.Hold side later after copies values :=
  ⟨hold.1, fun index located found => (hold.2 index located found).extend extends_ grows⟩

end Copies

section Reading

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} {typeTable : TypeTable} {rows : Scope operations} {callees : Scope functions}
  {functionTable : FunctionTable model functions} {side : Side}
  {valuation : Copies.Valuation model} {state : Copies.State} {Γ : List Located}
  {env : Environment (SideValue model side) Γ}

/-- The copy at the level of a reference is a copy of the value of the reference. -/
theorem Copies.State.Sound.reference
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env) {located : Located} (reference : Var Γ located) :
    (state.at_ (Scope.number Γ.length reference)).Holds side valuation state.next located
      (some ⟨plainType side located,
        plainValue (side located.holder) (type := located.type) (env reference)⟩) := by
  have known := sound.copies reference
  refine ⟨known.1, known.2.1, fun inside => ?_⟩
  rw [known.2.2 inside, plain_number]

/-- The copies at the levels of operands are copies of the values of the operands. -/
theorem Copies.State.Sound.operands
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env) :
    ∀ {types : List Located} (operands : Operands Γ types),
      Copies.Hold side valuation state.next
        ((Scope.numbers Γ.length operands).map state.at_) (Operands.eval env operands)
  | _, .nil => ⟨rfl, fun _ _ found => nomatch found⟩
  | _, .cons reference rest => by
      have tail := sound.operands rest
      refine ⟨congrArg (· + 1) tail.1, fun index located found => ?_⟩
      cases index with
      | zero =>
          cases Option.some.inj found
          exact sound.reference reference
      | succ index => exact tail.2 index located found

/-- A level with an entry is the level of a reference. -/
theorem var_of_atLevel {β : Type} {Δ : List β} {level : Nat} {entry : β}
    (found : atLevel? Δ Δ.length level = some entry) :
    ∃ reference : Var Δ entry, Scope.number Δ.length reference = level := by
  have below := atLevel?_lt found
  unfold atLevel? at found
  simp only [below, ↓reduceIte] at found
  refine ⟨⟨Δ.length - 1 - level, found⟩, ?_⟩
  simp only [Scope.number, Scope.position]
  omega

/-- After an instruction: the values in scope before it keep their copies under a valuation
that extends the one before, and the results are bound with their copies. -/
theorem Copies.State.Sound.bind
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env)
    {later : Copies.Valuation model} (extends_ : later.Extends valuation state.next)
    {after : Copies.State} (kept : after.values = state.values) (grows : state.next ≤ after.next)
    (made : ∀ entry ∈ after.made,
      Copies.MadeSound (deployed := deployed) typeTable rows callees functionTable later
        after.next entry)
    {added : List Located} {copies : List Copies.Copy}
    {values : Values (SideValue model side) added}
    (hold : Copies.Hold side later after.next copies values) :
    Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side later
      (after.push copies) (Environment.bindAll env values) := by
  have depth : after.values.length = Γ.length := kept ▸ sound.depth
  refine ⟨?_, fun {located} reference => ?_, made⟩
  · show (after.values ++ copies).length = _
    rw [List.length_append, depth, hold.1, length_bindAll]
  · have found := atLevel?_number reference
    rw [length_bindAll] at found ⊢
    rcases atLevel?_bindAll_cases added Γ found with ⟨below, earlier⟩ | ⟨beyond, new⟩
    · obtain ⟨old, level⟩ := var_of_atLevel earlier
      have copy : (after.push copies).at_ (Scope.number (Γ.length + added.length) reference) =
          state.at_ (Scope.number Γ.length old) := by
        show (after.values ++ copies).getD _ default = state.values.getD _ default
        have inside : Scope.number Γ.length old < state.values.length := by
          rw [level, sound.depth]; exact below
        rw [level, kept]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (level ▸ inside)]
      rw [copy]
      have known := (sound.reference old).extend extends_ grows
      refine ⟨known.1, known.2.1, fun inside => ?_⟩
      rw [known.2.2 inside, storeOf_plain_bound]
      simp only [below, ↓reduceIte]
      rw [← level, plain_number]
    · have copy : (after.push copies).at_ (Scope.number (Γ.length + added.length) reference) =
          copies.getD (Scope.number (Γ.length + added.length) reference - Γ.length) default := by
        show (after.values ++ copies).getD _ default = _
        have outside : after.values.length ≤ Scope.number (Γ.length + added.length) reference := by
          rw [depth]; exact beyond
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right outside, depth]
      rw [copy]
      have known := hold.2 _ located new
      refine ⟨known.1, known.2.1, fun inside => ?_⟩
      rw [known.2.2 inside, storeOf_plain_bound]
      simp only [Nat.not_lt.mpr beyond, ↓reduceIte]

end Reading

/-- A valuation with one more class. -/
def Copies.Valuation.set {model : Model} (valuation : Copies.Valuation model) (class_ : Nat)
    (entry : Option (Sigma model.Value)) : Copies.Valuation model :=
  { value := fun other => if other = class_ then entry else valuation.value other }

theorem Copies.Valuation.set_extends {model : Model} (valuation : Copies.Valuation model)
    {next class_ : Nat} (beyond : next ≤ class_) (entry : Option (Sigma model.Value)) :
    (valuation.set class_ entry).Extends valuation next := by
  intro other below
  have differs : other ≠ class_ := by omega
  simp only [Copies.Valuation.set, differs, ↓reduceIte]

section Fresh

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} {typeTable : TypeTable} {rows : Scope operations} {callees : Scope functions}
  {functionTable : FunctionTable model functions} {side : Side}
  {valuation : Copies.Valuation model} {state : Copies.State} {Γ : List Located}
  {env : Environment (SideValue model side) Γ}

/-- After an instruction whose results are copies of one new value: the class is the next
one, and its value is the value of every result whose support is inside the side. -/
theorem Copies.State.Sound.bindFresh
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env)
    {added : List Located} (values : Values (SideValue model side) added)
    (copies : List Copies.Copy) (entry : Option (Sigma model.Value))
    (counted : copies.length = added.length)
    (each : ∀ (index : Nat) (located : Located), added[index]? = some located →
      (copies.getD index default).class_ = state.next ∧
      (copies.getD index default).support.contains located.holder = true ∧
      ((copies.getD index default).support.all side = true →
        entryOf (plainValues side values) index = entry)) :
    ∃ later : Copies.Valuation model, later.Extends valuation state.next ∧
      Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side later
        (({ state with next := state.next + 1 } : Copies.State).push copies)
        (Environment.bindAll env values) := by
  have extends_ := Copies.Valuation.set_extends valuation (Nat.le_refl state.next) entry
  refine ⟨valuation.set state.next entry, extends_,
    sound.bind extends_ (after := { state with next := state.next + 1 }) rfl
      (Nat.le_succ _)
      (fun made member => (sound.made made member).extend typeTable rows callees functionTable
        extends_ (Nat.le_succ _))
      ⟨counted, fun index located found => ?_⟩⟩
  obtain ⟨class_, held, value⟩ := each index located found
  refine ⟨held, ?_, fun inside => ?_⟩
  · rw [class_]
    exact Nat.lt_succ_self _
  · rw [class_]
    simp only [Copies.Valuation.set, ↓reduceIte]
    exact (value inside).symm

end Fresh

/-! ## Presence steps -/

section Steps

variable {model : Model}

/-- An exchange never stops, and between two roles of the side the receiver has the value
sent. -/
theorem exchangeStep_coheres (site : Site) (type : Ty) : ∀ (sender receiver : Bool)
    (value : Held (model.Value type) sender),
    Coheres (fun result => sender = true → receiver = true →
        (⟨cond receiver type Ty.unit, plainValue receiver result⟩ : Sigma model.Value) =
          ⟨cond sender type Ty.unit, plainValue sender value⟩)
      (exchangeStep model site type sender receiver value)
  | true, true, _ => Coheres.done fun _ _ => rfl
  | true, false, _ => Coheres.call fun _ => Coheres.done fun _ absent => nomatch absent
  | false, true, _ => Coheres.call fun _ => Coheres.done fun absent _ => nomatch absent
  | false, false, _ => Coheres.done fun absent _ => nomatch absent

theorem receiveStep_coheres (site : Site) (type : Ty) : ∀ (receiver : Bool),
    Coheres (fun _ => True) (receiveStep model site type receiver)
  | true => Coheres.call fun _ => Coheres.done trivial
  | false => Coheres.done trivial

theorem receiverReplies_coheres (side : Side) (site : Site) (type : Ty) :
    ∀ (receivers : List Nat),
      Coheres (fun _ => True) (receiverReplies model side site type receivers)
  | [] => Coheres.done trivial
  | role :: rest =>
      (receiveStep_coheres site type (side role)).bind fun _ _ =>
        (receiverReplies_coheres side site type rest).bind fun _ _ => Coheres.done trivial

theorem sampleStep_coheres (site : Site) (law : SamplingRow) : ∀ (owner : Bool)
    (inputs : Values (fun type => Held (model.Value type) owner) law.inputs),
    Coheres (fun _ => True) (sampleStep model site law owner inputs)
  | true, _ => Coheres.call fun _ => Coheres.done trivial
  | false, _ => Coheres.done trivial

theorem drawStep_coheres {α : Type} {post : α → Prop} (site : Site) (law : SamplingRow)
    {onDraw : model.Value law.output → PIR.Process (Effects model) α}
    (drawn : ∀ reply, Coheres post (onDraw reply)) : ∀ (owner : Bool)
    (inputs : Values (fun type => Held (model.Value type) owner) law.inputs)
    (onOutside : owner = false → PIR.Process (Effects model) α),
    (∀ absent, Coheres post (onOutside absent)) →
      Coheres post (drawStep model site law onDraw owner inputs onOutside)
  | true, _, _, _ => Coheres.call drawn
  | false, _, _, outside => outside rfl

/-- A coin that every role of a list holds is, for a role of the side, the value at the role's
position. -/
theorem entryOf_heldCopies (side : Side) (type : Ty) (reply : model.Value type) :
    ∀ (roles : List Nat) (index role : Nat), roles[index]? = some role → side role = true →
      entryOf (plainValues side (heldCopies model side type reply roles)) index =
        some ⟨type, reply⟩
  | [], _, _, found, _ => nomatch found
  | first :: _, 0, _, found, member => by
      cases Option.some.inj found
      exact congrArg some (plain_entry_of (side first) member reply)
  | _ :: roles, index + 1, role, found, member =>
      entryOf_heldCopies side type reply roles index role found member

end Steps

/-! ## Local operations -/

namespace Copies

theorem contains_foldl_union {role : Nat} : ∀ (copies : List Copy) {start : List Nat},
    start.contains role = true →
      (copies.foldl (fun support copy => union support copy.support) start).contains role = true
  | [], _, inside => inside
  | copy :: rest, _, inside =>
      contains_foldl_union rest (contains_union_left (second := copy.support) inside)

theorem all_of_foldl_union {side : Side} : ∀ (copies : List Copy) {start : List Nat},
    (copies.foldl (fun support copy => union support copy.support) start).all side = true →
      start.all side = true ∧ ∀ copy ∈ copies, copy.support.all side = true
  | [], _, inside => ⟨inside, fun _ member => nomatch member⟩
  | copy :: rest, start, inside => by
      have later := all_of_foldl_union rest (start := union start copy.support) inside
      have parts := all_of_union later.1
      refine ⟨parts.1, fun other member => ?_⟩
      cases member with
      | head => exact parts.2
      | tail _ member => exact later.2 other member

end Copies

/-- Values read at levels are read at the images of the levels by a store that has, at the
image of each level, what the first store has at the level. -/
theorem Reads.map {model : Model} {store other : Store model} (image : Nat → Nat) :
    ∀ {levels : List Nat} {types : List Ty} {values : Values model.Value types},
      Reads store levels values → (∀ level ∈ levels, other (image level) = store level) →
        Reads other (levels.map image) values
  | [], _, .nil, _, _ => trivial
  | level :: _, _, .cons _ _, reads, same =>
      ⟨(same level (List.mem_cons_self ..)).trans reads.1,
        Reads.map image reads.2 fun other member => same other (List.mem_cons_of_mem _ member)⟩
  | [], _, .cons _ _, reads, _ => reads.elim
  | _ :: _, _, .nil, reads, _ => reads.elim

/-- Values are read at the consecutive numbers from a start by a store that has each at its
position. -/
theorem reads_range {model : Model} {store : Store model} :
    ∀ {types : List Ty} (values : Values model.Value types) (start : Nat),
      (∀ index, index < types.length → store (start + index) = entryOf values index) →
        Reads store ((List.range types.length).map (start + ·)) values
  | _, .nil, _, _ => trivial
  | _, .cons (Γ := rest) value values, start, each => by
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine ⟨each 0 (Nat.zero_lt_succ _), ?_⟩
      have tail := reads_range values (start + 1) fun index below => by
        have known := each (index + 1) (Nat.succ_lt_succ below)
        rw [← Nat.add_assoc, Nat.add_right_comm] at known
        exact known
      have same : (List.range rest.length).map ((start + ·) ∘ Nat.succ) =
          (List.range rest.length).map (start + 1 + ·) :=
        List.map_congr_left fun index _ => by
          show start + (index + 1) = start + 1 + index
          omega
      rw [same]
      exact tail

section Made

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} (typeTable : TypeTable) (rows : Scope operations) (callees : Scope functions)
  (functionTable : FunctionTable model functions)

/-- The results, by position, of the operation with a key on the arguments that a store reads
at its operands, when there is such an operation and it returns. -/
noncomputable def Copies.madeValue (deployed : Bool) (store : Store model) (key : Raw.LocalStep) :
    Nat → Option (Sigma model.Value) :=
  open Classical in
  if found : ∃ entries : Nat → Option (Sigma model.Value),
      ∃ (op : LocalOp operations functions deployed)
        (bodies : Regions (LocalDialect operations functions deployed) op.regions)
        (classes : List Nat) (arguments : Values model.Value op.arguments)
        (results : Values model.Value op.results),
        key = unelaborateLocalStep functions.length op classes
          (unelaborateLocalRegions functions.length bodies) ∧
        (Ty.allNamed typeTable op.arguments && Ty.allNamed typeTable op.results) = true ∧
        LocalRegionsOk typeTable rows callees bodies ∧
        Reads store classes arguments ∧
        localOperation model functionTable op arguments
          (bodies.denote (localMeaning model functionTable)) = .done results ∧
        entries = entryOf results
  then Classical.choose found else fun _ => none

variable {typeTable rows callees functionTable}

/-- The results of the operation with a key are those of any typed operation that has the
key, on arguments that the store reads: two such operations are one operation, since the
store gives the operands their types. -/
theorem Copies.madeValue_eq {store : Store model} {key : Raw.LocalStep}
    {op : LocalOp operations functions deployed}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions}
    {classes : List Nat} {arguments : Values model.Value op.arguments}
    {results : Values model.Value op.results}
    (keyed : key = unelaborateLocalStep functions.length op classes
      (unelaborateLocalRegions functions.length bodies))
    (named : (Ty.allNamed typeTable op.arguments && Ty.allNamed typeTable op.results) = true)
    (ok : LocalRegionsOk typeTable rows callees bodies)
    (reads : Reads store classes arguments)
    (returned : localOperation model functionTable op arguments
      (bodies.denote (localMeaning model functionTable)) = .done results) :
    Copies.madeValue typeTable rows callees functionTable deployed store key =
      entryOf results := by
  unfold Copies.madeValue
  split
  · rename_i chosen
    obtain ⟨other, otherBodies, otherClasses, otherArguments, otherResults, otherKeyed, otherNamed,
      otherOk, otherReads, otherReturned, entries⟩ := Classical.choose_spec chosen
    rw [entries]
    -- the operands of the key are the classes of both
    have operands : otherClasses = classes := by
      have one := unelaborateLocalStep_operands functions.length other otherBodies otherClasses
        otherReads.length
      have two := unelaborateLocalStep_operands functions.length op bodies classes reads.length
      rw [← otherKeyed] at one
      rw [← keyed] at two
      exact one.symm.trans two
    cases operands
    have same := LocalElaborated.eq_of_key typeTable rows callees
      (fun level => (store level).map (·.1)) otherReads.numbersHave reads.numbersHave otherNamed
      named otherOk ok (by rw [callees.counted, ← otherKeyed, ← keyed])
    exact localOperation_results_of_eq functionTable same otherReads reads otherReturned returned
  · rename_i missing
    exact absurd ⟨entryOf results, op, bodies, classes, arguments, results, keyed, named, ok,
      reads, returned, rfl⟩ missing

end Made

section At

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool} {typeTable : TypeTable}
  {rows : Scope operations} {callees : Scope functions}
  {functionTable : FunctionTable model functions} {side : Side}
  {valuation : Copies.Valuation model} {state : Copies.State} {Γ : List Located}
  {env : Environment (SideValue model side) Γ}

/-- The classes of copies of values are below the next class. -/
theorem Copies.Hold.below {next : Nat} {types : List Located} {copies : List Copies.Copy}
    {values : Values (SideValue model side) types}
    (hold : Copies.Hold side valuation next copies values) :
    ∀ copy ∈ copies, copy.class_ < next := by
  intro copy member
  obtain ⟨index, inside, at_⟩ := List.getElem_of_mem member
  have typed : index < types.length := hold.1 ▸ inside
  have known := hold.2 index types[index] (List.getElem?_eq_getElem typed)
  have same : copies.getD index default = copy := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some, at_]
  rw [same] at known
  exact known.2.1

/-- After a local operation of a role: its results are bound with the classes of the operation
made, under a valuation that extends the one before. `values` are the results for the side:
when the role is in the side, the results that the operation returned. -/
theorem Copies.at_bound
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env)
    (role : Nat) (op : LocalOp operations functions deployed)
    (bodies : Regions (LocalDialect operations functions deployed) op.regions)
    (arguments : Operands Γ (Located.atRole role op.arguments))
    (named : (Ty.allNamed typeTable op.arguments && Ty.allNamed typeTable op.results) = true)
    (ok : LocalRegionsOk typeTable rows callees bodies)
    (values : Values (SideValue model side) (Located.atRole role op.results))
    (performed : ∀ member : side role = true, ∃ results : Values model.Value op.results,
      localOperation model functionTable op
          (Operands.eval (plainEnvironment side env) (presentOperands side member arguments))
          (bodies.denote (localMeaning model functionTable)) = .done results ∧
        ∀ index, entryOf (plainValues side values) index = entryOf results index) :
    ∃ later : Copies.Valuation model, later.Extends valuation state.next ∧
      Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side later
        ((Copies.numbered state
            (unelaborateLocalStep functions.length op
              (((Scope.numbers Γ.length arguments).map state.at_).map (·.class_))
              (unelaborateLocalRegions functions.length bodies))
            op.results.length).2.push
          ((Copies.numbered state
            (unelaborateLocalStep functions.length op
              (((Scope.numbers Γ.length arguments).map state.at_).map (·.class_))
              (unelaborateLocalRegions functions.length bodies))
            op.results.length).1.map fun class_ =>
              ⟨class_, ((Scope.numbers Γ.length arguments).map state.at_).foldl
                (fun support copy => Copies.union support copy.support) [role]⟩))
        (Environment.bindAll env values) := by
  have operandsHold := sound.operands arguments
  have below := operandsHold.below
  have classesBelow : ∀ class_ ∈ ((Scope.numbers Γ.length arguments).map state.at_).map
      (·.class_), class_ < state.next := by
    intro class_ member
    obtain ⟨copy, inside, rfl⟩ := List.mem_map.mp member
    exact below copy inside
  have operandsOf : (unelaborateLocalStep functions.length op
      (((Scope.numbers Γ.length arguments).map state.at_).map (·.class_))
      (unelaborateLocalRegions functions.length bodies)).operands =
        ((Scope.numbers Γ.length arguments).map state.at_).map (·.class_) :=
    unelaborateLocalStep_operands functions.length op bodies _ (by
      rw [List.length_map, operandsHold.1]
      exact List.length_map _)
  have roleIn : (((Scope.numbers Γ.length arguments).map state.at_).foldl
      (fun support copy => Copies.union support copy.support) [role]).contains role = true :=
    Copies.contains_foldl_union _ (by simp)
  -- when the support is inside the side, the valuation reads the role's operands
  have reads : ∀ member : side role = true,
      (((Scope.numbers Γ.length arguments).map state.at_).foldl
        (fun support copy => Copies.union support copy.support) [role]).all side = true →
      Reads valuation.value (((Scope.numbers Γ.length arguments).map state.at_).map (·.class_))
        (Operands.eval (plainEnvironment side env) (presentOperands side member arguments)) := by
    intro member inside
    have each := (Copies.all_of_foldl_union _ inside).2
    have stored := reads_eval (plainEnvironment side env) (presentOperands side member arguments)
    rw [List.length_map, numbers_presentOperands side member Γ.length arguments] at stored
    rw [List.map_map]
    refine Reads.map _ stored fun level found => ?_
    obtain ⟨located, reference, rfl⟩ := numbers_levels Γ.length arguments level found
    exact (sound.copies reference).2.2 (each _ (List.mem_map_of_mem found))
  have counted : (Located.atRole role op.results).length = op.results.length := List.length_map _
  cases found : state.made.find? fun entry => decide (entry.1 =
      unelaborateLocalStep functions.length op
        (((Scope.numbers Γ.length arguments).map state.at_).map (·.class_))
        (unelaborateLocalRegions functions.length bodies)) &&
      decide (entry.2.length = op.results.length) with
  | some entry =>
      -- the operation was made before: the valuation has its results at the entry's classes
      have member := List.mem_of_find?_eq_some found
      have kept := List.find?_some found
      have decided := Bool.and_eq_true_iff.mp kept
      have same := of_decide_eq_true decided.1
      have sized := of_decide_eq_true decided.2
      obtain ⟨_, resultsBelow, made⟩ := sound.made entry member
      simp only [Copies.numbered, found]
      refine ⟨valuation, Copies.Valuation.Extends.refl _ _,
        sound.bind (Copies.Valuation.Extends.refl _ _) rfl (Nat.le_refl _) sound.made
          ⟨by rw [List.length_map, sized, counted], fun index located at_ => ?_⟩⟩
      have inner : (op.results.map fun type => (⟨type, role⟩ : Located))[index]? = some located :=
        at_
      rw [List.getElem?_map] at inner
      cases result : op.results[index]? with
      | none => rw [result] at inner; cases inner
      | some type =>
          rw [result] at inner
          cases Option.some.inj inner
          have inside : index < entry.2.length := sized ▸ (List.getElem?_eq_some_iff.mp result).1
          have classAt : entry.2[index]? = some entry.2[index] := List.getElem?_eq_getElem inside
          rw [getD_map_of_getElem? _ entry.2 classAt]
          refine ⟨roleIn, resultsBelow _ (List.mem_of_getElem? classAt), fun supported => ?_⟩
          have present := Copies.side_of_contains supported roleIn
          obtain ⟨results, returned, entries⟩ := performed present
          rw [entries index]
          exact made op bodies _ same named ok _ results (reads present supported) returned index _
            classAt
  | none =>
      -- a new operation: its results have new classes, whose values are the results of the
      -- operation with its key on the arguments that the valuation reads
      simp only [Copies.numbered, found, Copies.State.fresh]
      have extends_ : Copies.Valuation.Extends
          ({ value := fun class_ =>
                if state.next ≤ class_ ∧ class_ < state.next + op.results.length then
                  Copies.madeValue typeTable rows callees functionTable deployed valuation.value
                    (unelaborateLocalStep functions.length op
                      (((Scope.numbers Γ.length arguments).map state.at_).map (·.class_))
                      (unelaborateLocalRegions functions.length bodies))
                    (class_ - state.next)
                else valuation.value class_ } : Copies.Valuation model) valuation state.next := by
        intro class_ less
        have outside : ¬ (state.next ≤ class_ ∧ class_ < state.next + op.results.length) :=
          fun both => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le less both.1)
        simp only [outside, ↓reduceIte]
      refine ⟨_, extends_, sound.bind extends_
        (after := { values := state.values, next := state.next + op.results.length
                    made := (_, (List.range op.results.length).map (state.next + ·)) :: state.made })
        rfl (Nat.le_add_right _ _) (fun entry member => ?_)
        ⟨by rw [List.length_map, List.length_map, List.length_range, counted],
          fun index located at_ => ?_⟩⟩
      · cases member with
        | tail _ member =>
            exact (sound.made entry member).extend typeTable rows callees functionTable extends_
              (Nat.le_add_right _ _)
        | head =>
            refine ⟨fun class_ inside => ?_, fun class_ inside => ?_,
              fun other otherBodies classes keyed otherNamed otherOk arguments' results read
                returned index class_ classAt => ?_⟩
            · rw [operandsOf] at inside
              exact Nat.lt_of_lt_of_le (classesBelow class_ inside) (Nat.le_add_right _ _)
            · obtain ⟨index, inside', rfl⟩ := List.mem_map.mp inside
              exact Nat.add_lt_add_left (List.mem_range.mp inside') _
            · have operands := unelaborateLocalStep_operands functions.length other otherBodies
                classes read.length
              rw [← keyed, operandsOf] at operands
              have earlier : Reads valuation.value classes arguments' :=
                Reads.congr read fun class_ inside =>
                  (extends_ class_ (classesBelow class_ (operands ▸ inside))).symm
              obtain ⟨inside, value⟩ := List.getElem?_eq_some_iff.mp classAt
              rw [List.getElem_map, List.getElem_range] at value
              rw [List.length_map, List.length_range] at inside
              have within : state.next ≤ state.next + index ∧
                  state.next + index < state.next + op.results.length :=
                ⟨Nat.le_add_right _ _, Nat.add_lt_add_left inside _⟩
              rw [← value]
              simp only [within, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
              rw [Copies.madeValue_eq keyed otherNamed otherOk earlier returned]
      · have inner : (op.results.map fun type => (⟨type, role⟩ : Located))[index]? = some located :=
          at_
        rw [List.getElem?_map] at inner
        cases result : op.results[index]? with
        | none => rw [result] at inner; cases inner
        | some type =>
            rw [result] at inner
            cases Option.some.inj inner
            have inside := (List.getElem?_eq_some_iff.mp result).1
            have classAt : ((List.range op.results.length).map (state.next + ·))[index]? =
                some (state.next + index) := by
              rw [List.getElem?_map, List.getElem?_range inside]
              rfl
            rw [getD_map_of_getElem? _ _ classAt]
            have within : state.next ≤ state.next + index ∧
                state.next + index < state.next + op.results.length :=
              ⟨Nat.le_add_right _ _, Nat.add_lt_add_left inside _⟩
            refine ⟨roleIn, within.2, fun supported => ?_⟩
            have present := Copies.side_of_contains supported roleIn
            obtain ⟨results, returned, entries⟩ := performed present
            simp only [within, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
            rw [entries index, Copies.madeValue_eq rfl named ok (reads present supported) returned]

end At

/-! ## Requirements -/

theorem Side.supports_append {side : Side} {first second : List Copies.Requirement}
    (supported : side.supports (first ++ second) = true) :
    side.supports first = true ∧ side.supports second = true := by
  unfold Side.supports at supported ⊢
  rw [List.all_append, Bool.and_eq_true] at supported
  exact supported

theorem Side.supports_cons {side : Side} {requirement : Copies.Requirement}
    {rest : List Copies.Requirement} (supported : side.supports (requirement :: rest) = true) :
    side.supports [requirement] = true ∧ side.supports rest = true :=
  Side.supports_append (first := [requirement]) supported

/-! ## Ports and agreements

The inputs of a protocol and the results of an application are classed by agreements: the
copies of one agreement are one class. Read one way, an agreement that holds gives the class
one value; read the other way, copies that the check found to be one class, for a side that
supports the requirement, make the agreement hold. -/

section Ports

variable {model : Model}

/-- The entry of a port among the values of a side that has its holder. -/
theorem entryOf_plain_get (side : Side) : ∀ {types : List Located}
    (values : Values (SideValue model side) types) {located : Located} (port : Var types located)
    (member : side located.holder = true),
    entryOf (plainValues side values) port.index =
      some ⟨located.type, Held.value (side located.holder) member (values.get port)⟩
  | _, .nil, _, port, _ => port.elimNil
  | _, .cons value rest, _, port, member => by
      cases port with
      | here => exact congrArg some (plain_entry_present _ member value)
      | there port => exact entryOf_plain_get side rest port member

/-- The results of an application, read by the caller's side, are the callee's outputs read
by the side of the callee. -/
theorem entryOf_plain_remapRoles (side : Side) (roleMap : RoleMap) : ∀ (ports : List Located)
    (values : Values (SideValue model (Side.preimage roleMap side)) ports) (index : Nat),
    entryOf (plainValues side
        (remapValues (F := SideValue model side) (Located.rename roleMap) ports values)) index =
      entryOf (plainValues (Side.preimage roleMap side) values) index
  | [], .nil, _ => rfl
  | _ :: _, .cons _ _, 0 => rfl
  | _ :: rest, .cons _ values, index + 1 => entryOf_plain_remapRoles side roleMap rest values index

/-- The operands of an application, read by the side of the callee, are the operands read by
the caller's side. -/
theorem entryOf_plain_unmapRoles (side : Side) (roleMap : RoleMap) : ∀ (ports : List Located)
    (values : Values (SideValue model side) (ports.map (Located.rename roleMap))) (index : Nat),
    entryOf (plainValues (Side.preimage roleMap side)
        (unmapValues (F := SideValue model side) (Located.rename roleMap) ports values)) index =
      entryOf (plainValues side values) index
  | [], .nil, _ => rfl
  | _ :: _, .cons _ _, 0 => rfl
  | _ :: rest, .cons _ values, index + 1 => entryOf_plain_unmapRoles side roleMap rest values index

/-- An agreement that holds: the copies that the side holds are one entry. -/
theorem Agreement.Holds.entries {side : Side} {ports : List Located} {agreement : Agreement ports}
    {values : Values (SideValue model side) ports} (holds : agreement.Holds model side values)
    {first second : Copy ports agreement.type} (firstIn : first ∈ agreement.copies)
    (secondIn : second ∈ agreement.copies) (firstMember : side first.holder = true)
    (secondMember : side second.holder = true) :
    entryOf (plainValues side values) first.port.index =
      entryOf (plainValues side values) second.port.index := by
  rw [entryOf_plain_get side values first.port firstMember,
    entryOf_plain_get side values second.port secondMember,
    holds first firstIn second secondIn firstMember secondMember]

/-- Copies that the side holds with one entry: the agreement holds. -/
theorem Agreement.holds_of_entries {side : Side} {ports : List Located}
    {agreement : Agreement ports} {values : Values (SideValue model side) ports}
    (same : ∀ first ∈ agreement.copies, ∀ second ∈ agreement.copies,
      side first.holder = true → side second.holder = true →
        entryOf (plainValues side values) first.port.index =
          entryOf (plainValues side values) second.port.index) :
    agreement.Holds model side values := by
  intro first firstIn second secondIn firstMember secondMember
  have entries := same first firstIn second secondIn firstMember secondMember
  rw [entryOf_plain_get side values first.port firstMember,
    entryOf_plain_get side values second.port secondMember] at entries
  exact eq_of_heq (Sigma.mk.inj (Option.some.inj entries)).2

/-- Two different items of a list that a filter keeps: the filter keeps at least two. -/
theorem two_le_filter {α : Type} (keep : α → Bool) : ∀ (items : List α) {first second : α},
    first ∈ items → second ∈ items → first ≠ second → keep first = true → keep second = true →
      2 ≤ (items.filter keep).length
  | [], _, _, firstIn, _, _, _, _ => nomatch firstIn
  | head :: rest, first, second, firstIn, secondIn, differ, keepFirst, keepSecond => by
      have one : ∀ {item : α}, item ∈ rest → keep item = true → 1 ≤ (rest.filter keep).length :=
        fun inside kept => List.length_pos_of_mem (List.mem_filter.mpr ⟨inside, kept⟩)
      cases firstIn with
      | head =>
          cases secondIn with
          | head => exact absurd rfl differ
          | tail _ secondIn =>
              rw [List.filter_cons_of_pos keepFirst, List.length_cons]
              exact Nat.succ_le_succ (one secondIn keepSecond)
      | tail _ firstIn =>
          cases secondIn with
          | head =>
              rw [List.filter_cons_of_pos keepSecond, List.length_cons]
              exact Nat.succ_le_succ (one firstIn keepFirst)
          | tail _ secondIn =>
              have inner := two_le_filter keep rest firstIn secondIn differ keepFirst keepSecond
              cases kept : keep head with
              | true =>
                  rw [List.filter_cons_of_pos kept, List.length_cons]
                  exact Nat.le_succ_of_le inner
              | false =>
                  rw [List.filter_cons_of_neg (by simp [kept])]
                  exact inner

/-- A side that supports a requirement and has two of its copies contains the support of
each. -/
theorem Side.supports_two {side : Side} {α : Type} (copyOf : α → Nat × List Nat)
    {items : List α} (supported : side.supports [items.map copyOf] = true) {first second : α}
    (firstIn : first ∈ items) (secondIn : second ∈ items) (differ : first ≠ second)
    (firstMember : side (copyOf first).1 = true) (secondMember : side (copyOf second).1 = true) :
    (copyOf first).2.all side = true := by
  have present : 2 ≤ ((items.map copyOf).filter fun copy => side copy.1).length := by
    rw [List.filter_map, List.length_map]
    exact two_le_filter _ items firstIn secondIn differ firstMember secondMember
  have decided : (decide (((items.map copyOf).filter fun copy => side copy.1).length ≤ 1) ||
      ((items.map copyOf).filter fun copy => side copy.1).all fun copy => copy.2.all side) = true := by
    have whole : side.supports [items.map copyOf] =
        ((decide (((items.map copyOf).filter fun copy => side copy.1).length ≤ 1) ||
          ((items.map copyOf).filter fun copy => side copy.1).all fun copy => copy.2.all side) &&
          true) := rfl
    rw [whole, Bool.and_true] at supported
    exact supported
  rcases Bool.or_eq_true_iff.mp decided with few | every
  · exact absurd (of_decide_eq_true few) (by omega)
  · exact List.all_eq_true.mp every _
      (List.mem_filter.mpr ⟨List.mem_map_of_mem firstIn, firstMember⟩)

/-- A side that supports requirements supports each of them. -/
theorem Side.supports_mem {side : Side} {requirements : List Copies.Requirement}
    (supported : side.supports requirements = true) {requirement : Copies.Requirement}
    (inside : requirement ∈ requirements) : side.supports [requirement] = true := by
  unfold Side.supports at supported ⊢
  rw [List.all_cons, List.all_nil, Bool.and_true]
  exact List.all_eq_true.mp supported requirement inside

/-- A side supports the requirements of a callee in the caller's roles exactly when the side
of the callee supports them. -/
theorem Side.supports_mapped (side : Side) (roleMap : RoleMap)
    (requirements : List Copies.Requirement) :
    side.supports (Copies.mapped roleMap requirements) =
      (Side.preimage roleMap side).supports requirements := by
  unfold Side.supports Copies.mapped
  rw [List.all_map]
  congr 1
  funext requirement
  have filtered : ((requirement.map fun copy : Nat × List Nat =>
        (roleMap.apply copy.1, copy.2.map roleMap.apply)).filter fun copy => side copy.1) =
      (requirement.filter fun copy => Side.preimage roleMap side copy.1).map
        fun copy : Nat × List Nat => (roleMap.apply copy.1, copy.2.map roleMap.apply) := by
    rw [List.filter_map]
    rfl
  show (decide (((requirement.map fun copy : Nat × List Nat =>
        (roleMap.apply copy.1, copy.2.map roleMap.apply)).filter fun copy => side copy.1).length ≤ 1) ||
      ((requirement.map fun copy : Nat × List Nat =>
        (roleMap.apply copy.1, copy.2.map roleMap.apply)).filter fun copy => side copy.1).all
          fun copy => copy.2.all side) = _
  rw [filtered, List.length_map, List.all_map]
  congr 2
  funext copy
  show (copy.2.map roleMap.apply).all side = _
  rw [List.all_map]
  rfl

namespace Copies

/-- Copies of one class have one class, two by two. -/
theorem oneClass_same : ∀ {copies : List Copy}, oneClass copies = true →
    ∀ first ∈ copies, ∀ second ∈ copies, first.class_ = second.class_
  | [], _, _, firstIn, _, _ => nomatch firstIn
  | head :: rest, one, first, firstIn, second, secondIn => by
      have each : ∀ copy ∈ head :: rest, copy.class_ = head.class_ := by
        intro copy inside
        cases inside with
        | head => rfl
        | tail _ inside => exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp one copy inside)
      rw [each first firstIn, each second secondIn]

/-- The copies at an agreement that the check found to be one class, for a side that supports
the requirement: the copies that the side has are one entry. -/
theorem agreed_entries {side : Side} {valuation : Valuation model} {ports : List Located}
    (rename : Nat → Nat) (copies : List Copy) (agreement : Agreement ports)
    (entries : Nat → Option (Sigma model.Value))
    (held : ∀ copy ∈ agreement.copies, side (rename copy.holder) = true →
      (copies.getD copy.port.index default).support.all side = true →
        valuation.value (copies.getD copy.port.index default).class_ = entries copy.port.index)
    (one : oneClass (agreed rename copies agreement).2 = true)
    (supported : side.supports [(agreed rename copies agreement).1] = true) :
    ∀ first ∈ agreement.copies, ∀ second ∈ agreement.copies,
      side (rename first.holder) = true → side (rename second.holder) = true →
        entries first.port.index = entries second.port.index := by
  intro first firstIn second secondIn firstMember secondMember
  by_cases same : first = second
  · rw [same]
  · have shape : (agreed rename copies agreement).1 = agreement.copies.map fun copy =>
        (rename copy.holder, (copies.getD copy.port.index default).support) := by
      show List.map _ (List.map _ _) = _
      rw [List.map_map]
      rfl
    rw [shape] at supported
    have firstInside := Side.supports_two _ supported firstIn secondIn same firstMember
      secondMember
    have secondInside := Side.supports_two _ supported secondIn firstIn (Ne.symm same)
      secondMember firstMember
    have listed : ∀ copy ∈ agreement.copies,
        copies.getD copy.port.index default ∈ (agreed rename copies agreement).2 := by
      intro copy inside
      show _ ∈ List.map (·.2) (agreement.copies.map fun copy =>
        (rename copy.holder, copies.getD copy.port.index default))
      exact List.mem_map.mpr ⟨(rename copy.holder, copies.getD copy.port.index default),
        List.mem_map_of_mem inside, rfl⟩
    have classes : (copies.getD first.port.index default).class_ =
        (copies.getD second.port.index default).class_ :=
      oneClass_same one _ (listed first firstIn) _ (listed second secondIn)
    rw [← held first firstIn firstMember firstInside,
      ← held second secondIn secondMember secondInside, classes]

/-- Values bound with copies. A copy with a class known before holds as it did; the copies
with new classes hold under a valuation that gives each new class the entry of the values
that have it, when the values of one class, where the side contains the supports of two, are
one entry. -/
theorem Hold.fresh {side : Side} (valuation : Valuation model) {next after : Nat}
    {added : List Located} (values : Values (SideValue model side) added)
    (copies : List Copy) (counted : copies.length = added.length)
    (each : ∀ (index : Nat) (located : Located), added[index]? = some located →
      ((copies.getD index default).class_ < next ∧
        (copies.getD index default).Holds side valuation after located
          (entryOf (plainValues side values) index)) ∨
      (next ≤ (copies.getD index default).class_ ∧ (copies.getD index default).class_ < after ∧
        (copies.getD index default).support.contains located.holder = true))
    (alike : ∀ (first second : Nat) (firstLocated secondLocated : Located),
      added[first]? = some firstLocated → added[second]? = some secondLocated →
      next ≤ (copies.getD first default).class_ →
      (copies.getD first default).class_ = (copies.getD second default).class_ →
      (copies.getD first default).support.all side = true →
      (copies.getD second default).support.all side = true →
        entryOf (plainValues side values) first = entryOf (plainValues side values) second) :
    ∃ later : Valuation model, later.Extends valuation next ∧
      Hold side later after copies values := by
  have valueOf : ∀ class_ : Nat, ∃ entry : Option (Sigma model.Value),
      (class_ < next → entry = valuation.value class_) ∧
      (next ≤ class_ → ∀ (index : Nat) (located : Located), added[index]? = some located →
        (copies.getD index default).class_ = class_ →
        (copies.getD index default).support.all side = true →
          entry = entryOf (plainValues side values) index) := by
    intro class_
    by_cases below : class_ < next
    · exact ⟨valuation.value class_, fun _ => rfl,
        fun beyond => absurd below (Nat.not_lt.mpr beyond)⟩
    · by_cases known : ∃ (index : Nat) (located : Located), added[index]? = some located ∧
          (copies.getD index default).class_ = class_ ∧
          (copies.getD index default).support.all side = true
      · obtain ⟨chosen, chosenLocated, chosenAt, chosenClass, chosenInside⟩ := known
        refine ⟨entryOf (plainValues side values) chosen, fun earlier => absurd earlier below,
          fun beyond index located found classIs inside => ?_⟩
        exact alike chosen index chosenLocated located chosenAt found
          (by rw [chosenClass]; exact beyond) (chosenClass.trans classIs.symm) chosenInside inside
      · exact ⟨none, fun earlier => absurd earlier below,
          fun _ index located found classIs inside =>
            absurd ⟨index, located, found, classIs, inside⟩ known⟩
  obtain ⟨value, valueSpec⟩ := Classical.axiomOfChoice valueOf
  refine ⟨⟨value⟩, fun class_ below => (valueSpec class_).1 below, counted,
    fun index located found => ?_⟩
  rcases each index located found with ⟨old, holds⟩ | ⟨beyond, below, held⟩
  · exact ⟨holds.1, holds.2.1, fun inside => ((valueSpec _).1 old).trans (holds.2.2 inside)⟩
  · exact ⟨held, below, fun inside => (valueSpec _).2 beyond index located found rfl inside⟩

/-- Ports classed by agreements, shown to a side in roles renamed, where the copies of each
agreement that the side has are one entry: a valuation under which the copies that the check
gives the ports hold of the values. -/
theorem Hold.ports {side : Side} (valuation : Valuation model) (state : State)
    {ports : List Located} (agreements : List (Agreement ports)) (rename : Nat → Nat)
    {added : List Located} (shown : Values (SideValue model side) added)
    (renamed : added = ports.map fun located => (⟨located.type, rename located.holder⟩ : Located))
    (agree : ∀ agreement ∈ agreements, ∀ first ∈ agreement.copies, ∀ second ∈ agreement.copies,
      side (rename first.holder) = true → side (rename second.holder) = true →
        entryOf (plainValues side shown) first.port.index =
          entryOf (plainValues side shown) second.port.index) :
    ∃ later : Valuation model, later.Extends valuation state.next ∧
      Hold side later (portClasses state agreements).2.next
        (((portClasses state agreements).1.zip ports).map fun entry =>
          (⟨entry.1, [rename entry.2.holder]⟩ : Copy)) shown := by
  obtain ⟨counted, _, _, _, bounds, sameClass⟩ := portClasses_spec state agreements
  have copyAt : ∀ (index : Nat) (located : Located), added[index]? = some located →
      ∃ (class_ : Nat) (port : Located), (portClasses state agreements).1[index]? = some class_ ∧
        ports[index]? = some port ∧
        located = ⟨port.type, rename port.holder⟩ ∧
        (((portClasses state agreements).1.zip ports).map fun entry =>
          (⟨entry.1, [rename entry.2.holder]⟩ : Copy)).getD index default =
            ⟨class_, [rename port.holder]⟩ := by
    intro index located found
    rw [renamed, List.getElem?_map] at found
    cases portAt : ports[index]? with
    | none => rw [portAt] at found; cases found
    | some port =>
        rw [portAt] at found
        have below : index < (portClasses state agreements).1.length := by
          rw [counted]
          exact (List.getElem?_eq_some_iff.mp portAt).1
        exact ⟨_, port, List.getElem?_eq_getElem below, rfl, (Option.some.inj found).symm,
          getD_map_of_getElem?
            (fun entry : Nat × Located => (⟨entry.1, [rename entry.2.holder]⟩ : Copy))
            ((portClasses state agreements).1.zip ports)
            (item := ((portClasses state agreements).1[index], port))
            (List.getElem?_zip_eq_some.mpr ⟨List.getElem?_eq_getElem below, portAt⟩) default⟩
  refine Hold.fresh valuation shown _ ?_ (fun index located found => ?_)
    (fun first second firstLocated secondLocated firstFound secondFound _ same firstInside
      secondInside => ?_)
  · rw [List.length_map, List.length_zip, counted, Nat.min_self, renamed, List.length_map]
  · obtain ⟨class_, port, classAt, _, located_, copy⟩ := copyAt index located found
    rw [copy, located_]
    exact Or.inr ⟨(bounds index class_ classAt).1, (bounds index class_ classAt).2, by simp⟩
  · obtain ⟨firstClass, firstPort, firstClassAt, firstPortAt, firstIs, firstCopy⟩ :=
      copyAt first firstLocated firstFound
    obtain ⟨secondClass, secondPort, secondClassAt, secondPortAt, secondIs, secondCopy⟩ :=
      copyAt second secondLocated secondFound
    rw [firstCopy] at same firstInside
    rw [secondCopy] at same secondInside
    have classes : firstClass = secondClass := same
    rw [← classes] at secondClassAt
    rcases sameClass first second firstClass firstClassAt secondClassAt with
      equal | ⟨agreement, inside, ⟨firstOf, firstIn, firstAt⟩, ⟨secondOf, secondIn, secondAt⟩⟩
    · rw [equal]
    · have firstHolder : firstPort = ⟨agreement.type, firstOf.holder⟩ :=
        Option.some.inj (firstPortAt.symm.trans (firstAt ▸ firstOf.port.valid))
      have secondHolder : secondPort = ⟨agreement.type, secondOf.holder⟩ :=
        Option.some.inj (secondPortAt.symm.trans (secondAt ▸ secondOf.port.valid))
      rw [firstHolder] at firstInside
      rw [secondHolder] at secondInside
      rw [List.all_cons, List.all_nil, Bool.and_true] at firstInside secondInside
      have entries := agree agreement inside firstOf firstIn secondOf secondIn firstInside
        secondInside
      rw [firstAt, secondAt] at entries
      exact entries

end Copies

end Ports

/-! ## Nested regions: their start, and the operands that enter them -/

section Enter

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} {typeTable : TypeTable} {rows : Scope operations} {callees : Scope functions}
  {functionTable : FunctionTable model functions} {side : Side}

theorem Copies.Valuation.Extends.weaken {later earlier : Copies.Valuation model}
    {next lower : Nat} (extends_ : later.Extends earlier next) (le : lower ≤ next) :
    later.Extends earlier lower :=
  fun class_ below => extends_ class_ (Nat.lt_of_lt_of_le below le)

/-- A state that holds, holds with a later next class. -/
theorem Copies.State.Sound.grow {valuation : Copies.Valuation model} {state : Copies.State}
    {Γ : List Located} {env : Environment (SideValue model side) Γ}
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env) {next : Nat} (grows : state.next ≤ next) :
    Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side valuation
      { state with next := next } env :=
  ⟨sound.depth,
    fun reference => ⟨(sound.copies reference).1,
      Nat.lt_of_lt_of_le (sound.copies reference).2.1 grows, (sound.copies reference).2.2⟩,
    fun entry member => (sound.made entry member).extend typeTable rows callees functionTable
      (Copies.Valuation.Extends.refl _ _) grows⟩

/-- The state at the start of a nested region holds of its inputs when its copies do. -/
theorem Copies.State.Sound.enter {valuation : Copies.Valuation model} {next : Nat}
    {made : List (Raw.LocalStep × List Nat)}
    (madeSound : ∀ entry ∈ made,
      Copies.MadeSound (deployed := deployed) typeTable rows callees functionTable valuation next
        entry)
    {inputs : List Located} {copies : List Copies.Copy}
    {values : Values (SideValue model side) inputs}
    (hold : Copies.Hold side valuation next copies values) :
    Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side valuation
      ⟨copies, next, made⟩ (Environment.ofValues values) := by
  have empty : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation ⟨[], next, made⟩ (Environment.empty (Value := SideValue model side)) :=
    ⟨rfl, fun reference => reference.elimNil, madeSound⟩
  exact empty.bind (Copies.Valuation.Extends.refl valuation next) (after := ⟨[], next, made⟩) rfl
    (Nat.le_refl _) madeSound hold

/-- The copies after the first operands are copies of the values after the first. -/
theorem Copies.Hold.drop {valuation : Copies.Valuation model} {next : Nat} (first : List Located)
    {rest : List Located} {copies : List Copies.Copy}
    {values : Values (SideValue model side) (first ++ rest)}
    (hold : Copies.Hold side valuation next copies values) :
    Copies.Hold side valuation next (copies.drop first.length) (values.split first).2 := by
  refine ⟨by rw [List.length_drop, hold.1, List.length_append, Nat.add_sub_cancel_left],
    fun index located found => ?_⟩
  have whole := hold.2 (first.length + index) located (by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact found)
  have entry := entryOf_plain_append side (values.split first).1 (values.split first).2 index
  rw [Values.append_split] at entry
  rw [entry] at whole
  have copy : (copies.drop first.length).getD index default =
      copies.getD (first.length + index) default := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [copy]
  exact whole

/-- The copies at the positions of values hold of a tuple that has, at each position, the
entry of the values. -/
theorem Copies.Hold.of_entries {valuation : Copies.Valuation model} {next : Nat}
    {types others : List Located} {copies : List Copies.Copy}
    {values : Values (SideValue model side) types} {shown : Values (SideValue model side) others}
    (hold : Copies.Hold side valuation next copies values) (same : types = others)
    (entries : ∀ index, entryOf (plainValues side shown) index =
      entryOf (plainValues side values) index) :
    Copies.Hold side valuation next copies shown := by
  cases same
  exact ⟨hold.1, fun index located found => by
    rw [entries index]
    exact hold.2 index located found⟩

end Enter

/-! ## The tags of a choice -/

/-- Two items at different positions of a list that a filter keeps: the filter keeps at least
two. -/
theorem two_le_filter_at {α : Type} (keep : α → Bool) : ∀ (items : List α) {first second : Nat}
    {one two : α}, items[first]? = some one → items[second]? = some two → first ≠ second →
      keep one = true → keep two = true → 2 ≤ (items.filter keep).length
  | [], _, _, _, _, oneAt, _, _, _, _ => nomatch oneAt
  | head :: rest, first, second, one, two, oneAt, twoAt, differ, keepOne, keepTwo => by
      have least : ∀ {item : α}, item ∈ rest → keep item = true → 1 ≤ (rest.filter keep).length :=
        fun inside kept => List.length_pos_of_mem (List.mem_filter.mpr ⟨inside, kept⟩)
      cases first with
      | zero =>
          cases second with
          | zero => exact absurd rfl differ
          | succ second =>
              cases Option.some.inj oneAt
              rw [List.filter_cons_of_pos keepOne, List.length_cons]
              exact Nat.succ_le_succ (least (List.mem_of_getElem? twoAt) keepTwo)
      | succ first =>
          cases second with
          | zero =>
              cases Option.some.inj twoAt
              rw [List.filter_cons_of_pos keepTwo, List.length_cons]
              exact Nat.succ_le_succ (least (List.mem_of_getElem? oneAt) keepOne)
          | succ second =>
              have inner := two_le_filter_at keep rest oneAt twoAt
                (fun same => differ (congrArg (· + 1) same)) keepOne keepTwo
              cases kept : keep head with
              | true =>
                  rw [List.filter_cons_of_pos kept, List.length_cons]
                  exact Nat.le_succ_of_le inner
              | false =>
                  rw [List.filter_cons_of_neg (by simp [kept])]
                  exact inner

/-- A side that supports a requirement and has the copies at two of its positions contains
the support of each. -/
theorem Side.supports_two_at {side : Side} {α : Type} (copyOf : α → Nat × List Nat)
    {items : List α} (supported : side.supports [items.map copyOf] = true) {first second : Nat}
    {one two : α} (oneAt : items[first]? = some one) (twoAt : items[second]? = some two)
    (differ : first ≠ second) (oneMember : side (copyOf one).1 = true)
    (twoMember : side (copyOf two).1 = true) : (copyOf one).2.all side = true := by
  have present : 2 ≤ ((items.map copyOf).filter fun copy => side copy.1).length := by
    rw [List.filter_map, List.length_map]
    exact two_le_filter_at _ items oneAt twoAt differ oneMember twoMember
  have decided : (decide (((items.map copyOf).filter fun copy => side copy.1).length ≤ 1) ||
      ((items.map copyOf).filter fun copy => side copy.1).all fun copy => copy.2.all side) = true := by
    have whole : side.supports [items.map copyOf] =
        ((decide (((items.map copyOf).filter fun copy => side copy.1).length ≤ 1) ||
          ((items.map copyOf).filter fun copy => side copy.1).all fun copy => copy.2.all side) &&
          true) := rfl
    rw [whole, Bool.and_true] at supported
    exact supported
  rcases Bool.or_eq_true_iff.mp decided with few | every
  · exact absurd (of_decide_eq_true few) (by omega)
  · exact List.all_eq_true.mp every _
      (List.mem_filter.mpr ⟨List.mem_map_of_mem (List.mem_of_getElem? oneAt), oneMember⟩)

section Tags

variable {model : Model} {side : Side}

/-- The copies of a control value that the participants in the side hold are equal, when the
check found them to be one class and the side supports the requirement: two at different
positions put the supports of both inside the side, so each is the value of the class. -/
theorem Copies.controls_equal {valuation : Copies.Valuation model} {next : Nat} (type : Ty)
    (participants : List Nat) {rest : List Located} {operands : List Copies.Copy}
    {values : Values (SideValue model side) (Located.ofRoles type participants ++ rest)}
    (hold : Copies.Hold side valuation next operands values)
    (one : Copies.oneClass (operands.take participants.length) = true)
    (supported : side.supports [(participants.zip (operands.take participants.length)).map
      fun entry => (entry.1, entry.2.support)] = true) :
    ∀ {first : Nat} (firstAt : Var participants first) (firstMember : side first = true)
      {second : Nat} (secondAt : Var participants second) (secondMember : side second = true),
      Held.value (side first) firstMember
          ((unmapValues (F := SideValue model side) (fun role => (⟨type, role⟩ : Located))
            participants (values.split (Located.ofRoles type participants)).1).get firstAt) =
        Held.value (side second) secondMember
          ((unmapValues (F := SideValue model side) (fun role => (⟨type, role⟩ : Located))
            participants (values.split (Located.ofRoles type participants)).1).get secondAt) := by
  intro first firstAt firstMember second secondAt secondMember
  by_cases same : firstAt.index = secondAt.index
  · have roles : first = second :=
      Option.some.inj (firstAt.valid.symm.trans (same ▸ secondAt.valid))
    cases roles
    cases Var.ext same
    rfl
  · -- the copy of a participant, among the operands and among the tags
    have copyAt : ∀ {role : Nat} (position : Var participants role),
        (operands.take participants.length)[position.index]? =
          some (operands.getD position.index default) ∧
        (Located.ofRoles type participants ++ rest)[position.index]? = some ⟨type, role⟩ := by
      intro role position
      have inside : position.index < participants.length :=
        (List.getElem?_eq_some_iff.mp position.valid).1
      have within : position.index < operands.length := by
        rw [hold.1, List.length_append, List.length_map]
        exact Nat.lt_of_lt_of_le inside (Nat.le_add_right _ _)
      refine ⟨?_, ?_⟩
      · rw [List.getElem?_take_of_lt inside, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem within]
        rfl
      · rw [List.getElem?_append_left (by rw [List.length_map]; exact inside),
          List.getElem?_map, position.valid]
        rfl
    have entryAt : ∀ {role : Nat} (position : Var participants role) (member : side role = true)
        {other : Nat} (otherAt : Var participants other) (otherMember : side other = true),
        position.index ≠ otherAt.index →
        valuation.value (operands.getD position.index default).class_ =
          some ⟨type, Held.value (side role) member
            ((unmapValues (F := SideValue model side) (fun role => (⟨type, role⟩ : Located))
              participants (values.split (Located.ofRoles type participants)).1).get position)⟩ := by
      intro role position member other otherAt otherMember differ
      have inside := Side.supports_two_at
        (fun entry : Nat × Copies.Copy => (entry.1, entry.2.support)) supported
        (one := (role, operands.getD position.index default))
        (two := (other, operands.getD otherAt.index default))
        (List.getElem?_zip_eq_some.mpr ⟨position.valid, (copyAt position).1⟩)
        (List.getElem?_zip_eq_some.mpr ⟨otherAt.valid, (copyAt otherAt).1⟩) differ member
        otherMember
      rw [(hold.2 position.index ⟨type, role⟩ (copyAt position).2).2.2 inside]
      exact entryOf_plain_copy side type participants values position member
    have classes : (operands.getD firstAt.index default).class_ =
        (operands.getD secondAt.index default).class_ :=
      Copies.oneClass_same one _ (List.mem_of_getElem? (copyAt firstAt).1) _
        (List.mem_of_getElem? (copyAt secondAt).1)
    have entries := (entryAt firstAt firstMember secondAt secondMember same).symm.trans
      (classes ▸ entryAt secondAt secondMember firstAt firstMember (Ne.symm same))
    exact eq_of_heq (Sigma.mk.inj (Option.some.inj entries)).2

end Tags

section AgreementEqual

variable {X α : Type} {same : X → X → Bool} {side : Side} {onValue : X → α} {onDisagree : α}

/-- Comparing later copies with a first one that they all are continues with it. -/
theorem agreeWith_coincide (motive : α → Prop) (reflexive : ∀ value : X, same value value = true)
    (value : X) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles),
      (∀ {role : Nat} (position : Var roles role) (member : side role = true),
        Held.value (side role) member (values.get position) = value) →
      motive (onValue value) → motive (agreeWith same side onValue onDisagree value roles values)
  | [], _, _, done => done
  | role :: rest, values, equal, done => by
      have later : ∀ {other : Nat} (position : Var rest other) (member : side other = true),
          Held.value (side other) member (values.tail.get position) = value :=
        fun position member => tail_get values position ▸ equal position.there member
      cases present : side role with
      | true =>
          rw [agreeWith_present present, equal .here present, reflexive]
          exact agreeWith_coincide motive reflexive value rest values.tail later done
      | false =>
          rw [agreeWith_absent present]
          exact agreeWith_coincide motive reflexive value rest values.tail later done

/-- An agreement on copies that are equal wherever the side holds them does not disagree: it
continues without a participant in the side, or with the value that every copy in the side
is. -/
theorem agreed_coincide (motive : α → Prop) (reflexive : ∀ value : X, same value value = true) :
    ∀ (roles : List Nat) (values : Values (fun role => Held X (side role)) roles)
      (onNone : roles.any side = false → α),
      (∀ {first : Nat} (firstAt : Var roles first) (firstMember : side first = true)
        {second : Nat} (secondAt : Var roles second) (secondMember : side second = true),
        Held.value (side first) firstMember (values.get firstAt) =
          Held.value (side second) secondMember (values.get secondAt)) →
      (∀ none, motive (onNone none)) →
      (∀ value : X,
        (∀ {role : Nat} (position : Var roles role) (member : side role = true),
          Held.value (side role) member (values.get position) = value) →
        motive (onValue value)) →
      motive (agreed same side onValue onDisagree roles values onNone)
  | [], _, _, _, outside, _ => outside rfl
  | role :: rest, values, onNone, equal, outside, agree => by
      cases present : side role with
      | true =>
          rw [agreed_present present]
          have each : ∀ {other : Nat} (position : Var (role :: rest) other)
              (member : side other = true),
              Held.value (side other) member (values.get position) =
                Held.value (side role) present (values.get .here) :=
            fun position member => equal position member .here present
          exact agreeWith_coincide motive reflexive _ rest values.tail
            (fun position member => tail_get values position ▸ each position.there member)
            (agree _ each)
      | false =>
          rw [agreed_absent present]
          refine agreed_coincide motive reflexive rest values.tail _
            (fun firstAt firstMember => fun secondAt secondMember => ?_) (fun none => outside _)
            fun value each => agree value ?_
          · rw [tail_get, tail_get]
            exact equal firstAt.there firstMember secondAt.there secondMember
          · intro other position member
            cases position with
            | here => rw [present] at member; cases member
            | there position => exact tail_get values position ▸ each position member

end AgreementEqual

/-- A tag is the same as itself. -/
theorem ChoiceTag.same_refl (Carrier : Nat → Type) :
    ∀ (tag : ChoiceTag) (value : Ty.Value Carrier tag.type), tag.same Carrier value value = true
  | .condition, true => rfl
  | .condition, false => rfl
  | .arm _, value => Nat.beq_refl value.val
  | .alternative _ alternatives, value => Nat.beq_refl (alternativeNumber alternatives value)

/-! ## The state after a choice -/

/-- The item at a position among the first items of a list. -/
theorem getElem?_take_getD {α : Type} [Inhabited α] (items : List α) {count index : Nat}
    (below : index < count) (inside : index < items.length) :
    (items.take count)[index]? = some (items.getD index default) := by
  rw [List.getElem?_take_of_lt below, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
  rfl

section Choice

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} {typeTable : TypeTable} {rows : Scope operations} {callees : Scope functions}
  {functionTable : FunctionTable model functions} {side : Side}
  {valuation : Copies.Valuation model} {state : Copies.State} {Γ : List Located}
  {env : Environment (SideValue model side) Γ}

theorem entryOf_plain_append_left (side : Side) : ∀ {first rest : List Located}
    (values : Values (SideValue model side) first) (others : Values (SideValue model side) rest)
    (index : Nat), index < first.length →
    entryOf (plainValues side (values.append others)) index =
      entryOf (plainValues side values) index
  | _, _, .nil, _, _, below => nomatch below
  | _, _, .cons _ _, _, 0, _ => rfl
  | _, _, .cons _ values, others, index + 1, below =>
      entryOf_plain_append_left side values others index (Nat.lt_of_succ_lt_succ below)

/-- The entry of a participant's value among values held by the participants. -/
theorem entryOf_plain_roles (side : Side) (type : Ty) : ∀ (participants : List Nat)
    (values : Values (fun role => Held (model.Value type) (side role)) participants)
    {role : Nat} (position : Var participants role) (member : side role = true),
    entryOf (plainValues side
        (remapValues (F := SideValue model side) (fun role => (⟨type, role⟩ : Located))
          participants values)) position.index =
      some ⟨type, Held.value (side role) member (values.get position)⟩
  | [], _, _, position, _ => position.elimNil
  | _ :: participants, .cons value values, _, position, member => by
      cases position with
      | here => exact congrArg some (plain_entry_present _ member value)
      | there position => exact entryOf_plain_roles side type participants values position member

/-- Copies of two tuples, one after the other. -/
theorem Copies.Hold.append {next : Nat} {first rest : List Located}
    {firstCopies restCopies : List Copies.Copy}
    {values : Values (SideValue model side) first} {others : Values (SideValue model side) rest}
    (one : Copies.Hold side valuation next firstCopies values)
    (two : Copies.Hold side valuation next restCopies others) :
    Copies.Hold side valuation next (firstCopies ++ restCopies) (values.append others) := by
  refine ⟨by rw [List.length_append, List.length_append, one.1, two.1],
    fun index located found => ?_⟩
  by_cases below : index < first.length
  · rw [List.getElem?_append_left below] at found
    rw [entryOf_plain_append_left side values others index below]
    have copy : (firstCopies ++ restCopies).getD index default =
        firstCopies.getD index default := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (one.1 ▸ below)]
    rw [copy]
    exact one.2 index located found
  · have beyond := Nat.le_of_not_lt below
    rw [List.getElem?_append_right beyond] at found
    have entry := entryOf_plain_append side values others (index - first.length)
    rw [Nat.add_sub_cancel' beyond] at entry
    rw [entry]
    have copy : (firstCopies ++ restCopies).getD index default =
        restCopies.getD (index - first.length) default := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (one.1 ▸ beyond), one.1]
    rw [copy]
    exact two.2 _ located found

/-- A state that holds knows no class at or above its next class. -/
theorem Copies.State.Sound.below
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env) : state.Below := by
  refine ⟨fun copy inside => ?_, fun entry member => (sound.made entry member).2.1⟩
  obtain ⟨level, within, found⟩ := List.getElem_of_mem inside
  have deep : level < Γ.length := sound.depth ▸ within
  have valid : Γ[Γ.length - 1 - level]? = some (Γ[Γ.length - 1 - level]'(by omega)) :=
    List.getElem?_eq_getElem (by omega)
  have known := (sound.copies (⟨Γ.length - 1 - level, valid⟩ : Var Γ _)).2.1
  have number : Scope.number Γ.length (⟨Γ.length - 1 - level, valid⟩ : Var Γ _) = level := by
    simp only [Scope.number, Scope.position]
    omega
  rw [number] at known
  have same : state.at_ level = copy := by
    unfold Copies.State.at_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem within, found]
    rfl
  rw [same] at known
  exact known

/-- After a choice none of whose outputs is held in the side: the state after it holds under
the valuation before it. Nothing ran, and every output is absent. -/
theorem Copies.afterChoice_absent
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env)
    {next : Nat} (grows : state.next ≤ next) (returning : List (List Copies.Copy))
    {outputs : List Located}
    (each : ∀ copies ∈ returning,
      copies.length = outputs.length ∧ ∀ copy ∈ copies, copy.class_ < next)
    (results : Values (SideValue model side) outputs)
    (absent : ∀ located ∈ outputs, side located.holder = false) :
    Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side valuation
      (Copies.afterChoice state next returning outputs) (Environment.bindAll env results) := by
  have spec := Copies.blocks_spec { state with next := next }
    (Copies.choiceKeys returning outputs.length)
  have classes := Copies.choiceClasses_spec returning
    (Copies.blocks { state with next := next } (Copies.choiceKeys returning outputs.length)).1
    outputs.length
    (Copies.blocks { state with next := next } (Copies.choiceKeys returning outputs.length)).2.next
    (by rw [spec.1, Copies.choiceKeys_length])
    (fun class_ inside => by
      obtain ⟨index, _, found⟩ := List.getElem_of_mem inside
      exact (spec.2.2.1 index class_ (found ▸ List.getElem?_eq_getElem _)).2)
    (fun copies inside => ⟨(each copies inside).1, fun copy member =>
      Nat.lt_of_lt_of_le ((each copies inside).2 copy member) spec.2.1⟩)
  refine sound.bind (Copies.Valuation.Extends.refl _ _)
    (after := (Copies.blocks { state with next := next }
      (Copies.choiceKeys returning outputs.length)).2) rfl (Nat.le_trans grows spec.2.1)
    (fun entry member => (sound.made entry member).extend typeTable rows callees functionTable
      (Copies.Valuation.Extends.refl _ _) (Nat.le_trans grows spec.2.1))
    ⟨(Copies.choiceResults_spec returning _ outputs classes.1).1, fun index located found => ?_⟩
  obtain ⟨class_, classAt, copy⟩ := Copies.choiceResults_at returning _ outputs classes.1 found
  rw [copy]
  have holder : (Copies.choiceSupport returning located.holder index).contains located.holder =
      true := by
    rw [Copies.choiceSupport_eq]
    exact Copies.contains_foldl_union _ (by simp)
  refine ⟨holder, classes.2 class_ (List.mem_of_getElem? classAt), fun inside => ?_⟩
  have member := Copies.side_of_contains inside holder
  rw [absent located (List.mem_of_getElem? found)] at member
  cases member

/-- After a choice one of whose arms ran: the state after it holds, of the outputs that the
arm returned, under a valuation that extends the one before the choice. An output whose key
is one class in every arm has the class, and the value, that the arm returned; an output
with a new class takes the entry of what the arm returned at a position of its key. -/
theorem Copies.afterChoice_sound
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env)
    {next : Nat} (grows : state.next ≤ next) (returning : List (List Copies.Copy))
    {outputs : List Located}
    (each : ∀ copies ∈ returning,
      copies.length = outputs.length ∧ ∀ copy ∈ copies, copy.class_ < next)
    {later : Copies.Valuation model} (extends_ : later.Extends valuation state.next)
    {results : Values (SideValue model side) outputs} {copies : List Copies.Copy}
    (ran : copies ∈ returning) (hold : Copies.Hold side later next copies results) :
    ∃ final : Copies.Valuation model, final.Extends valuation state.next ∧
      Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side final
        (Copies.afterChoice state next returning outputs) (Environment.bindAll env results) := by
  cases returning with
  | nil => exact nomatch ran
  | cons first rest =>
  have spec := Copies.blocks_spec { state with next := next }
    (Copies.choiceKeys (first :: rest) outputs.length)
  have madeSized : (Copies.blocks { state with next := next }
      (Copies.choiceKeys (first :: rest) outputs.length)).1.length = outputs.length := by
    rw [spec.1, Copies.choiceKeys_length]
  have classes := Copies.choiceClasses_spec (first :: rest)
    (Copies.blocks { state with next := next }
      (Copies.choiceKeys (first :: rest) outputs.length)).1 outputs.length
    (Copies.blocks { state with next := next }
      (Copies.choiceKeys (first :: rest) outputs.length)).2.next madeSized
    (fun class_ inside => by
      obtain ⟨index, _, found⟩ := List.getElem_of_mem inside
      exact (spec.2.2.1 index class_ (found ▸ List.getElem?_eq_getElem _)).2)
    (fun copies inside => ⟨(each copies inside).1, fun copy member =>
      Nat.lt_of_lt_of_le ((each copies inside).2 copy member) spec.2.1⟩)
  -- the copy that the check gives the output at a position
  have copyAt : ∀ (index : Nat) (located : Located), outputs[index]? = some located →
      ∃ made, (Copies.blocks { state with next := next }
          (Copies.choiceKeys (first :: rest) outputs.length)).1[index]? = some made ∧
        (Copies.choiceResults (first :: rest)
          (Copies.choiceClasses (first :: rest)
            (Copies.blocks { state with next := next }
              (Copies.choiceKeys (first :: rest) outputs.length)).1
            (Copies.choiceKeys (first :: rest) outputs.length)) outputs).getD index default =
          ⟨Copies.choiceClass made
              ((first :: rest).map fun copies => (copies.getD index default).class_),
            Copies.choiceSupport (first :: rest) located.holder index⟩ := by
    intro index located found
    have below := (List.getElem?_eq_some_iff.mp found).1
    obtain ⟨made, madeAt, classAt⟩ := Copies.choiceClasses_at first rest _ madeSized below
    obtain ⟨class_, classIs, copy⟩ :=
      Copies.choiceResults_at (first :: rest) _ outputs classes.1 found
    rw [classAt] at classIs
    cases Option.some.inj classIs
    exact ⟨made, madeAt, copy⟩
  have holderIn : ∀ (index holder : Nat),
      (Copies.choiceSupport (first :: rest) holder index).contains holder = true := by
    intro index holder
    rw [Copies.choiceSupport_eq]
    exact Copies.contains_foldl_union _ (by simp)
  -- an output whose support is inside the side: so is the support of what the arm returned
  have ranInside : ∀ (index holder : Nat),
      (Copies.choiceSupport (first :: rest) holder index).all side = true →
      (copies.getD index default).support.all side = true := by
    intro index holder inside
    rw [Copies.choiceSupport_eq] at inside
    exact (Copies.all_of_foldl_union _ inside).2 _ (List.mem_map_of_mem ran)
  -- the class that every arm returns at a position is below the next class
  have firstBelow : ∀ (index : Nat), index < outputs.length →
      (first.getD index default).class_ < next := by
    intro index below
    have inside : index < first.length := (each first (List.mem_cons_self ..)).1 ▸ below
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
    exact (each first (List.mem_cons_self ..)).2 _ (List.getElem_mem inside)
  obtain ⟨final, finalExtends, finalHold⟩ := Copies.Hold.fresh later (next := next)
    (after := (Copies.blocks { state with next := next }
      (Copies.choiceKeys (first :: rest) outputs.length)).2.next) results
    (Copies.choiceResults (first :: rest)
      (Copies.choiceClasses (first :: rest)
        (Copies.blocks { state with next := next }
          (Copies.choiceKeys (first :: rest) outputs.length)).1
        (Copies.choiceKeys (first :: rest) outputs.length)) outputs)
    (Copies.choiceResults_spec (first :: rest) _ outputs classes.1).1
    (fun index located found => by
      obtain ⟨made, madeAt, copy⟩ := copyAt index located found
      have below := (List.getElem?_eq_some_iff.mp found).1
      rw [copy]
      dsimp only
      rcases Copies.choiceClass_at made first rest index with ⟨constant, all⟩ | fresh
      · rw [constant]
        refine Or.inl ⟨firstBelow index below, holderIn index located.holder,
          Nat.lt_of_lt_of_le (firstBelow index below) spec.2.1, fun inside => ?_⟩
        rw [← all copies ran]
        exact (hold.2 index located found).2.2 (ranInside index located.holder inside)
      · rw [fresh]
        exact Or.inr ⟨(spec.2.2.1 index made madeAt).1, (spec.2.2.1 index made madeAt).2,
          holderIn index located.holder⟩)
    (fun one two oneLocated twoLocated oneFound twoFound beyond same oneInside twoInside => by
      obtain ⟨oneMade, oneAt, oneCopy⟩ := copyAt one oneLocated oneFound
      obtain ⟨twoMade, twoAt, twoCopy⟩ := copyAt two twoLocated twoFound
      have oneBelow := (List.getElem?_eq_some_iff.mp oneFound).1
      have twoBelow := (List.getElem?_eq_some_iff.mp twoFound).1
      rw [oneCopy] at beyond same oneInside
      rw [twoCopy] at same twoInside
      dsimp only at beyond same oneInside twoInside
      -- a class at or above the next is the class of the key
      have isMade : ∀ (index made : Nat), index < outputs.length →
          next ≤ Copies.choiceClass made
            ((first :: rest).map fun copies => (copies.getD index default).class_) →
          Copies.choiceClass made
            ((first :: rest).map fun copies => (copies.getD index default).class_) = made := by
        intro index made below least
        rcases Copies.choiceClass_at made first rest index with ⟨constant, _⟩ | fresh
        · rw [constant] at least
          exact absurd (firstBelow index below) (Nat.not_lt.mpr least)
        · exact fresh
      have oneIs := isMade one oneMade oneBelow beyond
      have twoIs := isMade two twoMade twoBelow (same ▸ beyond)
      rw [oneIs, twoIs] at same
      have keys := (spec.2.2.2 one two _ _ oneMade twoMade
        (Copies.choiceKeys_at first rest oneBelow) (Copies.choiceKeys_at first rest twoBelow)
        oneAt twoAt).mp same
      have classes : (copies.getD one default).class_ = (copies.getD two default).class_ :=
        List.map_inj_left.mp keys copies ran
      rw [← (hold.2 one oneLocated oneFound).2.2 (ranInside one oneLocated.holder oneInside),
        ← (hold.2 two twoLocated twoFound).2.2 (ranInside two twoLocated.holder twoInside),
        classes])
  have whole := extends_.trans finalExtends grows
  exact ⟨final, whole, sound.bind whole
    (after := (Copies.blocks { state with next := next }
      (Copies.choiceKeys (first :: rest) outputs.length)).2) rfl (Nat.le_trans grows spec.2.1)
    (fun entry member => (sound.made entry member).extend typeTable rows callees functionTable
      whole (Nat.le_trans grows spec.2.1)) finalHold⟩

end Choice

/-! ## The sequences that a loop collects

At a holder in the side, the entry of a collected sequence is a function of the entries of the
value collected and of the sequence so far. So two collected positions of one type whose
values are one entry in every iteration have one sequence. -/

section Collected

variable {model : Model} {side : Side}

/-- The entry of a value whose holder is in the side has the type of the value. -/
theorem entryOf_plain_present {types : List Located} (values : Values (SideValue model side) types)
    {index : Nat} {type : Ty} {holder : Nat} (found : types[index]? = some ⟨type, holder⟩)
    (member : side holder = true) :
    ∃ value : model.Value type, entryOf (plainValues side values) index = some ⟨type, value⟩ :=
  ⟨_, entryOf_plain_get side values (⟨index, found⟩ : Var types ⟨type, holder⟩) member⟩

theorem collectedNone_entry : ∀ (collected : List Located) (index : Nat) (type : Ty)
    (holder : Nat), collected[index]? = some ⟨type, holder⟩ → side holder = true →
    entryOf (plainValues side (sideCollectedNone model side collected)) index =
      some ⟨.seq type (some 0), ⟨[], rfl⟩⟩
  | [], _, _, _, found, _ => nomatch found
  | ⟨_, owner⟩ :: _, 0, _, _, found, member => by
      cases Option.some.inj found
      exact congrArg some (plain_entry_of (side owner) member _)
  | ⟨_, _⟩ :: rest, index + 1, type, holder, found, member =>
      collectedNone_entry rest index type holder found member

theorem collectedPush_entry {done : Nat} : ∀ (collected : List Located)
    (values : Values (SideValue model side) collected)
    (earlier : Values (SideValue model side) (collectedSequencesAt (some done) collected))
    (index : Nat) (type : Ty) (holder : Nat) (value : model.Value type)
    (sequence : model.Value (.seq type (some done))),
    collected[index]? = some ⟨type, holder⟩ → side holder = true →
    entryOf (plainValues side values) index = some ⟨type, value⟩ →
    entryOf (plainValues side earlier) index = some ⟨.seq type (some done), sequence⟩ →
    entryOf (plainValues side (sideCollectedPush model side collected values earlier)) index =
      some ⟨.seq type (some (done + 1)),
        ⟨value :: sequence.val, congrArg (· + 1) sequence.property⟩⟩
  | [], _, _, _, _, _, _, _, found, _, _, _ => nomatch found
  | ⟨_, owner⟩ :: _, .cons head _, .cons past _, 0, _, _, value, sequence, found, member,
      valueAt, sequenceAt => by
      cases Option.some.inj found
      have headIs : Held.value (side owner) member head = value :=
        eq_of_heq (Sigma.mk.inj (Option.some.inj
          ((congrArg some (plain_entry_present (side owner) member head)).symm.trans valueAt))).2
      have pastIs : Held.value (side owner) member past = sequence :=
        eq_of_heq (Sigma.mk.inj (Option.some.inj
          ((congrArg some (plain_entry_present (side owner) member past)).symm.trans
            sequenceAt))).2
      refine congrArg some ((plain_entry_present (side owner) member _).trans ?_)
      rw [Held.value_map₂, Values.get_here, Values.get_here, headIs, pastIs]
  | ⟨_, _⟩ :: rest, .cons _ values, .cons _ earlier, index + 1, type, holder, value, sequence,
      found, member, valueAt, sequenceAt =>
      collectedPush_entry rest values earlier index type holder value sequence found member
        valueAt sequenceAt

theorem collectedLists_entry {total : Nat} : ∀ (collected : List Located)
    (values : Values (SideValue model side) (collectedSequencesAt (some total) collected))
    (index : Nat) (type : Ty) (holder : Nat) (sequence : model.Value (.seq type (some total))),
    collected[index]? = some ⟨type, holder⟩ → side holder = true →
    entryOf (plainValues side values) index = some ⟨.seq type (some total), sequence⟩ →
    entryOf (plainValues side (sideCollectedLists model side collected values)) index =
      some ⟨.seq type none, sequence.val.reverse⟩
  | [], _, _, _, _, _, found, _, _ => nomatch found
  | ⟨_, owner⟩ :: _, .cons past _, 0, _, _, sequence, found, member, sequenceAt => by
      cases Option.some.inj found
      have pastIs : Held.value (side owner) member past = sequence :=
        eq_of_heq (Sigma.mk.inj (Option.some.inj
          ((congrArg some (plain_entry_present (side owner) member past)).symm.trans
            sequenceAt))).2
      refine congrArg some ((plain_entry_present (side owner) member _).trans ?_)
      rw [Held.value_map, Values.get_here, pastIs]
  | ⟨_, _⟩ :: rest, .cons _ values, index + 1, type, holder, sequence, found, member,
      sequenceAt =>
      collectedLists_entry rest values index type holder sequence found member sequenceAt

theorem collectedSized_entry {total count : Nat} (same : total = count) :
    ∀ (collected : List Located)
    (values : Values (SideValue model side) (collectedSequencesAt (some total) collected))
    (index : Nat) (type : Ty) (holder : Nat) (sequence : model.Value (.seq type (some total))),
    collected[index]? = some ⟨type, holder⟩ → side holder = true →
    entryOf (plainValues side values) index = some ⟨.seq type (some total), sequence⟩ →
    entryOf (plainValues side (sideCollectedSized model side same collected values)) index =
      some ⟨.seq type (some count),
        ⟨sequence.val.reverse, List.length_reverse.trans (sequence.property.trans same)⟩⟩
  | [], _, _, _, _, _, found, _, _ => nomatch found
  | ⟨_, owner⟩ :: _, .cons past _, 0, _, _, sequence, found, member, sequenceAt => by
      cases Option.some.inj found
      have pastIs : Held.value (side owner) member past = sequence :=
        eq_of_heq (Sigma.mk.inj (Option.some.inj
          ((congrArg some (plain_entry_present (side owner) member past)).symm.trans
            sequenceAt))).2
      refine congrArg some ((plain_entry_present (side owner) member _).trans ?_)
      rw [Held.value_map, Values.get_here, pastIs]
  | ⟨_, _⟩ :: rest, .cons _ values, index + 1, type, holder, sequence, found, member,
      sequenceAt =>
      collectedSized_entry same rest values index type holder sequence found member sequenceAt

/-- Two values at holders in the side that are one entry: one type and one value. -/
theorem entries_same {types : List Located} (values : Values (SideValue model side) types)
    {one two : Nat} {type other : Ty} {holder owner : Nat}
    (oneAt : types[one]? = some ⟨type, holder⟩) (twoAt : types[two]? = some ⟨other, owner⟩)
    (oneMember : side holder = true) (twoMember : side owner = true)
    (same : entryOf (plainValues side values) one = entryOf (plainValues side values) two) :
    type = other ∧ ∃ value : model.Value type,
      entryOf (plainValues side values) one = some ⟨type, value⟩ ∧
      entryOf (plainValues side values) two = some ⟨type, value⟩ := by
  obtain ⟨first, firstAt⟩ := entryOf_plain_present values oneAt oneMember
  obtain ⟨second, secondAt⟩ := entryOf_plain_present values twoAt twoMember
  rw [firstAt, secondAt] at same
  have types_ := (Sigma.mk.inj (Option.some.inj same)).1
  cases types_
  cases eq_of_heq (Sigma.mk.inj (Option.some.inj same)).2
  exact ⟨rfl, first, firstAt, secondAt⟩

/-- No iteration: two collected positions of one type have one sequence. -/
theorem collectedNone_alike (collected : List Located) {one two : Nat} {type : Ty}
    {holder owner : Nat} (oneAt : collected[one]? = some ⟨type, holder⟩)
    (twoAt : collected[two]? = some ⟨type, owner⟩) (oneMember : side holder = true)
    (twoMember : side owner = true) :
    entryOf (plainValues side (sideCollectedNone model side collected)) one =
      entryOf (plainValues side (sideCollectedNone model side collected)) two := by
  rw [collectedNone_entry collected one type holder oneAt oneMember,
    collectedNone_entry collected two type owner twoAt twoMember]

/-- The sequence position of a collected position. -/
theorem collectedSequencesAt_at (size : Option Nat) {collected : List Located} {index : Nat}
    {type : Ty} {holder : Nat} (found : collected[index]? = some ⟨type, holder⟩) :
    (collectedSequencesAt size collected)[index]? = some ⟨.seq type size, holder⟩ := by
  show (collected.map _)[index]? = _
  rw [List.getElem?_map, found]
  rfl

/-- One more iteration: two collected positions whose values are one entry and whose sequences
so far are one entry have one sequence. -/
theorem collectedPush_alike {done : Nat} (collected : List Located)
    (values : Values (SideValue model side) collected)
    (earlier : Values (SideValue model side) (collectedSequencesAt (some done) collected))
    {one two : Nat} {type other : Ty} {holder owner : Nat}
    (oneAt : collected[one]? = some ⟨type, holder⟩) (twoAt : collected[two]? = some ⟨other, owner⟩)
    (oneMember : side holder = true) (twoMember : side owner = true)
    (valuesSame : entryOf (plainValues side values) one = entryOf (plainValues side values) two)
    (earlierSame : entryOf (plainValues side earlier) one =
      entryOf (plainValues side earlier) two) :
    entryOf (plainValues side (sideCollectedPush model side collected values earlier)) one =
      entryOf (plainValues side (sideCollectedPush model side collected values earlier)) two := by
  obtain ⟨types_, value, valueOne, valueTwo⟩ :=
    entries_same values oneAt twoAt oneMember twoMember valuesSame
  cases types_
  obtain ⟨_, sequence, sequenceOne, sequenceTwo⟩ :=
    entries_same earlier (collectedSequencesAt_at (some done) oneAt)
      (collectedSequencesAt_at (some done) twoAt) oneMember twoMember earlierSame
  rw [collectedPush_entry collected values earlier one type holder value sequence oneAt oneMember
      valueOne sequenceOne,
    collectedPush_entry collected values earlier two type owner value sequence twoAt twoMember
      valueTwo sequenceTwo]

/-- The finished sequences, unsized: one sequence so far is one sequence. -/
theorem collectedLists_alike {total : Nat} (collected : List Located)
    (values : Values (SideValue model side) (collectedSequencesAt (some total) collected))
    {one two : Nat} {type : Ty} {holder owner : Nat}
    (oneAt : collected[one]? = some ⟨type, holder⟩) (twoAt : collected[two]? = some ⟨type, owner⟩)
    (oneMember : side holder = true) (twoMember : side owner = true)
    (same : entryOf (plainValues side values) one = entryOf (plainValues side values) two) :
    entryOf (plainValues side (sideCollectedLists model side collected values)) one =
      entryOf (plainValues side (sideCollectedLists model side collected values)) two := by
  obtain ⟨_, sequence, sequenceOne, sequenceTwo⟩ :=
    entries_same values (collectedSequencesAt_at (some total) oneAt)
      (collectedSequencesAt_at (some total) twoAt) oneMember twoMember same
  rw [collectedLists_entry collected values one type holder sequence oneAt oneMember sequenceOne,
    collectedLists_entry collected values two type owner sequence twoAt twoMember sequenceTwo]

/-- The finished sequences, sized: one sequence so far is one sequence. -/
theorem collectedSized_alike {total count : Nat} (sized : total = count)
    (collected : List Located)
    (values : Values (SideValue model side) (collectedSequencesAt (some total) collected))
    {one two : Nat} {type : Ty} {holder owner : Nat}
    (oneAt : collected[one]? = some ⟨type, holder⟩) (twoAt : collected[two]? = some ⟨type, owner⟩)
    (oneMember : side holder = true) (twoMember : side owner = true)
    (same : entryOf (plainValues side values) one = entryOf (plainValues side values) two) :
    entryOf (plainValues side (sideCollectedSized model side sized collected values)) one =
      entryOf (plainValues side (sideCollectedSized model side sized collected values)) two := by
  obtain ⟨_, sequence, sequenceOne, sequenceTwo⟩ :=
    entries_same values (collectedSequencesAt_at (some total) oneAt)
      (collectedSequencesAt_at (some total) twoAt) oneMember twoMember same
  rw [collectedSized_entry sized collected values one type holder sequence oneAt oneMember
      sequenceOne,
    collectedSized_entry sized collected values two type owner sequence twoAt twoMember
      sequenceTwo]

end Collected

/-! ## The state after a loop -/

section Loop

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} {typeTable : TypeTable} {rows : Scope operations} {callees : Scope functions}
  {functionTable : FunctionTable model functions} {side : Side}
  {valuation : Copies.Valuation model} {state : Copies.State} {Γ : List Located}
  {env : Environment (SideValue model side) Γ}

/-- The state after a loop holds of its results, under a valuation that extends the one before
the loop, when: a carried value that the check found unchanged is the value before the loop;
two carried values of one settled class are one entry; two collections with one key are one
entry. The supports are the ones with which the check enters the body. -/
theorem Copies.afterLoop_sound
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env)
    {next : Nat} (grows : state.next ≤ next) (gathered : List Copies.Copy)
    (kept : List (Copies.Copy × Bool)) (initial : List Copies.Copy)
    (collected carried : List Located) (size : Option Nat)
    (keptSized : kept.length = initial.length) (initialSized : initial.length = carried.length)
    (initialBelow : ∀ copy ∈ initial, copy.class_ < state.next)
    (results : Values (SideValue model side) (collectedSequencesAt size collected ++ carried))
    (holders : ∀ (index : Nat) (located : Located) (entry : Copies.Copy × Bool),
      carried[index]? = some located → kept[index]? = some entry →
        entry.1.support.contains located.holder = true)
    (unchanged : ∀ (index : Nat) (entry : Copies.Copy × Bool) (before : Copies.Copy),
      kept[index]? = some entry → initial[index]? = some before → entry.2 = true →
      entry.1.support.all side = true →
        valuation.value before.class_ =
          entryOf (plainValues side results) (collected.length + index))
    (carriedAlike : ∀ (one two : Nat) (first second : Copies.Copy × Bool),
      kept[one]? = some first → kept[two]? = some second → first.1.class_ = second.1.class_ →
      first.1.support.all side = true → second.1.support.all side = true →
        entryOf (plainValues side results) (collected.length + one) =
          entryOf (plainValues side results) (collected.length + two))
    (collectedAlike : ∀ (one two : Nat) (first second : Located),
      collected[one]? = some first → collected[two]? = some second →
      Copies.collectionKey gathered collected one = Copies.collectionKey gathered collected two →
      side first.holder = true → side second.holder = true →
      (gathered.getD one default).support.all side = true →
      (gathered.getD two default).support.all side = true →
        entryOf (plainValues side results) one = entryOf (plainValues side results) two) :
    ∃ final : Copies.Valuation model, final.Extends valuation state.next ∧
      Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side final
        (Copies.afterLoop state next gathered kept initial collected)
        (Environment.bindAll env results) := by
  have first := Copies.blocks_spec { state with next := next }
    ((List.range collected.length).map (Copies.collectionKey gathered collected))
  have second := Copies.blocks_spec
    (Copies.blocks { state with next := next }
      ((List.range collected.length).map (Copies.collectionKey gathered collected))).2
    (kept.map fun entry => [entry.1.class_])
  have collectionsSized : (Copies.blocks { state with next := next }
      ((List.range collected.length).map (Copies.collectionKey gathered collected))).1.length =
      collected.length := by
    rw [first.1, List.length_map, List.length_range]
  have finalsSized : (Copies.blocks
      (Copies.blocks { state with next := next }
        ((List.range collected.length).map (Copies.collectionKey gathered collected))).2
      (kept.map fun entry => [entry.1.class_])).1.length = kept.length := by
    rw [second.1, List.length_map]
  have keyAt : ∀ position, position < collected.length →
      ((List.range collected.length).map (Copies.collectionKey gathered collected))[position]? =
        some (Copies.collectionKey gathered collected position) := by
    intro position below
    rw [List.getElem?_map, List.getElem?_range below]
    rfl
  -- the located type at a position of the results: a sequence, or a carried value
  have located_ : ∀ (index : Nat) (located : Located),
      (collectedSequencesAt size collected ++ carried)[index]? = some located →
      (index < collected.length ∧ ∃ entry, collected[index]? = some entry ∧
          located.holder = entry.holder) ∨
        (collected.length ≤ index ∧ carried[index - collected.length]? = some located) := by
    intro index located found
    by_cases below : index < collected.length
    · rw [List.getElem?_append_left (by rw [List.length_map]; exact below)] at found
      have mapped : (collected.map fun entry =>
          (⟨.seq entry.type size, entry.holder⟩ : Located))[index]? = some located := found
      rw [List.getElem?_map] at mapped
      cases at_ : collected[index]? with
      | none => rw [at_] at mapped; cases mapped
      | some entry =>
          rw [at_] at mapped
          cases Option.some.inj mapped
          exact Or.inl ⟨below, entry, rfl, rfl⟩
    · have beyond := Nat.le_of_not_lt below
      rw [List.getElem?_append_right (by rw [List.length_map]; exact beyond),
        List.length_map] at found
      exact Or.inr ⟨beyond, found⟩
  -- the copy of a collection, and of a carried value
  have collectionAt := fun (position : Nat) (entry : Located)
      (found : collected[position]? = some entry) =>
    Copies.loopResults_collected
      (Copies.blocks { state with next := next }
        ((List.range collected.length).map (Copies.collectionKey gathered collected))).1
      (Copies.blocks
        (Copies.blocks { state with next := next }
          ((List.range collected.length).map (Copies.collectionKey gathered collected))).2
        (kept.map fun entry => [entry.1.class_])).1
      gathered kept initial collected collectionsSized found
  have carriedAt := fun (position : Nat) (before : Copies.Copy)
      (found : initial[position]? = some before) =>
    Copies.loopResults_carried
      (Copies.blocks { state with next := next }
        ((List.range collected.length).map (Copies.collectionKey gathered collected))).1
      (Copies.blocks
        (Copies.blocks { state with next := next }
          ((List.range collected.length).map (Copies.collectionKey gathered collected))).2
        (kept.map fun entry => [entry.1.class_])).1
      gathered kept initial collected collectionsSized finalsSized keptSized found
  have finalKeyAt : ∀ (position : Nat) (entry : Copies.Copy × Bool),
      kept[position]? = some entry →
      (kept.map fun entry => [entry.1.class_])[position]? = some [entry.1.class_] := by
    intro position entry found
    rw [List.getElem?_map, found]
    rfl
  obtain ⟨final, finalExtends, finalHold⟩ := Copies.Hold.fresh valuation (next := state.next)
    (after := (Copies.blocks
      (Copies.blocks { state with next := next }
        ((List.range collected.length).map (Copies.collectionKey gathered collected))).2
      (kept.map fun entry => [entry.1.class_])).2.next) results
    (Copies.loopResults
      (Copies.blocks { state with next := next }
        ((List.range collected.length).map (Copies.collectionKey gathered collected))).1
      (Copies.blocks
        (Copies.blocks { state with next := next }
          ((List.range collected.length).map (Copies.collectionKey gathered collected))).2
        (kept.map fun entry => [entry.1.class_])).1
      gathered kept initial collected)
    (by
      rw [Copies.loopResults_length _ _ _ _ _ _ collectionsSized finalsSized keptSized,
        List.length_append, List.length_map, initialSized])
    (fun index located found => by
      rcases located_ index located found with ⟨below, entry, entryAt, holder⟩ | ⟨beyond, carriedAt_⟩
      · obtain ⟨class_, classAt, copy⟩ := collectionAt index entry entryAt
        rw [copy]
        have bounds := first.2.2.1 index class_ classAt
        exact Or.inr ⟨Nat.le_trans grows bounds.1, Nat.lt_of_lt_of_le bounds.2 second.2.1, by
          rw [holder]
          exact Copies.contains_withRole_self _ _⟩
      · have inside : index - collected.length < initial.length := by
          rw [initialSized]
          exact (List.getElem?_eq_some_iff.mp carriedAt_).1
        obtain ⟨class_, entry, classAt, entryAt, copy⟩ :=
          carriedAt (index - collected.length) _ (List.getElem?_eq_getElem inside)
        rw [Nat.add_sub_cancel' beyond] at copy
        rw [copy]
        have holder := holders _ located entry carriedAt_ entryAt
        have bounds := second.2.2.1 _ class_ classAt
        cases flag : entry.2 with
        | true =>
            have old := initialBelow _ (List.getElem_mem inside)
            refine Or.inl ⟨old, holder, Nat.lt_of_lt_of_le old
              (Nat.le_trans grows (Nat.le_trans first.2.1 second.2.1)), fun supported => ?_⟩
            have same := unchanged _ entry _ entryAt (List.getElem?_eq_getElem inside) flag
              supported
            rw [Nat.add_sub_cancel' beyond] at same
            exact same
        | false =>
            exact Or.inr ⟨Nat.le_trans grows (Nat.le_trans first.2.1 bounds.1), bounds.2, holder⟩)
    (fun one two oneLocated twoLocated oneFound twoFound beyond same oneInside twoInside => by
      rcases located_ one oneLocated oneFound with
        ⟨oneBelow, oneEntry, oneEntryAt, _⟩ | ⟨oneBeyond, oneCarried⟩
      · obtain ⟨oneClass, oneClassAt, oneCopy⟩ := collectionAt one oneEntry oneEntryAt
        rw [oneCopy] at same oneInside
        have oneBounds := first.2.2.1 one oneClass oneClassAt
        rcases located_ two twoLocated twoFound with
          ⟨twoBelow, twoEntry, twoEntryAt, _⟩ | ⟨twoBeyond, twoCarried⟩
        · obtain ⟨twoClass, twoClassAt, twoCopy⟩ := collectionAt two twoEntry twoEntryAt
          rw [twoCopy] at same twoInside
          have keys := (first.2.2.2 one two _ _ oneClass twoClass (keyAt one oneBelow)
            (keyAt two twoBelow) oneClassAt twoClassAt).mp same
          obtain ⟨oneSupport, oneMember⟩ := Copies.all_of_withRole oneInside
          obtain ⟨twoSupport, twoMember⟩ := Copies.all_of_withRole twoInside
          exact collectedAlike one two oneEntry twoEntry oneEntryAt twoEntryAt keys oneMember
            twoMember oneSupport twoSupport
        · -- a collection and a carried value have different classes
          have inside : two - collected.length < initial.length := by
            rw [initialSized]
            exact (List.getElem?_eq_some_iff.mp twoCarried).1
          obtain ⟨twoClass, twoEntry, twoClassAt, twoEntryAt, twoCopy⟩ :=
            carriedAt (two - collected.length) _ (List.getElem?_eq_getElem inside)
          rw [Nat.add_sub_cancel' twoBeyond] at twoCopy
          rw [twoCopy] at same
          have twoLow : (Copies.blocks { state with next := next }
              ((List.range collected.length).map
                (Copies.collectionKey gathered collected))).2.next ≤ twoClass :=
            (second.2.2.1 _ twoClass twoClassAt).1
          have old := initialBelow _ (List.getElem_mem inside)
          have oneLow : next ≤ oneClass := oneBounds.1
          have differs : oneClass ≠ cond twoEntry.2
              (initial[two - collected.length]'inside).class_ twoClass := by
            cases twoEntry.2 with
            | true =>
                exact Nat.ne_of_gt (Nat.lt_of_lt_of_le old (Nat.le_trans grows oneLow))
            | false => exact Nat.ne_of_lt (Nat.lt_of_lt_of_le oneBounds.2 twoLow)
          exact absurd same differs
      · have oneIn : one - collected.length < initial.length := by
          rw [initialSized]
          exact (List.getElem?_eq_some_iff.mp oneCarried).1
        obtain ⟨oneClass, oneEntry, oneClassAt, oneEntryAt, oneCopy⟩ :=
          carriedAt (one - collected.length) _ (List.getElem?_eq_getElem oneIn)
        rw [Nat.add_sub_cancel' oneBeyond] at oneCopy
        rw [oneCopy] at beyond same oneInside
        have oneBounds := second.2.2.1 _ oneClass oneClassAt
        have oneOld := initialBelow _ (List.getElem_mem oneIn)
        -- a class at or above the state's next is the class of the settled class
        have oneFlag : oneEntry.2 = false := by
          cases flag : oneEntry.2 with
          | false => rfl
          | true =>
              rw [flag] at beyond
              exact absurd oneOld (Nat.not_lt.mpr beyond)
        rw [oneFlag] at same
        rcases located_ two twoLocated twoFound with
          ⟨twoBelow, twoEntry, twoEntryAt, _⟩ | ⟨twoBeyond, twoCarried⟩
        · obtain ⟨twoClass, twoClassAt, twoCopy⟩ := collectionAt two twoEntry twoEntryAt
          rw [twoCopy] at same
          have twoBounds := first.2.2.1 two twoClass twoClassAt
          have oneLow : (Copies.blocks { state with next := next }
              ((List.range collected.length).map
                (Copies.collectionKey gathered collected))).2.next ≤ oneClass := oneBounds.1
          have classes : oneClass = twoClass := same
          exact absurd classes (Nat.ne_of_gt (Nat.lt_of_lt_of_le twoBounds.2 oneLow))
        · have twoIn : two - collected.length < initial.length := by
            rw [initialSized]
            exact (List.getElem?_eq_some_iff.mp twoCarried).1
          obtain ⟨twoClass, twoEntry, twoClassAt, twoEntryAt, twoCopy⟩ :=
            carriedAt (two - collected.length) _ (List.getElem?_eq_getElem twoIn)
          rw [Nat.add_sub_cancel' twoBeyond] at twoCopy
          rw [twoCopy] at same twoInside
          have twoBounds := second.2.2.1 _ twoClass twoClassAt
          have twoOld := initialBelow _ (List.getElem_mem twoIn)
          have twoFlag : twoEntry.2 = false := by
            cases flag : twoEntry.2 with
            | false => rfl
            | true =>
                rw [flag] at same
                have classes : oneClass = (initial[two - collected.length]'twoIn).class_ := same
                have oneLow : (Copies.blocks { state with next := next }
                    ((List.range collected.length).map
                      (Copies.collectionKey gathered collected))).2.next ≤ oneClass := oneBounds.1
                have low : next ≤ (Copies.blocks { state with next := next }
                    ((List.range collected.length).map
                      (Copies.collectionKey gathered collected))).2.next := first.2.1
                exact absurd (classes ▸ twoOld)
                  (Nat.not_lt.mpr (Nat.le_trans grows (Nat.le_trans low oneLow)))
          rw [twoFlag] at same
          have keys := (second.2.2.2 _ _ _ _ oneClass twoClass (finalKeyAt _ oneEntry oneEntryAt)
            (finalKeyAt _ twoEntry twoEntryAt) oneClassAt twoClassAt).mp same
          have alike := carriedAlike _ _ oneEntry twoEntry oneEntryAt twoEntryAt
            (List.head_eq_of_cons_eq keys) oneInside twoInside
          rw [Nat.add_sub_cancel' oneBeyond, Nat.add_sub_cancel' twoBeyond] at alike
          exact alike)
  refine ⟨final, finalExtends, sound.bind finalExtends
    (after := (Copies.blocks
      (Copies.blocks { state with next := next }
        ((List.range collected.length).map (Copies.collectionKey gathered collected))).2
      (kept.map fun entry : Copies.Copy × Bool => [entry.1.class_])).2) rfl
    (Nat.le_trans grows (Nat.le_trans first.2.1 second.2.1))
    (fun entry member => (sound.made entry member).extend typeTable rows callees functionTable
      finalExtends (Nat.le_trans grows (Nat.le_trans first.2.1 second.2.1))) finalHold⟩

end Loop

/-! ## The iterations of a loop -/

/-- Iterations keep what every step keeps. -/
theorem iterations_coheres {I : PIR.Signature} {State Produced : Type} {Collected : Nat → Type}
    {step : Nat → State → PIR.Process I Produced} {carry : Produced → State}
    {push : (done : Nat) → Produced → Collected done → Collected (done + 1)}
    (holds : (done : Nat) → State → Collected done → Prop)
    (steps : ∀ (done : Nat) (state : State) (earlier : Collected done), holds done state earlier →
      Coheres (fun produced => holds (done + 1) (carry produced) (push done produced earlier))
        (step done state)) :
    ∀ (remaining done : Nat) (state : State) (earlier : Collected done),
      holds done state earlier →
        Coheres (fun final => holds (iterationsAfter remaining done) final.1 final.2)
          (iterations step carry push remaining done state earlier)
  | 0, _, _, _, start => Coheres.done start
  | remaining + 1, done, state, earlier, start =>
      (steps done state earlier start).bind fun produced next =>
        iterations_coheres holds steps remaining (done + 1) (carry produced)
          (push done produced earlier) next

/-- A support whose roles are all in another that is inside a side is inside the side. -/
theorem Copies.all_of_contains {side : Side} {old new : List Nat}
    (within : ∀ role, new.contains role = true → old.contains role = true)
    (inside : old.all side = true) : new.all side = true := by
  rw [List.all_eq_true] at inside ⊢
  intro role member
  exact inside role (by simpa using within role (by simpa using member))

section Iterations

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} {typeTable : TypeTable} {rows : Scope operations} {callees : Scope functions}
  {functionTable : FunctionTable model functions} {side : Side}

/-- The copies before the first operands are copies of the first values. -/
theorem Copies.Hold.take {valuation : Copies.Valuation model} {next : Nat} (first : List Located)
    {rest : List Located} {copies : List Copies.Copy}
    {values : Values (SideValue model side) (first ++ rest)}
    (hold : Copies.Hold side valuation next copies values) :
    Copies.Hold side valuation next (copies.take first.length) (values.split first).1 := by
  refine ⟨by
    rw [List.length_take, hold.1, List.length_append, Nat.min_eq_left (Nat.le_add_right _ _)],
    fun index located found => ?_⟩
  have below : index < first.length := (List.getElem?_eq_some_iff.mp found).1
  have whole := hold.2 index located (by
    rw [List.getElem?_append_left below]
    exact found)
  have entry := entryOf_plain_append_left side (values.split first).1 (values.split first).2
    index below
  rw [Values.append_split] at entry
  rw [entry] at whole
  have copy : (copies.take first.length).getD index default = copies.getD index default := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt below]
  rw [copy]
  exact whole

/-- A value that every role of a list holds, at a role in the side. -/
theorem heldCopies_value (side : Side) (type : Ty) (reply : model.Value type) :
    ∀ (participants : List Nat) {role : Nat} (position : Var participants role)
      (member : side role = true),
      Held.value (side role) member
        ((unmapValues (F := SideValue model side) (fun role => (⟨type, role⟩ : Located))
          participants (heldCopies model side type reply participants)).get position) = reply
  | [], _, position, _ => position.elimNil
  | _ :: participants, _, position, member => by
      cases position with
      | here => exact Held.value_of _ member reply
      | there position => exact heldCopies_value side type reply participants position member

/-- What holds of the carried values and of the sequences collected so far, between the
iterations of a loop: two carried values of one settled class whose entering supports are
inside the side are one entry; a carried value that the check found unchanged, with its
entering support inside the side, is the value before the loop; two collected positions of
one type whose values the body returns in one class, with supports inside the side, have one
sequence so far. -/
structure Copies.LoopHolds (side : Side) (kept : List (Copies.Copy × Bool))
    (gathered : List Copies.Copy) (collected carried : List Located)
    (start : Values (SideValue model side) carried) {done : Nat}
    (current : Values (SideValue model side) carried)
    (sequences : Values (SideValue model side) (collectedSequencesAt (some done) collected)) :
    Prop where
  alike : ∀ (one two : Nat) (first second : Copies.Copy × Bool),
    kept[one]? = some first → kept[two]? = some second → first.1.class_ = second.1.class_ →
    first.1.support.all side = true → second.1.support.all side = true →
      entryOf (plainValues side current) one = entryOf (plainValues side current) two
  unchanged : ∀ (index : Nat) (entry : Copies.Copy × Bool), kept[index]? = some entry →
    entry.2 = true → entry.1.support.all side = true →
      entryOf (plainValues side current) index = entryOf (plainValues side start) index
  sequences : ∀ (one two : Nat) (type : Ty) (holder owner : Nat),
    collected[one]? = some ⟨type, holder⟩ → collected[two]? = some ⟨type, owner⟩ →
    side holder = true → side owner = true →
    (gathered.getD one default).class_ = (gathered.getD two default).class_ →
    (gathered.getD one default).support.all side = true →
    (gathered.getD two default).support.all side = true →
      entryOf (plainValues side sequences) one = entryOf (plainValues side sequences) two

/-- The state at the start of an iteration holds, under a valuation made from the one before
the loop: the iteration number has the class before the entering classes, each carried value
has its entering class, and the captures are as they were. -/
theorem Copies.loop_enter {valuation : Copies.Valuation model} {state : Copies.State}
    (madeSound : ∀ entry ∈ state.made,
      Copies.MadeSound (deployed := deployed) typeTable rows callees functionTable valuation
        state.next entry)
    (participants : List Nat) (carried captures : List Located)
    (classes : List Nat) (supports : List (List Nat)) (entered : Nat)
    (classesSized : classes.length = carried.length)
    (supportsSized : supports.length = carried.length)
    (grows : state.next + 1 ≤ entered)
    (bounds : ∀ (index class_ : Nat), classes[index]? = some class_ →
      state.next + 1 ≤ class_ ∧ class_ < entered)
    (holders : ∀ (index : Nat) (located : Located) (support : List Nat),
      carried[index]? = some located → supports[index]? = some support →
        support.contains located.holder = true)
    {capturedCopies : List Copies.Copy} {captured : Values (SideValue model side) captures}
    (capturedHold : Copies.Hold side valuation state.next capturedCopies captured)
    (iteration : Nat) (current : Values (SideValue model side) carried)
    (alike : ∀ (one two : Nat) (oneClass twoClass : Nat) (oneSupport twoSupport : List Nat),
      classes[one]? = some oneClass → classes[two]? = some twoClass →
      supports[one]? = some oneSupport → supports[two]? = some twoSupport →
      oneClass = twoClass → oneSupport.all side = true → twoSupport.all side = true →
        entryOf (plainValues side current) one = entryOf (plainValues side current) two) :
    ∃ entering : Copies.Valuation model, entering.Extends valuation state.next ∧
      Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side entering
        ⟨Copies.loopOwn participants state.next classes supports ++ capturedCopies, entered,
          state.made⟩
        (Environment.ofValues
          ((heldCopies model side .nat iteration participants).append
            (current.append captured))) ∧
      ∀ (index class_ : Nat) (support : List Nat), classes[index]? = some class_ →
        supports[index]? = some support → support.all side = true →
          entering.value class_ = entryOf (plainValues side current) index := by
  -- the iteration number
  have numbered := Copies.Valuation.set_extends valuation (Nat.le_refl state.next)
    (some ⟨.nat, iteration⟩)
  have numbersHold : Copies.Hold side (valuation.set state.next (some ⟨.nat, iteration⟩))
      (state.next + 1) (participants.map fun role => (⟨state.next, [role]⟩ : Copies.Copy))
      (heldCopies model side .nat iteration participants) := by
    refine ⟨by rw [List.length_map, List.length_map], fun index located found => ?_⟩
    have found' : (participants.map fun role => (⟨.nat, role⟩ : Located))[index]? = some located :=
      found
    rw [List.getElem?_map] at found'
    cases roleAt : participants[index]? with
    | none => rw [roleAt] at found'; cases found'
    | some role =>
        rw [roleAt] at found'
        cases Option.some.inj found'
        rw [getD_map_of_getElem? _ _ roleAt]
        refine ⟨by simp, Nat.lt_succ_self _, fun inside => ?_⟩
        rw [List.all_cons, List.all_nil, Bool.and_true] at inside
        rw [entryOf_heldCopies side .nat iteration participants index role roleAt inside]
        simp only [Copies.Valuation.set, ↓reduceIte]
  -- the copy with which a carried value enters
  have copyAt : ∀ (index : Nat) (located : Located), carried[index]? = some located →
      ∃ (class_ : Nat) (support : List Nat), classes[index]? = some class_ ∧
        supports[index]? = some support ∧
        ((classes.zip supports).map fun entry => (⟨entry.1, entry.2⟩ : Copies.Copy)).getD index
          default = ⟨class_, support⟩ := by
    intro index located found
    have below : index < carried.length := (List.getElem?_eq_some_iff.mp found).1
    have classBelow : index < classes.length := classesSized ▸ below
    have supportBelow : index < supports.length := supportsSized ▸ below
    exact ⟨classes[index], supports[index], List.getElem?_eq_getElem classBelow,
      List.getElem?_eq_getElem supportBelow,
      getD_map_of_getElem? (fun entry : Nat × List Nat => (⟨entry.1, entry.2⟩ : Copies.Copy))
        (classes.zip supports) (item := (classes[index], supports[index]))
        (List.getElem?_zip_eq_some.mpr
          ⟨List.getElem?_eq_getElem classBelow, List.getElem?_eq_getElem supportBelow⟩) default⟩
  obtain ⟨entering, extends_, carriedHold⟩ := Copies.Hold.fresh
    (valuation.set state.next (some ⟨.nat, iteration⟩)) (next := state.next + 1) (after := entered)
    current ((classes.zip supports).map fun entry => (⟨entry.1, entry.2⟩ : Copies.Copy))
    (by rw [List.length_map, List.length_zip, classesSized, supportsSized, Nat.min_self])
    (fun index located found => by
      obtain ⟨class_, support, classAt, supportAt, copy⟩ := copyAt index located found
      rw [copy]
      exact Or.inr ⟨(bounds index class_ classAt).1, (bounds index class_ classAt).2,
        holders index located support found supportAt⟩)
    (fun one two oneLocated twoLocated oneFound twoFound _ same oneInside twoInside => by
      obtain ⟨oneClass, oneSupport, oneClassAt, oneSupportAt, oneCopy⟩ :=
        copyAt one oneLocated oneFound
      obtain ⟨twoClass, twoSupport, twoClassAt, twoSupportAt, twoCopy⟩ :=
        copyAt two twoLocated twoFound
      rw [oneCopy] at same oneInside
      rw [twoCopy] at same twoInside
      exact alike one two oneClass twoClass oneSupport twoSupport oneClassAt twoClassAt
        oneSupportAt twoSupportAt same oneInside twoInside)
  have whole := numbered.trans extends_ (Nat.le_succ _)
  have hold := (numbersHold.extend extends_ grows).append
    (carriedHold.append (capturedHold.extend whole (Nat.le_trans (Nat.le_succ _) grows)))
  rw [← List.append_assoc] at hold
  refine ⟨entering, whole, Copies.State.Sound.enter
    (fun entry member => (madeSound entry member).extend typeTable rows callees functionTable
      whole (Nat.le_trans (Nat.le_succ _) grows)) hold,
    fun index class_ support classAt supportAt inside => ?_⟩
  have below : index < carried.length :=
    classesSized ▸ (List.getElem?_eq_some_iff.mp classAt).1
  obtain ⟨other, otherSupport, otherAt, otherSupportAt, copy⟩ :=
    copyAt index carried[index] (List.getElem?_eq_getElem below)
  cases Option.some.inj (classAt.symm.trans otherAt)
  cases Option.some.inj (supportAt.symm.trans otherSupportAt)
  have known := (carriedHold.2 index carried[index] (List.getElem?_eq_getElem below)).2.2
  rw [copy] at known
  exact known inside

/-- What holds between the iterations holds after one more: of the carried values that the
body returned and of the sequences with what it collected. `classes` and `supports` are those
with which the carried values enter the body, and `returned` what the check says the body
returns: the carried values of one entering class in one class, each with a support inside
the entering one. -/
theorem Copies.loop_leave {kept : List (Copies.Copy × Bool)} {gathered : List Copies.Copy}
    {collected carried : List Located} {start : Values (SideValue model side) carried}
    (classes : List Nat) (supports : List (List Nat))
    (classesSized : classes.length = carried.length)
    (supportsSized : supports.length = carried.length) (keptSized : kept.length = carried.length)
    (entered : Nat) (bounds : ∀ (index class_ : Nat), classes[index]? = some class_ →
      class_ < entered)
    (keptAt : ∀ (index class_ : Nat) (support : List Nat), classes[index]? = some class_ →
      supports[index]? = some support → ∃ flag, kept[index]? = some (⟨class_, support⟩, flag))
    (returned : List Copies.Copy) (gatheredIs : gathered = returned.take collected.length)
    (refinedSame : ∀ (one two : Nat) (oneClass twoClass : Nat) (first second : Copies.Copy),
      classes[one]? = some oneClass → classes[two]? = some twoClass → oneClass = twoClass →
      (returned.drop collected.length)[one]? = some first →
      (returned.drop collected.length)[two]? = some second → first.class_ = second.class_)
    (within : ∀ (index : Nat) (support : List Nat) (after : Copies.Copy),
      supports[index]? = some support → (returned.drop collected.length)[index]? = some after →
      ∀ role, after.support.contains role = true → support.contains role = true)
    (flagged : ∀ (index class_ : Nat) (support : List Nat) (after : Copies.Copy),
      kept[index]? = some (⟨class_, support⟩, true) →
      (returned.drop collected.length)[index]? = some after → after.class_ = class_)
    {entering later : Copies.Valuation model} {next done : Nat}
    {current : Values (SideValue model side) carried}
    {sequences : Values (SideValue model side) (collectedSequencesAt (some done) collected)}
    (enteringValues : ∀ (index class_ : Nat) (support : List Nat), classes[index]? = some class_ →
      supports[index]? = some support → support.all side = true →
        entering.value class_ = entryOf (plainValues side current) index)
    (extends_ : later.Extends entering entered)
    {produced : Values (SideValue model side) (collected ++ carried)}
    (hold : Copies.Hold side later next returned produced)
    (before : Copies.LoopHolds side kept gathered collected carried start current sequences) :
    Copies.LoopHolds side kept gathered collected carried start (produced.split collected).2
      (sideCollectedPush model side collected (produced.split collected).1 sequences) := by
  have afterHold := hold.drop collected
  have gatheredHold := hold.take collected
  -- a kept entry: the entering class and support at its position, and what the body returns
  have entryAt : ∀ (index : Nat) (entry : Copies.Copy × Bool), kept[index]? = some entry →
      ∃ (class_ : Nat) (support : List Nat) (flag : Bool) (after : Copies.Copy) (located : Located),
        classes[index]? = some class_ ∧ supports[index]? = some support ∧
        entry = (⟨class_, support⟩, flag) ∧
        (returned.drop collected.length)[index]? = some after ∧ carried[index]? = some located := by
    intro index entry found
    have below : index < carried.length := keptSized ▸ (List.getElem?_eq_some_iff.mp found).1
    have classBelow : index < classes.length := classesSized ▸ below
    have supportBelow : index < supports.length := supportsSized ▸ below
    have afterBelow : index < (returned.drop collected.length).length := afterHold.1 ▸ below
    obtain ⟨flag, keptIs⟩ := keptAt index classes[index] supports[index]
      (List.getElem?_eq_getElem classBelow) (List.getElem?_eq_getElem supportBelow)
    exact ⟨classes[index], supports[index], flag, (returned.drop collected.length)[index],
      carried[index], List.getElem?_eq_getElem classBelow, List.getElem?_eq_getElem supportBelow,
      Option.some.inj (found.symm.trans keptIs), List.getElem?_eq_getElem afterBelow,
      List.getElem?_eq_getElem below⟩
  -- what the body returns at a carried position whose entering support is inside the side
  have returnedAt : ∀ (index : Nat) (support : List Nat) (after : Copies.Copy) (located : Located),
      supports[index]? = some support → (returned.drop collected.length)[index]? = some after →
      carried[index]? = some located → support.all side = true →
        later.value after.class_ =
          entryOf (plainValues side (produced.split collected).2) index := by
    intro index support after located supportAt afterAt locatedAt inside
    have known := (afterHold.2 index located locatedAt).2.2
    rw [List.getD_eq_getElem?_getD, afterAt] at known
    exact known (Copies.all_of_contains (within index support after supportAt afterAt) inside)
  refine ⟨fun one two first second firstAt secondAt same firstInside secondInside => ?_,
    fun index entry found flag inside => ?_,
    fun one two type holder owner oneAt twoAt oneMember twoMember same oneInside twoInside => ?_⟩
  · obtain ⟨oneClass, oneSupport, _, oneAfter, oneLocated, oneClassAt, oneSupportAt, rfl,
      oneAfterAt, oneLocatedAt⟩ := entryAt one first firstAt
    obtain ⟨twoClass, twoSupport, _, twoAfter, twoLocated, twoClassAt, twoSupportAt, rfl,
      twoAfterAt, twoLocatedAt⟩ := entryAt two second secondAt
    rw [← returnedAt one oneSupport oneAfter oneLocated oneSupportAt oneAfterAt oneLocatedAt
        firstInside,
      ← returnedAt two twoSupport twoAfter twoLocated twoSupportAt twoAfterAt twoLocatedAt
        secondInside,
      refinedSame one two oneClass twoClass oneAfter twoAfter oneClassAt twoClassAt same
        oneAfterAt twoAfterAt]
  · obtain ⟨class_, support, entryFlag, after, located, classAt, supportAt, rfl, afterAt,
      locatedAt⟩ := entryAt index entry found
    cases flag
    have returnedClass := flagged index class_ support after found afterAt
    rw [← before.unchanged index _ found rfl inside,
      ← enteringValues index class_ support classAt supportAt inside,
      ← extends_ class_ (bounds index class_ classAt), ← returnedClass]
    exact (returnedAt index support after located supportAt afterAt locatedAt inside).symm
  · have collectedAt : ∀ (index : Nat) (role : Nat), collected[index]? = some ⟨type, role⟩ →
        (gathered.getD index default).support.all side = true →
        later.value (gathered.getD index default).class_ =
          entryOf (plainValues side (produced.split collected).1) index := by
      intro index role found inside
      have known := (gatheredHold.2 index ⟨type, role⟩ found).2.2
      rw [← gatheredIs] at known
      exact known inside
    exact collectedPush_alike collected _ sequences oneAt twoAt oneMember twoMember
      (by rw [← collectedAt one holder oneAt oneInside, ← collectedAt two owner twoAt twoInside,
        same])
      (before.sequences one two type holder owner oneAt twoAt oneMember twoMember same oneInside
        twoInside)

end Iterations

/-! ## Regions -/

section Region

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool} (typeTable : TypeTable)
  (rows : Scope operations) (callees : Scope functions)
  (functionTable : FunctionTable model functions)

/-- What a region returns holds of its outputs under a valuation: the copies it returns are
copies of the outputs, and the operations made up to its end are sound. -/
def Copies.Returned.Sound (side : Side) (valuation : Copies.Valuation model)
    (returned : Copies.Returned) {out : List Located}
    (outputs : Values (SideValue model side) out) : Prop :=
  (∃ copies, returned.copies = some copies ∧
      Copies.Hold side valuation returned.next copies outputs) ∧
    ∀ entry ∈ returned.made,
      Copies.MadeSound (deployed := deployed) typeTable rows callees functionTable valuation
        returned.next entry

/-- What holds after a region that started from a state under a valuation: a valuation that
extends the first, of which what the region returns holds. -/
def Copies.After (side : Side) (valuation : Copies.Valuation model) (state : Copies.State)
    (returned : Copies.Returned) {out : List Located}
    (outputs : Values (SideValue model side) out) : Prop :=
  ∃ later : Copies.Valuation model, later.Extends valuation state.next ∧
    state.next ≤ returned.next ∧
    Copies.Returned.Sound (deployed := deployed) typeTable rows callees functionTable side later
      returned outputs

/-- Every protocol of a table, for a side that supports its requirements, on arguments of
which its input agreements hold, never stops `incomplete` and returns values of which its
output agreements hold. -/
@[expose] def Copies.AgreeingProtocols (table : ProtocolTable model protocols)
    (summaries : List (List Copies.Requirement)) : Prop :=
  ∀ {header : ProtocolHeader} (callee : Var protocols header) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) header.inputs),
    header.agreements.InputsHold model side arguments →
    side.supports (summaries.getD callee.index []) = true →
    Coheres (fun outputs => ∀ agreement ∈ header.agreements.outputs,
        agreement.Holds model side outputs)
      (table.get callee path side arguments)

/-- The nested regions of an instruction, for a side. For the region with each number, from
any valuation under which the state at the start of the regions holds of its inputs, the
region coheres with: a later valuation that extends the first from the next class at the
start, under which the copies that the check says the region returns hold of its outputs, at
the next class after all the regions. -/
def Copies.RegionsCohere (side : Side) (base : Copies.State) (start after : Nat) :
    List (Option (List Copies.Copy)) → {signatures : List (List Located × List Located)} →
      Values (RegionFunction (SideValue model side) (Effects model)) signatures → Prop
  | arms, _, .nil => arms = []
  | arms, _, .cons (ty := signature) body rest =>
      ∃ arm others, arms = arm :: others ∧
        (∀ (valuation : Copies.Valuation model)
          (inputs : Values (SideValue model side) signature.1),
          Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
            valuation { base with next := start } (Environment.ofValues inputs) →
          Coheres (fun outputs => ∃ later : Copies.Valuation model,
              later.Extends valuation start ∧
              ∃ copies, arm = some copies ∧ Copies.Hold side later after copies outputs)
            (body inputs)) ∧
        Copies.RegionsCohere side base start after others rest

/-- One of the nested regions ran: a later valuation under which the copies that the check
says one of them returns hold of the outputs. -/
def Copies.ArmRan (side : Side) (valuation : Copies.Valuation model) (lower after : Nat)
    (arms : List (Option (List Copies.Copy))) {outputs : List Located}
    (results : Values (SideValue model side) outputs) : Prop :=
  ∃ later : Copies.Valuation model, later.Extends valuation lower ∧
    ∃ copies, some copies ∈ arms ∧ Copies.Hold side later after copies results

variable {typeTable rows callees functionTable}

/-- The region with a number among equal regions. -/
theorem Copies.selectArm_coheres (side : Side) (base : Copies.State) (start after : Nat)
    (signature : List Located × List Located) : ∀ (count : Nat)
    (regions : Values (RegionFunction (SideValue model side) (Effects model))
      (List.replicate count signature)) (number : Fin count)
    (arms : List (Option (List Copies.Copy))),
    Copies.RegionsCohere (deployed := deployed) typeTable rows callees functionTable side base
      start after arms regions →
    ∀ (valuation : Copies.Valuation model) (inputs : Values (SideValue model side) signature.1),
      Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side valuation
        { base with next := start } (Environment.ofValues inputs) →
      Coheres (Copies.ArmRan side valuation start after arms)
        (selectArm signature count regions number inputs)
  | 0, _, number, _, _ => number.elim0
  | count + 1, regions, ⟨0, _⟩, arms, sound => by
      cases regions with
      | cons body rest =>
          obtain ⟨arm, others, rfl, here, _⟩ := sound
          exact fun valuation inputs entered => (here valuation inputs entered).weaken
            fun _ ran => by
              obtain ⟨later, extends_, copies, same, hold⟩ := ran
              exact ⟨later, extends_, copies, same ▸ List.mem_cons_self .., hold⟩
  | count + 1, regions, ⟨number + 1, below⟩, arms, sound => by
      cases regions with
      | cons body rest =>
          obtain ⟨arm, others, rfl, _, there⟩ := sound
          intro valuation inputs entered
          exact (Copies.selectArm_coheres side base start after signature count rest
            ⟨number, Nat.lt_of_succ_lt_succ below⟩ others there valuation inputs entered).weaken
              fun _ ran => by
                obtain ⟨later, extends_, copies, inside, hold⟩ := ran
                exact ⟨later, extends_, copies, List.mem_cons_of_mem _ inside, hold⟩

/-- A copy that is the first alternative wherever it is held has its payload. -/
theorem firstPayload_inl {First Later : Type} (value : First) :
    ∀ (present : Bool) (held : Held (First ⊕ Later) present),
      (∀ member : present = true, Held.value present member held = .inl value) →
      ∃ payload, firstPayload present held = some payload ∧
        ∀ member : present = true, Held.value present member payload = value
  | true, .inl _, equal => ⟨_, rfl, fun _ => Sum.inl.inj (equal rfl)⟩
  | true, .inr _, equal => nomatch equal rfl
  | false, _, _ => ⟨PUnit.unit, rfl, fun member => nomatch member⟩

/-- A copy that is a later alternative wherever it is held is a copy of it. -/
theorem laterCopy_inr {First Later : Type} (value : Later) :
    ∀ (present : Bool) (held : Held (First ⊕ Later) present),
      (∀ member : present = true, Held.value present member held = .inr value) →
      ∃ later, laterCopy present held = some later ∧
        ∀ member : present = true, Held.value present member later = value
  | true, .inr _, equal => ⟨_, rfl, fun _ => Sum.inr.inj (equal rfl)⟩
  | true, .inl _, equal => nomatch equal rfl
  | false, _, _ => ⟨PUnit.unit, rfl, fun member => nomatch member⟩

/-- Copies of a variant that are, wherever the side holds them, the first alternative with one
payload: every participant has its payload, and the payloads in the side are that payload. -/
theorem firstPayloads_equal (side : Side) (payload : Ty) (rest : List Ty)
    (value : model.Value payload) :
    ∀ (roles : List Nat)
      (copies : Values (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side role))
        roles),
      (∀ {role : Nat} (position : Var roles role) (member : side role = true),
        Held.value (side role) member (copies.get position) = .inl value) →
      ∃ payloads, firstPayloads model side payload rest roles copies = some payloads ∧
        ∀ {role : Nat} (position : Var roles role) (member : side role = true),
          Held.value (side role) member (payloads.get position) = value
  | [], _, _ => ⟨.nil, rfl, fun position _ => position.elimNil⟩
  | role :: roles, copies, equal => by
      obtain ⟨tail, found, each⟩ := firstPayloads_equal side payload rest value roles copies.tail
        fun position member => tail_get copies position ▸ equal position.there member
      obtain ⟨first, firstFound, firstIs⟩ := firstPayload_inl value (side role) (copies.get .here)
        fun member => equal .here member
      refine ⟨.cons first tail, by rw [firstPayloads, firstFound, found]; rfl,
        fun position member => ?_⟩
      cases position with
      | here => exact firstIs member
      | there position => exact each position member

/-- Copies of a variant that are, wherever the side holds them, one later alternative: they
are copies of that value of the variant of the later alternatives. -/
theorem laterCopies_equal (side : Side) (payload : Ty) (rest : List Ty)
    (value : Ty.Variant model.Carrier rest) :
    ∀ (roles : List Nat)
      (copies : Values (fun role => Held (Ty.Variant model.Carrier (payload :: rest)) (side role))
        roles),
      (∀ {role : Nat} (position : Var roles role) (member : side role = true),
        Held.value (side role) member (copies.get position) = .inr value) →
      ∃ later, laterCopies model side payload rest roles copies = some later ∧
        ∀ {role : Nat} (position : Var roles role) (member : side role = true),
          Held.value (side role) member (later.get position) = value
  | [], _, _ => ⟨.nil, rfl, fun position _ => position.elimNil⟩
  | role :: roles, copies, equal => by
      obtain ⟨tail, found, each⟩ := laterCopies_equal side payload rest value roles copies.tail
        fun position member => tail_get copies position ▸ equal position.there member
      obtain ⟨first, firstFound, firstIs⟩ := laterCopy_inr value (side role) (copies.get .here)
        fun member => equal .here member
      refine ⟨.cons first tail, by rw [laterCopies, firstFound, found]; rfl,
        fun position member => ?_⟩
      cases position with
      | here => exact firstIs member
      | there position => exact each position member

/-- The region of the alternative that the participants in the side all hold: it runs, on the
payload of that alternative, from a state that holds of the payloads and the captures. -/
theorem Copies.alternativeProcess_coheres (side : Side) (participants : List Nat)
    (captures outputs : List Located) (captured : Values (SideValue model side) captures)
    (base : Copies.State) (start after : Nat) (valuation : Copies.Valuation model) (lower : Nat)
    (grows : lower ≤ start)
    (enters : ∀ {payload : Ty} (value : model.Value payload)
      (payloads : Values (fun role => Held (model.Value payload) (side role)) participants),
      (∀ {role : Nat} (position : Var participants role) (member : side role = true),
        Held.value (side role) member (payloads.get position) = value) →
      ∃ entered : Copies.Valuation model, entered.Extends valuation lower ∧
        Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side entered
          { base with next := start }
          (Environment.ofValues
            ((remapValues (F := SideValue model side) (fun role => (⟨payload, role⟩ : Located))
              participants payloads).append captured))) :
    ∀ (alternatives : List Ty)
      (regions : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (value : Ty.Variant model.Carrier alternatives)
      (copies : Values (fun role => Held (Ty.Variant model.Carrier alternatives) (side role))
        participants)
      (arms : List (Option (List Copies.Copy))),
      Copies.RegionsCohere (deployed := deployed) typeTable rows callees functionTable side base
        start after arms regions →
      (∀ {role : Nat} (position : Var participants role) (member : side role = true),
        Held.value (side role) member (copies.get position) = value) →
      Coheres (Copies.ArmRan side valuation lower after arms)
        (alternativeProcess model side participants captures outputs alternatives regions
          (alternativeNumber alternatives value) copies captured)
  | [], _, value, _, _, _, _ => nomatch value
  | payload :: rest, regions, .inl first, copies, arms, sound, equal => by
      cases regions with
      | cons body others =>
          obtain ⟨arm, remaining, rfl, here, _⟩ := sound
          obtain ⟨payloads, found, each⟩ :=
            firstPayloads_equal side payload rest first participants copies equal
          obtain ⟨entered, extends_, enteredSound⟩ := enters first payloads each
          show Coheres _ (alternativeProcess model side participants captures outputs
            (payload :: rest) (.cons body others) 0 copies captured)
          rw [alternativeProcess, found]
          exact (here entered _ enteredSound).weaken fun _ ran => by
            obtain ⟨last, lastExtends, found', same, hold⟩ := ran
            exact ⟨last, extends_.trans lastExtends grows, found', same ▸ List.mem_cons_self ..,
              hold⟩
  | payload :: rest, regions, .inr later, copies, arms, sound, equal => by
      cases regions with
      | cons body others =>
          obtain ⟨arm, remaining, rfl, _, there⟩ := sound
          obtain ⟨laterOnes, found, each⟩ :=
            laterCopies_equal side payload rest later participants copies equal
          show Coheres _ (alternativeProcess model side participants captures outputs
            (payload :: rest) (.cons body others) (alternativeNumber rest later + 1) copies captured)
          rw [alternativeProcess, found]
          exact (Copies.alternativeProcess_coheres side participants captures outputs captured base
            start after valuation lower grows enters rest others later laterOnes remaining there
            each).weaken fun _ ran => by
              obtain ⟨last, lastExtends, found', inside, hold⟩ := ran
              exact ⟨last, lastExtends, found', List.mem_cons_of_mem _ inside, hold⟩

variable {table : ProtocolTable model protocols}

/-- A choice coheres, for a side that supports the requirement of its tags: the tags that the
side holds are equal, so the agreement does not stop; without a participant in the side the
outputs are absent; otherwise the arm that the tag selects runs, from a state that holds of
its inputs, and the state after the choice holds of what it returns. -/
theorem Copies.choose_coheres (label : Nat → Site) {side : Side}
    {valuation : Copies.Valuation model} {state : Copies.State} {Γ : List Located}
    {env : Environment (SideValue model side) Γ}
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env)
    (participants : List Nat) (tag : ChoiceTag) (captures outputs : List Located)
    (covered : Located.heldBy participants outputs = true)
    (arguments : Operands Γ (Located.ofRoles tag.type participants ++ captures))
    (regions : Values (RegionFunction (SideValue model side) (Effects model))
      (tag.regions participants captures outputs))
    {arms : List (Option (List Copies.Copy))} {after : Nat}
    (one : Copies.oneClass
      (((Scope.numbers Γ.length arguments).map state.at_).take participants.length) = true)
    (supported : side.supports
      [(participants.zip
        (((Scope.numbers Γ.length arguments).map state.at_).take participants.length)).map
          fun entry => (entry.1, entry.2.support)] = true)
    (grows : state.next + 1 ≤ after)
    (each : ∀ copies ∈ arms.filterMap id,
      copies.length = outputs.length ∧ ∀ copy ∈ copies, copy.class_ < after)
    (armsCohere : Copies.RegionsCohere (deployed := deployed) typeTable rows callees functionTable
      side
      { state with
        next := state.next + 1
        values := Copies.choiceOwn tag state.next
            (((Scope.numbers Γ.length arguments).map state.at_).take participants.length) ++
          ((Scope.numbers Γ.length arguments).map state.at_).drop participants.length }
      (state.next + 1) after arms regions) :
    Coheres (fun results => ∃ later : Copies.Valuation model,
        later.Extends valuation state.next ∧
        Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side later
          (Copies.afterChoice state after (arms.filterMap id) outputs)
          (Environment.bindAll env results))
      (labelledOperation model label functionTable table side
        (ProtocolOp.choose (operations := operations) (functions := functions)
          (protocols := protocols) (deployed := deployed) participants tag captures outputs
          covered)
        (Operands.eval env arguments) regions) := by
  have operandsHold := sound.operands arguments
  have captured := operandsHold.drop (Located.ofRoles tag.type participants)
  rw [List.length_map] at captured
  have madeSound : ∀ (later : Copies.Valuation model), later.Extends valuation state.next →
      ∀ entry ∈ state.made,
        Copies.MadeSound (deployed := deployed) typeTable rows callees functionTable later
          (state.next + 1) entry :=
    fun later extends_ entry member => (sound.made entry member).extend typeTable rows callees
      functionTable extends_ (Nat.le_succ _)
  refine agreed_coincide (motive := Coheres _) (ChoiceTag.same_refl model.Carrier tag)
    participants _ _ (Copies.controls_equal tag.type participants operandsHold one supported)
    (fun none => Coheres.done ?_) fun value same => ?_
  · exact ⟨valuation, Copies.Valuation.Extends.refl _ _,
      Copies.afterChoice_absent sound (Nat.le_of_succ_le grows) _ each _
        fun located member => not_held_of_heldBy covered none member⟩
  · have ran : Coheres (Copies.ArmRan side valuation state.next after arms)
        (chosenRegion model side participants captures outputs tag regions
          (unmapValues (F := SideValue model side) (fun role => (⟨tag.type, role⟩ : Located))
            participants
            ((Operands.eval env arguments).split (Located.ofRoles tag.type participants)).1)
          ((Operands.eval env arguments).split (Located.ofRoles tag.type participants)).2
          value) := by
      -- the arms of a condition and of an arm number start from the captures
      have plain : ∀ (count : Nat)
          (bodies : Values (RegionFunction (SideValue model side) (Effects model))
            (List.replicate count (captures, outputs))) (number : Fin count),
          Copies.RegionsCohere (deployed := deployed) typeTable rows callees functionTable side
            { state with
              next := state.next + 1
              values := [] ++
                ((Scope.numbers Γ.length arguments).map state.at_).drop participants.length }
            (state.next + 1) after arms bodies →
          Coheres (Copies.ArmRan side valuation state.next after arms)
            (selectArm (captures, outputs) count bodies number
              ((Operands.eval env arguments).split (Located.ofRoles tag.type participants)).2) := by
        intro count bodies number cohere
        exact (Copies.selectArm_coheres side _ (state.next + 1) after (captures, outputs) count
          bodies number arms cohere valuation _
          (Copies.State.Sound.enter (madeSound valuation (Copies.Valuation.Extends.refl _ _))
            (captured.extend (Copies.Valuation.Extends.refl _ _) (Nat.le_succ _)))).weaken
            fun _ arm => by
              obtain ⟨later, extends_, copies, inside, hold⟩ := arm
              exact ⟨later, extends_.weaken (Nat.le_succ _), copies, inside, hold⟩
      cases tag with
      | condition => exact plain 2 regions _ armsCohere
      | arm count => exact plain count regions _ armsCohere
      | alternative declaration alternatives =>
          refine Copies.alternativeProcess_coheres side participants captures outputs _ _
            (state.next + 1) after valuation state.next (Nat.le_succ _)
            (fun {payload} payloadValue payloads agree => ?_) alternatives regions value _ arms
            armsCohere same
          have entered := Copies.Valuation.set_extends valuation (Nat.le_refl state.next)
            (some ⟨payload, payloadValue⟩)
          have payloadHold : Copies.Hold side
              (valuation.set state.next (some ⟨payload, payloadValue⟩)) (state.next + 1)
              ((((Scope.numbers Γ.length arguments).map state.at_).take participants.length).map
                fun copy => ⟨state.next, copy.support⟩)
              (remapValues (F := SideValue model side) (fun role => (⟨payload, role⟩ : Located))
                participants payloads) := by
            refine ⟨by
              rw [List.length_map, List.length_take, operandsHold.1, List.length_append,
                List.length_map, List.length_map, Nat.min_eq_left (Nat.le_add_right _ _)],
              fun index located found => ?_⟩
            have found' : (participants.map fun role => (⟨payload, role⟩ : Located))[index]? =
                some located := found
            rw [List.getElem?_map] at found'
            cases roleAt : participants[index]? with
            | none => rw [roleAt] at found'; cases found'
            | some role =>
                rw [roleAt] at found'
                cases Option.some.inj found'
                have inside : index < participants.length :=
                  (List.getElem?_eq_some_iff.mp roleAt).1
                have within : index <
                    ((Scope.numbers Γ.length arguments).map state.at_).length := by
                  rw [operandsHold.1, List.length_append, List.length_map]
                  exact Nat.lt_of_lt_of_le inside (Nat.le_add_right _ _)
                rw [getD_map_of_getElem? _ _ (getElem?_take_getD _ inside within)]
                have tagHolds := operandsHold.2 index
                  ⟨.variant declaration alternatives, role⟩ (by
                    rw [List.getElem?_append_left (by rw [List.length_map]; exact inside),
                      List.getElem?_map, roleAt]
                    rfl)
                refine ⟨tagHolds.1, Nat.lt_succ_self _, fun supportInside => ?_⟩
                have member := Copies.side_of_contains supportInside tagHolds.1
                rw [entryOf_plain_roles side payload participants payloads ⟨index, roleAt⟩ member,
                  agree ⟨index, roleAt⟩ member]
                simp only [Copies.Valuation.set, ↓reduceIte]
          exact ⟨_, entered, Copies.State.Sound.enter (madeSound _ entered)
            (payloadHold.append (captured.extend entered (Nat.le_succ _)))⟩
    exact ran.weaken fun results arm => by
      obtain ⟨later, extends_, copies, inside, hold⟩ := arm
      exact Copies.afterChoice_sound sound (Nat.le_of_succ_le grows) _ each extends_
        (List.mem_filterMap.mpr ⟨some copies, inside, rfl⟩) hold

/-- The first collected entry of the type of a collected entry has its type. -/
theorem Copies.type_of_findIdx (collected : List Located) {index : Nat} {located : Located}
    (found : collected[index]? = some located) :
    ∃ first, collected[collected.findIdx fun other =>
        decide (other.type = (collected.getD index default).type)]? = some first ∧
      first.type = located.type := by
  have same : collected.getD index default = located := by
    rw [List.getD_eq_getElem?_getD, found]
    rfl
  rw [same]
  have exists_ : ∃ other ∈ collected, decide (other.type = located.type) = true :=
    ⟨located, List.mem_of_getElem? found, by simp⟩
  have below := List.findIdx_lt_length_of_exists exists_
  exact ⟨_, List.getElem?_eq_getElem below,
    of_decide_eq_true (List.findIdx_getElem (w := below))⟩

/-- A loop coheres, for a side that supports the requirement of its counts: the counts that the
side holds are equal, so the agreement does not stop; without a participant in the side the
carried values are as they were; otherwise every iteration runs the body from a state that
holds of its inputs and keeps what holds between iterations, and the state after the loop
holds of the carried values and of the sequences collected. -/
theorem Copies.repeat_coheres (label : Nat → Site) {side : Side}
    {valuation : Copies.Valuation model} {state : Copies.State} {Γ : List Located}
    {env : Environment (SideValue model side) Γ}
    (sound : Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
      valuation state env)
    (participants : List Nat) (count : RepeatCount) (carried collected captures : List Located)
    (covered : Located.heldBy participants collected = true)
    (arguments : Operands Γ (count.operands participants ++ (carried ++ captures)))
    (regions : Values (RegionFunction (SideValue model side) (Effects model))
      [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)])
    {gathered : List Copies.Copy} {kept : List (Copies.Copy × Bool)} {after : Nat}
    (one : Copies.oneClass (Copies.loopOperands count participants.length
      ((Scope.numbers Γ.length arguments).map state.at_)).1 = true)
    (supported : side.supports
      [(participants.zip (Copies.loopOperands count participants.length
        ((Scope.numbers Γ.length arguments).map state.at_)).1).map
          fun entry => (entry.1, entry.2.support)] = true)
    (grows : state.next ≤ after) (keptSized : kept.length = carried.length)
    (settledKeys : List (List Nat)) (settledSupports : List (List Nat))
    (bodies : List (Option (List Copies.Copy)))
    (keysSized : settledKeys.length = carried.length)
    (supportsSized : settledSupports.length = carried.length)
    (keysFrom : ∀ (one two : Nat), one < carried.length → two < carried.length →
      settledKeys[one]? = settledKeys[two]? →
      ((((Copies.loopOperands count participants.length
          ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length).map
            fun copy => [copy.class_])[one]? =
        (((Copies.loopOperands count participants.length
          ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length).map
            fun copy => [copy.class_])[two]?))
    (supportsFrom : ∀ (index : Nat) (start settled : List Nat),
      ((((Copies.loopOperands count participants.length
          ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length).zip
            carried).map fun entry => Copies.withRole entry.1.support entry.2.holder)[index]? =
        some start →
      settledSupports[index]? = some settled →
      ∀ role, start.contains role = true → settled.contains role = true)
    (outcome : (bodies.headD none = none ∧ gathered = [] ∧
        kept = ((Copies.blocks { state with next := state.next + 1 } settledKeys).1.zip
          settledSupports).map fun entry => (⟨entry.1, entry.2⟩, false)) ∨
      ∃ returned, bodies.headD none = some returned ∧
        gathered = returned.take collected.length ∧
        kept = (((Copies.blocks { state with next := state.next + 1 } settledKeys).1.zip
          settledSupports).zip (returned.drop collected.length)).map
            (fun entry => (⟨entry.1.1, entry.1.2⟩, Nat.beq entry.2.class_ entry.1.1)) ∧
        (Copies.blocks { state with next := state.next + 1 }
          ((settledKeys.zip (returned.drop collected.length)).map
            fun entry => entry.1 ++ [entry.2.class_])).1 =
          (Copies.blocks { state with next := state.next + 1 } settledKeys).1 ∧
        ((settledSupports.zip ((settledSupports.zip (returned.drop collected.length)).map
          fun entry => Copies.union entry.1 entry.2.support)).all
            fun entry => Copies.sameRoles entry.1 entry.2) = true)
    (returnedSized : ∀ returned, bodies.headD none = some returned →
      returned.length = collected.length + carried.length)
    (bodyCoheres : Copies.RegionsCohere (deployed := deployed) typeTable rows callees functionTable
      side
      { (Copies.blocks { state with next := state.next + 1 } settledKeys).2 with
        values := Copies.loopOwn participants state.next
            (Copies.blocks { state with next := state.next + 1 } settledKeys).1 settledSupports ++
          (Copies.loopOperands count participants.length
            ((Scope.numbers Γ.length arguments).map state.at_)).2.drop carried.length }
      (Copies.blocks { state with next := state.next + 1 } settledKeys).2.next after bodies
      regions) :
    Coheres (fun results => ∃ later : Copies.Valuation model,
        later.Extends valuation state.next ∧
        Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side later
          (Copies.afterLoop state after gathered kept
            ((Copies.loopOperands count participants.length
              ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length)
            collected)
          (Environment.bindAll env results))
      (labelledOperation model label functionTable table side
        (ProtocolOp.repeat (operations := operations) (functions := functions)
          (protocols := protocols) (deployed := deployed) participants count carried collected
          captures covered)
        (Operands.eval env arguments) regions) := by
  have operandsHold := sound.operands arguments
  -- the operands after the counts, and the counts that the side holds
  have restHold : Copies.Hold side valuation state.next
      (Copies.loopOperands count participants.length
        ((Scope.numbers Γ.length arguments).map state.at_)).2
      ((Operands.eval env arguments).split (count.operands participants)).2 := by
    cases count with
    | «static» number => exact operandsHold
    | runtime maximum =>
        have dropped := operandsHold.drop (Located.ofRoles .nat participants)
        rw [List.length_map] at dropped
        exact dropped
  have countsEqual : ∀ {first : Nat} (firstAt : Var participants first)
      (firstMember : side first = true) {second : Nat} (secondAt : Var participants second)
      (secondMember : side second = true),
      Held.value (side first) firstMember
          ((repeatCopies model side participants count
            ((Operands.eval env arguments).split (count.operands participants)).1).get firstAt) =
        Held.value (side second) secondMember
          ((repeatCopies model side participants count
            ((Operands.eval env arguments).split (count.operands participants)).1).get
              secondAt) := by
    cases count with
    | «static» number =>
        intro first firstAt firstMember second secondAt secondMember
        exact (heldCopies_value side .nat number participants firstAt firstMember).trans
          (heldCopies_value side .nat number participants secondAt secondMember).symm
    | runtime maximum => exact Copies.controls_equal .nat participants operandsHold one supported
  have initialHold := restHold.take carried
  have capturedHold := restHold.drop carried
  have initialSized := initialHold.1
  have initialBelow := initialHold.below
  have spec := Copies.blocks_spec { state with next := state.next + 1 } settledKeys
  have classesSized : (Copies.blocks { state with next := state.next + 1 }
      settledKeys).1.length = carried.length := spec.1.trans keysSized
  -- the kept entry at a position
  have keptAt : ∀ (index class_ : Nat) (support : List Nat),
      (Copies.blocks { state with next := state.next + 1 } settledKeys).1[index]? = some class_ →
      settledSupports[index]? = some support →
      ∃ flag, kept[index]? = some (⟨class_, support⟩, flag) := by
    intro index class_ support classAt supportAt
    rcases outcome with ⟨_, _, keptIs⟩ | ⟨returned, found, _, keptIs, _, _⟩
    · refine ⟨false, ?_⟩
      rw [keptIs, List.getElem?_map, List.getElem?_zip_eq_some (z := (class_, support))
        |>.mpr ⟨classAt, supportAt⟩]
      rfl
    · have below : index < carried.length :=
        classesSized ▸ (List.getElem?_eq_some_iff.mp classAt).1
      have afterBelow : index < (returned.drop collected.length).length := by
        rw [List.length_drop, returnedSized returned found, Nat.add_sub_cancel_left]
        exact below
      refine ⟨Nat.beq ((returned.drop collected.length)[index]).class_ class_, ?_⟩
      rw [keptIs, List.getElem?_map, List.getElem?_zip_eq_some
        (z := ((class_, support), (returned.drop collected.length)[index]))
        |>.mpr ⟨List.getElem?_zip_eq_some.mpr ⟨classAt, supportAt⟩,
          List.getElem?_eq_getElem afterBelow⟩]
      rfl
  have entryAt : ∀ (index : Nat) (entry : Copies.Copy × Bool), kept[index]? = some entry →
      ∃ (class_ : Nat) (support : List Nat) (flag : Bool) (before : Copies.Copy)
        (located : Located),
        (Copies.blocks { state with next := state.next + 1 } settledKeys).1[index]? =
          some class_ ∧
        settledSupports[index]? = some support ∧ entry = (⟨class_, support⟩, flag) ∧
        ((Copies.loopOperands count participants.length
          ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length)[index]? =
            some before ∧
        carried[index]? = some located := by
    intro index entry found
    have below : index < carried.length := keptSized ▸ (List.getElem?_eq_some_iff.mp found).1
    have classBelow : index < (Copies.blocks { state with next := state.next + 1 }
        settledKeys).1.length := by
      rw [classesSized]
      exact below
    have supportBelow : index < settledSupports.length := by
      rw [supportsSized]
      exact below
    have beforeBelow : index < ((Copies.loopOperands count participants.length
        ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length).length := by
      rw [initialSized]
      exact below
    obtain ⟨flag, keptIs⟩ := keptAt index _ _ (List.getElem?_eq_getElem classBelow)
      (List.getElem?_eq_getElem supportBelow)
    exact ⟨(Copies.blocks { state with next := state.next + 1 } settledKeys).1[index],
      settledSupports[index], flag,
      ((Copies.loopOperands count participants.length
        ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length)[index],
      carried[index], List.getElem?_eq_getElem classBelow,
      List.getElem?_eq_getElem supportBelow, Option.some.inj (found.symm.trans keptIs),
      List.getElem?_eq_getElem beforeBelow, List.getElem?_eq_getElem below⟩
  -- the support with which a carried value starts is inside the one it enters with
  have fromFirst : ∀ (index : Nat) (before : Copies.Copy) (located : Located)
      (support : List Nat),
      ((Copies.loopOperands count participants.length
        ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length)[index]? =
          some before →
      carried[index]? = some located → settledSupports[index]? = some support →
      ∀ role, (Copies.withRole before.support located.holder).contains role = true →
        support.contains role = true := by
    intro index before located support beforeAt locatedAt supportAt
    refine supportsFrom index _ support ?_ supportAt
    rw [List.getElem?_map, List.getElem?_zip_eq_some (z := (before, located))
      |>.mpr ⟨beforeAt, locatedAt⟩]
    rfl
  have holders : ∀ (index : Nat) (located : Located) (support : List Nat),
      carried[index]? = some located → settledSupports[index]? = some support →
        support.contains located.holder = true := by
    intro index located support locatedAt supportAt
    have below : index < carried.length := (List.getElem?_eq_some_iff.mp locatedAt).1
    have beforeBelow : index < ((Copies.loopOperands count participants.length
        ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length).length := by
      rw [initialSized]
      exact below
    exact fromFirst index _ located support (List.getElem?_eq_getElem beforeBelow)
      locatedAt supportAt _ (Copies.contains_withRole_self _ _)
  -- the value before the loop of a carried value whose entering support is inside the side
  have initialValue : ∀ (index : Nat) (before : Copies.Copy) (located : Located)
      (support : List Nat),
      ((Copies.loopOperands count participants.length
        ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length)[index]? =
          some before →
      carried[index]? = some located → settledSupports[index]? = some support →
      support.all side = true →
        valuation.value before.class_ =
          entryOf (plainValues side
            ((((Operands.eval env arguments).split (count.operands participants)).2.split
              carried).1)) index := by
    intro index before located support beforeAt locatedAt supportAt inside
    have known := (initialHold.2 index located locatedAt).2.2
    rw [List.getD_eq_getElem?_getD, beforeAt] at known
    exact known (Copies.all_of_withRole (Copies.all_of_contains
      (fromFirst index before located support beforeAt locatedAt supportAt) inside)).1
  -- two carried values of one entering class had one class before the loop
  have initialClass : ∀ (one two : Nat) (oneClass twoClass : Nat)
      (first second : Copies.Copy),
      (Copies.blocks { state with next := state.next + 1 } settledKeys).1[one]? = some oneClass →
      (Copies.blocks { state with next := state.next + 1 } settledKeys).1[two]? = some twoClass →
      oneClass = twoClass →
      ((Copies.loopOperands count participants.length
        ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length)[one]? =
          some first →
      ((Copies.loopOperands count participants.length
        ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length)[two]? =
          some second →
      first.class_ = second.class_ := by
    intro one two oneClass twoClass first second oneAt twoAt same firstAt secondAt
    have oneBelow : one < carried.length :=
      classesSized ▸ (List.getElem?_eq_some_iff.mp oneAt).1
    have twoBelow : two < carried.length :=
      classesSized ▸ (List.getElem?_eq_some_iff.mp twoAt).1
    have keys := (spec.2.2.2 one two _ _ oneClass twoClass
      (List.getElem?_eq_getElem (keysSized ▸ oneBelow))
      (List.getElem?_eq_getElem (keysSized ▸ twoBelow)) oneAt twoAt).mp same
    have started := keysFrom one two oneBelow twoBelow (by
      rw [List.getElem?_eq_getElem (keysSized ▸ oneBelow),
        List.getElem?_eq_getElem (keysSized ▸ twoBelow), keys])
    rw [List.getElem?_map, List.getElem?_map, firstAt, secondAt] at started
    exact List.head_eq_of_cons_eq (Option.some.inj started)
  -- what holds before the first iteration
  have init : Copies.LoopHolds side kept gathered collected carried
      ((((Operands.eval env arguments).split (count.operands participants)).2.split carried).1)
      ((((Operands.eval env arguments).split (count.operands participants)).2.split carried).1)
      (sideCollectedNone model side collected) := by
    refine ⟨fun one two first second firstAt secondAt same firstInside secondInside => ?_,
      fun _ _ _ _ _ => rfl,
      fun one two type holder owner oneAt twoAt oneMember twoMember _ _ _ =>
        collectedNone_alike collected oneAt twoAt oneMember twoMember⟩
    obtain ⟨oneClass, oneSupport, _, oneBefore, oneLocated, oneClassAt, oneSupportAt, rfl,
      oneBeforeAt, oneLocatedAt⟩ := entryAt one first firstAt
    obtain ⟨twoClass, twoSupport, _, twoBefore, twoLocated, twoClassAt, twoSupportAt, rfl,
      twoBeforeAt, twoLocatedAt⟩ := entryAt two second secondAt
    rw [← initialValue one oneBefore oneLocated oneSupport oneBeforeAt oneLocatedAt oneSupportAt
        firstInside,
      ← initialValue two twoBefore twoLocated twoSupport twoBeforeAt twoLocatedAt twoSupportAt
        secondInside,
      initialClass one two oneClass twoClass oneBefore twoBefore oneClassAt twoClassAt same
        oneBeforeAt twoBeforeAt]
  -- the state after the loop, from what holds after the last iteration
  have finish : ∀ {done : Nat} (current : Values (SideValue model side) carried)
      (sequences : Values (SideValue model side) (collectedSequencesAt (some done) collected))
      (results : Values (SideValue model side)
        (collectedSequencesAt count.size collected ++ carried)),
      Copies.LoopHolds side kept gathered collected carried
        ((((Operands.eval env arguments).split (count.operands participants)).2.split carried).1)
        current sequences →
      (∀ index, entryOf (plainValues side results) (collected.length + index) =
        entryOf (plainValues side current) index) →
      (∀ (one two : Nat) (first second : Located), collected[one]? = some first →
        collected[two]? = some second →
        Copies.collectionKey gathered collected one =
          Copies.collectionKey gathered collected two →
        side first.holder = true → side second.holder = true →
        (gathered.getD one default).support.all side = true →
        (gathered.getD two default).support.all side = true →
          entryOf (plainValues side results) one = entryOf (plainValues side results) two) →
      ∃ later : Copies.Valuation model, later.Extends valuation state.next ∧
        Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side later
          (Copies.afterLoop state after gathered kept
            ((Copies.loopOperands count participants.length
              ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length)
            collected)
          (Environment.bindAll env results) := by
    intro done current sequences results holds carriedEntries collectedAlike
    refine Copies.afterLoop_sound sound grows gathered kept _ collected carried count.size
      (keptSized.trans initialSized.symm) initialSized initialBelow results
      (fun index located entry locatedAt found => ?_)
      (fun index entry before found beforeAt flag inside => ?_)
      (fun one two first second firstAt secondAt same firstInside secondInside => ?_)
      collectedAlike
    · obtain ⟨_, support, _, _, _, _, supportAt, rfl, _, _⟩ := entryAt index entry found
      exact holders index located support locatedAt supportAt
    · obtain ⟨_, support, _, other, located, _, supportAt, rfl, otherAt, locatedAt⟩ :=
        entryAt index entry found
      cases Option.some.inj (beforeAt.symm.trans otherAt)
      rw [carriedEntries index, holds.unchanged index _ found flag inside]
      exact initialValue index before located support beforeAt locatedAt supportAt inside
    · rw [carriedEntries one, carriedEntries two]
      exact holds.alike one two first second firstAt secondAt same firstInside secondInside
  -- two collections with one key: one position, or one type and one gathered class
  have keysAlike : ∀ (one two : Nat) (first second : Located), collected[one]? = some first →
      collected[two]? = some second →
      Copies.collectionKey gathered collected one = Copies.collectionKey gathered collected two →
      one = two ∨ (first.type = second.type ∧
        (gathered.getD one default).class_ = (gathered.getD two default).class_) := by
    intro one two first second firstAt secondAt keys
    unfold Copies.collectionKey at keys
    have classes := List.head_eq_of_cons_eq keys
    have later := List.tail_eq_of_cons_eq keys
    have empties := List.head_eq_of_cons_eq later
    have indexes := List.head_eq_of_cons_eq (List.tail_eq_of_cons_eq later)
    cases empty : gathered.isEmpty with
    | true =>
        rw [empty] at empties
        exact Or.inl (Nat.succ.inj empties)
    | false =>
        right
        obtain ⟨oneFirst, oneAt, oneType⟩ := Copies.type_of_findIdx collected firstAt
        obtain ⟨twoFirst, twoAt, twoType⟩ := Copies.type_of_findIdx collected secondAt
        rw [indexes] at oneAt
        cases Option.some.inj (oneAt.symm.trans twoAt)
        refine ⟨oneType.symm.trans twoType, ?_⟩
        -- the body collects: the gathered copies are as many as the collected entries
        have sized : gathered.length = collected.length := by
          rcases outcome with ⟨_, none, _⟩ | ⟨returned, found, gatheredIs, _, _, _⟩
          · rw [none] at empty
            cases empty
          · rw [gatheredIs, List.length_take, returnedSized returned found,
              Nat.min_eq_left (Nat.le_add_right _ _)]
        have oneBelow : one < gathered.length :=
          sized ▸ (List.getElem?_eq_some_iff.mp firstAt).1
        have twoBelow : two < gathered.length :=
          sized ▸ (List.getElem?_eq_some_iff.mp secondAt).1
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem oneBelow,
          List.getElem?_eq_getElem twoBelow, Option.getD_some] at classes ⊢
        exact classes
  -- one iteration
  have steps : ∀ (done : Nat) (current : Values (SideValue model side) carried)
      (sequences : Values (SideValue model side) (collectedSequencesAt (some done) collected)),
      Copies.LoopHolds side kept gathered collected carried
        ((((Operands.eval env arguments).split (count.operands participants)).2.split carried).1)
        current sequences →
      Coheres (fun produced => Copies.LoopHolds side kept gathered collected carried
          ((((Operands.eval env arguments).split (count.operands participants)).2.split
            carried).1)
          (produced.split collected).2
          (sideCollectedPush model side collected (produced.split collected).1 sequences))
        ((regions.get .here) ((heldCopies model side .nat done participants).append
          (current.append
            ((((Operands.eval env arguments).split (count.operands participants)).2.split
              carried).2)))) := by
    intro done current sequences holds
    obtain ⟨entering, _, enteringSound, enteringValues⟩ := Copies.loop_enter sound.made
      participants carried captures
      (Copies.blocks { state with next := state.next + 1 } settledKeys).1 settledSupports
      (Copies.blocks { state with next := state.next + 1 } settledKeys).2.next classesSized
      supportsSized spec.2.1 (fun index class_ classAt => spec.2.2.1 index class_ classAt) holders
      capturedHold done current
      (fun one two oneClass twoClass oneSupport twoSupport oneAt twoAt oneSupportAt twoSupportAt
          same oneInside twoInside => by
        obtain ⟨_, oneKept⟩ := keptAt one oneClass oneSupport oneAt oneSupportAt
        obtain ⟨_, twoKept⟩ := keptAt two twoClass twoSupport twoAt twoSupportAt
        exact holds.alike one two _ _ oneKept twoKept same oneInside twoInside)
    cases regions with
    | cons body rest =>
        obtain ⟨arm, others, bodiesAre, here, _⟩ := bodyCoheres
        refine (here entering _ enteringSound).weaken fun produced ran => ?_
        obtain ⟨later, laterExtends, copies, armIs, hold⟩ := ran
        rw [bodiesAre] at outcome returnedSized
        rcases outcome with ⟨stopped, _, _⟩ | ⟨returned, found, gatheredIs, keptIs, refined, widened⟩
        · exact nomatch armIs.symm.trans stopped
        · cases Option.some.inj (armIs.symm.trans found)
          have afterSized : (copies.drop collected.length).length = carried.length := by
            rw [List.length_drop, returnedSized copies found, Nat.add_sub_cancel_left]
          refine Copies.loop_leave _ settledSupports classesSized supportsSized keptSized _
            (fun index class_ classAt => (spec.2.2.1 index class_ classAt).2) keptAt copies
            gatheredIs
            (fun one two oneClass twoClass first second oneAt twoAt same firstAt secondAt => ?_)
            (fun index support after_ supportAt afterAt role inside => ?_)
            (fun index class_ support after_ found_ afterAt => ?_) enteringValues laterExtends
            hold holds
          · -- the refined keys give the entering classes: one class, one refined key
            have oneBelow : one < carried.length :=
              classesSized ▸ (List.getElem?_eq_some_iff.mp oneAt).1
            have twoBelow : two < carried.length :=
              classesSized ▸ (List.getElem?_eq_some_iff.mp twoAt).1
            have refinedAt : ∀ (index : Nat) (below : index < carried.length)
                (returnedAt : Copies.Copy),
                (copies.drop collected.length)[index]? = some returnedAt →
                ((settledKeys.zip (copies.drop collected.length)).map
                  fun entry => entry.1 ++ [entry.2.class_])[index]? =
                  some (settledKeys[index]'(keysSized ▸ below) ++ [returnedAt.class_]) := by
              intro index below returnedAt at_
              rw [List.getElem?_map, List.getElem?_zip_eq_some
                (z := (settledKeys[index]'(keysSized ▸ below), returnedAt))
                |>.mpr ⟨List.getElem?_eq_getElem _, at_⟩]
              rfl
            have keys := ((Copies.blocks_spec { state with next := state.next + 1 }
              ((settledKeys.zip (copies.drop collected.length)).map
                fun entry => entry.1 ++ [entry.2.class_])).2.2.2 one two _ _ oneClass twoClass
              (refinedAt one oneBelow first firstAt) (refinedAt two twoBelow second secondAt)
              (by rw [refined]; exact oneAt) (by rw [refined]; exact twoAt)).mp same
            exact List.head_eq_of_cons_eq (List.append_inj_right' keys rfl)
          · have listed : (settledSupports.zip ((settledSupports.zip
                (copies.drop collected.length)).map
                  fun entry => Copies.union entry.1 entry.2.support))[index]? =
                some (support, Copies.union support after_.support) := by
              refine List.getElem?_zip_eq_some.mpr ⟨supportAt, ?_⟩
              rw [List.getElem?_map, List.getElem?_zip_eq_some (z := (support, after_))
                |>.mpr ⟨supportAt, afterAt⟩]
              rfl
            exact Copies.contains_of_sameRoles
              (List.all_eq_true.mp widened _ (List.mem_of_getElem? listed)) inside
          · rw [keptIs, List.getElem?_map] at found_
            cases zipped : (((Copies.blocks { state with next := state.next + 1 }
                settledKeys).1.zip settledSupports).zip (copies.drop collected.length))[index]? with
            | none => rw [zipped] at found_; cases found_
            | some entry =>
                rw [zipped] at found_
                have parts := List.getElem?_zip_eq_some.mp zipped
                have same := Option.some.inj found_
                have flag : Nat.beq entry.2.class_ entry.1.1 = true := congrArg Prod.snd same
                have classIs : entry.1.1 = class_ :=
                  congrArg (fun kept : Copies.Copy × Bool => kept.1.class_) same
                cases Option.some.inj (parts.2.symm.trans afterAt)
                rw [← classIs]
                exact Nat.eq_of_beq_eq_true flag
  -- the loop
  show Coheres _ (repeatOperation model side participants count carried collected captures
    covered (regions.get .here)
    (repeatCopies model side participants count
      ((Operands.eval env arguments).split (count.operands participants)).1)
    ((((Operands.eval env arguments).split (count.operands participants)).2.split carried).1)
    ((((Operands.eval env arguments).split (count.operands participants)).2.split carried).2))
  unfold repeatOperation
  refine agreed_coincide (motive := Coheres _) Nat.beq_refl participants _ _ countsEqual
    (fun none => Coheres.done ?_) fun agreed _ => ?_
  · refine finish _ (sideCollectedNone model side collected) _ init (fun index => ?_)
      (fun one two first second firstAt _ _ firstMember _ _ _ => ?_)
    · have entry := entryOf_plain_append side
        (absentSequences model side count.size collected fun _ member =>
          not_held_of_heldBy covered none member)
        ((((Operands.eval env arguments).split (count.operands participants)).2.split carried).1)
        index
      rw [List.length_map] at entry
      exact entry
    · rw [not_held_of_heldBy covered none (List.mem_of_getElem? firstAt)] at firstMember
      cases firstMember
  · -- the sequences that the iterations collected, finished
    have finished : ∀ {done : Nat} (current : Values (SideValue model side) carried)
        (sequences : Values (SideValue model side) (collectedSequencesAt (some done) collected))
        (ended : Values (SideValue model side) (collectedSequencesAt count.size collected)),
        Copies.LoopHolds side kept gathered collected carried
          ((((Operands.eval env arguments).split (count.operands participants)).2.split
            carried).1) current sequences →
        (∀ (one two : Nat) (type : Ty) (holder owner : Nat),
          collected[one]? = some ⟨type, holder⟩ → collected[two]? = some ⟨type, owner⟩ →
          side holder = true → side owner = true →
          entryOf (plainValues side sequences) one = entryOf (plainValues side sequences) two →
            entryOf (plainValues side ended) one = entryOf (plainValues side ended) two) →
        ∃ later : Copies.Valuation model, later.Extends valuation state.next ∧
          Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
            later
            (Copies.afterLoop state after gathered kept
              ((Copies.loopOperands count participants.length
                ((Scope.numbers Γ.length arguments).map state.at_)).2.take carried.length)
              collected)
            (Environment.bindAll env (ended.append current)) := by
      intro done current sequences ended holds endedAlike
      refine finish current sequences _ holds (fun index => ?_)
        (fun one two first second firstAt secondAt keys firstMember secondMember firstInside
          secondInside => ?_)
      · have entry := entryOf_plain_append side ended current index
        rw [List.length_map] at entry
        exact entry
      · rcases keysAlike one two first second firstAt secondAt keys with same | ⟨types, classes⟩
        · rw [same]
        · obtain ⟨type, holder⟩ := first
          obtain ⟨other, owner⟩ := second
          have types_ : type = other := types
          cases types_
          rw [entryOf_plain_append_left side ended current one (by
              rw [List.length_map]
              exact (List.getElem?_eq_some_iff.mp firstAt).1),
            entryOf_plain_append_left side ended current two (by
              rw [List.length_map]
              exact (List.getElem?_eq_some_iff.mp secondAt).1)]
          exact endedAlike one two type holder owner firstAt secondAt firstMember secondMember
            (holds.sequences one two type holder owner firstAt secondAt firstMember secondMember
              classes firstInside secondInside)
    show Coheres _ (repeatProcess model side count carried collected _ agreed _)
    cases count with
    | «static» number =>
        refine (iterations_coheres
          (fun done current sequences => Copies.LoopHolds side kept gathered collected carried
            _ current sequences) steps number 0 _ _ init).bind fun final holds => Coheres.done ?_
        exact finished final.1 final.2 _ holds
          fun one two type holder owner oneAt twoAt oneMember twoMember same =>
            collectedSized_alike (iterationsAfter_eq number 0) collected final.2 oneAt twoAt
              oneMember twoMember same
    | runtime maximum =>
        show Coheres _ (if agreed ≤ maximum then _ else _)
        split
        · refine (iterations_coheres
            (fun done current sequences => Copies.LoopHolds side kept gathered collected carried
              _ current sequences) steps agreed 0 _ _ init).bind fun final holds =>
                Coheres.done ?_
          exact finished final.1 final.2 _ holds
            fun one two type holder owner oneAt twoAt oneMember twoMember same =>
              collectedLists_alike collected final.2 oneAt twoAt oneMember twoMember same
        · exact Coheres.halt fun stopped => nomatch stopped

/-- The inputs of the nested regions of an instruction whose operands have types of the
package have types of the package. -/
theorem ProtocolOp.regions_named {typeTable : TypeTable}
    (op : ProtocolOp operations functions protocols deployed)
    (named : Located.allNamed typeTable op.arguments = true) :
    ∀ signature ∈ op.regions, Located.allNamed typeTable signature.1 = true := by
  intro signature inside
  rw [Located.allNamed_iff] at named ⊢
  cases op with
  | «at» role local_ bodies => exact nomatch inside
  | exchange sender receiver site type => exact nomatch inside
  | draw owner receivers site law populated => exact nomatch inside
  | sample owner site law populated => exact nomatch inside
  | apply callee roleMap site permitted => exact nomatch inside
  | «repeat» participants count carried collected captures covered =>
      cases List.mem_singleton.mp inside
      intro located member
      rcases List.mem_append.mp member with number | rest
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp number
        rfl
      · exact named located (List.mem_append_right _ rest)
  | choose participants tag captures outputs covered =>
      have capturesNamed : ∀ located ∈ captures, Ty.named typeTable located.type = true :=
        fun located member => named located (List.mem_append_right _ member)
      cases tag with
      | condition =>
          cases List.eq_of_mem_replicate inside
          exact capturesNamed
      | arm count =>
          cases List.eq_of_mem_replicate inside
          exact capturesNamed
      | alternative declaration alternatives =>
          obtain ⟨payload, listed, rfl⟩ := List.mem_map.mp inside
          intro located member
          rcases List.mem_append.mp member with own | captured
          · obtain ⟨role, roleIn, rfl⟩ := List.mem_map.mp own
            have tagNamed : Ty.named typeTable (.variant declaration alternatives) = true :=
              named ⟨.variant declaration alternatives, role⟩
                (List.mem_append_left _ (List.mem_map_of_mem roleIn))
            rw [Ty.named, Bool.and_eq_true] at tagNamed
            exact (Ty.allNamed_iff typeTable alternatives).mp tagNamed.2 payload listed
          · exact capturesNamed located captured

variable {summaries : List (List Copies.Requirement)}

mutual
  /-- A region that passes the check, run for a side that supports its requirements from values
  of which the check's state holds, never stops `incomplete`, and what the check returns holds
  of its outputs. -/
  theorem Copies.checkRegion_sound (ending : EndingTable functionTable)
      (earlier : Copies.AgreeingProtocols table summaries) (label : Nat → Site) (side : Side) :
      ∀ {Γ out : List Located}
        (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
        (roles : Nat) (enclosing : Option (List Nat)) (sites result : List Nat),
        LocatedNamed typeTable Γ →
        protocolRegionSites typeTable roles enclosing region sites = .ok result →
        ∀ (bound : Nat) (path : List Nat) (index : Nat) (state : Copies.State)
          (returned : Copies.Returned),
          Copies.checkRegion summaries bound path index state region = .ok returned →
          side.supports returned.requirements = true →
          ∀ (valuation : Copies.Valuation model) (env : Environment (SideValue model side) Γ),
            Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable side
              valuation state env →
            Coheres (Copies.After (deployed := deployed) typeTable rows callees functionTable side
                valuation state returned)
              (region.denote (labelledMeaning model label functionTable table side) env)
    | _, _, .ret values, _, _, _, _, _, _, _, _, _, state, returned, checked, _, valuation, env,
        sound => by
        rw [Copies.checkRegion] at checked
        cases checked
        refine Coheres.done ⟨valuation, Copies.Valuation.Extends.refl _ _, Nat.le_refl _,
          ⟨_, rfl, ?_⟩, sound.made⟩
        rw [sound.depth]
        exact sound.operands values
    | _, _, .stop _, _, _, _, _, _, clean, _, _, _, _, _, _, _, _, _, _ => by
        rw [protocolRegionSites] at clean
        cases clean
    | Γ, _, .letOp op arguments bodies next, roles, enclosing, sites, result, named, clean,
        bound, path, index, state, returned, checked, supported, valuation, env, sound => by
        obtain ⟨opClean, resultsNamed, middle, nested, nextClean⟩ := protocolRegionSites_letOp clean
        have argumentsNamed := Operands.locatedNamed named arguments
        -- what every instruction does after its own rule: the rest of the region, from the
        -- state with its results
        have continue_ : ∀ (entered : Copies.State) (requirements : List Copies.Requirement),
            (match Copies.checkRegion summaries bound path (index + 1) entered next with
              | .error refusal => (Except.error refusal : Except Copies.Refusal Copies.Returned)
              | .ok rest =>
                  Except.ok { rest with requirements := requirements ++ rest.requirements }) =
              Except.ok returned →
            state.next ≤ entered.next →
            ∀ process : PIR.Process (Effects model) (Values (SideValue model side) op.results),
              (side.supports requirements = true →
                Coheres (fun results => ∃ later : Copies.Valuation model,
                    later.Extends valuation state.next ∧
                    Copies.State.Sound (deployed := deployed) typeTable rows callees functionTable
                      side later entered (Environment.bindAll env results)) process) →
              Coheres (Copies.After (deployed := deployed) typeTable rows callees functionTable
                  side valuation state returned)
                (process.bind fun results =>
                  next.denote (labelledMeaning model label functionTable table side)
                    (Environment.bindAll env results)) := by
          intro entered requirements continued grows process stepped
          split at continued
          · cases continued
          · rename_i rest nextChecked
            cases continued
            obtain ⟨ownSupported, restSupported⟩ := Side.supports_append supported
            refine (stepped ownSupported).bind fun results after => ?_
            obtain ⟨later, extends_, entered_⟩ := after
            refine (Copies.checkRegion_sound ending earlier label side next roles enclosing middle
              result (named.bindAll resultsNamed) nextClean bound _ _ entered rest
              nextChecked restSupported later _ entered_).weaken fun outputs final => ?_
            obtain ⟨last, lastExtends, lastGrows, lastSound⟩ := final
            exact ⟨last, extends_.trans lastExtends grows, Nat.le_trans grows lastGrows, lastSound⟩
        -- the nested regions, read before the instruction is taken apart
        have regionsNamed := ProtocolOp.regions_named op argumentsNamed
        have regionsCohere := Copies.checkRegions_sound ending earlier label side bodies roles
          (ProtocolOp.enclosing enclosing op) (ProtocolOp.sites op ++ sites) middle nested
          regionsNamed
        have regionsClasses := Copies.checkRegions_classes summaries bound bodies
        have operandsSpec := Copies.operands_spec state sound.depth sound.below.1 arguments
        rw [sound.depth] at operandsSpec
        cases op with
        | exchange sender receiver site type =>
            rw [Copies.checkRegion] at checked
            cases arguments with
            | cons reference rest =>
            cases rest
            refine continue_ _ _ checked (Nat.le_refl _) _ fun _ => ?_
            refine (exchangeStep_coheres (label site) type (side sender) (side receiver)
              (env reference)).bind fun result same => Coheres.done ⟨valuation,
                Copies.Valuation.Extends.refl _ _, ?_⟩
            have known := sound.reference reference
            refine sound.bind (Copies.Valuation.Extends.refl _ _) rfl (Nat.le_refl _) sound.made
              ⟨rfl, fun position located found => ?_⟩
            cases position with
            | succ position => exact nomatch found
            | zero =>
                cases Option.some.inj found
                rw [sound.depth]
                refine ⟨Copies.contains_withRole_self _ _, known.2.1, fun inside => ?_⟩
                obtain ⟨sentInside, receiverInside⟩ := Copies.all_of_withRole inside
                exact (known.2.2 sentInside).trans (congrArg some
                  (same (Copies.side_of_contains sentInside known.1) receiverInside).symm)
        | sample owner site law populated =>
            rw [Copies.checkRegion] at checked
            simp only [Copies.State.fresh] at checked
            have fresh : (List.map (fun x => state.next + x) (List.range 1)).headD 0 = state.next :=
              rfl
            rw [fresh] at checked
            refine continue_ _ _ checked (Nat.le_succ _) _ fun _ => ?_
            refine (sampleStep_coheres (label site) (.of law populated) (side owner) _).bind
              fun reply _ => Coheres.done ?_
            refine sound.bindFresh
              (Values.cons (ty := (⟨(SamplingRow.of law populated).output, owner⟩ : Located)) reply
                Values.nil)
              [⟨state.next, [owner]⟩]
              (entryOf (plainValues side
                (Values.cons (ty := (⟨(SamplingRow.of law populated).output, owner⟩ : Located)) reply
                  Values.nil)) 0) rfl
              fun position located found => ?_
            cases position with
            | succ position => exact nomatch found
            | zero =>
                cases Option.some.inj found
                exact ⟨rfl, by simp, fun _ => rfl⟩
        | draw owner receivers site law populated =>
            rw [Copies.checkRegion] at checked
            simp only [Copies.State.fresh] at checked
            have fresh : (List.map (fun x => state.next + x) (List.range 1)).headD 0 = state.next :=
              rfl
            rw [fresh] at checked
            refine continue_ _ _ checked (Nat.le_succ _) _ fun _ => ?_
            -- the copy at a position of the results: the owner's, or a receiver's
            have copyAt : ∀ (position : Nat) (located : Located),
                (ProtocolOp.draw owner receivers site law populated :
                  ProtocolOp operations functions protocols deployed).results[position]? =
                    some located →
                (((⟨state.next, [owner]⟩ : Copies.Copy) :: receivers.map fun receiver =>
                    (⟨state.next, Copies.withRole [owner] receiver⟩ : Copies.Copy)).getD position
                      default).class_ = state.next ∧
                  (((⟨state.next, [owner]⟩ : Copies.Copy) :: receivers.map fun receiver =>
                    (⟨state.next, Copies.withRole [owner] receiver⟩ : Copies.Copy)).getD position
                      default).support.contains located.holder = true ∧
                  (((⟨state.next, [owner]⟩ : Copies.Copy) :: receivers.map fun receiver =>
                    (⟨state.next, Copies.withRole [owner] receiver⟩ : Copies.Copy)).getD position
                      default).support.contains owner = true := by
              intro position located found
              cases position with
              | zero =>
                  cases Option.some.inj found
                  exact ⟨rfl, by simp, by simp⟩
              | succ position =>
                  have inner : (receivers.map fun role => (⟨_, role⟩ : Located))[position]? =
                      some located := found
                  rw [List.getElem?_map] at inner
                  cases at_ : receivers[position]? with
                  | none => rw [at_] at inner; cases inner
                  | some receiver =>
                      rw [at_] at inner
                      cases Option.some.inj inner
                      have copy : ((⟨state.next, [owner]⟩ : Copies.Copy) :: receivers.map
                          fun receiver =>
                            (⟨state.next, Copies.withRole [owner] receiver⟩ : Copies.Copy)).getD
                              (position + 1) default =
                          ⟨state.next, Copies.withRole [owner] receiver⟩ :=
                        getD_map_of_getElem? _ receivers at_ _
                      rw [copy]
                      exact ⟨rfl, Copies.contains_withRole_self _ _,
                        Copies.contains_withRole (support := [owner]) (other := owner) receiver
                          (by simp)⟩
            apply drawStep_coheres
            · intro reply
              refine Coheres.done ?_
              refine sound.bindFresh _ _
                (some ⟨_, reply⟩) (by simp [ProtocolOp.results]) fun position located found => ?_
              obtain ⟨class_, held, _⟩ := copyAt position located found
              refine ⟨class_, held, fun inside => ?_⟩
              · have member := Copies.side_of_contains inside held
                cases position with
                | zero =>
                    cases Option.some.inj found
                    exact congrArg some (plain_entry_of (side owner) member reply)
                | succ position =>
                    have inner : (receivers.map fun role => (⟨_, role⟩ : Located))[position]? =
                        some located := found
                    rw [List.getElem?_map] at inner
                    cases at_ : receivers[position]? with
                    | none => rw [at_] at inner; cases inner
                    | some receiver =>
                        rw [at_] at inner
                        cases Option.some.inj inner
                        exact entryOf_heldCopies side _ reply receivers position receiver at_ member
            · intro absent
              refine (receiverReplies_coheres side (label site) _ receivers).bind fun replies _ =>
                Coheres.done ?_
              refine sound.bindFresh _ _
                none (by simp [ProtocolOp.results]) fun position located found => ?_
              obtain ⟨class_, held, owned⟩ := copyAt position located found
              refine ⟨class_, held, fun inside => ?_⟩
              · have member := Copies.side_of_contains inside owned
                rw [absent] at member
                cases member
        | «at» role op localBodies =>
            rw [Copies.checkRegion, sound.depth] at checked
            rw [show Copies.numbered state
                (unelaborateLocalStep functions.length op
                  (((Scope.numbers _ arguments).map state.at_).map (·.class_))
                  (unelaborateLocalRegions functions.length localBodies)) op.results.length =
              ((Copies.numbered state
                (unelaborateLocalStep functions.length op
                  (((Scope.numbers _ arguments).map state.at_).map (·.class_))
                  (unelaborateLocalRegions functions.length localBodies)) op.results.length).1,
               (Copies.numbered state
                (unelaborateLocalStep functions.length op
                  (((Scope.numbers _ arguments).map state.at_).map (·.class_))
                  (unelaborateLocalRegions functions.length localBodies)) op.results.length).2)
              from rfl] at checked
            dsimp only at checked
            refine continue_ _ _ checked (Copies.numbered_next_le _ _ _) _ fun _ => ?_
            have localNamed : (Ty.allNamed typeTable op.arguments &&
                Ty.allNamed typeTable op.results) = true := by
              have one := argumentsNamed
              have two := resultsNamed
              simp only [ProtocolOp.arguments, ProtocolOp.results, Located.allNamed_atRole]
                at one two
              rw [one, two]
              rfl
            have localClean := (earlierViolation_both opClean).2
            have ok := elaborateLocalRegions_unelaborate typeTable rows callees localBodies
              (LocalOp.inputsNamed op (by
                simp only [Bool.and_eq_true] at localNamed
                exact localNamed.1)) localClean
            show Coheres _ (labelledOperation model label functionTable table side
              (.at role op localBodies) (Operands.eval env arguments)
              (bodies.denote (labelledMeaning model label functionTable table side)))
            cases member : side role with
            | false =>
                rw [at_absent member]
                exact Coheres.done (Copies.at_bound sound role op localBodies arguments localNamed
                  ok _ fun present => absurd (member ▸ present) Bool.false_ne_true)
            | true =>
                rw [at_present member, ← eval_presentOperands side member env arguments]
                rcases localOperation_ends ending op
                    (Operands.eval (plainEnvironment side env)
                      (presentOperands side member arguments)) _
                    (localRegions_end (typeTable := typeTable) ending localBodies localClean) with
                  ⟨results, returned⟩ | ⟨why, other, stopped⟩
                · rw [returned]
                  exact Coheres.done (Copies.at_bound sound role op localBodies arguments localNamed
                    ok _ fun present => ⟨results, returned, fun position =>
                      entryOf_plain_held side present results position⟩)
                · rw [stopped]
                  exact Coheres.halt other
        | «repeat» participants count carried collected captures covered =>
            rw [Copies.checkRegion, sound.depth] at checked
            split at checked
            · cases checked
            · rename_i countsDiffer
              split at checked
              · cases checked
              · rename_i gathered kept after inner settled
                have one : Copies.oneClass (Copies.loopOperands count participants.length
                    ((Scope.numbers Γ.length arguments).map state.at_)).1 = true := by
                  cases same : Copies.oneClass (Copies.loopOperands count participants.length
                      ((Scope.numbers Γ.length arguments).map state.at_)).1 with
                  | true => rfl
                  | false => exact absurd (by rw [same]; rfl) countsDiffer
                have rest := Copies.loopOperands_spec count participants carried captures _
                  state.next operandsSpec.1 operandsSpec.2
                have sizes := Copies.loopSplit_spec carried captures _ rest.1
                have capturedBelow : ∀ copy ∈ (Copies.loopOperands count participants.length
                    ((Scope.numbers Γ.length arguments).map state.at_)).2.drop carried.length,
                    copy.class_ < state.next :=
                  fun copy inside => rest.2 copy (List.mem_of_mem_drop inside)
                have checks := Copies.loopBody_checks state sound.below participants carried
                  captures collected _ sizes.2 capturedBelow
                  (fun start => Copies.checkRegions summaries bound (path ++ [index])
                    (fun _ => start) 0 start.next bodies)
                  (fun base result bodyChecked => regionsClasses (path ++ [index]) base 0
                    base.next result bodyChecked)
                have loop := Copies.settle_classes state participants collected.length _ _ _
                  carried.length checks _ _ _ _ settled
                  (by rw [List.length_map, sizes.1])
                  (by rw [List.length_map, List.length_zip, sizes.1, Nat.min_self])
                obtain ⟨settledKeys, settledSupports, found, keysSized, supportsSized,
                  bodyChecked, keysFrom, supportsFrom, outcome⟩ :=
                  Copies.settle_spec state participants collected.length _ _ _ carried.length
                    checks _ _ _ _ settled
                    (by rw [List.length_map, sizes.1])
                    (by rw [List.length_map, List.length_zip, sizes.1, Nat.min_self])
                have looped := Copies.afterLoop_spec state after gathered kept _ collected
                  sound.below loop.1 (loop.2.trans sizes.1.symm)
                  (fun copy inside => rest.2 copy (List.mem_of_mem_take inside))
                have start := Copies.loopStart_spec state sound.below participants carried
                  captures collected _ sizes.2 capturedBelow settledKeys settledSupports keysSized
                  supportsSized
                refine continue_ _ _ checked (Nat.le_trans loop.1 looped.2.2) _
                  fun ownSupported => ?_
                obtain ⟨countsSupported, bodySupported⟩ := Side.supports_cons ownSupported
                exact Copies.repeat_coheres (table := table) label sound participants count
                  carried collected captures covered arguments _ one countsSupported loop.1
                  loop.2 settledKeys settledSupports found keysSized supportsSized keysFrom
                  supportsFrom outcome
                  (fun returned headed =>
                    (checks settledKeys settledSupports _ keysSized supportsSized
                      bodyChecked).2 returned headed)
                  (regionsCohere bound (path ++ [index]) _ 0 _ _ bodyChecked bodySupported
                    start.1 start.2.1 start.2.2.1 _ (Nat.le_refl _))
        | choose participants tag captures outputs covered =>
            rw [Copies.checkRegion, sound.depth] at checked
            split at checked
            · cases checked
            · rename_i tagsDiffer
              split at checked
              · cases checked
              · rename_i arms after inner armsChecked
                have one : Copies.oneClass
                    (((Scope.numbers Γ.length arguments).map state.at_).take participants.length) =
                      true := by
                  cases same : Copies.oneClass
                      (((Scope.numbers Γ.length arguments).map state.at_).take
                        participants.length) with
                  | true => rfl
                  | false => exact absurd (by rw [same]; rfl) tagsDiffer
                have sized : ((Scope.numbers Γ.length arguments).map state.at_).length =
                    participants.length + captures.length := by
                  rw [operandsSpec.1]
                  show (Located.ofRoles tag.type participants ++ captures).length = _
                  rw [List.length_append, List.length_map]
                have start := Copies.choiceStart_spec state sound.below participants tag captures
                  outputs _ sized operandsSpec.2
                have nestedClasses := regionsClasses _ _ 0 (state.next + 1) _ armsChecked start.1
                  start.2.1 start.2.2
                have each := Copies.choiceArms_spec participants tag captures outputs arms after
                  nestedClasses.2.1 nestedClasses.2.2
                have chosen := Copies.afterChoice_spec state after (arms.filterMap id) outputs
                  sound.below (Nat.le_trans (Nat.le_succ _) nestedClasses.1) each
                refine continue_ _ _ checked
                  (Nat.le_trans (Nat.le_trans (Nat.le_succ _) nestedClasses.1) chosen.2.2) _
                  fun ownSupported => ?_
                obtain ⟨tagsSupported, armsSupported⟩ := Side.supports_cons ownSupported
                exact Copies.choose_coheres (table := table) label sound participants tag captures outputs covered
                  arguments _ one tagsSupported nestedClasses.1 each
                  (regionsCohere bound _ _ 0 (state.next + 1) _ armsChecked armsSupported start.1
                    start.2.1 start.2.2 (state.next + 1) (Nat.le_refl _))
        | @apply header callee roleMap site permitted =>
            rw [Copies.checkRegion, sound.depth] at checked
            split at checked
            · cases checked
            · rename_i allOne
              rw [show Copies.portClasses state header.agreements.outputs =
                ((Copies.portClasses state header.agreements.outputs).1,
                  (Copies.portClasses state header.agreements.outputs).2) from rfl] at checked
              dsimp only at checked
              obtain ⟨_, grows, kept, madeKept, _, _⟩ :=
                Copies.portClasses_spec state header.agreements.outputs
              refine continue_ _ _ checked grows _ fun ownSupported => ?_
              obtain ⟨inputsSupported, calleeSupported⟩ := Side.supports_append ownSupported
              have operandsHold := sound.operands arguments
              -- the input agreements of the callee hold of the operands
              have inputsHold : header.agreements.InputsHold model (Side.preimage roleMap side)
                  (unmapValues (F := SideValue model side) (Located.rename roleMap) _
                    (Operands.eval env arguments)) := by
                intro agreement inside
                refine Agreement.holds_of_entries fun first firstIn second secondIn firstMember
                  secondMember => ?_
                rw [entryOf_plain_unmapRoles, entryOf_plain_unmapRoles]
                refine Copies.agreed_entries (valuation := valuation) roleMap.apply
                  ((Scope.numbers Γ.length arguments).map state.at_) agreement
                  (entryOf (plainValues side (Operands.eval env arguments)))
                  (fun copy copyIn _ supportInside => ?_) ?_ ?_ first firstIn second secondIn
                  firstMember secondMember
                · exact (operandsHold.2 copy.port.index ⟨agreement.type, roleMap.apply copy.holder⟩
                    (by
                      show (header.inputs.map (Located.rename roleMap))[copy.port.index]? = _
                      rw [List.getElem?_map, copy.port.valid]
                      rfl)).2.2 supportInside
                · have none := List.find?_eq_none.mp allOne _ (List.mem_map_of_mem inside)
                  simpa using none
                · exact Side.supports_mem inputsSupported
                    (List.mem_map_of_mem (List.mem_map_of_mem inside))
              rw [Side.supports_mapped] at calleeSupported
              show Coheres _
                (((table.get callee) (label site).below (Side.preimage roleMap side)
                  (unmapValues (F := SideValue model side) (Located.rename roleMap) _
                    (Operands.eval env arguments))).bind fun values =>
                  .done (remapValues (F := SideValue model side) (Located.rename roleMap) _ values))
              refine (earlier callee (label site).below (Side.preimage roleMap side) _ inputsHold
                calleeSupported).bind fun values outputsHold => Coheres.done ?_
              -- the results are classed by the output agreements, which hold of them
              obtain ⟨later, extends_, hold⟩ := Copies.Hold.ports valuation state
                header.agreements.outputs roleMap.apply
                (remapValues (F := SideValue model side) (Located.rename roleMap) _ values) rfl
                (fun agreement inside first firstIn second secondIn firstMember secondMember => by
                  rw [entryOf_plain_remapRoles, entryOf_plain_remapRoles]
                  exact (outputsHold agreement inside).entries firstIn secondIn firstMember
                    secondMember)
              exact ⟨later, extends_, sound.bind extends_ kept grows
                (fun entry member => (sound.made entry (madeKept ▸ member)).extend typeTable rows
                  callees functionTable extends_ grows) hold⟩
    | Γ, _, .bind (mid := mid) body next, roles, enclosing, sites, result, named, clean,
        bound, path, index, state, returned, checked, supported, valuation, env, sound => by
        obtain ⟨midNamed, middle, bodyClean, nextClean⟩ := protocolRegionSites_bind clean
        rw [Copies.checkRegion] at checked
        split at checked
        · cases checked
        · rename_i inner bodyChecked
          cases copiesOf : inner.copies with
          | none =>
              -- the block does not stop: what it returns has copies
              have innerSupported : side.supports inner.requirements = true := by
                simp only [copiesOf, Copies.State.fresh] at checked
                split at checked
                · cases checked
                · cases checked
                  exact (Side.supports_append supported).1
              refine (Copies.checkRegion_sound ending earlier label side body roles enclosing sites
                middle named bodyClean bound _ _ state inner bodyChecked innerSupported
                valuation env sound).bind fun values after => ?_
              obtain ⟨_, _, _, ⟨copies, returnedCopies, _⟩, _⟩ := after
              rw [copiesOf] at returnedCopies
              cases returnedCopies
          | some copies =>
              simp only [copiesOf, Copies.State.fresh] at checked
              split at checked
              · cases checked
              · rename_i rest nextChecked
                cases checked
                obtain ⟨innerSupported, restSupported⟩ := Side.supports_append supported
                refine (Copies.checkRegion_sound ending earlier label side body roles enclosing
                  sites middle named bodyClean bound _ _ state inner bodyChecked
                  innerSupported valuation env sound).bind fun values after => ?_
                obtain ⟨later, extends_, grows, ⟨found, returnedCopies, hold⟩, made⟩ := after
                rw [copiesOf] at returnedCopies
                cases returnedCopies
                refine (Copies.checkRegion_sound ending earlier label side next roles enclosing
                  middle result (named.bindAll midNamed) nextClean bound _ _ _ rest
                  nextChecked restSupported later _
                  (sound.bind extends_
                    (after := { state with next := inner.next + mid.length, made := inner.made })
                    rfl (Nat.le_trans grows (Nat.le_add_right _ _))
                    (fun entry member => (made entry member).extend typeTable rows callees
                      functionTable (Copies.Valuation.Extends.refl _ _) (Nat.le_add_right _ _))
                    (hold.extend (Copies.Valuation.Extends.refl _ _)
                      (Nat.le_add_right _ _)))).weaken fun outputs final => ?_
                obtain ⟨last, lastExtends, lastGrows, lastSound⟩ := final
                exact ⟨last,
                  extends_.trans lastExtends (Nat.le_trans grows (Nat.le_add_right _ _)),
                  Nat.le_trans (Nat.le_trans grows (Nat.le_add_right _ _)) lastGrows, lastSound⟩

  /-- The nested regions of an instruction that pass the check, for a side that supports their
  requirements: each coheres from the state at its start. -/
  theorem Copies.checkRegions_sound (ending : EndingTable functionTable)
      (earlier : Copies.AgreeingProtocols table summaries) (label : Nat → Site) (side : Side) :
      ∀ {signatures : List (List Located × List Located)}
        (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures)
        (roles : Nat) (enclosing : Option (List Nat)) (sites result : List Nat),
        protocolRegionsSites typeTable roles enclosing regions sites = .ok result →
        (∀ signature ∈ signatures, Located.allNamed typeTable signature.1 = true) →
        ∀ (bound : Nat) (path : List Nat) (base : Copies.State) (number next : Nat)
          (found : List (Option (List Copies.Copy)) × Nat × List Copies.Requirement),
          Copies.checkRegions summaries bound path (fun _ => base) number next regions =
            .ok found →
          side.supports found.2.2 = true →
          (∀ signature ∈ signatures, base.values.length = signature.1.length) →
          (∀ copy ∈ base.values, copy.class_ < next) →
          (∀ entry ∈ base.made, ∀ class_ ∈ entry.2, class_ < next) →
          ∀ start, start ≤ next →
            Copies.RegionsCohere (deployed := deployed) typeTable rows callees functionTable side
              base start found.2.1 found.1
              (regions.denote (labelledMeaning model label functionTable table side))
    | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, checked, _, _, _, _, _, _ => by
        rw [Copies.checkRegions] at checked
        cases checked
        exact rfl
    | _, .cons (inputs := inputs) (outputs := outputs) (rest := later) body tail, roles, enclosing,
        sites, result,
        clean, named, bound, path, base, number, next, found, checked, supported, sized,
        valuesBelow, madeBelow, start, least => by
        rw [protocolRegionsSites] at clean
        split at clean
        · cases clean
        · rename_i middle bodyClean
          rw [Copies.checkRegions] at checked
          split at checked
          · cases checked
          · rename_i returned bodyChecked
            split at checked
            · cases checked
            · rename_i others after requirements tailChecked
              cases checked
              obtain ⟨bodySupported, restSupported⟩ := Side.supports_append supported
              have bodyClasses := Copies.checkRegion_classes summaries bound body _ 0
                { base with next := next } returned bodyChecked
                (by
                  rw [length_bindAll, List.length_nil, Nat.zero_add]
                  exact sized (inputs, outputs) (List.mem_cons_self ..))
                ⟨valuesBelow, madeBelow⟩
              have tailSized : ∀ signature ∈ later, base.values.length = signature.1.length :=
                fun signature inside => sized signature (List.mem_cons_of_mem _ inside)
              have tailValues : ∀ copy ∈ base.values, copy.class_ < returned.next :=
                fun copy inside => Nat.lt_of_lt_of_le (valuesBelow copy inside) bodyClasses.1
              have tailMade : ∀ entry ∈ base.made, ∀ class_ ∈ entry.2, class_ < returned.next :=
                fun entry inside class_ member =>
                  Nat.lt_of_lt_of_le (madeBelow entry inside class_ member) bodyClasses.1
              have tailClasses := Copies.checkRegions_classes summaries bound tail path base
                (number + 1) returned.next _ tailChecked tailSized tailValues tailMade
              refine ⟨returned.copies, others, rfl, fun valuation inputs_ entered => ?_, ?_⟩
              · refine (Copies.checkRegion_sound ending earlier label side body roles enclosing
                  sites middle
                  (LocatedNamed.inputs ((Located.allNamed_iff typeTable inputs).mp
                    (named (inputs, outputs) (List.mem_cons_self ..))))
                  bodyClean bound _ 0 _ returned bodyChecked bodySupported valuation _
                  (entered.grow (next := next) least)).weaken fun results after_ => ?_
                obtain ⟨later, extends_, _, ⟨copies, returnedCopies, hold⟩, _⟩ := after_
                exact ⟨later, extends_.weaken least, copies, returnedCopies,
                  hold.extend (Copies.Valuation.Extends.refl _ _) tailClasses.1⟩
              · exact Copies.checkRegions_sound ending earlier label side tail roles enclosing
                  middle result clean
                  (fun signature inside => named signature (List.mem_cons_of_mem _ inside)) bound
                  path base (number + 1) returned.next _ tailChecked restSupported tailSized
                  tailValues tailMade start (Nat.le_trans least bodyClasses.1)
end

end Region

/-! ## Protocols and programs -/

section Programs

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- A protocol that passes the check of copies, over protocols that keep their agreements:
for a side that supports its requirements, on arguments of which its input agreements hold,
it never stops `incomplete`, and its output agreements hold of what it returns. -/
theorem ProtocolDefinition.copies_sound {typeTable : TypeTable}
    {functionTable : FunctionTable model functions} (ending : EndingTable functionTable)
    {table : ProtocolTable model protocols} {summaries : List (List Copies.Requirement)}
    (earlier : Copies.AgreeingProtocols table summaries) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (wellFormed : definition.violation typeTable = none)
    {requirements : List Copies.Requirement}
    (checked : definition.copies summaries = .ok requirements)
    (identity : Nat) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) header.inputs)
    (inputsHold : header.agreements.InputsHold model side arguments)
    (supported : side.supports requirements = true) :
    Coheres (fun outputs => ∀ agreement ∈ header.agreements.outputs,
        agreement.Holds model side outputs)
      (definition.meaning model functionTable table identity path side arguments) := by
  obtain ⟨inputsNamed, _, sites, clean⟩ := ProtocolDefinition.violation_none wellFormed
  have named : LocatedNamed typeTable (Zkc.Source.bindAll [] header.inputs) :=
    LocatedNamed.inputs ((Located.allNamed_iff typeTable header.inputs).mp inputsNamed)
  -- the state at the start: the inputs classed by the input agreements, which hold
  obtain ⟨_, _, kept, madeKept, _, _⟩ :=
    Copies.portClasses_spec ⟨[], 0, []⟩ header.agreements.inputs
  obtain ⟨start, _, hold⟩ := Copies.Hold.ports (side := side) ⟨fun _ => none⟩
    ⟨[], 0, []⟩ header.agreements.inputs id arguments
    ((List.map_id _).symm.trans (List.map_congr_left fun _ _ => rfl))
    (fun agreement inside first firstIn second secondIn firstMember secondMember =>
      (inputsHold agreement inside).entries firstIn secondIn firstMember secondMember)
  have empty : Copies.State.Sound (deployed := !header.specificationOnly) typeTable
      (tableScope operations) (tableScope functions) functionTable side start ⟨[], 0, []⟩
      (Environment.empty (Value := SideValue model side)) :=
    ⟨rfl, fun reference => reference.elimNil, fun _ member => nomatch member⟩
  have entered := empty.bind (Copies.Valuation.Extends.refl start 0) kept (Nat.zero_le _)
    (fun entry member => nomatch (madeKept ▸ member)) hold
  unfold ProtocolDefinition.copies at checked
  rw [show Copies.portClasses ⟨[], 0, []⟩ header.agreements.inputs =
    ((Copies.portClasses ⟨[], 0, []⟩ header.agreements.inputs).1,
      (Copies.portClasses ⟨[], 0, []⟩ header.agreements.inputs).2) from rfl] at checked
  dsimp only at checked
  split at checked
  · cases checked
  · rename_i returned bodyChecked
    have bodySupported : side.supports returned.requirements = true := by
      split at checked
      · cases checked
        exact supported
      · split at checked
        · cases checked
        · cases checked
          exact (Side.supports_append supported).1
    refine (Copies.checkRegion_sound ending earlier (ownSites identity path) side definition.body
      header.roles none [] sites named clean header.roles [] 0 _ returned bodyChecked
      bodySupported start _ entered).weaken fun outputs after agreement inside => ?_
    obtain ⟨last, _, _, ⟨copies, returnedCopies, held⟩, _⟩ := after
    rw [returnedCopies] at checked
    dsimp only at checked
    split at checked
    · cases checked
    · rename_i allOne
      cases checked
      refine Agreement.holds_of_entries (Copies.agreed_entries (valuation := last) id copies
        agreement (entryOf (plainValues side outputs))
        (fun copy _ _ supportInside =>
          (held.2 copy.port.index ⟨agreement.type, copy.holder⟩ copy.port.valid).2.2
            supportInside) ?_ ?_)
      · have none := List.find?_eq_none.mp allOne _ (List.mem_map_of_mem inside)
        simpa using none
      · exact Side.supports_mem (Side.supports_append supported).2
          (List.mem_map_of_mem (List.mem_map_of_mem inside))

/-- The protocols of a program that all pass the check of copies keep their agreements. -/
theorem Protocols.table_agrees {typeTable : TypeTable}
    {functionTable : FunctionTable model functions} (ending : EndingTable functionTable)
    (identities : Identities) :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols),
      program.coherent = true →
        Copies.AgreeingProtocols (program.table model functionTable identities) program.copies.1
  | _, .nil, _ => fun callee => callee.elimNil
  | _, .snoc (protocols := earlierHeaders) earlier definition wellFormed, passes => by
      -- the earlier protocols pass, and this one has requirements
      have split : earlier.coherent = true ∧ ∃ requirements,
          definition.copies earlier.copies.1 = .ok requirements ∧
          (Protocols.snoc earlier definition wellFormed).copies.1 =
            requirements :: earlier.copies.1 := by
        unfold Protocols.coherent at passes ⊢
        rw [Protocols.copies] at passes ⊢
        rw [show earlier.copies = (earlier.copies.1, earlier.copies.2) from rfl] at passes ⊢
        dsimp only at passes ⊢
        cases own : definition.copies earlier.copies.1 with
        | ok requirements =>
            rw [own] at passes
            exact ⟨passes, requirements, rfl, rfl⟩
        | error refusal =>
            rw [own] at passes
            simp at passes
      obtain ⟨earlierPasses, requirements, own, summaries⟩ := split
      have before : Copies.AgreeingProtocols (earlier.table model functionTable identities)
          earlier.copies.1 :=
        Protocols.table_agrees ending identities earlier earlierPasses
      rw [summaries]
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ (path : List Nat) (side : Side)
          (arguments : Values (SideValue model side) header.inputs),
          header.agreements.InputsHold model side arguments →
          side.supports ((requirements :: earlier.copies.1).getD callee.index []) = true →
          Coheres (fun outputs => ∀ agreement ∈ header.agreements.outputs,
              agreement.Holds model side outputs)
            (Values.get ((Protocols.snoc earlier definition wellFormed).table model functionTable
              identities) callee path side arguments))
        (fun path side arguments inputsHold supported =>
          definition.copies_sound ending before wellFormed own _ path side arguments
            inputsHold supported)
        (fun callee path side arguments inputsHold supported =>
          before callee path side arguments inputsHold supported)
        callee

/-! ## Sides that support every requirement -/

/-- The side of every role supports every requirement: it contains every support. -/
theorem Side.supports_everyone (requirements : List Copies.Requirement) :
    Side.supports (fun _ => true) requirements = true := by
  unfold Side.supports
  rw [List.all_eq_true]
  intro requirement _
  rw [Bool.or_eq_true]
  right
  rw [List.all_eq_true]
  intro copy _
  rw [List.all_eq_true]
  exact fun _ _ => rfl

/-- The side of one role supports requirements each of which names the role at most once: it
never has two copies of one requirement. -/
theorem Side.supports_single (role : Nat) (requirements : List Copies.Requirement)
    (once : ∀ requirement ∈ requirements,
      (requirement.filter fun copy => Nat.beq copy.1 role).length ≤ 1) :
    Side.supports (fun other => Nat.beq other role) requirements = true := by
  unfold Side.supports
  rw [List.all_eq_true]
  intro requirement inside
  rw [Bool.or_eq_true]
  exact Or.inl (decide_eq_true (once requirement inside))

end Programs

end Zkc.Core
