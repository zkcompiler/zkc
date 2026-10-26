module

public import Zkc.Construction.Uniform.DomainAdapter
public import Zkc.Executable.Helpers
public import Zkc.Executable.Soundness
public import Zkc.Source.Structured.Linking

@[expose] public section

/-! Soundness of the helper rule.

A walk relates the names of a region's context to an executable environment
(`NamesAgree`): each position's name is bound to the encoding of the structured
value at that position. Every recipe preserves the relation, binding only fresh
names, and keeps the index names it tracks below the index limit
(`ScopeHolds`). When a walked region returns, the executable steps it consumed
reach its remaining steps in an environment extended by fresh names, in which
the returned names denote the region's results; when the region stops, the
steps stop for the same reason (`walkRegion_sound`). An accepted helper is
therefore prepared: on arguments of its declared sorts, its executable body
hands back exactly the helper's results or stops in the helper's stop class
(`checkHelper_sound`, `checkHelpers_sound`).
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source Zkc.Source.Structured

variable {F G : Type}

/-! ## Names and values -/

section Names

/-- The names of a context denote its values in an executable environment. -/
def NamesAgree (names : List String) (env : Env F G) {Γ : List Ty}
    (values : Environment (assignment F G) Γ) : Prop :=
  ∀ (ty : Ty) (variable_ : Var Γ ty), ∃ name, names[variable_.index]? = some name ∧
    List.lookup name env = some (Value.encode ty (values variable_))

/-- Names bound fresh with respect to `used`. -/
def Fresh (used : List String) (bound : Env F G) : Prop := ∀ entry ∈ bound, entry.1 ∉ used

/-- The scope of a walk holds of an environment: the context's names and the
bounded names were bound, and every bounded name that denotes an index denotes
one below the index limit. -/
structure ScopeHolds (scope : Scope) (names : List String) (env : Env F G) : Prop where
  named : ∀ name ∈ names, name ∈ scope.used
  boundedUsed : ∀ name ∈ scope.bounded, name ∈ scope.used
  bounded : ∀ name ∈ scope.bounded, ∀ index, List.lookup name env = some (.index index) → index < indexLimit

theorem lookup_fresh {used : List String} {bound env : Env F G} (fresh : Fresh used bound) {name : String}
    (member : name ∈ used) : List.lookup name (bound ++ env) = List.lookup name env := by
  rw [lookup_append_some]
  have absent : List.lookup name bound = none := by
    induction bound with
    | nil => rfl
    | cons entry rest ih =>
        obtain ⟨key, value⟩ := entry
        have different : (name == key) = false := by
          have := fresh (key, value) List.mem_cons_self
          simp only at this
          simp only [beq_eq_false_iff_ne]
          intro same
          exact this (same ▸ member)
        simp only [List.lookup, different]
        exact ih (fun entry member' => fresh entry (List.mem_cons_of_mem _ member'))
  rw [absent, Option.none_or]

theorem NamesAgree.extend {names : List String} {env : Env F G} {Γ : List Ty}
    {values : Environment (assignment F G) Γ} (agrees : NamesAgree names env values) {used : List String}
    (named : ∀ name ∈ names, name ∈ used) {bound : Env F G} (fresh : Fresh used bound) :
    NamesAgree names (bound ++ env) values := by
  intro ty variable_
  obtain ⟨name, found, looked⟩ := agrees ty variable_
  refine ⟨name, found, ?_⟩
  rw [lookup_fresh fresh (named name (List.mem_of_getElem? found)), looked]

theorem ScopeHolds.extend {scope : Scope} {names : List String} {env : Env F G}
    (holds : ScopeHolds scope names env) {bound : Env F G} (fresh : Fresh scope.used bound) :
    ScopeHolds scope names (bound ++ env) where
  named := holds.named
  boundedUsed := holds.boundedUsed
  bounded := fun name member index looked => by
    rw [lookup_fresh fresh (holds.boundedUsed name member)] at looked
    exact holds.bounded name member index looked

theorem Fresh.append {used : List String} {first second : Env F G} (firstFresh : Fresh used first)
    (secondFresh : Fresh used second) : Fresh used (first ++ second) := by
  intro entry member
  rcases List.mem_append.mp member with member | member
  · exact firstFresh entry member
  · exact secondFresh entry member

theorem Fresh.mono {used used' : List String} {bound : Env F G} (fresh : Fresh used' bound)
    (sub : ∀ name ∈ used, name ∈ used') : Fresh used bound :=
  fun entry member inside => fresh entry member (sub _ inside)

/-- Values of a list of types agree with names. -/
theorem NamesAgree.values_length {names : List String} {env : Env F G} :
    ∀ {tys : List Ty} {values : Values (assignment F G) tys},
      NamesAgree names env values.get → tys.length ≤ names.length
  | [], _, _ => Nat.zero_le _
  | ty :: tys, .cons value rest, agrees => by
      obtain ⟨name, found, -⟩ := agrees ty .here
      cases names with
      | nil => simp at found
      | cons head names =>
          have tail : NamesAgree names env rest.get := by
            intro ty' variable_
            obtain ⟨name', found', looked'⟩ := agrees ty' (.there variable_)
            exact ⟨name', by simpa [Var.index] using found', looked'⟩
          simpa using tail.values_length

/-- Prepending results to a context prepends their names. -/
theorem NamesAgree.prepend {names : List String} {env : Env F G} {Γ : List Ty}
    {values : Environment (assignment F G) Γ} (agrees : NamesAgree names env values) :
    ∀ {Δ : List Ty} {returned : List String} (outs : Values (assignment F G) Δ),
      returned.length = Δ.length → NamesAgree returned env outs.get →
        NamesAgree (returned ++ names) env (values.prepend outs)
  | [], [], .nil, _, _ => agrees
  | _ :: _, [], .cons _ _, length, _ => by simp at length
  | ty :: Δ, name :: returned, .cons value rest, length, here => by
      have tail : NamesAgree returned env rest.get := by
        intro ty' variable_
        obtain ⟨name', found', looked'⟩ := here ty' (.there variable_)
        exact ⟨name', by simpa [Var.index] using found', looked'⟩
      have restAgrees := NamesAgree.prepend agrees rest (by simpa using length) tail
      intro ty' variable_
      cases variable_ with
      | here =>
          obtain ⟨name', found', looked'⟩ := here _ .here
          exact ⟨name', by simpa [Var.index] using found', looked'⟩
      | there variable_ =>
          obtain ⟨name', found', looked'⟩ := restAgrees _ variable_
          exact ⟨name', by simpa [Var.index] using found', looked'⟩

/-- The names of operands denote the evaluated operands. -/
theorem lookupAll_operands {names : List String} {env : Env F G} {Γ : List Ty}
    {values : Environment (assignment F G) Γ} (agrees : NamesAgree names env values) :
    ∀ {args : List Ty} (operands : Operands Γ args) {inputs : List String},
      operandNames names operands = some inputs →
        lookupAll env inputs = some (encodeValues (Operands.eval values operands)) ∧
          NamesAgree inputs env (Operands.eval values operands).get
  | [], .nil, inputs, found => by
      change some [] = some inputs at found
      cases found
      refine ⟨rfl, ?_⟩
      intro ty variable_
      cases variable_
  | ty :: args, .cons variable_ operands, inputs, found => by
      simp only [operandNames, Operands.indices, List.mapM_cons, Option.bind_eq_bind] at found
      cases first : names[variable_.index]? with
      | none => simp [first] at found
      | some name =>
          cases rest : (Operands.indices operands).mapM (names[·]?) with
          | none => simp [first, rest] at found
          | some names' =>
              simp only [first, rest, Option.bind_some] at found
              change some (name :: names') = some inputs at found
              cases found
              obtain ⟨tailLooked, tailAgrees⟩ := lookupAll_operands agrees operands (inputs := names') rest
              obtain ⟨name', found', looked'⟩ := agrees ty variable_
              rw [first, Option.some.injEq] at found'
              subst found'
              refine ⟨?_, ?_⟩
              · simp only [lookupAll, List.mapM_cons] at tailLooked ⊢
                rw [looked', tailLooked]
                rfl
              · intro ty' variable'
                cases variable' with
                | here => exact ⟨name, rfl, looked'⟩
                | there variable' =>
                    obtain ⟨name'', found'', looked''⟩ := tailAgrees ty' variable'
                    exact ⟨name'', by simpa [Var.index] using found'', looked''⟩

/-- Distinct names bound to encoded values denote them. -/
theorem NamesAgree.zip : ∀ {Δ : List Ty} {outputs : List String} (outs : Values (assignment F G) Δ)
    (env : Env F G), outputs.Nodup → outputs.length = Δ.length →
      NamesAgree outputs (outputs.zip (encodeValues outs) ++ env) outs.get
  | [], [], .nil, _, _, _ => by
      intro ty variable_
      cases variable_
  | _ :: _, [], .cons _ _, _, _, length => by simp at length
  | ty :: Δ, name :: outputs, .cons value rest, env, distinct, length => by
      have tail := NamesAgree.zip rest env (List.nodup_cons.mp distinct).2 (by simpa using length)
      intro ty' variable_
      cases variable_ with
      | here =>
          refine ⟨name, rfl, ?_⟩
          show List.lookup name ((name, Value.encode ty value) :: (outputs.zip (encodeValues rest) ++ env)) =
            some (Value.encode ty value)
          simp [List.lookup]
      | there variable_ =>
          obtain ⟨name', found', looked'⟩ := tail ty' variable_
          refine ⟨name', by simpa [Var.index] using found', ?_⟩
          have different : (name' == name) = false := by
            simp only [beq_eq_false_iff_ne]
            intro same
            subst same
            exact (List.nodup_cons.mp distinct).1 (List.mem_of_getElem? found')
          simp only [encodeValues, List.zip_cons_cons, List.cons_append, List.lookup, different]
          exact looked'

/-- Looking a name up among names zipped with their own lookups is looking it up. -/
theorem lookup_zip_lookupAll {env : Env F G} :
    ∀ {names : List String} {values : List (Value F G)}, lookupAll env names = some values →
      ∀ name ∈ names, List.lookup name (names.zip values) = List.lookup name env
  | [], _, _, _, member => by simp at member
  | head :: names, values, looked, name, member => by
      simp only [lookupAll, List.mapM_cons] at looked
      cases headEq : List.lookup head env with
      | none => simp [headEq] at looked
      | some value =>
          cases restEq : names.mapM (fun name => List.lookup name env) with
          | none => simp [headEq, restEq] at looked
          | some rest =>
              simp only [headEq, restEq, Option.bind_eq_bind, Option.bind_some] at looked
              change some (value :: rest) = some values at looked
              cases looked
              simp only [List.zip_cons_cons, List.lookup]
              by_cases same : name = head
              · subst same
                simp [headEq]
              · have different : (name == head) = false := by simpa using same
                simp only [different]
                exact lookup_zip_lookupAll (names := names) restEq name
                  ((List.mem_cons.mp member).resolve_left same)

end Names

/-! ## Encoded values -/

section Encoding

theorem decodeValues_encodeValues :
    ∀ {tys : List Ty} (values : Values (assignment F G) tys), tys.all dataType = true →
      decodeValues tys (encodeValues values) = some values
  | [], .nil, _ => rfl
  | ty :: tys, .cons value rest, data => by
      simp only [List.all_cons, Bool.and_eq_true] at data
      simp only [encodeValues, decodeValues, Value.decode_encode data.1, decodeValues_encodeValues rest data.2]
      rfl

/-- Arguments of the sorts of data types are encodings of structured values. -/
theorem sorted_encoded :
    ∀ {tys : List Ty} {arguments : List (Value F G)}, tys.length = arguments.length →
      (∀ (index : Nat) (value : Value F G) (sort : ValueSort), arguments[index]? = some value →
        (tys.map ValueSort.data)[index]? = some sort → HasSort value sort) →
      ∃ values : Values (assignment F G) tys, encodeValues values = arguments
  | [], [], _, _ => ⟨.nil, rfl⟩
  | [], _ :: _, length, _ => by simp at length
  | _ :: _, [], length, _ => by simp at length
  | ty :: tys, argument :: arguments, length, sorted => by
      obtain ⟨value, encoded⟩ := sorted 0 argument (.data ty) rfl rfl
      obtain ⟨rest, restEncoded⟩ := sorted_encoded (tys := tys) (arguments := arguments) (by simpa using length)
        (fun index value sort found sortFound => sorted (index + 1) value sort found sortFound)
      exact ⟨.cons value rest, by simp [encodeValues, encoded, restEncoded]⟩

end Encoding

/-! ## Evaluations -/

theorem Evaluated.after_after (result : Evaluated F G) (first second : Nat) :
    (result.after second).after first = result.after (first + second) := by
  cases result <;> simp [Evaluated.after, Nat.add_assoc]

theorem Evaluated.after_zero (result : Evaluated F G) : result.after 0 = result := by
  cases result <;> simp [Evaluated.after]

section Evaluations
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The outcome of a closed process followed by a continuation. -/
theorem closedOutcome_bind {A B : Type} (process : PIR.Process closedInterface A)
    (next : A → PIR.Process closedInterface B) :
    Construction.closedOutcome (process.bind next) =
      Finite.continueWith (Construction.closedOutcome process) fun value =>
        Construction.closedOutcome (next value) := by
  cases process with
  | done value => rfl
  | halt reason => rfl
  | call operation _ => exact (show Empty from operation).elim

end Evaluations

/-! ## Checked helper tables -/

section Tables
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The closed table of checked definitions in declaration order: each
definition's body sees the definitions before it. -/
def tableOf (F G : Type) [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (available : List CheckedDefinition) : Structured.Meanings F G :=
  available.foldl (Evaluation.extendMeanings SiteObservations.closed) []

theorem helperTable_eq (program : Structured.Program) :
    helperTable program F G = tableOf F G program.payload.definitions := rfl

theorem find_foldl_other (table : Structured.Meanings F G) (definitions : List CheckedDefinition)
    (name : String) (different : ∀ definition ∈ definitions, definition.name ≠ name) :
    (definitions.foldl (Evaluation.extendMeanings SiteObservations.closed) table).find?
        (fun entry => entry.helper.name == name) =
      table.find? (fun entry => entry.helper.name == name) := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun other member => different other (List.mem_cons_of_mem _ member))]
    simp [Evaluation.extendMeanings, CheckedDefinition.helper, different _ List.mem_cons_self]

theorem split_at {available : List CheckedDefinition} {index : Nat} {definition : CheckedDefinition}
    (found : available[index]? = some definition) :
    available = available.take index ++ definition :: available.drop (index + 1) := by
  have bound : index < available.length := by
    by_contra outside
    rw [List.getElem?_eq_none (by omega)] at found
    cases found
  rw [List.getElem?_eq_getElem bound, Option.some.injEq] at found
  subst found
  simp

theorem later_different {available : List CheckedDefinition} {index : Nat} {definition : CheckedDefinition}
    (distinct : (available.map (·.name)).Nodup) (found : available[index]? = some definition) :
    ∀ other ∈ available.drop (index + 1), other.name ≠ definition.name := by
  have split := split_at found
  rw [split] at distinct
  simp only [List.map_append, List.map_cons] at distinct
  have tail := (List.nodup_append.mp distinct).2.1
  intro other member same
  exact (List.nodup_cons.mp tail).1 (by rw [← same]; exact List.mem_map_of_mem member)

/-- The table of the available definitions, past one of them. -/
theorem tableOf_split {available : List CheckedDefinition} {index : Nat} {definition : CheckedDefinition}
    (found : available[index]? = some definition) :
    tableOf F G available = (available.drop (index + 1)).foldl
      (Evaluation.extendMeanings SiteObservations.closed)
      (Evaluation.extendMeanings SiteObservations.closed (tableOf F G (available.take index)) definition) := by
  unfold tableOf
  conv_lhs => rw [split_at found]
  rw [List.foldl_append, List.foldl_cons]

/-- A checked definition invoked in the table of the definitions available to
it is its body, interpreted in the table of the definitions before it. -/
theorem invoke_tableOf {available : List CheckedDefinition} {index : Nat} {definition : CheckedDefinition}
    (distinct : (available.map (·.name)).Nodup) (found : available[index]? = some definition)
    (arguments : Values (assignment F G) definition.inputs) :
    invoke (tableOf F G available) definition.helper arguments =
      definition.body.denote (Evaluation.meaning SiteObservations.closed (tableOf F G (available.take index)))
        arguments.get := by
  rw [tableOf_split found,
    Evaluation.invoke_foldl_other SiteObservations.closed _ _ definition.helper (later_different distinct found)]
  exact Evaluation.invoke_extended SiteObservations.closed _ definition arguments

/-- A call by name of an available checked definition on arguments that decode
at its inputs invokes it. -/
theorem callHelper_tableOf {available : List CheckedDefinition} {index : Nat} {definition : CheckedDefinition}
    (distinct : (available.map (·.name)).Nodup) (found : available[index]? = some definition)
    (arguments : List (Value F G)) (values : Values (assignment F G) definition.inputs)
    (decoded : decodeValues definition.inputs arguments = some values) :
    callHelper (tableOf F G available) definition.name arguments =
      mapOutcome encodeValues (Construction.closedOutcome (invoke (tableOf F G available) definition.helper values)) := by
  have present : ∃ entry : HelperDefinition (assignment F G) closedInterface,
      (tableOf F G available).find? (fun entry => entry.helper.name == definition.name) = some entry ∧
        entry.helper = definition.helper := by
    refine ⟨⟨definition.helper, fun values => definition.body.denote
      (Evaluation.meaning SiteObservations.closed (tableOf F G (available.take index))) values.get⟩, ?_, rfl⟩
    rw [tableOf_split found, find_foldl_other _ _ _ (later_different distinct found)]
    simp [Evaluation.extendMeanings, CheckedDefinition.helper]
  obtain ⟨⟨helper', body⟩, entry, same⟩ := present
  simp only at same
  subst same
  have invoked : invoke (tableOf F G available) definition.helper values = body values := by
    simp [invoke, show definition.helper.name = definition.name from rfl, entry]
  have decoded' : decodeValues definition.helper.inputs arguments = some values := decoded
  rw [invoked]
  simp only [callHelper, entry, decoded']
  generalize Construction.closedOutcome (body values) = outcome
  cases outcome <;> rfl

end Tables

/-! ## Operations -/

section Operations
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem Primitive.arguments_data (primitive : Primitive) : primitive.arguments.all dataType = true := by
  cases primitive <;> rfl

theorem calculate_encode (calculation : Calculation) (data : calculation.op.arguments.all dataType = true)
    (arguments : Values (assignment F G) calculation.op.arguments) :
    (Resolved.calculate calculation).evaluate (encodeValues arguments) =
      mapOutcome encodeValues (calculation.evaluate arguments) := by
  simp only [Resolved.evaluate, Zkc.Construction.calculate, decodeValues_encodeValues arguments data]
  cases calculation.evaluate arguments <;> rfl

theorem sound_indexConstant (table : Structured.Meanings F G) (value : Nat) (below : value < indexLimit)
    (callbacks : Values (RegionFunction (assignment F G) closedInterface) []) :
    (Resolved.calculate (.indexConstant value)).evaluate (encodeValues (Values.nil : Values (assignment F G) [])) =
      mapOutcome encodeValues (Construction.closedOutcome
        (Evaluation.operation SiteObservations.closed table (.exec (.indexConstant value)) .nil callbacks)) := by
  refine (calculate_encode (.indexConstant value) rfl Values.nil).trans ?_
  cases callbacks
  simp [Evaluation.operation, Primitive.evaluate, primitiveOutcome, below, Construction.closedOutcome,
    Calculation.evaluate]
  rfl

theorem sound_indexEqual (table : Structured.Meanings F G) (a b : Nat) (aBound : a < indexLimit)
    (bBound : b < indexLimit) (callbacks : Values (RegionFunction (assignment F G) closedInterface) []) :
    (Resolved.calculate .indexEqual).evaluate
        (encodeValues (Values.cons a (Values.cons b Values.nil) : Values (assignment F G) [.index, .index])) =
      mapOutcome encodeValues (Construction.closedOutcome
        (Evaluation.operation SiteObservations.closed table (.exec .indexEqual)
          (Values.cons a (Values.cons b Values.nil)) callbacks)) := by
  refine (calculate_encode .indexEqual rfl (Values.cons a (Values.cons b Values.nil))).trans ?_
  cases callbacks
  simp [Evaluation.operation, Primitive.evaluate, primitiveOutcome, checkedIndices, aBound, bBound,
    Construction.closedOutcome, Calculation.evaluate]
  rfl

theorem sound_fieldEqual (table : Structured.Meanings F G) (domain : String) (a b : F)
    (callbacks : Values (RegionFunction (assignment F G) closedInterface) []) :
    (Resolved.calculate (.fieldEqual domain)).evaluate
        (encodeValues (Values.cons a (Values.cons b Values.nil) :
          Values (assignment F G) [.field domain, .field domain])) =
      mapOutcome encodeValues (Construction.closedOutcome
        (Evaluation.operation SiteObservations.closed table (.exec (.fieldEqual domain))
          (Values.cons a (Values.cons b Values.nil)) callbacks)) := by
  refine (calculate_encode (.fieldEqual domain) rfl (Values.cons a (Values.cons b Values.nil))).trans ?_
  cases callbacks
  simp [Evaluation.operation, Primitive.evaluate, primitiveOutcome, Construction.closedOutcome,
    Calculation.evaluate]
  rfl

theorem sound_primitive (table : Structured.Meanings F G) (primitive : Primitive)
    (arguments : Values (assignment F G) primitive.arguments)
    (callbacks : Values (RegionFunction (assignment F G) closedInterface) []) :
    (Resolved.compute (.primitive primitive)).evaluate (encodeValues arguments) =
      mapOutcome encodeValues (Construction.closedOutcome
        (Evaluation.operation SiteObservations.closed table (.exec primitive) arguments callbacks)) := by
  cases callbacks
  simp only [Resolved.evaluate, Computation.apply, decodeValues_encodeValues arguments (Primitive.arguments_data _)]
  change _ = mapOutcome encodeValues (Construction.closedOutcome (primitiveOutcome (primitive.evaluate arguments)))
  cases primitive.evaluate arguments <;> rfl

theorem sound_calculation (table : Structured.Meanings F G) (calculation : Calculation)
    (data : calculation.op.arguments.all dataType = true)
    (arguments : Values (assignment F G) calculation.op.arguments)
    (callbacks : Values (RegionFunction (assignment F G) closedInterface) calculation.op.regions) :
    (Resolved.calculate calculation).evaluate (encodeValues arguments) =
      mapOutcome encodeValues (Construction.closedOutcome
        (Evaluation.operation SiteObservations.closed table calculation.op arguments callbacks)) := by
  rw [Evaluation.operation_eq_operationOn, Uniform.DomainAdapter.operationOn_calculation]
  simp only [Resolved.evaluate, Zkc.Construction.calculate, decodeValues_encodeValues arguments data]
  cases calculation.evaluate arguments <;> rfl

/-- An installed operation that implements a structured operation computes its
meaning on encoded arguments. -/
theorem implements_sound (table : Structured.Meanings F G) {op : Structured.Op} {resolved : Resolved}
    (implemented : implements op resolved = true) (arguments : Values (assignment F G) op.arguments)
    (callbacks : Values (RegionFunction (assignment F G) closedInterface) op.regions)
    (bounded : needsBounded op resolved = true →
      ∀ value ∈ encodeValues arguments, ∀ index, value = .index index → index < indexLimit) :
    resolved.evaluate (encodeValues arguments) =
      mapOutcome encodeValues
        (Construction.closedOutcome (Evaluation.operation SiteObservations.closed table op arguments callbacks)) := by
  cases op with
  | exec primitive =>
      cases resolved with
      | calculate calculation =>
          cases primitive <;> cases calculation <;> simp [implements, Calculation.ofOp?] at implemented
          · obtain ⟨rfl, below⟩ := implemented
            cases arguments
            exact sound_indexConstant table _ below callbacks
          · rcases arguments with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            have bounds := bounded rfl
            exact sound_indexEqual table a b
              (bounds (.index a) List.mem_cons_self a rfl)
              (bounds (.index b) (List.mem_cons_of_mem _ List.mem_cons_self) b rfl) callbacks
          · subst implemented
            rcases arguments with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            exact sound_fieldEqual table _ a b callbacks
      | compute computation =>
          cases computation with
          | primitive primitive' =>
              simp [implements] at implemented
              subst implemented
              exact sound_primitive table _ arguments callbacks
          | _ => simp [implements] at implemented
      | _ => simp [implements] at implemented
  | _ =>
      cases resolved with
      | calculate calculation =>
          first
          | (simp only [implements, Calculation.ofOp?, Bool.false_eq_true] at implemented; done)
          | (simp only [implements, Calculation.ofOp?, Bool.and_eq_true, beq_iff_eq] at implemented
             obtain ⟨rfl, data⟩ := implemented
             exact sound_calculation table _ data arguments callbacks)
      | _ => simp [implements] at implemented

end Operations

/-! ## Walks -/

section WalkLemmas

theorem lookupAll_mem {env : Env F G} : ∀ {names : List String} {values : List (Value F G)},
    lookupAll env names = some values → ∀ value ∈ values, ∃ name ∈ names, List.lookup name env = some value
  | [], values, looked, value, member => by
      change some [] = some values at looked
      cases looked
      simp at member
  | head :: names, values, looked, value, member => by
      simp only [lookupAll, List.mapM_cons] at looked
      cases headEq : List.lookup head env with
      | none => simp [headEq] at looked
      | some first =>
          cases restEq : names.mapM (fun name => List.lookup name env) with
          | none => simp [headEq, restEq] at looked
          | some rest =>
              simp only [headEq, restEq, Option.bind_eq_bind, Option.bind_some] at looked
              change some (first :: rest) = some values at looked
              cases looked
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨head, List.mem_cons_self, headEq⟩
              · obtain ⟨name, inside, found⟩ := lookupAll_mem (names := names) restEq value member
                exact ⟨name, List.mem_cons_of_mem _ inside, found⟩

theorem operandNames_cons {names : List String} {Γ args : List Ty} {ty : Ty} (variable_ : Var Γ ty)
    (operands : Operands Γ args) {inputs : List String}
    (found : operandNames names (Values.cons variable_ operands : Operands Γ (ty :: args)) = some inputs) :
    ∃ name rest, names[variable_.index]? = some name ∧ operandNames names operands = some rest ∧
      inputs = name :: rest := by
  simp only [operandNames, Operands.indices, List.mapM_cons, Option.bind_eq_bind] at found
  cases first : names[variable_.index]? with
  | none => simp [first] at found
  | some name =>
      cases rest : (Operands.indices operands).mapM (names[·]?) with
      | none => simp [first, rest] at found
      | some rest' =>
          simp only [first, rest, Option.bind_some] at found
          change some (name :: rest') = some inputs at found
          cases found
          exact ⟨name, rest', rfl, rest, rfl⟩

theorem operandNames_mem {names : List String} {Γ : List Ty} :
    ∀ {args : List Ty} (operands : Operands Γ args) {inputs : List String},
      operandNames names operands = some inputs → (∀ name ∈ inputs, name ∈ names) ∧ inputs.length = args.length
  | [], .nil, inputs, found => by
      change some [] = some inputs at found
      cases found
      simp
  | _ :: _, .cons variable_ operands, inputs, found => by
      obtain ⟨name, rest, first, restFound, rfl⟩ := operandNames_cons variable_ operands found
      obtain ⟨restMem, restLength⟩ := operandNames_mem operands restFound
      refine ⟨?_, by simp [restLength]⟩
      intro name' member
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_of_getElem? first
      · exact restMem name' member

theorem Scope.bind_eq {scope : Scope} {outputs : List String} {bounded : Bool} {scope' : Scope}
    (bound : scope.bind outputs bounded = some scope') :
    outputs.Nodup ∧ (∀ output ∈ outputs, output ∉ scope.used) ∧
      scope' = ⟨outputs ++ scope.used, if bounded then outputs ++ scope.bounded else scope.bounded⟩ := by
  unfold Scope.bind at bound
  split at bound
  · rename_i fresh
    cases bound
    exact ⟨fresh.1, fresh.2, rfl⟩
  · cases bound

theorem fresh_zip {used outputs : List String} (fresh : ∀ output ∈ outputs, output ∉ used)
    (values : List (Value F G)) : Fresh used (outputs.zip values) := by
  intro entry member
  exact fresh _ (List.of_mem_zip member).1

theorem lookup_zip_none {name : String} :
    ∀ {keys : List String} {values : List (Value F G)}, name ∉ keys → List.lookup name (keys.zip values) = none
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | key :: keys, _ :: values, absent => by
      have different : (name == key) = false := by
        simp only [beq_eq_false_iff_ne]
        intro same
        exact absent (same ▸ List.mem_cons_self)
      simp only [List.zip_cons_cons, List.lookup, different]
      exact lookup_zip_none (fun member => absent (List.mem_cons_of_mem _ member))

theorem lookup_zip_present {name : String} :
    ∀ {keys : List String} {values : List (Value F G)}, name ∈ keys → keys.length = values.length →
      ∃ value ∈ values, List.lookup name (keys.zip values) = some value
  | [], _, member, _ => by simp at member
  | _ :: _, [], _, length => by simp at length
  | key :: keys, value :: values, member, length => by
      by_cases same : name = key
      · subst same
        exact ⟨value, List.mem_cons_self, by simp⟩
      · have different : (name == key) = false := by simpa using same
        obtain ⟨found, inside, looked⟩ := lookup_zip_present (keys := keys) (values := values)
          ((List.mem_cons.mp member).resolve_left same) (by simpa using length)
        exact ⟨found, List.mem_cons_of_mem _ inside, by simp only [List.zip_cons_cons, List.lookup, different]; exact looked⟩

/-- The scope after binding fresh names to results holds. -/
theorem ScopeHolds.bind {scope scope' : Scope} {names outputs : List String} {env : Env F G}
    {results : List (Value F G)} {flag : Bool} (holds : ScopeHolds scope names env)
    (bound : scope.bind outputs flag = some scope') (length : outputs.length = results.length)
    (resultsBound : flag = true → ∀ value ∈ results, ∀ index, value = .index index → index < indexLimit) :
    ScopeHolds scope' (outputs ++ names) (outputs.zip results ++ env) := by
  obtain ⟨-, fresh, rfl⟩ := Scope.bind_eq bound
  refine ⟨?_, ?_, ?_⟩
  · intro name member
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ member
    · exact List.mem_append_right _ (holds.named name member)
  · intro name member
    cases flag
    · exact List.mem_append_right _ (holds.boundedUsed name member)
    · rcases List.mem_append.mp member with member | member
      · exact List.mem_append_left _ member
      · exact List.mem_append_right _ (holds.boundedUsed name member)
  · intro name member index looked
    have old : name ∈ scope.bounded → index < indexLimit := by
      intro inside
      have absent : name ∉ outputs := fun output => fresh name output (holds.boundedUsed name inside)
      rw [lookup_append_some, lookup_zip_none absent, Option.none_or] at looked
      exact holds.bounded name inside index looked
    cases flag
    · exact old member
    · rcases List.mem_append.mp member with member | member
      · obtain ⟨value, inside, found⟩ := lookup_zip_present member length (values := results)
        rw [lookup_append_some, found, Option.some_or, Option.some.injEq] at looked
        subst looked
        exact resultsBound rfl _ inside index rfl
      · exact old member

/-- Names that agree with values look them all up. -/
theorem lookupAll_of_agrees {env : Env F G} : ∀ {tys : List Ty} {names : List String}
    (values : Values (assignment F G) tys), names.length = tys.length → NamesAgree names env values.get →
      lookupAll env names = some (encodeValues values)
  | [], [], .nil, _, _ => rfl
  | _ :: _, [], .cons _ _, length, _ => by simp at length
  | ty :: tys, name :: names, .cons value rest, length, agrees => by
      obtain ⟨name', found, looked⟩ := agrees ty .here
      simp only [Var.index, List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      have tail : NamesAgree names env rest.get := by
        intro ty' variable_
        obtain ⟨name'', found', looked'⟩ := agrees ty' (.there variable_)
        exact ⟨name'', by simpa [Var.index] using found', looked'⟩
      have restLooked := lookupAll_of_agrees rest (by simpa using length) tail
      simp only [lookupAll, List.mapM_cons] at restLooked ⊢
      rw [looked, restLooked]
      rfl

end WalkLemmas

section Operation
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (vocabulary : Vocabulary) (validator : Validator)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A single index result below the limit. -/
theorem single_bounded {n : Nat} (below : n < indexLimit) :
    ∀ value ∈ [(Value.index n : Value F G)], ∀ index, value = .index index → index < indexLimit := by
  intro value member index same
  simp only [List.mem_singleton] at member
  subst member
  cases same
  exact below

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- An index primitive that returns, on checked arguments, returns one index
below the limit. -/
theorem primitive_bounded {primitive : Primitive}
    (arguments : Values (assignment F G) primitive.arguments) {outs : Values (assignment F G) primitive.results}
    (returned : primitive.evaluate arguments = .returned outs) :
    ∀ value ∈ encodeValues outs, ∀ index, value = .index index → index < indexLimit := by
  cases primitive with
  | indexConstant n =>
      cases arguments
      by_cases below : n < indexLimit
      · simp only [Primitive.evaluate, below, ite_true] at returned
        injection returned with returned
        subst returned
        exact single_bounded below
      · simp [Primitive.evaluate, below] at returned
  | indexAdd | indexMul | indexSub | indexDiv | indexMod =>
      rcases arguments with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      simp only [Primitive.evaluate, checkedIndices] at returned
      by_cases inRange : a < indexLimit ∧ b < indexLimit
      · simp only [inRange, and_self, ite_true] at returned
        split at returned
        all_goals first
          | (injection returned with returned
             subst returned
             apply single_bounded
             first
               | assumption
               | omega
               | exact lt_of_le_of_lt (Nat.div_le_self _ _) inRange.1
               | exact lt_of_le_of_lt (Nat.sub_le _ _) inRange.1
               | (rename_i positive
                  exact lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero positive)) inRange.2))
          | cases returned
      · simp [inRange] at returned
  | vectorLength domain =>
      rcases arguments with _ | ⟨xs, _ | _⟩
      by_cases below : xs.length < indexLimit
      · simp only [Primitive.evaluate, below, ite_true] at returned
        injection returned with returned
        subst returned
        exact single_bounded below
      · simp [Primitive.evaluate, below] at returned
  | indexEqual | indexLess | vectorEqual _ | fieldEqual _ =>
      intro value member index same
      subst same
      rcases outs with _ | ⟨x, _ | _⟩
      have member' : Value.index index ∈ [(Value.encode .boolean x : Value F G)] := member
      simp [Value.encode] at member'
  | vectorEmpty domain | vectorAppend domain =>
      intro value member index same
      subst same
      rcases outs with _ | ⟨x, _ | _⟩
      have member' : Value.index index ∈ [(Value.encode (.vector domain) x : Value F G)] := member
      simp [Value.encode] at member'
  | vectorSum domain =>
      intro value member index same
      subst same
      rcases outs with _ | ⟨x, _ | _⟩
      have member' : Value.index index ∈ [(Value.encode (.field domain) x : Value F G)] := member
      simp [Value.encode] at member'
  | vectorSplit domain =>
      intro value member index same
      subst same
      rcases outs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
      have member' : Value.index index ∈
          [(Value.encode (.vector domain) x : Value F G), Value.encode (.vector domain) y] := member
      simp [Value.encode] at member'

/-- An operation whose results are bounded returns indices below the limit. -/
theorem resultsBounded_sound (table : Structured.Meanings F G) {op : Structured.Op}
    (bounded : resultsBounded op = true) (arguments : Values (assignment F G) op.arguments)
    (callbacks : Values (RegionFunction (assignment F G) closedInterface) op.regions)
    {outs : Values (assignment F G) op.results}
    (returned : Construction.closedOutcome (Evaluation.operation SiteObservations.closed table op arguments callbacks) =
      .returned outs) :
    ∀ value ∈ encodeValues outs, ∀ index, value = .index index → index < indexLimit := by
  cases op with
  | exec primitive =>
      cases callbacks
      change Construction.closedOutcome (primitiveOutcome (primitive.evaluate arguments)) = _ at returned
      apply primitive_bounded arguments (outs := outs)
      cases evaluated : primitive.evaluate arguments with
      | returned results =>
          rw [evaluated] at returned
          injection returned with returned
          rw [returned]
      | stopped reason =>
          rw [evaluated] at returned
          cases returned
  | indexConstant value =>
      cases arguments
      cases callbacks
      simp only [resultsBounded, decide_eq_true_eq] at bounded
      change PIR.Outcome.returned (Values.cons (Value := assignment F G) (ty := .index) value Values.nil) = _
        at returned
      injection returned with returned
      subst returned
      exact single_bounded bounded
  | _ => simp [resultsBounded] at bounded

/-- One walked operation: on a return its step reaches the remaining steps with
its results bound to fresh names; on a stop it stops for the same reason. -/
theorem walkOperation_sound (table : Structured.Meanings F G) {op : Structured.Op} {inputs : List String}
    {scope : Scope} {steps : List Step} {outputs : List String} {scope' : Scope} {rest : List Step}
    (walked : walkOperation vocabulary validator op inputs scope steps = .ok (outputs, scope', rest))
    {names : List String} {env : Env F G} (holds : ScopeHolds scope names env)
    (arguments : Values (assignment F G) op.arguments)
    (callbacks : Values (RegionFunction (assignment F G) closedInterface) op.regions)
    (looked : lookupAll env inputs = some (encodeValues arguments)) :
    (∀ outs, Construction.closedOutcome (Evaluation.operation SiteObservations.closed table op arguments callbacks) =
        .returned outs →
      evalSteps vocabulary validator steps env =
          (evalSteps vocabulary validator rest (outputs.zip (encodeValues outs) ++ env)).after 1 ∧
        Fresh scope.used (outputs.zip (encodeValues outs)) ∧
        NamesAgree outputs (outputs.zip (encodeValues outs) ++ env) outs.get ∧
        outputs.length = op.results.length ∧
        ScopeHolds scope' (outputs ++ names) (outputs.zip (encodeValues outs) ++ env)) ∧
    (∀ reason, Construction.closedOutcome (Evaluation.operation SiteObservations.closed table op arguments callbacks) =
        .stopped reason →
      ∃ cause cost, evalSteps vocabulary validator steps env = .stopped cause cost ∧ cause.outcome = reason) := by
  unfold walkOperation at walked
  by_cases recipe : hasRecipe op = true
  · simp only [recipe, ite_true] at walked
    cases steps with
    | nil => cases walked
    | cons step rest' =>
        cases step with
        | operation site binding parameters inputs' outputs' =>
            simp only at walked
            cases resolvedEq : validator.binding? binding >>= (vocabulary.resolve · parameters) with
            | none => simp [resolvedEq] at walked
            | some resolved =>
                simp only [resolvedEq] at walked
                by_cases conditions : implements op resolved = true ∧ inputs' = inputs ∧
                    outputs'.length = op.results.length
                · simp only [conditions, and_self, ite_true] at walked
                  by_cases boundedOk : needsBounded op resolved = true → ∀ input ∈ inputs, input ∈ scope.bounded
                  · rw [ite_eq_left_of_eq_true _ _ (eq_true boundedOk)] at walked
                    cases bindEq : scope.bind outputs' (resultsBounded op) with
                    | none => simp [bindEq] at walked
                    | some scope'' =>
                        simp only [bindEq, Except.ok.injEq, Prod.mk.injEq] at walked
                        obtain ⟨rfl, rfl, rfl⟩ := walked
                        obtain ⟨implemented, rfl, length⟩ := conditions
                        obtain ⟨distinct, fresh, -⟩ := Scope.bind_eq bindEq
                        have computed := implements_sound table implemented arguments callbacks
                          (fun needed value member index same => by
                            obtain ⟨name, inside, found⟩ := lookupAll_mem looked value member
                            rw [same] at found
                            exact holds.bounded name (boundedOk needed name inside) index found)
                        refine ⟨fun outs returned => ?_, fun reason stopped => ?_⟩
                        · rw [returned] at computed
                          have encodedLength : outputs'.length = (encodeValues outs).length := by
                            rw [Zkc.Construction.Uniform.encodeValues_length]; exact length
                          refine ⟨evalSteps_operation vocabulary validator resolvedEq looked computed encodedLength,
                            fresh_zip fresh _, NamesAgree.zip outs env distinct length, length, ?_⟩
                          exact ScopeHolds.bind holds bindEq encodedLength
                            (fun _ => resultsBounded_sound table (by
                              cases flag : resultsBounded op
                              · simp [Scope.bind_eq bindEq |>.2.2, flag] at *
                              · rfl) arguments callbacks returned)
                        · rw [stopped] at computed
                          exact ⟨_, _, evalSteps_operation_stopped vocabulary validator resolvedEq looked computed, rfl⟩
                  · rw [ite_eq_right_of_eq_false _ _ (eq_false boundedOk)] at walked
                    cases walked
                · simp [conditions] at walked
        | constant site output value =>
            simp only at walked
            cases op with
            | booleanConstant value' =>
                by_cases same : value = value'
                · subst same
                  simp only [ite_true] at walked
                  cases bindEq : scope.bind [output] false with
                  | none => simp [bindEq] at walked
                  | some scope'' =>
                      simp only [bindEq, Except.ok.injEq, Prod.mk.injEq] at walked
                      obtain ⟨rfl, rfl, rfl⟩ := walked
                      obtain ⟨distinct, fresh, -⟩ := Scope.bind_eq bindEq
                      cases callbacks
                      cases arguments
                      refine ⟨fun outs returned => ?_, fun reason stopped => by cases stopped⟩
                      change PIR.Outcome.returned (Values.cons (Value := assignment F G) (ty := .boolean) value Values.nil) =
                        _ at returned
                      injection returned with returned
                      subst returned
                      refine ⟨evalSteps_constant vocabulary validator, fresh_zip fresh _,
                        NamesAgree.zip _ env distinct rfl, rfl, ?_⟩
                      exact ScopeHolds.bind holds bindEq rfl (fun flag => by cases flag)
                · simp [same] at walked
            | _ => cases walked
        | _ => cases walked
  · simp [recipe] at walked

theorem walkOperation_used {op : Structured.Op} {inputs : List String} {scope : Scope} {steps : List Step}
    {outputs : List String} {scope' : Scope} {rest : List Step}
    (walked : walkOperation vocabulary validator op inputs scope steps = .ok (outputs, scope', rest)) :
    ∀ name ∈ scope.used, name ∈ scope'.used := by
  unfold walkOperation at walked
  split at walked
  · split at walked
    · split at walked
      · split at walked
        · split at walked
          · split at walked
            · rename_i bindEq
              simp only [Except.ok.injEq, Prod.mk.injEq] at walked
              obtain ⟨-, rfl, -⟩ := walked
              obtain ⟨-, -, rfl⟩ := Scope.bind_eq bindEq
              exact fun name member => List.mem_append_right _ member
            · cases walked
          · cases walked
        · cases walked
      · cases walked
    · split at walked
      · split at walked
        · split at walked
          · rename_i bindEq
            simp only [Except.ok.injEq, Prod.mk.injEq] at walked
            obtain ⟨-, rfl, -⟩ := walked
            obtain ⟨-, -, rfl⟩ := Scope.bind_eq bindEq
            exact fun name member => List.mem_append_right _ member
          · cases walked
        · cases walked
      · cases walked
    · cases walked
    · cases walked
  · cases walked

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Except.bind_eq_ok {ε α β : Type} {first : Except ε α} {next : α → Except ε β} {result : β}
    (bound : first.bind next = .ok result) : ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error refusal => cases bound
  | ok value => exact ⟨value, rfl, bound⟩

/-- What a walk establishes of a region's outcome on executable steps. A stop
stops the steps for the same reason. A return reaches the remaining steps in an
environment extended by fresh names, where the returned names denote the
results and the walk's scope holds. A walk that ends in a stop never returns. -/
def WalkSound (steps : List Step) (env : Env F G) (used : List String) {out : List Ty} :
    PIR.Outcome (Values (assignment F G) out) → Walked → Prop
  | .stopped reason, _ =>
      ∃ cause cost, evalSteps vocabulary validator steps env = .stopped cause cost ∧ cause.outcome = reason
  | .returned outs, .returned rest names scope =>
      ∃ (bound : Env F G) (cost : Nat), Fresh used bound ∧
        evalSteps vocabulary validator steps env = (evalSteps vocabulary validator rest (bound ++ env)).after cost ∧
        NamesAgree names (bound ++ env) outs.get ∧ names.length = out.length ∧
        ScopeHolds scope names (bound ++ env)
  | .returned _, .stopped => False

/-- Steps that reach other steps in a fresh extension inherit what a walk of the
other steps establishes. -/
theorem WalkSound.after {steps rest : List Step} {env bound : Env F G} {cost : Nat} {used used' : List String}
    (reached : evalSteps vocabulary validator steps env =
      (evalSteps vocabulary validator rest (bound ++ env)).after cost)
    (fresh : Fresh used bound) (sub : ∀ name ∈ used, name ∈ used') {out : List Ty}
    {outcome : PIR.Outcome (Values (assignment F G) out)} {walked : Walked}
    (sound : WalkSound vocabulary validator rest (bound ++ env) used' outcome walked) :
    WalkSound vocabulary validator steps env used outcome walked := by
  cases outcome with
  | stopped reason =>
      obtain ⟨cause, cost', stopped, same⟩ := sound
      exact ⟨cause, cost + cost', by rw [reached, stopped]; rfl, same⟩
  | returned outs =>
      cases walked with
      | stopped => exact sound.elim
      | returned rest' names scope =>
          obtain ⟨bound', cost', fresh', reached', agrees, length, holds⟩ := sound
          refine ⟨bound' ++ bound, cost + cost', (fresh'.mono sub).append fresh, ?_, ?_, length, ?_⟩
          · rw [reached, reached', Evaluated.after_after, List.append_assoc]
          · rw [List.append_assoc]; exact agrees
          · rw [List.append_assoc]; exact holds

theorem findDefinition_some {available : List CheckedDefinition} {helper : Helper} {index : Nat}
    (found : findDefinition available helper = some index) {definition : CheckedDefinition}
    (present : available[index]? = some definition) : definition.helper = helper := by
  obtain ⟨bound, matches_, -⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  rw [List.getElem?_eq_getElem bound, Option.some.injEq] at present
  subst present
  simpa using matches_

theorem guardCondition?_some {step : Step} {condition : String} (found : guardCondition? step = some condition) :
    ∃ site stopSite, step = .cond site condition [] [.yield []] [.stop stopSite "reject"] [] := by
  unfold guardCondition? at found
  split at found
  · cases found
    exact ⟨_, _, rfl⟩
  · cases found

theorem regionEnds_returned {rest : List Step} {names : List String} {scope : Scope}
    (ends : regionEnds (.returned rest names scope) = true) : rest = [.yield names] := by
  unfold regionEnds at ends
  split at ends
  · rename_i values _ _ same
    cases same
    simp only [beq_iff_eq] at ends
    rw [ends]
  · cases ends
  · rename_i same
    cases same

/-- A region that yields: its steps hand back the encoded results. -/
theorem region_values {steps : List Step} {env : Env F G} {used : List String} {out : List Ty}
    {outs : Values (assignment F G) out} {walked : Walked} (ends : regionEnds walked = true)
    (sound : WalkSound vocabulary validator steps env used (.returned outs) walked) :
    ∃ cost, evalSteps vocabulary validator steps env = .values (encodeValues outs) cost := by
  cases walked with
  | stopped => exact sound.elim
  | returned rest names scope =>
      have ending := regionEnds_returned ends
      subst ending
      obtain ⟨bound, cost, -, reached, agrees, length, -⟩ := sound
      refine ⟨cost + 1, ?_⟩
      rw [reached, evalSteps_yield vocabulary validator (lookupAll_of_agrees outs length agrees)]
      rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The captured names of a region denote its captured values in the region's
environment, and the walk's scope holds there. -/
theorem region_entered {names captures : List String} {scope : Scope} {env : Env F G}
    (holds : ScopeHolds scope names env) (named : ∀ name ∈ captures, name ∈ names) {tys : List Ty}
    {captured : Values (assignment F G) tys} (looked : lookupAll env captures = some (encodeValues captured))
    (agrees : NamesAgree captures env captured.get) :
    NamesAgree captures (captures.zip (encodeValues captured)) captured.get ∧
      ScopeHolds scope captures (captures.zip (encodeValues captured)) := by
  have same := lookup_zip_lookupAll looked
  refine ⟨fun ty variable_ => ?_, ⟨fun name member => holds.named name (named name member), holds.boundedUsed, ?_⟩⟩
  · obtain ⟨name, found, foundLooked⟩ := agrees ty variable_
    exact ⟨name, found, by rw [same name (List.mem_of_getElem? found)]; exact foundLooked⟩
  · intro name member index foundLooked
    by_cases inside : name ∈ captures
    · rw [same name inside] at foundLooked
      exact holds.bounded name member index foundLooked
    · rw [lookup_zip_none inside] at foundLooked
      cases foundLooked

/-- Soundness of a walk: the steps a walk consumes implement the region on
every environment the names agree with. -/
theorem walkRegion_sound : ∀ (fuel : Nat) (available : List CheckedDefinition) {Γ out : List Ty}
    (names : List String) (scope : Scope) (region : Region dialect Γ out) (steps : List Step) (walked : Walked),
    (available.map (·.name)).Nodup →
    walkRegion vocabulary validator fuel available names scope region steps = .ok walked →
    ∀ (env : Env F G) (values : Environment (assignment F G) Γ), NamesAgree names env values →
      ScopeHolds scope names env →
      WalkSound vocabulary validator steps env scope.used
        (Construction.closedOutcome
          (region.denote (Evaluation.meaning SiteObservations.closed (tableOf F G available)) values)) walked
  | 0, _, _, _, _, _, _, _, _, _, accepted => by simp [walkRegion] at accepted
  | fuel + 1, available, Γ, out, names, scope, region, steps, walked, distinct, accepted => by
    intro env values agrees holds
    match region, accepted with
    | .ret returnedOperands, accepted =>
        simp only [walkRegion] at accepted
        cases found : operandNames names returnedOperands with
        | none => simp [found] at accepted
        | some returned =>
            simp only [found, Except.ok.injEq] at accepted
            subst accepted
            obtain ⟨-, returnedAgree⟩ := lookupAll_operands agrees returnedOperands found
            obtain ⟨member, length⟩ := operandNames_mem returnedOperands found
            refine ⟨[], 0, fun _ inside => by simp at inside, (Evaluated.after_zero _).symm, returnedAgree, length, ?_⟩
            exact ⟨fun name inside => holds.named name (member name inside), holds.boundedUsed, holds.bounded⟩
    | .stop reason, accepted =>
        simp only [walkRegion] at accepted
        cases steps with
        | nil => cases accepted
        | cons step rest =>
            cases step with
            | stop site text =>
                simp only at accepted
                by_cases named : stopReason? text = some reason
                · simp only [named, ite_true, Except.ok.injEq] at accepted
                  subst accepted
                  exact ⟨.explicit reason, 1, by simp [evalSteps, evalStep, named], rfl⟩
                · simp [named] at accepted
            | _ => cases accepted
    | .bind _ _, accepted => simp [walkRegion] at accepted
    | .letOp op arguments bodies next, accepted =>
        simp only [walkRegion] at accepted
        cases inputsEq : operandNames names arguments with
        | none => simp [inputsEq] at accepted
        | some inputs =>
            simp only [inputsEq] at accepted
            obtain ⟨looked, inputsAgree⟩ := lookupAll_operands agrees arguments inputsEq
            obtain ⟨inputsMember, -⟩ := operandNames_mem arguments inputsEq
            have denoted : Construction.closedOutcome ((Region.letOp op arguments bodies next).denote
                  (Evaluation.meaning SiteObservations.closed (tableOf F G available)) values) =
                Finite.continueWith (Construction.closedOutcome (Evaluation.operation SiteObservations.closed
                    (tableOf F G available) op (Operands.eval values arguments)
                    (bodies.denote (Evaluation.meaning SiteObservations.closed (tableOf F G available))))) fun results =>
                  Construction.closedOutcome (next.denote
                    (Evaluation.meaning SiteObservations.closed (tableOf F G available)) (values.prepend results)) := by
              simp only [Region.denote]
              exact closedOutcome_bind _ _
            rw [denoted]
            -- One operation followed by its continuation.
            have continued : ∀ {outputs : List String} {scope' : Scope} {rest : List Step},
                walkOperation vocabulary validator op inputs scope steps = .ok (outputs, scope', rest) →
                walkRegion vocabulary validator fuel available (outputs ++ names) scope' next rest = .ok walked →
                WalkSound vocabulary validator steps env scope.used
                  (Finite.continueWith (Construction.closedOutcome (Evaluation.operation SiteObservations.closed
                      (tableOf F G available) op (Operands.eval values arguments)
                      (bodies.denote (Evaluation.meaning SiteObservations.closed (tableOf F G available))))) fun results =>
                    Construction.closedOutcome (next.denote
                      (Evaluation.meaning SiteObservations.closed (tableOf F G available)) (values.prepend results)))
                  walked := by
              intro outputs scope' rest opWalked nextWalked
              obtain ⟨returnedSound, stoppedSound⟩ := walkOperation_sound vocabulary validator (tableOf F G available)
                opWalked holds (Operands.eval values arguments)
                (bodies.denote (Evaluation.meaning SiteObservations.closed (tableOf F G available))) looked
              cases outcome : Construction.closedOutcome (Evaluation.operation SiteObservations.closed
                  (tableOf F G available) op (Operands.eval values arguments)
                  (bodies.denote (Evaluation.meaning SiteObservations.closed (tableOf F G available)))) with
              | returned results =>
                  simp only [Finite.continueWith]
                  obtain ⟨reached, fresh, outputsAgree, length, holds'⟩ := returnedSound results outcome
                  exact WalkSound.after vocabulary validator reached fresh (walkOperation_used vocabulary validator opWalked)
                    (walkRegion_sound fuel available (outputs ++ names) scope' next rest walked distinct nextWalked _ _
                      ((agrees.extend holds.named fresh).prepend results length outputsAgree) holds')
              | stopped reason =>
                  simp only [Finite.continueWith]
                  exact stoppedSound reason outcome
            cases op with
            | mark site =>
                cases arguments
                cases bodies
                exact walkRegion_sound fuel available names scope next steps walked distinct accepted env values agrees holds
            | invoke helper =>
                cases bodies
                cases indexEq : findDefinition available helper with
                | none => simp [indexEq] at accepted
                | some index =>
                    simp only [indexEq] at accepted
                    cases definitionEq : available[index]? with
                    | none => simp [definitionEq] at accepted
                    | some definition =>
                        simp only [definitionEq] at accepted
                        have same := findDefinition_some indexEq definitionEq
                        subst same
                        have prefixDistinct : ((available.take index).map (·.name)).Nodup :=
                          (List.take_sublist index available).map _ |>.nodup distinct
                        have invoked : Evaluation.operation SiteObservations.closed (tableOf F G available)
                            (.invoke definition.helper) (Operands.eval values arguments)
                              (Regions.denote (Evaluation.meaning SiteObservations.closed (tableOf F G available))
                                Regions.nil) =
                            definition.body.denote (Evaluation.meaning SiteObservations.closed
                              (tableOf F G (available.take index))) (Operands.eval values arguments).get :=
                          invoke_tableOf distinct definitionEq _
                        rw [invoked]
                        have calleeSound : ∀ calleeWalked, walkRegion vocabulary validator fuel (available.take index)
                            inputs scope definition.body steps = .ok calleeWalked →
                            WalkSound vocabulary validator steps env scope.used
                              (Construction.closedOutcome
                                (A := Values (assignment F G) (dialect.results (.invoke definition.helper)))
                                (definition.body.denote (Evaluation.meaning
                                SiteObservations.closed (tableOf F G (available.take index)))
                                (Operands.eval values arguments).get)) calleeWalked :=
                          fun calleeWalked calleeWalk => walkRegion_sound fuel (available.take index) inputs scope
                            definition.body steps calleeWalked prefixDistinct calleeWalk env _ inputsAgree
                            ⟨fun name inside => holds.named name (inputsMember name inside), holds.boundedUsed,
                              holds.bounded⟩
                        generalize Construction.closedOutcome
                            (A := Values (assignment F G) (dialect.results (.invoke definition.helper)))
                            (definition.body.denote (Evaluation.meaning
                            SiteObservations.closed (tableOf F G (available.take index)))
                            (Operands.eval values arguments).get) = calleeResult at calleeSound ⊢
                        cases calleeWalk : walkRegion vocabulary validator fuel (available.take index) inputs scope
                            definition.body steps with
                        | error refusal => simp [calleeWalk] at accepted
                        | ok calleeWalked =>
                            have callee := calleeSound calleeWalked calleeWalk
                            cases calleeWalked with
                            | stopped =>
                                simp only [calleeWalk, Except.ok.injEq] at accepted
                                subst accepted
                                cases calleeResult with
                                | returned results => exact callee.elim
                                | stopped reason => exact callee
                            | returned rest returned scope' =>
                                simp only [calleeWalk] at accepted
                                by_cases length : returned.length = definition.helper.outputs.length
                                · simp only [length, ite_true] at accepted
                                  cases calleeResult with
                                  | returned results =>
                                      simp only [Finite.continueWith]
                                      obtain ⟨bound, cost, fresh, reached, returnedAgree, -, holds'⟩ := callee
                                      have nextHolds : ScopeHolds ⟨scope'.used ++ scope.used, scope'.bounded⟩
                                          (returned ++ names) (bound ++ env) :=
                                        ⟨fun name inside => by
                                            rcases List.mem_append.mp inside with inside | inside
                                            · exact List.mem_append_left _ (holds'.named name inside)
                                            · exact List.mem_append_right _ (holds.named name inside),
                                          fun name inside => List.mem_append_left _ (holds'.boundedUsed name inside),
                                          holds'.bounded⟩
                                      exact WalkSound.after vocabulary validator reached fresh
                                        (fun name inside => List.mem_append_right _ inside)
                                        (walkRegion_sound fuel available (returned ++ names) _ next rest walked distinct
                                          accepted _ _ ((agrees.extend holds.named fresh).prepend results length
                                            returnedAgree) nextHolds)
                                  | stopped reason => exact callee
                                · simp [length] at accepted
            | guard =>
                have guardOutcome : Construction.closedOutcome (Evaluation.operation SiteObservations.closed
                    (tableOf F G available) .guard (Operands.eval values arguments)
                    (bodies.denote (Evaluation.meaning SiteObservations.closed (tableOf F G available)))) =
                    if (Operands.eval values arguments).get .here then .returned .nil else .stopped .reject := by
                  rcases arguments with _ | ⟨conditionVariable, _ | _⟩
                  cases bodies
                  change Construction.closedOutcome (if values conditionVariable then PIR.Process.done Values.nil
                    else PIR.Process.halt .reject) = (if values conditionVariable then _ else _)
                  cases values conditionVariable <;> rfl
                rw [guardOutcome]
                obtain ⟨condition₀, conditionFound, conditionLooked⟩ := inputsAgree _ .here
                cases steps with
                | nil => cases accepted
                | cons step rest =>
                    simp only at accepted
                    cases guardEq : guardCondition? step with
                    | none => simp [guardEq] at accepted
                    | some condition =>
                        simp only [guardEq] at accepted
                        by_cases same : inputs = [condition]
                        · simp only [same, ite_true] at accepted
                          have nextAccepted := accepted
                          clear accepted
                          obtain ⟨site, stopSite, rfl⟩ := guardCondition?_some guardEq
                          subst same
                          simp only [Var.index, List.getElem?_cons_zero, Option.some.injEq] at conditionFound
                          subst conditionFound
                          cases decision : (Operands.eval values arguments).get .here with
                          | true =>
                              have conditionLooked : List.lookup condition env = some (.data (.boolean true)) := by
                                rw [← decision]; exact conditionLooked
                              have reached : evalSteps vocabulary validator
                                  (.cond site condition [] [.yield []] [.stop stopSite "reject"] [] :: rest) env =
                                  (evalSteps vocabulary validator rest ([] ++ env)).after 2 :=
                                evalSteps_cond vocabulary validator (decision := true) conditionLooked rfl
                                  (results := []) (cost := 1) rfl rfl
                              simp only [ite_true, Finite.continueWith]
                              exact WalkSound.after vocabulary validator reached (fun _ inside => by simp at inside)
                                (fun _ inside => inside)
                                (walkRegion_sound fuel available names scope next rest walked distinct nextAccepted
                                  env _ agrees holds)
                          | false =>
                              have conditionLooked : List.lookup condition env = some (.data (.boolean false)) := by
                                rw [← decision]; exact conditionLooked
                              simp only [Bool.false_eq_true, ite_false, Finite.continueWith]
                              exact ⟨_, _, evalSteps_cond_stopped vocabulary validator (decision := false)
                                conditionLooked rfl (cause := .explicit .reject) (cost := 1) rfl, rfl⟩
                        · simp [same] at accepted
            | branch captureTypes outputTypes =>
                have branchOutcome : Construction.closedOutcome (Evaluation.operation SiteObservations.closed
                    (tableOf F G available) (.branch captureTypes outputTypes) (Operands.eval values arguments)
                    (bodies.denote (Evaluation.meaning SiteObservations.closed (tableOf F G available)))) =
                    Construction.closedOutcome ((if (Operands.eval values arguments).get .here then
                      (branchRegions bodies).1 else (branchRegions bodies).2).denote
                      (Evaluation.meaning SiteObservations.closed (tableOf F G available))
                      (valuesTail (Operands.eval values arguments)).get) := by
                  rcases bodies with _ | ⟨yes, _ | ⟨no, _ | _⟩⟩
                  rcases arguments with _ | ⟨conditionVariable, captureOperands⟩
                  change Construction.closedOutcome (Evaluation.invokeCallback (if values conditionVariable then
                    (fun captured => yes.denote (Evaluation.meaning SiteObservations.closed (tableOf F G available))
                      captured.get) else (fun captured => no.denote
                      (Evaluation.meaning SiteObservations.closed (tableOf F G available)) captured.get))
                    (Operands.eval values captureOperands)) =
                    Construction.closedOutcome ((if values conditionVariable then yes else no).denote
                      (Evaluation.meaning SiteObservations.closed (tableOf F G available))
                      (Operands.eval values captureOperands).get)
                  cases values conditionVariable <;> rfl
                rw [branchOutcome]
                cases steps with
                | nil => cases accepted
                | cons step rest =>
                    cases step with
                    | cond site condition captures yesSteps noSteps bound =>
                        simp only at accepted
                        by_cases shape : inputs = condition :: captures ∧ bound.length = outputTypes.length
                        · simp only [shape, and_self, ite_true] at accepted
                          obtain ⟨rfl, length⟩ := shape
                          obtain ⟨-, inputsLength⟩ := operandNames_mem arguments inputsEq
                          obtain ⟨condition₀, conditionFound, conditionLooked⟩ := inputsAgree _ .here
                          simp only [Var.index, List.getElem?_cons_zero, Option.some.injEq] at conditionFound
                          subst conditionFound
                          have capturesAgree : NamesAgree captures env (valuesTail (Operands.eval values arguments)).get := by
                            intro ty variable_
                            obtain ⟨name, found, foundLooked⟩ := inputsAgree ty (.there variable_)
                            refine ⟨name, by simpa [Var.index] using found, ?_⟩
                            rw [foundLooked]
                            rcases arguments with _ | ⟨conditionVariable, captureOperands⟩
                            rfl
                          have capturesLooked := lookupAll_of_agrees (valuesTail (Operands.eval values arguments))
                            (by simp only [List.length_cons] at inputsLength; exact Nat.succ.inj inputsLength)
                            capturesAgree
                          cases yesWalk : walkRegion vocabulary validator fuel available captures scope
                              (branchRegions bodies).1 yesSteps with
                          | error refusal => simp [yesWalk] at accepted
                          | ok yesWalked =>
                              cases noWalk : walkRegion vocabulary validator fuel available captures scope
                                  (branchRegions bodies).2 noSteps with
                              | error refusal => simp [yesWalk, noWalk] at accepted
                              | ok noWalked =>
                                  simp only [yesWalk, noWalk] at accepted
                                  by_cases ends : regionEnds yesWalked = true ∧ regionEnds noWalked = true
                                  · simp only [ends, and_self, ite_true] at accepted
                                    cases bindEq : scope.bind bound false with
                                    | none => simp [bindEq] at accepted
                                    | some scope' =>
                                        simp only [bindEq] at accepted
                                        obtain ⟨distinctBound, freshBound, scopeEq⟩ := Scope.bind_eq bindEq
                                        obtain ⟨regionAgree, regionHolds⟩ := region_entered holds
                                          (fun name inside => inputsMember name (List.mem_cons_of_mem _ inside))
                                          capturesLooked capturesAgree
                                        have taken : ∀ (decision : Bool) (takenSteps : List Step) (takenWalked : Walked),
                                            walkRegion vocabulary validator fuel available captures scope
                                              (if decision then (branchRegions bodies).1 else (branchRegions bodies).2)
                                              takenSteps = .ok takenWalked → regionEnds takenWalked = true →
                                            (Operands.eval values arguments).get .here = decision →
                                            evalSteps vocabulary validator (if decision then yesSteps else noSteps)
                                                (captures.zip (encodeValues (valuesTail (Operands.eval values arguments)))) =
                                              evalSteps vocabulary validator takenSteps
                                                (captures.zip (encodeValues (valuesTail (Operands.eval values arguments)))) →
                                            WalkSound vocabulary validator
                                              (.cond site condition captures yesSteps noSteps bound :: rest) env scope.used
                                              (Finite.continueWith (Construction.closedOutcome
                                                ((if (Operands.eval values arguments).get .here then
                                                  (branchRegions bodies).1 else (branchRegions bodies).2).denote
                                                  (Evaluation.meaning SiteObservations.closed (tableOf F G available))
                                                  (valuesTail (Operands.eval values arguments)).get)) fun results =>
                                                Construction.closedOutcome (next.denote
                                                  (Evaluation.meaning SiteObservations.closed (tableOf F G available))
                                                  (values.prepend results))) walked := by
                                          intro decision takenSteps takenWalked takenWalk takenEnds decided sameSteps
                                          have regionSound := walkRegion_sound fuel available captures scope _
                                            takenSteps takenWalked distinct takenWalk _ _ regionAgree regionHolds
                                          have conditionLooked : List.lookup condition env =
                                              some (.data (.boolean decision)) := by
                                            rw [← decided]; exact conditionLooked
                                          rw [decided]
                                          generalize Construction.closedOutcome
                                              ((if decision then (branchRegions bodies).1 else (branchRegions bodies).2).denote
                                              (Evaluation.meaning SiteObservations.closed (tableOf F G available))
                                              (valuesTail (Operands.eval values arguments)).get) = regionResult
                                            at regionSound ⊢
                                          cases regionResult with
                                          | returned results =>
                                              simp only [Finite.continueWith]
                                              obtain ⟨cost, evaluated⟩ := region_values vocabulary validator takenEnds
                                                regionSound
                                              have encodedLength : bound.length = (encodeValues results).length := by
                                                rw [Zkc.Construction.Uniform.encodeValues_length]; exact length
                                              have reached := evalSteps_cond vocabulary validator (rest := rest)
                                                (site := site) (yes := yesSteps) (no := noSteps) (outputs := bound)
                                                conditionLooked capturesLooked (by rw [sameSteps]; exact evaluated)
                                                encodedLength
                                              exact WalkSound.after vocabulary validator reached (fresh_zip freshBound _)
                                                (fun name inside => by
                                                  rw [scopeEq]; exact List.mem_append_right _ inside)
                                                (walkRegion_sound fuel available (bound ++ names) scope' next rest walked
                                                  distinct accepted _ _
                                                  ((agrees.extend holds.named (fresh_zip freshBound _)).prepend results
                                                    length (NamesAgree.zip results env distinctBound length))
                                                  (ScopeHolds.bind holds bindEq encodedLength (fun flag => by cases flag)))
                                          | stopped reason =>
                                              simp only [Finite.continueWith]
                                              obtain ⟨cause, cost, stopped, same⟩ := regionSound
                                              exact ⟨cause, 1 + cost, evalSteps_cond_stopped vocabulary validator
                                                conditionLooked capturesLooked (by rw [sameSteps]; exact stopped), same⟩
                                        by_cases decision : (Operands.eval values arguments).get .here = true
                                        · exact taken true yesSteps yesWalked yesWalk ends.1 decision rfl
                                        · exact taken false noSteps noWalked noWalk ends.2 (by simpa using decision) rfl
                                  · simp [ends] at accepted
                        · simp [shape] at accepted
                    | _ => cases accepted
            | _ =>
                all_goals
                  obtain ⟨⟨outputs, scope', rest⟩, opWalked, nextWalked⟩ := Except.bind_eq_ok accepted
                  exact continued opWalked nextWalked

/-! ## The helper rule -/

/-- A helper the rule accepts is prepared: on arguments of its declared sorts,
its local function hands back exactly the checked helper's results, at the
declared result sorts, or stops in the class the helper stops in. -/
theorem checkHelper_sound {definitions : List CheckedDefinition} (distinct : (definitions.map (·.name)).Nodup)
    {name : String} (accepted : checkHelper vocabulary validator definitions name = .ok ()) :
    Prepared vocabulary validator (tableOf F G definitions) name := by
  unfold checkHelper at accepted
  cases functionEq : validator.function? name with
  | none => simp [functionEq] at accepted
  | some function =>
      cases indexEq : definitions.findIdx? (·.name == name) with
      | none => simp [functionEq, indexEq] at accepted
      | some index =>
          cases definitionEq : definitions[index]? with
          | none => simp [functionEq, indexEq, definitionEq] at accepted
          | some definition =>
              simp only [functionEq, indexEq, definitionEq] at accepted
              have named : definition.name = name := by
                obtain ⟨bound, matches_, -⟩ := List.findIdx?_eq_some_iff_getElem.mp indexEq
                rw [List.getElem?_eq_getElem bound, Option.some.injEq] at definitionEq
                subst definitionEq
                simpa using matches_
              subst named
              by_cases signature : function.inputs.map (·.2.sort) = definition.inputs.map .data ∧
                  function.results.map (·.sort) = definition.outputs.map .data ∧
                  (function.inputs.map (·.1)).Nodup ∧ definition.inputs.all dataType = true
              · rw [ite_eq_left_of_eq_true _ _ (eq_true signature)] at accepted
                obtain ⟨inputSorts, resultSorts, formalsDistinct, data⟩ := signature
                intro callee calleeEq arguments length sorted
                rw [functionEq, Option.some.injEq] at calleeEq
                subst calleeEq
                have formalsLength : (function.inputs.map (·.1)).length = definition.inputs.length := by
                  simpa using congrArg List.length inputSorts
                rw [inputSorts] at sorted
                obtain ⟨values, encoded⟩ := sorted_encoded (tys := definition.inputs) (arguments := arguments)
                  (by rw [← length]; simpa using formalsLength.symm) sorted
                subst encoded
                have decoded := decodeValues_encodeValues values data
                have callEq : callHelper (tableOf F G definitions) definition.name (encodeValues values) =
                    mapOutcome encodeValues (Construction.closedOutcome (definition.body.denote
                      (Evaluation.meaning SiteObservations.closed (tableOf F G (definitions.take index))) values.get)) := by
                  rw [callHelper_tableOf distinct definitionEq _ values decoded, invoke_tableOf distinct definitionEq]
                  rfl
                have prefixDistinct : ((definitions.take index).map (·.name)).Nodup :=
                  (List.take_sublist index definitions).map _ |>.nodup distinct
                have agrees : NamesAgree (function.inputs.map (·.1))
                    ((function.inputs.map (·.1)).zip (encodeValues values)) values.get := by
                  have zipped := NamesAgree.zip values [] formalsDistinct formalsLength
                  rwa [List.append_nil] at zipped
                have holds : ScopeHolds ⟨function.inputs.map (·.1), []⟩ (function.inputs.map (·.1))
                    ((function.inputs.map (·.1)).zip (encodeValues values)) :=
                  ⟨fun _ inside => inside, fun _ inside => by simp at inside, fun _ inside => by simp at inside⟩
                cases walk : walkRegion vocabulary validator helperFuel (definitions.take index)
                    (function.inputs.map (·.1)) ⟨function.inputs.map (·.1), []⟩ definition.body function.body with
                | error refusal => simp [walk] at accepted
                | ok walked =>
                    have sound : WalkSound vocabulary validator function.body
                        ((function.inputs.map (·.1)).zip (encodeValues values)) (function.inputs.map (·.1))
                        (Construction.closedOutcome (definition.body.denote
                          (Evaluation.meaning SiteObservations.closed (tableOf F G (definitions.take index))) values.get))
                        walked :=
                      walkRegion_sound vocabulary validator helperFuel (definitions.take index) _ _ _ _ walked
                        prefixDistinct walk _ _ agrees holds
                    generalize Construction.closedOutcome (definition.body.denote (Evaluation.meaning
                      SiteObservations.closed (tableOf F G (definitions.take index))) values.get) = outcome at sound callEq
                    rw [callEq]
                    cases outcome with
                    | stopped reason =>
                        obtain ⟨cause, cost, stopped, same⟩ := sound
                        rw [stopped]
                        exact same
                    | returned outs =>
                        cases walked with
                        | stopped => exact sound.elim
                        | returned rest returned scope =>
                            obtain ⟨bound, cost, -, reached, returnedAgree, returnedLength, -⟩ := sound
                            simp only [walk] at accepted
                            cases rest with
                            | nil => cases accepted
                            | cons last tail =>
                                cases last with
                                | ret returnedValues =>
                                    cases tail with
                                    | cons _ _ => cases accepted
                                    | nil =>
                                        by_cases sameNames : returnedValues = returned
                                        · subst sameNames
                                          rw [reached, evalSteps_ret vocabulary validator
                                            (lookupAll_of_agrees outs returnedLength returnedAgree)]
                                          refine ⟨rfl, ?_, ?_⟩
                                          · rw [Zkc.Construction.Uniform.encodeValues_length]
                                            simpa using (congrArg List.length resultSorts).symm
                                          · rw [resultSorts]
                                            exact encodeValues_sorted outs
                                        · simp [sameNames] at accepted
                                | _ => cases accepted
              · rw [ite_eq_right_of_eq_false _ _ (eq_false signature)] at accepted
                cases accepted

/-- The helpers the rule accepts against an admitted program are prepared for its
closed helper table. -/
theorem checkHelpers_sound (program : Structured.Program) :
    ∀ {names : List String}, checkHelpers vocabulary validator program names = .ok () →
      ∀ name ∈ names, Prepared vocabulary validator (helperTable program F G) name
  | [], _, name, member => by simp at member
  | first :: rest, accepted, name, member => by
      simp only [checkHelpers] at accepted
      cases firstEq : checkHelper vocabulary validator program.payload.definitions first with
      | error refusal => simp [firstEq] at accepted
      | ok checked =>
          simp only [firstEq] at accepted
          rcases List.mem_cons.mp member with rfl | member
          · rw [helperTable_eq]
            exact checkHelper_sound vocabulary validator program.payload.linked.nodup firstEq
          · exact checkHelpers_sound program accepted name member

/-- Helpers prepared by the rule and helpers prepared by a proof of their own
together prepare every helper a reading calls. -/
theorem prepared_of_cover {table : Structured.Meanings F G} {helpers checked : List String}
    (rule : ∀ name ∈ checked, Prepared vocabulary validator table name)
    (own : ∀ name ∈ helpers, name ∉ checked → Prepared vocabulary validator table name) :
    ∀ name ∈ helpers, Prepared vocabulary validator table name := by
  intro name member
  by_cases inside : name ∈ checked
  · exact rule name inside
  · exact own name member inside

end Operation

end Zkc.Executable
