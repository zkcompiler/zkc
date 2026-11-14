module

public import Zkc.Core.Unelaborate

public section

/-! Elaboration inverts unelaboration: `elaborate (unelaborate typed) = .ok typed`, for
every typed package, without a side condition.

The number of a value is a function of its position and the depth of its context, so
the proof needs no invariant about numbering: `Scope.find?_number` says that looking
the number of a reference up gives the reference back.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## References -/

section References

variable {α : Type}

/-- Every number of a list has, by `typeOf`, the type at its position. -/
@[expose] def NumbersHave (typeOf : Nat → Option α) : List Nat → List α → Prop
  | [], [] => True
  | value :: values, type :: types => typeOf value = some type ∧ NumbersHave typeOf values types
  | [], _ :: _ => False
  | _ :: _, [] => False

theorem typesWith_of_numbersHave {typeOf : Nat → Option α} :
    ∀ {values : List Nat} {types : List α}, NumbersHave typeOf values types →
      typesWith typeOf values = some types
  | [], [], _ => rfl
  | value :: values, type :: types, ⟨first, rest⟩ => by
      simp only [typesWith, first, typesWith_of_numbersHave rest]
  | [], _ :: _, impossible => impossible.elim
  | _ :: _, [], impossible => impossible.elim

theorem NumbersHave.take {typeOf : Nat → Option α} :
    ∀ {values : List Nat} (first : List α) {second : List α},
      NumbersHave typeOf values (first ++ second) → NumbersHave typeOf (values.take first.length) first
  | [], [], _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | [], _ :: _, _, impossible => impossible.elim
  | _ :: _, _ :: first, _, ⟨head, rest⟩ => ⟨head, NumbersHave.take first rest⟩

theorem NumbersHave.drop {typeOf : Nat → Option α} :
    ∀ {values : List Nat} (first : List α) {second : List α},
      NumbersHave typeOf values (first ++ second) → NumbersHave typeOf (values.drop first.length) second
  | _, [], _, have_ => have_
  | [], _ :: _, _, impossible => impossible.elim
  | _ :: _, _ :: first, _, ⟨_, rest⟩ => NumbersHave.drop first rest

theorem numbersHave_numbers {Γ : List α} (scope : Scope Γ) :
    ∀ {types : List α} (operands : Operands Γ types),
      NumbersHave scope.type? (Scope.numbers scope.depth operands) types
  | _, .nil => trivial
  | _, .cons reference rest => ⟨scope.type?_number reference, numbersHave_numbers scope rest⟩

/-- The scope of the inputs of a closed region has their number as its depth. -/
theorem depth_inputs (inputs : List α) : (Scope.empty.bindAll inputs).depth = inputs.length := by
  rw [Scope.depth_bindAll]
  exact Nat.zero_add _

end References

/-! ## Literals -/

theorem elaborateBytes_unelaborate : ∀ (data : List (Fin 256)),
    elaborateBytes (data.map Fin.val) = some data
  | [] => rfl
  | byte :: rest => by
      simp only [List.map_cons, elaborateBytes, byte.isLt, ↓reduceDIte,
        elaborateBytes_unelaborate rest]

theorem elaborateLiteral_unelaborate : ∀ (literal : Literal),
    elaborateLiteral (unelaborateLiteral literal) = some literal
  | .nat _ => rfl
  | .bool _ => rfl
  | .fin _ value => by simp only [unelaborateLiteral, elaborateLiteral, value.isLt, ↓reduceDIte]
  | .nominal _ _ => rfl
  | .bytes data => by
      simp only [unelaborateLiteral, elaborateLiteral, elaborateBytes_unelaborate]

/-! ## Declared types

A type of the package names its declarations with the use and the shape that they have,
so reading the stripped type in the type table gives it back. -/

mutual
  theorem Ty.fill_strip (typeTable : TypeTable) :
      ∀ (type : Ty), Ty.named typeTable type = true → Ty.fill typeTable type.strip = some type
    | .bool, _ => rfl
    | .nat, _ => rfl
    | .fin _, _ => rfl
    | .nominal _, _ => rfl
    | .seq element size, named => by
        simp only [Ty.strip, Ty.fill, Ty.fill_strip typeTable element named]
    | .tuple components, named => by
        simp only [Ty.strip, Ty.fill, Ty.fillAll_stripAll typeTable components named]
    | .record declaration use fields, named => by
        simp only [Ty.named, Bool.and_eq_true, decide_eq_true_eq] at named
        simp only [Ty.strip, Ty.fill, named.1]
    | .variant declaration alternatives, named => by
        simp only [Ty.named, Bool.and_eq_true, decide_eq_true_eq] at named
        simp only [Ty.strip, Ty.fill, named.1]

  theorem Ty.fillAll_stripAll (typeTable : TypeTable) :
      ∀ (types : List Ty), Ty.allNamed typeTable types = true →
        Ty.fillAll typeTable (Ty.stripAll types) = some types
    | [], _ => rfl
    | type :: rest, named => by
        simp only [Ty.allNamed, Bool.and_eq_true] at named
        simp only [Ty.stripAll, Ty.fillAll, Ty.fill_strip typeTable type named.1,
          Ty.fillAll_stripAll typeTable rest named.2]
end

/-- The tag of a choice whose type is a type of the package is what its raw form stands
for. -/
theorem ChoiceTag.fill_strip (typeTable : TypeTable) :
    ∀ (tag : ChoiceTag), Ty.named typeTable tag.type = true →
      ChoiceTag.fill typeTable tag.strip = some tag
  | .condition, _ => rfl
  | .arm _, _ => rfl
  | .alternative declaration alternatives, named => by
      simp only [Ty.named, Bool.and_eq_true, decide_eq_true_eq] at named
      simp only [ChoiceTag.strip, ChoiceTag.fill, named.1]

theorem Located.fillAll_stripAll (typeTable : TypeTable) :
    ∀ (types : List Located), Located.allNamed typeTable types = true →
      Located.fillAll typeTable (Located.stripAll types) = some types
  | [], _ => rfl
  | ⟨type, holder⟩ :: rest, named => by
      simp only [Located.allNamed, Bool.and_eq_true] at named
      simp only [Located.stripAll, Located.strip, Located.fillAll,
        Ty.fill_strip typeTable type named.1, Located.fillAll_stripAll typeTable rest named.2]

theorem Located.allNamed_atRole (typeTable : TypeTable) (role : Nat) :
    ∀ (types : List Ty),
      Located.allNamed typeTable (Located.atRole role types) = Ty.allNamed typeTable types
  | [] => rfl
  | type :: rest => by
      show (Ty.named typeTable type && Located.allNamed typeTable (Located.atRole role rest)) = _
      rw [Located.allNamed_atRole typeTable role rest]
      rfl

theorem Located.allNamed_append (typeTable : TypeTable) :
    ∀ (first second : List Located), Located.allNamed typeTable (first ++ second) =
      (Located.allNamed typeTable first && Located.allNamed typeTable second)
  | [], _ => rfl
  | located :: rest, second => by
      show (Ty.named typeTable located.type && Located.allNamed typeTable (rest ++ second)) =
        ((Ty.named typeTable located.type && Located.allNamed typeTable rest) &&
          Located.allNamed typeTable second)
      rw [Located.allNamed_append typeTable rest second, Bool.and_assoc]

theorem Ty.allNamed_head {typeTable : TypeTable} {type : Ty} {rest : List Ty}
    (named : Ty.allNamed typeTable (type :: rest) = true) : Ty.named typeTable type = true := by
  simp only [Ty.allNamed, Bool.and_eq_true] at named
  exact named.1

theorem Ty.named_element {typeTable : TypeTable} {element : Ty} {size : Option Nat}
    (named : Ty.named typeTable (.seq element size) = true) : Ty.named typeTable element = true :=
  named

theorem Ty.named_tuple {typeTable : TypeTable} {components : List Ty}
    (named : Ty.named typeTable (.tuple components) = true) :
    Ty.allNamed typeTable components = true :=
  named

theorem Ty.named_record {typeTable : TypeTable} {declaration : Nat} {use : Use} {fields : List Ty}
    (named : Ty.named typeTable (.record declaration use fields) = true) :
    typeTable.records[declaration]? = some ⟨use, fields⟩ := by
  simp only [Ty.named, Bool.and_eq_true, decide_eq_true_eq] at named
  exact named.1

theorem Ty.named_variant {typeTable : TypeTable} {declaration : Nat} {alternatives : List Ty}
    (named : Ty.named typeTable (.variant declaration alternatives) = true) :
    typeTable.variants[declaration]? = some ⟨alternatives⟩ := by
  simp only [Ty.named, Bool.and_eq_true, decide_eq_true_eq] at named
  exact named.1

/-! ## Operations the core owns -/

/-- An operation the core owns whose operand and result types are types of the package. -/
theorem elaborateBuiltin_unelaborate (typeTable : TypeTable) : ∀ (operation : Builtin),
    Ty.allNamed typeTable operation.arguments = true →
      Ty.allNamed typeTable operation.results = true →
        elaborateBuiltin typeTable (unelaborateBuiltin operation) = some operation
  | .natAdd, _, _ | .natMul, _, _ | .natPow, _, _ | .natEqual, _, _ | .natLess, _, _
  | .natSub, _, _ | .natDiv, _, _ | .natRem, _, _ | .boolAnd, _, _ | .boolOr, _, _
  | .boolNot, _, _ | .boolEqual, _, _ | .natBelow _, _, _ | .finToNat _, _, _ => rfl
  | .seqLength element _, arguments, _ | .seqAt element _, arguments, _
  | .seqSlice element .., arguments, _ | .seqConcat element .., arguments, _
  | .seqSized element _, arguments, _ | .seqUnsized element _, arguments, _ => by
      simp only [unelaborateBuiltin, elaborateBuiltin,
        Ty.fill_strip typeTable element (Ty.named_element (Ty.allNamed_head arguments)),
        Option.map_some]
  | .seqFill element _, arguments, _ => by
      simp only [unelaborateBuiltin, elaborateBuiltin,
        Ty.fill_strip typeTable element (Ty.allNamed_head arguments), Option.map_some]
  | .seqMake element _, _, results => by
      simp only [unelaborateBuiltin, elaborateBuiltin,
        Ty.fill_strip typeTable element (Ty.named_element (Ty.allNamed_head results)),
        Option.map_some]
  | .finWiden _ _ fits, _, _ => by
      simp only [unelaborateBuiltin, elaborateBuiltin, fits, ↓reduceDIte]
  | .tupleMake components, _, results => by
      simp only [unelaborateBuiltin, elaborateBuiltin,
        Ty.fillAll_stripAll typeTable components (Ty.named_tuple (Ty.allNamed_head results)),
        Option.map_some]
  | .tupleGet components type position, arguments, _ => by
      show elaborateBuiltin typeTable (.tupleGet (Ty.stripAll components) position.index) = _
      dsimp only [elaborateBuiltin]
      rw [Ty.fillAll_stripAll typeTable components (Ty.named_tuple (Ty.allNamed_head arguments))]
      dsimp only
      split
      · rename_i found' found
        have same : found' = type := Option.some.inj (found.symm.trans position.valid)
        subst same
        rfl
      · rename_i missing
        rw [position.valid] at missing
        cases missing
  | .recordMake declaration use fields, _, results => by
      simp only [unelaborateBuiltin, elaborateBuiltin,
        Ty.named_record (Ty.allNamed_head results)]
  | .recordGet declaration use fields type position, arguments, _ => by
      show elaborateBuiltin typeTable (.recordGet declaration position.index) = _
      dsimp only [elaborateBuiltin]
      rw [Ty.named_record (Ty.allNamed_head arguments)]
      dsimp only
      split
      · rename_i found' found
        have same : found' = type := Option.some.inj (found.symm.trans position.valid)
        subst same
        rfl
      · rename_i missing
        rw [position.valid] at missing
        cases missing
  | .variantMake declaration alternatives payload position, _, results => by
      show elaborateBuiltin typeTable (.variantMake declaration position.index) = _
      dsimp only [elaborateBuiltin]
      rw [Ty.named_variant (Ty.allNamed_head results)]
      dsimp only
      split
      · rename_i found' found
        have same : found' = payload := Option.some.inj (found.symm.trans position.valid)
        subst same
        rfl
      · rename_i missing
        rw [position.valid] at missing
        cases missing

/-! ## Types of a context

Every value of a region has a type of the package: the inputs of a definition are
checked, the results of every operation are checked, and the inputs of a nested region
are operands of the operation or, for a `match`, a payload of the variant an operand has.
-/

theorem Ty.allNamed_iff (typeTable : TypeTable) :
    ∀ (types : List Ty), Ty.allNamed typeTable types = true ↔
      ∀ type ∈ types, Ty.named typeTable type = true
  | [] => by simp only [Ty.allNamed, List.not_mem_nil, false_implies, implies_true]
  | type :: rest => by
      simp only [Ty.allNamed, Bool.and_eq_true, Ty.allNamed_iff typeTable rest, List.mem_cons,
        forall_eq_or_imp]

/-- The collected types of a loop whose results have types of the package are types of
the package. -/
theorem Ty.allNamed_collected {typeTable : TypeTable} {carried collected : List Ty}
    {size : Option Nat}
    (named : Ty.allNamed typeTable (collectedSequences size collected ++ carried) = true) :
    Ty.allNamed typeTable collected = true := by
  rw [Ty.allNamed_iff] at named ⊢
  intro type member
  have sequence := named (.seq type size)
    (List.mem_append_left _ (List.mem_map_of_mem (f := fun type => Ty.seq type size) member))
  exact Ty.named_element sequence

theorem Located.allNamed_iff (typeTable : TypeTable) :
    ∀ (types : List Located), Located.allNamed typeTable types = true ↔
      ∀ located ∈ types, Ty.named typeTable located.type = true
  | [] => by simp only [Located.allNamed, List.not_mem_nil, false_implies, implies_true]
  | located :: rest => by
      simp only [Located.allNamed, Bool.and_eq_true, Located.allNamed_iff typeTable rest,
        List.mem_cons, forall_eq_or_imp]

theorem mem_bindAll {α : Type} {item : α} :
    ∀ {Γ : List α} (added : List α), item ∈ bindAll Γ added → item ∈ Γ ∨ item ∈ added
  | _, [], member => .inl member
  | _, ty :: rest, member => by
      rcases mem_bindAll rest member with inside | later
      · rcases List.mem_cons.mp inside with rfl | earlier
        · exact .inr (List.mem_cons_self ..)
        · exact .inl earlier
      · exact .inr (List.mem_cons_of_mem _ later)

/-- Every type of a context is a type of the package. -/
abbrev ContextNamed (typeTable : TypeTable) (Γ : List Ty) : Prop :=
  ∀ type ∈ Γ, Ty.named typeTable type = true

/-- The collected types of a `repeat` whose results have types of the package are types of
the package. -/
theorem Located.allNamed_collected {typeTable : TypeTable} {carried collected : List Located}
    {size : Option Nat}
    (named : Located.allNamed typeTable (collectedSequencesAt size collected ++ carried) = true) :
    Located.allNamed typeTable collected = true := by
  rw [Located.allNamed_iff] at named ⊢
  intro located member
  have sequence := named ⟨.seq located.type size, located.holder⟩
    (List.mem_append_left _
      (List.mem_map_of_mem
        (f := fun located : Located => (⟨Ty.seq located.type size, located.holder⟩ : Located))
        member))
  exact Ty.named_element sequence

/-- Every located type of a context is a type of the package. -/
abbrev LocatedNamed (typeTable : TypeTable) (Γ : List Located) : Prop :=
  ∀ located ∈ Γ, Ty.named typeTable located.type = true

theorem ContextNamed.bindAll {typeTable : TypeTable} {Γ : List Ty} (named : ContextNamed typeTable Γ)
    {added : List Ty} (addedNamed : Ty.allNamed typeTable added = true) :
    ContextNamed typeTable (Zkc.Source.bindAll Γ added) := fun type member =>
  (mem_bindAll added member).elim (named type)
    ((Ty.allNamed_iff typeTable added).mp addedNamed type)

theorem LocatedNamed.bindAll {typeTable : TypeTable} {Γ : List Located}
    (named : LocatedNamed typeTable Γ) {added : List Located}
    (addedNamed : Located.allNamed typeTable added = true) :
    LocatedNamed typeTable (Zkc.Source.bindAll Γ added) := fun located member =>
  (mem_bindAll added member).elim (named located)
    ((Located.allNamed_iff typeTable added).mp addedNamed located)

theorem ContextNamed.inputs {typeTable : TypeTable} {inputs : List Ty}
    (named : ContextNamed typeTable inputs) :
    ContextNamed typeTable (Zkc.Source.bindAll [] inputs) :=
  fun type member => (mem_bindAll inputs member).elim (fun outside => nomatch outside) (named type)

theorem LocatedNamed.inputs {typeTable : TypeTable} {inputs : List Located}
    (named : LocatedNamed typeTable inputs) :
    LocatedNamed typeTable (Zkc.Source.bindAll [] inputs) :=
  fun located member =>
    (mem_bindAll inputs member).elim (fun outside => nomatch outside) (named located)

/-- The operands of a context of types of the package have types of the package. -/
theorem Operands.named {typeTable : TypeTable} {Γ : List Ty} (named : ContextNamed typeTable Γ) :
    ∀ {types : List Ty} (_ : Operands Γ types), Ty.allNamed typeTable types = true
  | _, .nil => rfl
  | _, .cons (ty := type) reference rest => by
      show (Ty.named typeTable type && Ty.allNamed typeTable _) = true
      rw [named type (List.mem_of_getElem? reference.valid), Operands.named named rest]
      rfl

theorem Operands.locatedNamed {typeTable : TypeTable} {Γ : List Located}
    (named : LocatedNamed typeTable Γ) :
    ∀ {types : List Located} (_ : Operands Γ types), Located.allNamed typeTable types = true
  | _, .nil => rfl
  | _, .cons (ty := located) reference rest => by
      show (Ty.named typeTable located.type && Located.allNamed typeTable _) = true
      rw [named located (List.mem_of_getElem? reference.valid), Operands.locatedNamed named rest]
      rfl

section Inputs

variable {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}

/-- The inputs of the regions of a local operation whose operands have types of the
package have types of the package. -/
theorem LocalOp.inputsNamed :
    ∀ (op : LocalOp operations functions deployed), Ty.allNamed typeTable op.arguments = true →
      ∀ signature ∈ op.regions, ContextNamed typeTable signature.1
  | .conditional captures outputs, named, signature, member, type, inside => by
      have each := (Ty.allNamed_iff typeTable _).mp named
      have same : signature = (captures, outputs) := by
        simp only [LocalOp.regions, List.mem_cons, List.not_mem_nil, or_false, or_self] at member
        exact member
      subst same
      exact each type (List.mem_cons_of_mem _ inside)
  | .match declaration alternatives captures outputs, named, signature, member, type, inside => by
      have each := (Ty.allNamed_iff typeTable _).mp named
      simp only [LocalOp.regions, List.mem_map] at member
      obtain ⟨payload, found, rfl⟩ := member
      rcases List.mem_cons.mp inside with rfl | captured
      · have variantNamed := each _ (List.mem_cons_self ..)
        simp only [Ty.named, Bool.and_eq_true] at variantNamed
        exact (Ty.allNamed_iff typeTable alternatives).mp variantNamed.2 type found
      · exact each type (List.mem_cons_of_mem _ captured)
  | .loop count carried collected captures, named, signature, member, type, inside => by
      have same : signature = (.nat :: (carried ++ captures), collected ++ carried) := by
        simp only [LocalOp.regions, List.mem_cons, List.not_mem_nil, or_false] at member
        exact member
      subst same
      cases count with
      | static _ =>
          have each := (Ty.allNamed_iff typeTable (carried ++ captures)).mp named
          rcases List.mem_cons.mp inside with rfl | later
          · rfl
          · exact each type later
      | runtime _ =>
          exact (Ty.allNamed_iff typeTable (.nat :: (carried ++ captures))).mp named type inside
  | .op .., _, _, member, _, _ | .call .., _, _, member, _, _ | .guard _, _, _, member, _, _
  | .literal _, _, _, member, _, _ | .builtin _, _, _, member, _, _ => nomatch member

/-- The inputs of the regions of a protocol operation whose operands have types of the
package have types of the package. -/
theorem ProtocolOp.inputsNamed :
    ∀ (op : ProtocolOp operations functions protocols deployed),
      Located.allNamed typeTable op.arguments = true →
        ∀ signature ∈ op.regions, LocatedNamed typeTable signature.1
  | .repeat participants count carried collected captures covered, named, signature, member,
      located, inside => by
      have same : signature =
          (Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried) := by
        simp only [ProtocolOp.regions, List.mem_cons, List.not_mem_nil, or_false] at member
        exact member
      subst same
      -- An iteration number is a `nat`; the other inputs are operands.
      rcases List.mem_append.mp inside with number | operand
      · obtain ⟨role, _, rfl⟩ := List.mem_map.mp number
        rfl
      · cases count with
        | static _ => exact (Located.allNamed_iff typeTable _).mp named located operand
        | runtime _ =>
            exact (Located.allNamed_iff typeTable _).mp named located
              (List.mem_append_right _ operand)
  | .choose participants tag captures outputs covered, named, signature, member, located,
      inside => by
      have each := (Located.allNamed_iff typeTable _).mp named
      cases tag with
      | condition =>
          have same : signature = (captures, outputs) := List.eq_of_mem_replicate member
          subst same
          exact each located (List.mem_append_right _ inside)
      | arm count =>
          have same : signature = (captures, outputs) := List.eq_of_mem_replicate member
          subst same
          exact each located (List.mem_append_right _ inside)
      | alternative declaration alternatives =>
          -- A payload is an alternative of the variant that a participant holds; the other
          -- inputs are captures.
          simp only [ProtocolOp.regions, ChoiceTag.regions, List.mem_map] at member
          obtain ⟨payload, found, rfl⟩ := member
          rcases List.mem_append.mp inside with copy | captured
          · obtain ⟨role, held, rfl⟩ := List.mem_map.mp copy
            have variantNamed := each ⟨.variant declaration alternatives, role⟩
              (List.mem_append_left _ (List.mem_map.mpr ⟨role, held, rfl⟩))
            simp only [Ty.named, Bool.and_eq_true] at variantNamed
            exact (Ty.allNamed_iff typeTable alternatives).mp variantNamed.2 payload found
          · exact each located (List.mem_append_right _ captured)
  | .at .., _, _, member, _, _ | .exchange .., _, _, member, _, _ | .draw .., _, _, member, _, _
  | .sample .., _, _, member, _, _ | .apply .., _, _, member, _, _ => nomatch member

end Inputs

/-! ## The residual checks of regions -/

section Checks

variable {typeTable : TypeTable}

theorem localRegionViolation_letOp {operations : List OperationSignature}
    {functions : List FunctionHeader} {deployed : Bool} {Γ out : List Ty}
    {op : LocalOp operations functions deployed}
    {arguments : Operands Γ (LocalOp.arguments op)}
    {bodies : Regions (LocalDialect operations functions deployed) (LocalOp.regions op)}
    {next : Region (LocalDialect operations functions deployed) (bindAll Γ (LocalOp.results op)) out}
    (clean : localRegionViolation typeTable
      (Region.letOp (dialect := LocalDialect operations functions deployed) op arguments bodies
        next) = none) :
    Ty.allNamed typeTable (LocalOp.results op) = true ∧
      localRegionsViolation typeTable bodies = none ∧ localRegionViolation typeTable next = none := by
  rw [localRegionViolation] at clean
  cases named : Ty.allNamed typeTable (LocalOp.results op) with
  | false =>
      rw [named] at clean
      cases clean
  | true =>
      rw [named] at clean
      exact ⟨rfl, earlierViolation_both clean⟩

theorem localRegionViolation_bind {operations : List OperationSignature}
    {functions : List FunctionHeader} {deployed : Bool} {Γ mid out : List Ty}
    {body : Region (LocalDialect operations functions deployed) Γ mid}
    {next : Region (LocalDialect operations functions deployed) (bindAll Γ mid) out}
    (clean : localRegionViolation typeTable (Region.bind body next) = none) :
    Ty.allNamed typeTable mid = true ∧
      localRegionViolation typeTable body = none ∧ localRegionViolation typeTable next = none := by
  rw [localRegionViolation] at clean
  cases named : Ty.allNamed typeTable mid with
  | false =>
      rw [named] at clean
      cases clean
  | true =>
      rw [named] at clean
      exact ⟨rfl, earlierViolation_both clean⟩

theorem protocolRegionSites_letOp {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
    {roles : Nat} {enclosing : Option (List Nat)} {sites result : List Nat}
    {Γ out : List Located} {op : ProtocolOp operations functions protocols deployed}
    {arguments : Operands Γ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions protocols deployed)
      (ProtocolOp.regions op)}
    {next : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll Γ (ProtocolOp.results op)) out}
    (clean : protocolRegionSites typeTable roles enclosing
      (Region.letOp (dialect := ProtocolDialect operations functions protocols deployed) op
        arguments bodies next) sites = .ok result) :
    ProtocolOp.violation typeTable roles enclosing op = none ∧
      Located.allNamed typeTable (ProtocolOp.results op) = true ∧
      ∃ middle, protocolRegionsSites typeTable roles (ProtocolOp.enclosing enclosing op) bodies
          (ProtocolOp.sites op ++ sites) = .ok middle ∧
        protocolRegionSites typeTable roles enclosing next middle = .ok result := by
  unfold protocolRegionSites at clean
  split at clean
  · cases clean
  · rename_i opClean
    cases named : Located.allNamed typeTable (ProtocolOp.results op) with
    | false =>
        rw [named] at clean
        cases clean
    | true =>
        rw [named] at clean
        simp only [Bool.cond_true] at clean
        split at clean
        · cases clean
        · rename_i middle nested
          exact ⟨opClean, rfl, middle, nested, clean⟩

theorem protocolRegionSites_bind {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
    {roles : Nat} {enclosing : Option (List Nat)} {sites result : List Nat}
    {Γ mid out : List Located}
    {body : Region (ProtocolDialect operations functions protocols deployed) Γ mid}
    {next : Region (ProtocolDialect operations functions protocols deployed) (bindAll Γ mid) out}
    (clean : protocolRegionSites typeTable roles enclosing (Region.bind body next) sites =
      .ok result) :
    Located.allNamed typeTable mid = true ∧
      ∃ middle, protocolRegionSites typeTable roles enclosing body sites = .ok middle ∧
        protocolRegionSites typeTable roles enclosing next middle = .ok result := by
  unfold protocolRegionSites at clean
  cases named : Located.allNamed typeTable mid with
  | false =>
      rw [named] at clean
      cases clean
  | true =>
      rw [named] at clean
      simp only [Bool.cond_true] at clean
      split at clean
      · cases clean
      · rename_i middle first
        exact ⟨rfl, middle, first, clean⟩

end Checks

/-! ## Local regions -/

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool} (typeTable : TypeTable) (rows : Scope operations) (callees : Scope functions)

/-- Every nested region elaborates from its raw syntax to itself. -/
def LocalRegionsOk : {signatures : List (List Ty × List Ty)} →
    Regions (LocalDialect operations functions deployed) signatures → Prop
  | _, .nil => True
  | _, .cons (inputs := inputs) (outputs := outputs) body tail =>
      elaborateLocalRegion typeTable rows callees deployed (bindAll [] inputs)
          (Scope.empty.bindAll inputs) outputs
          (unelaborateLocalRegion callees.depth inputs.length body) = .ok body ∧
        LocalRegionsOk tail

/-- The arms of a `match`, given that each elaborates to itself. -/
theorem elaborateLocalArms_unelaborate :
    ∀ {signatures : List (List Ty × List Ty)}
      (bodies : Regions (LocalDialect operations functions deployed) signatures),
      LocalRegionsOk typeTable rows callees bodies →
        elaborateLocalArms typeTable rows callees deployed signatures
            (.ofList (unelaborateLocalRegions callees.depth bodies)) = .ok bodies
  | _, .nil, _ => rfl
  | _, .cons body tail, bothOk => by
      have bodyOk := bothOk.1
      have tailOk := elaborateLocalArms_unelaborate tail bothOk.2
      simp only [unelaborateLocalRegions, Raw.LocalArms.ofList, elaborateLocalArms, bodyOk, tailOk]

/-- One local operation: given operand numbers of the operation's argument types, operand
and result types that are types of the package, and nested regions that elaborate to
themselves. -/
theorem elaborateLocalStep_unelaborate (typeOf : Nat → Option Ty) :
    ∀ (op : LocalOp operations functions deployed)
      (bodies : Regions (LocalDialect operations functions deployed) op.regions) (values : List Nat),
      NumbersHave typeOf values op.arguments →
      (Ty.allNamed typeTable op.arguments && Ty.allNamed typeTable op.results) = true →
      LocalRegionsOk typeTable rows callees bodies →
        elaborateLocalStep typeTable rows callees deployed typeOf
            (unelaborateLocalStep callees.depth op values
              (unelaborateLocalRegions callees.depth bodies)) =
          .ok ⟨op, bodies, values⟩
  | .op row applies, .nil, values, _, _, _ => by
      simp only [unelaborateLocalStep, elaborateLocalStep, Scope.at?_index, applies, ↓reduceDIte]
  | .call callee permitted, .nil, values, _, _, _ => by
      simp only [unelaborateLocalStep, elaborateLocalStep, Scope.value?_number, permitted,
        ↓reduceDIte]
  | .conditional captures outputs, .cons onTrue (.cons onFalse .nil), condition :: values,
      ⟨_, typed⟩, named, ⟨trueOk, falseOk, _⟩ => by
      simp only [Bool.and_eq_true] at named
      simp only [unelaborateLocalStep, unelaborateLocalRegions, elaborateLocalStep,
        typesWith_of_numbersHave typed, Ty.fillAll_stripAll typeTable outputs named.2, trueOk,
        falseOk]
  | .match declaration alternatives captures outputs, bodies, value :: values, ⟨_, typed⟩, named,
      bodiesOk => by
      simp only [Bool.and_eq_true] at named
      have arms := elaborateLocalArms_unelaborate typeTable rows callees bodies bodiesOk
      simp only [unelaborateLocalStep, elaborateLocalStep,
        Ty.named_variant (Ty.allNamed_head named.1), typesWith_of_numbersHave typed,
        Ty.fillAll_stripAll typeTable outputs named.2, arms]
  | .loop (.static count) carried collected captures, .cons body .nil, values, typed, named,
      ⟨bodyOk, _⟩ => by
      simp only [Bool.and_eq_true] at named
      simp only [unelaborateLocalStep, unelaborateLocalRegions, elaborateLocalStep,
        typesWith_of_numbersHave (NumbersHave.take carried typed),
        typesWith_of_numbersHave (NumbersHave.drop carried typed),
        Ty.fillAll_stripAll typeTable collected (Ty.allNamed_collected named.2), bodyOk,
        Raw.LoopCount.typed, Raw.LoopCount.operands, List.take_append_drop, List.nil_append]
  | .loop (.runtime maximum) carried collected captures, .cons body .nil, count :: values,
      ⟨_, typed⟩, named, ⟨bodyOk, _⟩ => by
      simp only [Bool.and_eq_true] at named
      simp only [unelaborateLocalStep, unelaborateLocalRegions, elaborateLocalStep,
        typesWith_of_numbersHave (NumbersHave.take carried typed),
        typesWith_of_numbersHave (NumbersHave.drop carried typed),
        Ty.fillAll_stripAll typeTable collected (Ty.allNamed_collected named.2), bodyOk,
        Raw.LoopCount.typed, Raw.LoopCount.operands, List.take_append_drop, List.cons_append,
        List.nil_append]
  | .guard reason, .nil, [condition], _, _, _ => rfl
  | .guard _, .nil, [], impossible, _, _ => impossible.elim
  | .guard _, .nil, _ :: _ :: _, impossible, _, _ => impossible.2.elim
  | .literal value, .nil, [], _, _, _ => by
      simp only [unelaborateLocalStep, elaborateLocalStep, elaborateLiteral_unelaborate]
  | .literal _, .nil, _ :: _, impossible, _, _ => impossible.elim
  | .builtin operation, .nil, values, _, named, _ => by
      simp only [Bool.and_eq_true] at named
      simp only [unelaborateLocalStep, elaborateLocalStep,
        elaborateBuiltin_unelaborate typeTable operation named.1 named.2]
  | .conditional .., _, [], impossible, _, _ => impossible.elim
  | .match .., _, [], impossible, _, _ => impossible.elim
  | .loop (.runtime _) .., _, [], impossible, _, _ => impossible.elim

mutual
  theorem elaborateLocalRegion_unelaborate {Γ out : List Ty} :
      ∀ (region : Region (LocalDialect operations functions deployed) Γ out) (scope : Scope Γ),
        ContextNamed typeTable Γ → localRegionViolation typeTable region = none →
          elaborateLocalRegion typeTable rows callees deployed Γ scope out
            (unelaborateLocalRegion callees.depth scope.depth region) = .ok region
    | .ret values, scope, _, _ => by
        simp only [unelaborateLocalRegion, elaborateLocalRegion, Scope.operands?_numbers]
    | .stop _, _, _, _ => rfl
    | .letOp op arguments bodies rest, scope, named, clean => by
        obtain ⟨resultsNamed, bodiesClean, restClean⟩ := localRegionViolation_letOp clean
        have argumentsNamed := Operands.named named arguments
        have step := elaborateLocalStep_unelaborate typeTable rows callees scope.type? op bodies
          (Scope.numbers scope.depth arguments) (numbersHave_numbers scope arguments)
          (by rw [argumentsNamed, resultsNamed]; rfl)
          (elaborateLocalRegions_unelaborate bodies (LocalOp.inputsNamed op argumentsNamed)
            bodiesClean)
        have restOk := elaborateLocalRegion_unelaborate rest (scope.bindAll (LocalOp.results op))
          (named.bindAll resultsNamed) restClean
        rw [Scope.depth_bindAll] at restOk
        have found := Scope.operands?_numbers scope arguments
        simp only [unelaborateLocalRegion, elaborateLocalRegion, step, found, restOk]
    | .bind (mid := mid) body rest, scope, named, clean => by
        obtain ⟨midNamed, bodyClean, restClean⟩ := localRegionViolation_bind clean
        have bodyOk := elaborateLocalRegion_unelaborate body scope named bodyClean
        have restOk := elaborateLocalRegion_unelaborate rest (scope.bindAll mid)
          (named.bindAll midNamed) restClean
        rw [Scope.depth_bindAll] at restOk
        simp only [unelaborateLocalRegion, elaborateLocalRegion,
          Ty.fillAll_stripAll typeTable mid midNamed, bodyOk, restOk]

  theorem elaborateLocalRegions_unelaborate {signatures : List (List Ty × List Ty)} :
      ∀ (bodies : Regions (LocalDialect operations functions deployed) signatures),
        (∀ signature ∈ signatures, ContextNamed typeTable signature.1) →
          localRegionsViolation typeTable bodies = none →
            LocalRegionsOk typeTable rows callees bodies
    | .nil, _, _ => trivial
    | .cons (inputs := inputs) body tail, named, clean => by
        rw [localRegionsViolation] at clean
        have both := earlierViolation_both clean
        have bodyOk := elaborateLocalRegion_unelaborate body (Scope.empty.bindAll inputs)
          (ContextNamed.inputs (named _ (List.mem_cons_self ..))) both.1
        rw [depth_inputs] at bodyOk
        exact ⟨bodyOk, elaborateLocalRegions_unelaborate tail
          (fun signature member => named signature (List.mem_cons_of_mem _ member)) both.2⟩
end

end Local

/-! ## Protocol regions -/

section Protocol

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool} (typeTable : TypeTable)
  (rows : Scope operations) (callees : Scope functions) (applied : Scope protocols)

def ProtocolRegionsOk : {signatures : List (List Located × List Located)} →
    Regions (ProtocolDialect operations functions protocols deployed) signatures → Prop
  | _, .nil => True
  | _, .cons (inputs := inputs) (outputs := outputs) body tail =>
      elaborateProtocolRegion typeTable rows callees applied deployed (bindAll [] inputs)
          (Scope.empty.bindAll inputs) outputs
          (unelaborateProtocolRegion callees.depth applied.depth inputs.length body) = .ok body ∧
        ProtocolRegionsOk tail

/-- Values at located types of one role have, without holders, the local types. -/
theorem numbersHave_localType {Γ : List Located} (scope : Scope Γ) (role : Nat) :
    ∀ {values : List Nat} {types : List Ty},
      NumbersHave scope.type? values (Located.atRole role types) →
        NumbersHave (localType scope) values types
  | [], [], _ => trivial
  | value :: values, type :: types, ⟨first, rest⟩ =>
      ⟨by simp only [localType, first], numbersHave_localType scope role rest⟩
  | [], _ :: _, impossible => impossible.elim
  | _ :: _, [], impossible => impossible.elim

theorem length_ofRoles (type : Ty) (roles : List Nat) :
    (Located.ofRoles type roles).length = roles.length := by
  simp [Located.ofRoles]

/-- The arms of a `choose`, given that each elaborates to itself. -/
theorem elaborateProtocolArms_unelaborate :
    ∀ {signatures : List (List Located × List Located)}
      (bodies : Regions (ProtocolDialect operations functions protocols deployed) signatures),
      ProtocolRegionsOk typeTable rows callees applied bodies →
        elaborateProtocolArms typeTable rows callees applied deployed signatures
            (.ofList (unelaborateProtocolRegions callees.depth applied.depth bodies)) =
          .ok bodies
  | _, .nil, _ => rfl
  | _, .cons body tail, bothOk => by
      have bodyOk := bothOk.1
      have tailOk := elaborateProtocolArms_unelaborate tail bothOk.2
      simp only [unelaborateProtocolRegions, Raw.ProtocolArms.ofList, elaborateProtocolArms, bodyOk,
        tailOk]

/-- One protocol operation, given its typed operands, operand and result types that are
types of the package, local regions without a violation, and nested protocol regions
that elaborate to themselves. -/
theorem elaborateProtocolStep_unelaborate {Γ : List Located} (scope : Scope Γ) (roles : Nat)
    (enclosing : Option (List Nat)) :
    ∀ (op : ProtocolOp operations functions protocols deployed)
      (bodies : Regions (ProtocolDialect operations functions protocols deployed) op.regions)
      (arguments : Operands Γ op.arguments),
      ProtocolOp.violation typeTable roles enclosing op = none →
      (Located.allNamed typeTable op.arguments && Located.allNamed typeTable op.results) = true →
      ProtocolRegionsOk typeTable rows callees applied bodies →
        elaborateProtocolStep typeTable rows callees applied deployed scope
            (unelaborateProtocolStep callees.depth applied.depth op
              (Scope.numbers scope.depth arguments)
              (unelaborateProtocolRegions callees.depth applied.depth bodies)) =
          .ok ⟨op, bodies, Scope.numbers scope.depth arguments⟩
  | .at role op bodies, .nil, arguments, clean, named, _ => by
      have localClean := (earlierViolation_both clean).2
      simp only [ProtocolOp.arguments, ProtocolOp.results, Located.allNamed_atRole] at named
      have argumentsNamed : Ty.allNamed typeTable op.arguments = true := by
        simp only [Bool.and_eq_true] at named
        exact named.1
      have step := elaborateLocalStep_unelaborate typeTable rows callees (localType scope) op bodies
        (Scope.numbers scope.depth arguments)
        (numbersHave_localType scope role (numbersHave_numbers scope arguments)) named
        (elaborateLocalRegions_unelaborate typeTable rows callees bodies
          (LocalOp.inputsNamed op argumentsNamed) localClean)
      simp only [unelaborateProtocolStep, elaborateProtocolStep, step]
  | .exchange sender receiver site type, .nil, .cons value .nil, _, _, _ => by
      simp only [Scope.numbers, unelaborateProtocolStep, elaborateProtocolStep,
        Scope.type?_number]
  | .draw owner receivers site law populated, .nil, arguments, _, _, _ => by
      simp only [unelaborateProtocolStep, elaborateProtocolStep, Scope.at?_index, populated,
        ↓reduceDIte]
  | .sample owner site law populated, .nil, arguments, _, _, _ => by
      simp only [unelaborateProtocolStep, elaborateProtocolStep, Scope.at?_index, populated,
        ↓reduceDIte]
  | .repeat participants (.static number) carried collected captures covered, .cons body .nil,
      arguments, _, named, ⟨bodyOk, _⟩ => by
      simp only [Bool.and_eq_true] at named
      have typed := numbersHave_numbers scope arguments
      simp only [unelaborateProtocolStep, unelaborateProtocolRegions, elaborateProtocolStep,
        typesWith_of_numbersHave (NumbersHave.take carried typed),
        typesWith_of_numbersHave (NumbersHave.drop carried typed),
        Located.fillAll_stripAll typeTable collected (Located.allNamed_collected named.2),
        covered, ↓reduceDIte, bodyOk,
        Raw.RepeatCount.typed, Raw.RepeatCount.operands, List.take_append_drop, List.nil_append]
  | .repeat participants (.runtime maximum) carried collected captures covered, .cons body .nil,
      arguments, _, named, ⟨bodyOk, _⟩ => by
      simp only [Bool.and_eq_true] at named
      have typed := NumbersHave.drop (Located.ofRoles .nat participants)
        (numbersHave_numbers scope arguments)
      rw [length_ofRoles] at typed
      simp only [unelaborateProtocolStep, unelaborateProtocolRegions, elaborateProtocolStep,
        typesWith_of_numbersHave (NumbersHave.take carried typed),
        typesWith_of_numbersHave (NumbersHave.drop carried typed),
        Located.fillAll_stripAll typeTable collected (Located.allNamed_collected named.2),
        covered, ↓reduceDIte, bodyOk,
        Raw.RepeatCount.typed, Raw.RepeatCount.operands, List.take_append_drop]
  | .choose participants tag captures outputs covered, arms, arguments, clean, named, armsOk => by
      simp only [Bool.and_eq_true] at named
      have typed := NumbersHave.drop (Located.ofRoles tag.type participants)
        (numbersHave_numbers scope arguments)
      rw [length_ofRoles] at typed
      -- A participant holds the tag, so the type of the tag is a type of the package.
      have tagNamed : Ty.named typeTable tag.type = true := by
        have inhabited := firstViolation_holds _ clean (!participants.isEmpty, .noParticipant)
          (List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self))
        cases participants with
        | nil => cases inhabited
        | cons role rest =>
            exact (Located.allNamed_iff typeTable _).mp named.1 ⟨tag.type, role⟩
              List.mem_cons_self
      simp only [unelaborateProtocolStep, elaborateProtocolStep,
        ChoiceTag.fill_strip typeTable tag tagNamed,
        typesWith_of_numbersHave typed, Located.fillAll_stripAll typeTable outputs named.2,
        covered, ↓reduceDIte,
        elaborateProtocolArms_unelaborate typeTable rows callees applied arms armsOk,
        List.take_append_drop]
  | .apply callee roleMap site permitted, .nil, arguments, _, _, _ => by
      simp only [unelaborateProtocolStep, elaborateProtocolStep, Scope.value?_number, permitted,
        ↓reduceDIte]

mutual
  theorem elaborateProtocolRegion_unelaborate {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out)
        (scope : Scope Γ) (roles : Nat) (enclosing : Option (List Nat)) (sites result : List Nat),
        LocatedNamed typeTable Γ →
          protocolRegionSites typeTable roles enclosing region sites = .ok result →
            elaborateProtocolRegion typeTable rows callees applied deployed Γ scope out
              (unelaborateProtocolRegion callees.depth applied.depth scope.depth region) =
              .ok region
    | .ret values, scope, _, _, _, _, _, _ => by
        simp only [unelaborateProtocolRegion, elaborateProtocolRegion, Scope.operands?_numbers]
    | .stop _, _, _, _, _, _, _, _ => rfl
    | .letOp op arguments bodies rest, scope, roles, enclosing, sites, result, named, clean => by
        obtain ⟨opClean, resultsNamed, middle, nested, restClean⟩ := protocolRegionSites_letOp clean
        have argumentsNamed := Operands.locatedNamed named arguments
        have step := elaborateProtocolStep_unelaborate typeTable rows callees applied scope roles
          enclosing op bodies arguments opClean (by rw [argumentsNamed, resultsNamed]; rfl)
          (elaborateProtocolRegions_unelaborate bodies roles _ _ middle
            (ProtocolOp.inputsNamed op argumentsNamed) nested)
        have restOk := elaborateProtocolRegion_unelaborate rest
          (scope.bindAll (ProtocolOp.results op)) roles enclosing middle result
          (named.bindAll resultsNamed) restClean
        rw [Scope.depth_bindAll] at restOk
        have found := Scope.operands?_numbers scope arguments
        simp only [unelaborateProtocolRegion, elaborateProtocolRegion, step, found, restOk]
    | .bind (mid := mid) body rest, scope, roles, enclosing, sites, result, named, clean => by
        obtain ⟨midNamed, middle, bodyClean, restClean⟩ := protocolRegionSites_bind clean
        have bodyOk := elaborateProtocolRegion_unelaborate body scope roles enclosing sites middle
          named bodyClean
        have restOk := elaborateProtocolRegion_unelaborate rest (scope.bindAll mid) roles
          enclosing middle result (named.bindAll midNamed) restClean
        rw [Scope.depth_bindAll] at restOk
        simp only [unelaborateProtocolRegion, elaborateProtocolRegion,
          Located.fillAll_stripAll typeTable mid midNamed, bodyOk, restOk]

  theorem elaborateProtocolRegions_unelaborate
      {signatures : List (List Located × List Located)} :
      ∀ (bodies : Regions (ProtocolDialect operations functions protocols deployed) signatures)
        (roles : Nat) (enclosing : Option (List Nat)) (sites result : List Nat),
        (∀ signature ∈ signatures, LocatedNamed typeTable signature.1) →
          protocolRegionsSites typeTable roles enclosing bodies sites = .ok result →
            ProtocolRegionsOk typeTable rows callees applied bodies
    | .nil, _, _, _, _, _, _ => trivial
    | .cons (inputs := inputs) body tail, roles, enclosing, sites, result, named, clean => by
        unfold protocolRegionsSites at clean
        split at clean
        · cases clean
        · rename_i middle first
          have bodyOk := elaborateProtocolRegion_unelaborate body (Scope.empty.bindAll inputs)
            roles enclosing sites middle
            (LocatedNamed.inputs (named _ (List.mem_cons_self ..))) first
          rw [depth_inputs] at bodyOk
          exact ⟨bodyOk, elaborateProtocolRegions_unelaborate tail roles enclosing middle result
            (fun signature member => named signature (List.mem_cons_of_mem _ member)) clean⟩
end

end Protocol

/-! ## Signatures -/

theorem elaborateCopy_unelaborate {ports : List Located} {type : Ty} (copy : Copy ports type) :
    elaborateCopy ports type copy.port.index = some copy := by
  obtain ⟨holder, port⟩ := copy
  have found := port.valid
  unfold elaborateCopy
  split
  · rename_i located found'
    have same : located = ⟨type, holder⟩ := Option.some.inj (found'.symm.trans found)
    subst same
    simp only [↓reduceDIte]
  · rename_i missing
    rw [found] at missing
    cases missing

theorem elaborateCopies_unelaborate {ports : List Located} {type : Ty} :
    ∀ (copies : List (Copy ports type)),
      elaborateCopies ports type (copies.map (·.port.index)) = some copies
  | [] => rfl
  | copy :: rest => by
      simp only [List.map_cons, elaborateCopies, elaborateCopy_unelaborate,
        elaborateCopies_unelaborate rest]

theorem elaborateAgreement_unelaborate {ports : List Located} (agreement : Agreement ports) :
    elaborateAgreement ports (agreement.copies.map (·.port.index)) = some agreement := by
  obtain ⟨type, first, others⟩ := agreement
  simp only [Agreement.copies, List.map_cons, elaborateAgreement, first.port.valid,
    elaborateCopy_unelaborate, elaborateCopies_unelaborate]

/-- The agreements of the other side are skipped. -/
theorem elaborateSide_other {ports others : List Located} (overOutputs : Bool)
    (agreements : List (Agreement others)) (later : List Raw.Agreement) :
    elaborateSide ports overOutputs (unelaborateSide (!overOutputs) agreements ++ later) =
      elaborateSide ports overOutputs later := by
  induction agreements with
  | nil => rfl
  | cons agreement rest ih =>
      have ih' : elaborateSide ports overOutputs
          (List.map (unelaborateAgreement (!overOutputs)) rest ++ later) =
            elaborateSide ports overOutputs later := ih
      cases overOutputs <;> cases found : elaborateSide ports _ later <;>
        simp_all [unelaborateSide, unelaborateAgreement, elaborateSide]

theorem elaborateSide_same {ports : List Located} (overOutputs : Bool)
    (agreements : List (Agreement ports)) (later : List Raw.Agreement)
    (skipped : elaborateSide ports overOutputs later = some []) :
    elaborateSide ports overOutputs (unelaborateSide overOutputs agreements ++ later) =
      some agreements := by
  induction agreements with
  | nil => exact skipped
  | cons agreement rest ih =>
      have ih' : elaborateSide ports overOutputs
          (List.map (unelaborateAgreement overOutputs) rest ++ later) = some rest := ih
      simp only [unelaborateSide, List.map_cons, List.cons_append, elaborateSide, ih',
        unelaborateAgreement, ↓reduceIte, elaborateAgreement_unelaborate agreement]

theorem elaborateAgreements_unelaborate {inputs outputs : List Located}
    (agreements : Agreements inputs outputs) :
    elaborateAgreements inputs outputs (unelaborateAgreements agreements) = some agreements := by
  obtain ⟨overInputs, overOutputs⟩ := agreements
  have first : elaborateSide inputs false
      (unelaborateSide false overInputs ++ unelaborateSide true overOutputs) = some overInputs := by
    refine elaborateSide_same false overInputs _ ?_
    have skip := elaborateSide_other (ports := inputs) false overOutputs []
    simp only [Bool.not_false, List.append_nil] at skip
    rw [skip]
    rfl
  have second : elaborateSide outputs true
      (unelaborateSide false overInputs ++ unelaborateSide true overOutputs) = some overOutputs := by
    have skip := elaborateSide_other (ports := outputs) true overInputs
      (unelaborateSide true overOutputs)
    have same := elaborateSide_same true overOutputs [] rfl
    simp only [Bool.not_true, List.append_nil] at skip same
    rw [skip, same]
  simp only [elaborateAgreements, unelaborateAgreements, first, second]

/-! ## Definitions, programs and packages -/

theorem elaborateFunction_unelaborate (typeTable : TypeTable) {operations : List OperationSignature}
    {functions : List FunctionHeader} (rows : Scope operations) (callees : Scope functions)
    {header : FunctionHeader} (definition : FunctionDefinition operations functions header)
    (inputsNamed : Ty.allNamed typeTable header.inputs = true)
    (clean : localRegionViolation typeTable definition.body = none) :
    elaborateFunction typeTable rows callees header
        (unelaborateLocalRegion callees.depth header.inputs.length definition.body) =
      .ok definition := by
  have bodyOk := elaborateLocalRegion_unelaborate typeTable rows callees
    (deployed := !header.specificationOnly) definition.body (Scope.empty.bindAll header.inputs)
    (ContextNamed.inputs ((Ty.allNamed_iff typeTable _).mp inputsNamed)) clean
  rw [depth_inputs] at bodyOk
  unfold elaborateFunction
  simp only [bodyOk]

/-- A function without a violation has a header of types of the package and a body
without a violation. -/
theorem FunctionDefinition.violation_none {typeTable : TypeTable}
    {operations : List OperationSignature} {functions : List FunctionHeader}
    {header : FunctionHeader} {definition : FunctionDefinition operations functions header}
    (clean : definition.violation typeTable = none) :
    (Ty.allNamed typeTable header.inputs && Ty.allNamed typeTable header.outputs) = true ∧
      localRegionViolation typeTable definition.body = none := by
  unfold FunctionDefinition.violation at clean
  cases named : (Ty.allNamed typeTable header.inputs && Ty.allNamed typeTable header.outputs) with
  | false =>
      rw [named] at clean
      cases clean
  | true =>
      rw [named] at clean
      exact ⟨rfl, clean⟩

/-- The header of a function whose types are types of the package. -/
theorem header_unelaborate {typeTable : TypeTable} {header : FunctionHeader}
    (named : (Ty.allNamed typeTable header.inputs && Ty.allNamed typeTable header.outputs) = true)
    (body : Option Raw.LocalRegion) :
    Raw.Function.header typeTable
        ⟨header.specificationOnly, Ty.stripAll header.inputs, Ty.stripAll header.outputs, body⟩ =
      some header := by
  simp only [Bool.and_eq_true] at named
  simp only [Raw.Function.header, Ty.fillAll_stripAll typeTable header.inputs named.1,
    Ty.fillAll_stripAll typeTable header.outputs named.2]

/-- A protocol without a violation has ports of types of the package and a body whose
one pass collects its sites. -/
theorem ProtocolDefinition.violation_none {typeTable : TypeTable}
    {operations : List OperationSignature} {functions : List FunctionHeader}
    {protocols : List ProtocolHeader} {header : ProtocolHeader}
    {definition : ProtocolDefinition operations functions protocols header}
    (clean : definition.violation typeTable = none) :
    Located.allNamed typeTable header.inputs = true ∧
      Located.allNamed typeTable header.outputs = true ∧
      ∃ sites, protocolRegionSites typeTable header.roles none definition.body [] = .ok sites := by
  unfold ProtocolDefinition.violation at clean
  have both := earlierViolation_both clean
  have ports := firstViolation_holds _ both.1
    (Located.allNamed typeTable (header.inputs ++ header.outputs), .nominalRow)
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  rw [Located.allNamed_append, Bool.and_eq_true] at ports
  refine ⟨ports.1, ports.2, ?_⟩
  have sitesClean := both.2
  unfold ProtocolDefinition.sites at sitesClean
  split at sitesClean
  · cases sitesClean
  · rename_i sites found
    exact ⟨sites, found⟩

theorem elaborateProtocol_unelaborate (typeTable : TypeTable) {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader} (rows : Scope operations)
    (callees : Scope functions) (applied : Scope protocols) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (clean : definition.violation typeTable = none) :
    elaborateProtocol typeTable rows callees applied
        (unelaborateProtocol callees.depth applied.depth definition) = .ok ⟨header, definition⟩ := by
  obtain ⟨inputsNamed, outputsNamed, sites, bodyClean⟩ := ProtocolDefinition.violation_none clean
  have bodyOk := elaborateProtocolRegion_unelaborate typeTable rows callees applied
    (deployed := !header.specificationOnly) definition.body (Scope.empty.bindAll header.inputs)
    header.roles none [] sites
    (LocatedNamed.inputs ((Located.allNamed_iff typeTable _).mp inputsNamed)) bodyClean
  rw [depth_inputs] at bodyOk
  unfold elaborateProtocol unelaborateProtocol
  simp only [Located.fillAll_stripAll typeTable header.inputs inputsNamed,
    Located.fillAll_stripAll typeTable header.outputs outputsNamed,
    elaborateAgreements_unelaborate, bodyOk]

/-- The scope that elaboration builds for the headers of functions. -/
def Functions.scope {typeTable : TypeTable} {operations : List OperationSignature} :
    {functions : List FunctionHeader} → Functions typeTable operations functions → Scope functions
  | _, .nil => .empty
  | _, .snoc (header := header) earlier _ _ => earlier.scope.push header
  | _, .opaque earlier header _ => earlier.scope.push header

def Protocols.scope {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      Scope protocols
  | _, .nil => .empty
  | _, .snoc (header := header) earlier _ _ => earlier.scope.push header

theorem elaborateFunctions_unelaborate {typeTable : TypeTable} {operations : List OperationSignature}
    (rows : Scope operations) :
    ∀ {functions : List FunctionHeader} (typed : Functions typeTable operations functions)
      (later : List Raw.Function),
      elaborateFunctions typeTable rows (unelaborateFunctions functions.length typed later)
          ⟨[], .empty, .nil⟩ =
        elaborateFunctions typeTable rows later ⟨functions, typed.scope, typed⟩
  | _, .nil, _ => rfl
  | _, .snoc (functions := functions) (header := header) earlier definition wellFormed, later => by
      have count : (header :: functions).length - 1 = earlier.scope.depth := by
        rw [earlier.scope.counted]; rfl
      have ih := elaborateFunctions_unelaborate rows earlier
        (unelaborateFunction earlier.scope.depth definition :: later)
      rw [← earlier.scope.counted] at ih
      obtain ⟨named, bodyClean⟩ := FunctionDefinition.violation_none wellFormed
      have inputsNamed : Ty.allNamed typeTable header.inputs = true := by
        simp only [Bool.and_eq_true] at named
        exact named.1
      have bodyOk := elaborateFunction_unelaborate typeTable rows earlier.scope definition
        inputsNamed bodyClean
      rw [unelaborateFunctions, count, ih, elaborateFunctions]
      simp only [unelaborateFunction, header_unelaborate named, bodyOk]
      split
      · rfl
      · rename_i violation found
        exact nomatch wellFormed.symm.trans found
  | _, .opaque (functions := functions) earlier header named, later => by
      have count : (header :: functions).length - 1 = earlier.scope.depth := by
        rw [earlier.scope.counted]; rfl
      have ih := elaborateFunctions_unelaborate rows earlier (unelaborateOpaque header :: later)
      rw [← earlier.scope.counted] at ih
      rw [unelaborateFunctions, count, ih, elaborateFunctions]
      simp only [unelaborateOpaque, header_unelaborate named]
      exact dite_eq_left_of_eq_true (eq_true named)

theorem elaborateProtocols_unelaborate {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} (rows : Scope operations) (callees : Scope functions) :
    ∀ {protocols : List ProtocolHeader} (typed : Protocols typeTable operations functions protocols)
      (later : List Raw.Protocol),
      elaborateProtocols typeTable rows callees
          (unelaborateProtocols callees.depth protocols.length typed later) ⟨[], .empty, .nil⟩ =
        elaborateProtocols typeTable rows callees later ⟨protocols, typed.scope, typed⟩
  | _, .nil, _ => rfl
  | _, .snoc (protocols := protocols) (header := header) earlier definition wellFormed, later => by
      have count : (header :: protocols).length - 1 = earlier.scope.depth := by
        rw [earlier.scope.counted]; rfl
      have ih := elaborateProtocols_unelaborate rows callees earlier
        (unelaborateProtocol callees.depth earlier.scope.depth definition :: later)
      rw [← earlier.scope.counted] at ih
      rw [unelaborateProtocols, count, ih, elaborateProtocols,
        elaborateProtocol_unelaborate typeTable rows callees earlier.scope definition wellFormed]
      simp only
      split
      · rfl
      · rename_i violation found
        rw [wellFormed] at found
        cases found

/-! ## Tables -/

theorem fillEach_map {α : Type} (fill : α → Option α) (strip : α → α) :
    ∀ (entries : List α), (∀ entry ∈ entries, fill (strip entry) = some entry) →
      fillEach fill (entries.map strip) = some entries
  | [], _ => rfl
  | entry :: rest, filled => by
      simp only [List.map_cons, fillEach, filled entry (List.mem_cons_self ..),
        fillEach_map fill strip rest fun later member => filled later (List.mem_cons_of_mem _ member)]

theorem Static.fill_strip (typeTable : TypeTable) :
    ∀ (statics : List Static), staticsNamed typeTable statics = true →
      ∀ static ∈ statics, Static.fill typeTable static.strip = some static
  | [], _, _, member => nomatch member
  | .type given :: rest, named, static, member => by
      simp only [staticsNamed, Bool.and_eq_true] at named
      rcases List.mem_cons.mp member with rfl | later
      · simp only [Static.strip, Static.fill, Ty.fill_strip typeTable given named.1]
      · exact Static.fill_strip typeTable rest named.2 static later
  | .domain _ :: rest, named, static, member => by
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact Static.fill_strip typeTable rest named static later
  | .nat _ :: rest, named, static, member => by
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact Static.fill_strip typeTable rest named static later

theorem CatalogueRow.fill_strip (typeTable : TypeTable) (row : CatalogueRow)
    (named : staticsNamed typeTable row.statics = true) :
    row.strip.fill typeTable = some row := by
  simp only [CatalogueRow.strip, CatalogueRow.fill,
    fillEach_map (Static.fill typeTable) Static.strip row.statics
      (Static.fill_strip typeTable row.statics named)]

theorem Operation.fill_strip (typeTable : TypeTable) (row : Operation)
    (named : (staticsNamed typeTable row.identity.statics &&
      (Ty.allNamed typeTable row.signature.inputs && Ty.allNamed typeTable row.signature.outputs))
        = true) :
    row.strip.fill typeTable = some row := by
  simp only [Bool.and_eq_true] at named
  simp only [Operation.strip, Operation.fill, CatalogueRow.fill_strip typeTable row.identity named.1,
    Ty.fillAll_stripAll typeTable _ named.2.1, Ty.fillAll_stripAll typeTable _ named.2.2]

/-- Elaboration inverts unelaboration, for every typed package. -/
theorem elaborate_unelaborate (typed : Typed) : elaborate (unelaborate typed) = .ok typed := by
  obtain ⟨types, records, variants, table, functions, protocols, ⟨typedFunctions, typedProtocols⟩,
    names, tablesFormed, namesFormed⟩ := typed
  have conditions := firstViolation_holds _ tablesFormed
  have typesNamed : (types.all fun row =>
      staticsNamed (typeTableOf types records variants) row.statics) = true :=
    conditions _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have operationsNamed : (table.all fun row =>
      staticsNamed (typeTableOf types records variants) row.identity.statics &&
        (Ty.allNamed (typeTableOf types records variants) row.signature.inputs &&
          Ty.allNamed (typeTableOf types records variants) row.signature.outputs)) = true :=
    conditions _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  rw [List.all_eq_true] at typesNamed operationsNamed
  have reading : typeTableOf (types.map CatalogueRow.strip) records variants =
      typeTableOf types records variants := by
    simp only [typeTableOf, List.length_map]
  have typesOk := fillEach_map (CatalogueRow.fill (typeTableOf types records variants))
    CatalogueRow.strip types fun row member =>
      CatalogueRow.fill_strip _ row (typesNamed row member)
  have operationsOk := fillEach_map (Operation.fill (typeTableOf types records variants))
    Operation.strip table fun row member =>
      Operation.fill_strip _ row (operationsNamed row member)
  have functionsOk := elaborateFunctions_unelaborate (typeTable := typeTableOf types records variants)
    (tableScope (table.map (·.signature))) typedFunctions []
  have protocolsOk := elaborateProtocols_unelaborate (typeTable := typeTableOf types records variants)
    (tableScope (table.map (·.signature))) typedFunctions.scope typedProtocols []
  rw [typedFunctions.scope.counted] at protocolsOk
  unfold elaborate unelaborate
  simp only [reading, typesOk, operationsOk]
  split
  · rename_i violation found
    rw [tablesFormed] at found
    cases found
  · rw [functionsOk]
    simp only [elaborateFunctions, protocolsOk, elaborateProtocols]
    split
    · rename_i violation found
      rw [namesFormed] at found
      cases found
    · rfl

end Zkc.Core
