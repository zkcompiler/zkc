module

public import Zkc.Construction.ConnectionCalculations
public import Zkc.Construction.OriginalFrameRelations

@[expose] public section

/-! Physical layout facts for closed mathematical regions. These use the same
optional-value relation as protocol connection. Allocating a result extends the
physical frame while prepending the corresponding typed source variables.
No result equation, arithmetic interpretation or source identity is assumed. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionMathFrames
open Zkc.Source Zkc.Source.Structured
variable {carriers : Carriers}

/-- Fresh physical positions in the declared result order. -/
def allocated (start count : Nat) : List Original.Location :=
  (List.range' start count).map Original.Location.data

theorem valuesHolds_append {first rest : List Ty}
    {frame : Domain.Environment carriers} {left right : List Original.Location}
    (values : Values (Component carriers.Value) first)
    (remaining : Values (Component carriers.Value) rest)
    (head : Original.ValuesHolds frame left values)
    (tail : Original.ValuesHolds frame right remaining) :
    Original.ValuesHolds frame (left ++ right) (values.append remaining) := by
  induction values generalizing left with
  | nil => cases left with
    | nil => exact tail
    | cons => exact False.elim head
  | cons value values ih =>
    cases left with
    | nil => exact False.elim head
    | cons location left => exact ⟨head.1, ih head.2⟩

/-- Exact encoding supplies the source relation at every freshly allocated
slot, including repeated values and multiple results. -/
theorem valuesHolds_encoded {types : List Ty}
    (values : Values carriers.Value types) (before suffix : Domain.Environment carriers)
    {encoded : Domain.Environment carriers} (encoding : Domain.encodeValues values = some encoded) :
    Original.ValuesHolds (before ++ encoded ++ suffix)
      (allocated before.length types.length) values.present := by
  induction values generalizing before encoded with
  | nil =>
    have empty : encoded = [] := by simpa only [Domain.encodeValues, Option.some.injEq] using encoding.symm
    subst encoded
    trivial
  | @cons ty types value values ih =>
    cases head : Domain.Value.encode ty value with
    | none => simp [Domain.encodeValues, head] at encoding
    | some physical =>
      cases tail : Domain.encodeValues values with
      | none => simp [Domain.encodeValues, head, tail] at encoding
      | some remaining =>
        have encodedEq : encoded = physical :: remaining := by
          simpa only [Domain.encodeValues, head, tail, bind, Option.bind,
            Option.pure_def, Option.some.injEq] using encoding.symm
        subst encoded
        change Original.ComponentHolds _ (.data before.length) ty (some value) ∧ _
        constructor
        · refine ⟨value, rfl, ?_⟩
          simp only [List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self]
          exact Domain.Value.decode_encode head
        · simpa only [allocated, List.length_append, List.length_singleton,
            List.append_assoc, List.singleton_append] using ih (before ++ [physical]) tail

/-- Adding computed cells preserves all earlier source variables and adds the
complete new tuple. The extent bound is a static layout obligation. -/
theorem extend {types added : List Ty}
    {environment : Domain.Environment carriers} {locations : List Original.Location}
    (values : Values (Component carriers.Value) types) (results : Values carriers.Value added)
    (bound : Original.LocationsBound environment.length locations)
    (related : Original.ValuesHolds environment locations values)
    {encoded : Domain.Environment carriers} (encoding : Domain.encodeValues results = some encoded) :
    Original.ValuesHolds (environment ++ encoded)
      (allocated environment.length added.length ++ locations) (results.present.append values) := by
  apply valuesHolds_append
  · simpa only [List.append_nil] using valuesHolds_encoded results environment [] encoding
  · exact Original.valuesHolds_of_captures values bound related
      (ArtifactBinding.captures_append environment encoded)

theorem present_append {types added : List Ty}
    (values : Values carriers.Value types) (results : Values carriers.Value added) :
    (results.append values).present = results.present.append values.present := by
  induction results with
  | nil => rfl
  | cons value results ih => simpa only [Values.append, Values.present] using congrArg (Values.cons (some value)) ih

/-- The typed source environment prepends results in exactly the order used by
`Values.append`. This equation avoids expanding dependent environment lookups
through every individual operation in connection proofs. -/
theorem append_get {types added : List Ty}
    (values : Values carriers.Value types) (results : Values carriers.Value added) :
    @Eq (Environment carriers.Value (added ++ types))
      (results.append values).get (Environment.prepend values.get results) := by
  induction results with
  | nil => rfl
  | cons value results ih =>
    funext ty position
    cases position with
    | here => rfl
    | there position => exact congrFun (congrFun ih _) position

theorem allocated_bound (start count : Nat) :
    Original.LocationsBound (start + count) (allocated start count) := by
  intro reference present
  obtain ⟨position, inside, same⟩ := List.mem_map.mp present
  have equal : position = reference := Original.Location.data.inj same
  subst reference
  obtain ⟨index, _, bound, equal⟩ := List.mem_range'.mp inside
  omega

theorem append_bound {left right : List Original.Location} {size : Nat}
    (first : Original.LocationsBound size left) (second : Original.LocationsBound size right) :
    Original.LocationsBound size (left ++ right) := by
  intro reference present
  rcases List.mem_append.mp present with head | tail
  · exact first reference head
  · exact second reference tail

theorem bound_mono {locations : List Original.Location} {before after : Nat}
    (bound : Original.LocationsBound before locations) (larger : before ≤ after) :
    Original.LocationsBound after locations := fun reference present =>
  Nat.lt_of_lt_of_le (bound reference present) larger

theorem encoded_length {types : List Ty} (values : Values carriers.Value types)
    {encoded : Domain.Environment carriers} (encoding : Domain.encodeValues values = some encoded) :
    encoded.length = types.length := by
  have lengths := congrArg List.length (Domain.encodeValues_sorts encoding)
  simpa only [List.length_map] using lengths

/-- Operand selection in a present typed source frame reads exactly that
source tuple. It never infers equivalence from equal types or names. -/
theorem read_present {inputs outputs : List Ty}
    (values : Values carriers.Value inputs) (positions : Operands inputs outputs)
    {environment : Domain.Environment carriers} {locations : List Original.Location}
    {references : List Nat}
    (selected : ConnectionCalculations.operandReferences locations positions = some references)
    (related : Original.ValuesHolds environment locations values.present) :
    Domain.read environment references = Domain.encodeValues (positions.eval values.get) := by
  obtain ⟨actual, present, read⟩ :=
    ConnectionCalculations.operandReferences_read values.present positions selected related
  have input : @Eq (Environment (Component carriers.Value) inputs)
      values.present.get (fun position => some (values.get position)) := by
    funext ty position
    exact Values.get_present values position
  rw [input, Operands.eval_present] at present
  have same := congrArg RoleFamily.sequence present
  simp only [RoleFamily.sequence_present, Option.some.injEq] at same
  simpa only [same] using read

theorem read_cons (environment : Domain.Environment carriers) (reference : Nat)
    (references : List Nat) :
    Domain.read environment (reference :: references) =
      (environment[reference]?).bind (fun value =>
        (Domain.read environment references).bind (fun values => some (value :: values))) := by
  simp [Domain.read, List.mapM_cons]

/-- A successful ordered read provides both the exact typed value relation and
an in-bounds location for every coordinate. Duplicate coordinates are allowed. -/
theorem read_encoded {types : List Ty} (values : Values carriers.Value types)
    (environment : Domain.Environment carriers) (references : List Nat)
    {encoded : Domain.Environment carriers}
    (encoding : Domain.encodeValues values = some encoded)
    (read : Domain.read environment references = some encoded) :
    Original.ValuesHolds environment (references.map Original.Location.data) values.present ∧
      Original.LocationsBound environment.length (references.map Original.Location.data) := by
  induction values generalizing references encoded with
  | nil =>
    have empty : encoded = [] := by simpa only [Domain.encodeValues, Option.some.injEq] using encoding.symm
    subst encoded
    cases references with
    | nil => exact ⟨trivial, by simp [Original.LocationsBound]⟩
    | cons reference references =>
      rw [read_cons] at read
      cases found : environment[reference]? <;> cases rest : Domain.read environment references <;>
        simp_all only [Option.bind_none, Option.bind_some, Option.some.injEq, List.cons_ne_nil, reduceCtorEq]
  | @cons ty types value values ih =>
    cases head : Domain.Value.encode ty value with
    | none => simp [Domain.encodeValues, head] at encoding
    | some physical =>
      cases tail : Domain.encodeValues values with
      | none => simp [Domain.encodeValues, head, tail] at encoding
      | some remaining =>
        have same : encoded = physical :: remaining := by
          simpa only [Domain.encodeValues, head, tail, bind, Option.bind,
            Option.pure_def, Option.some.injEq] using encoding.symm
        subst encoded
        cases references with
        | nil => simp [Domain.read] at read
        | cons reference references =>
          rw [read_cons] at read
          cases found : environment[reference]? with
          | none => simp only [found, Option.bind_none, reduceCtorEq] at read
          | some actual =>
            cases rest : Domain.read environment references with
            | none => simp only [found, rest, Option.bind_some, Option.bind_none, reduceCtorEq] at read
            | some actuals =>
              have same : actual = physical ∧ actuals = remaining := by
                simpa only [found, rest, Option.bind_some, Option.some.injEq, List.cons.injEq] using read
              obtain ⟨rfl, rfl⟩ := same
              obtain ⟨related, bound⟩ := ih references tail rest
              refine ⟨⟨⟨value, rfl, ?_⟩, related⟩, ?_⟩
              · simpa only [found, Option.bind_some] using Domain.Value.decode_encode head
              · intro index present
                simp only [List.map_cons, List.mem_cons, Original.Location.data.injEq] at present
                rcases present with rfl | inside
                · exact List.getElem?_eq_some_iff.mp found |>.1
                · exact bound index inside

/-- Recover the Boolean selector and exact capture tuple from one checked
ordered operand row. -/
theorem selection_read {inputs captures : List Ty}
    (values : Values carriers.Value inputs) (condition : Var inputs .boolean)
    (captured : Operands inputs captures)
    {environment : Domain.Environment carriers} {locations : List Original.Location}
    {selector : Nat} {references : List Nat}
    (selected : ConnectionCalculations.operandReferences locations (.cons condition captured) =
      some (selector :: references))
    (data : captures.all Domain.localType = true)
    (related : Original.ValuesHolds environment locations values.present) :
    environment[selector]? = some (.data (.boolean (values.get condition))) ∧
      Domain.read environment references = Domain.encodeValues (captured.eval values.get) := by
  have all := read_present values (.cons condition captured) selected related
  have encoding := Original.encodeHelperResult_eq data (captured.eval values.get)
  change Domain.read environment (selector :: references) =
    (Domain.encodeValues (captured.eval values.get)).bind
      (fun rest => some (.data (.boolean (values.get condition)) :: rest)) at all
  rw [encoding, Option.bind_some] at all
  rw [read_cons] at all
  cases found : environment[selector]? <;>
    cases rest : Domain.read environment references <;>
    simp_all only [Option.bind_none, Option.bind_some, Option.some.injEq, List.cons.injEq, reduceCtorEq]
  trivial

end Zkc.Construction.ConnectionMathFrames
