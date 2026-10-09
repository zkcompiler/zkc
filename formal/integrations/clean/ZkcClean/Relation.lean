import ZkcClean.Expression

/-! Obligation (2): the zkc finite AIR relation of an exported and imported
component holds on a nonempty trace exactly when Clean's upstream
`Operations.ConstraintsHold` holds on every row.

Both directions are proved for every trace, every row-width-matching Clean
table and every `Environment.data`. In the admitted fragment the constraints do
not read `Environment.data`; `constraintsHold_data` states that explicitly, so
the zkc relation acquires no authority over that external data.
-/

set_option autoImplicit false

namespace ZkcClean

open Zkc.Relation

variable {F : Type} [FiniteField F]

theorem decodeAssertions_encode {width : Nat} :
    ∀ {es : List (Expression F)} {cs : List (AIR.Constraint F 0 width)},
      decodeAssertions F width (es.map encode) = some cs →
      List.Forall₂ (fun e c => c.scope = .every ∧ (encode e).decode F width = some c.expression)
        es cs
  | [], cs, h => by
      cases h
      exact .nil
  | e :: es, cs, h => by
      simp only [List.map_cons, decodeAssertions] at h
      split at h
      · rename_i x rest hx hrest
        cases h
        exact .cons ⟨rfl, hx⟩ (decodeAssertions_encode hrest)
      · cases h

theorem decodeAssertions_of_bounded {width : Nat} :
    ∀ {es : List (Expression F)}, (∀ e ∈ es, Bounded width e) →
      ∃ cs, decodeAssertions F width (es.map encode) = some cs
  | [], _ => ⟨[], rfl⟩
  | e :: es, h => by
      obtain ⟨x, hx⟩ := decode_encode (h e (by simp))
      obtain ⟨cs, hcs⟩ := decodeAssertions_of_bounded (es := es) (fun e' h' => h e' (by simp [h']))
      exact ⟨⟨.every, x⟩ :: cs, by simp [decodeAssertions, hx, hcs]⟩

theorem forall_iff_of_forall₂ {α β : Type} {R : α → β → Prop} {P : β → Prop} {Q : α → Prop}
    (equivalent : ∀ a b, R a b → (P b ↔ Q a)) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs →
      ((∀ b ∈ bs, P b) ↔ (∀ a ∈ as, Q a))
  | _, _, .nil => by simp
  | _, _, .cons related rest => by
      simp only [List.mem_cons, forall_eq_or_imp]
      exact and_congr (equivalent _ _ related) (forall_iff_of_forall₂ equivalent rest)

/-- In the admitted fragment Clean's constraint predicate is the assertion
list; lookups contribute nothing because there are none. -/
theorem constraintsHold_iff {operations : Operations F} (noLookups : operations.lookups = [])
    (env : Environment F) :
    operations.ConstraintsHold env ↔ ∀ e ∈ operations.constraints, Expression.eval env e = 0 := by
  simp [Operations.ConstraintsHold, noLookups]

/-- A kernel-evaluable form of Clean's constraint predicate that uses neither
the exporter nor the zkc relation. Controls use it to evaluate the source side
independently. -/
theorem constraintsHold_iff_flatten {operations : Operations F}
    (noLookups : FlatOperation.lookups (flatten operations) = []) (env : Environment F) :
    operations.ConstraintsHold env ↔
      ∀ e ∈ FlatOperation.constraints (flatten operations), Expression.eval env e = 0 := by
  rw [lookups_flatten] at noLookups
  rw [constraintsHold_iff noLookups, constraints_flatten]

/-- The constraints of an admitted export never read `Environment.data`. -/
theorem constraintsHold_data {component : Air.Flat.Component F} {artifact : Artifact}
    (exported : exportComponent component = .ok artifact) (row : Array F)
    (data data' : ProverData F) :
    component.operations.ConstraintsHold (Environment.fromArray row data) ↔
      component.operations.ConstraintsHold (Environment.fromArray row data') := by
  have admitted := exportComponent_ok exported
  rw [constraintsHold_iff admitted.noLookups, constraintsHold_iff admitted.noLookups]
  have same : ∀ e : Expression F,
      Expression.eval (Environment.fromArray row data) e =
        Expression.eval (Environment.fromArray row data') e := by
    intro e
    induction e with
    | var v => rfl
    | const c => rfl
    | add l r ihl ihr => simp only [Expression.eval, ihl, ihr]
    | mul l r ihl ihr => simp only [Expression.eval, ihl, ihr]
  simp only [same]

/-- Import admission succeeds on every exported component. -/
theorem decode_export {component : Air.Flat.Component F} {artifact : Artifact}
    (exported : exportComponent component = .ok artifact) :
    ∃ cs, artifact.decode F = some cs := by
  have admitted := exportComponent_ok exported
  unfold Artifact.decode
  rw [if_pos admitted.fieldSize_eq, admitted.assertions]
  exact decodeAssertions_of_bounded (fun e h => admitted.width_eq ▸ admitted.bounded e h)

/-- Obligation (2) for an arbitrary nonempty trace of the artifact's width. -/
theorem holds_iff {component : Air.Flat.Component F} {artifact : Artifact}
    (exported : exportComponent component = .ok artifact)
    {cs : List (AIR.Constraint F 0 artifact.width)} (decoded : artifact.decode F = some cs)
    {height : Nat} (statement : Fin 0 → F) (trace : Fin (height + 1) → Fin artifact.width → F)
    (data : ProverData F) :
    (AIR.family cs height).holds statement trace ↔
      ∀ row, component.operations.ConstraintsHold (rowEnvironment (trace row) data) := by
  have admitted := exportComponent_ok exported
  unfold Artifact.decode at decoded
  rw [if_pos admitted.fieldSize_eq, admitted.assertions] at decoded
  have related := decodeAssertions_encode decoded
  change (∀ c ∈ cs, c.Holds statement trace) ↔ _
  simp only [constraintsHold_iff admitted.noLookups]
  have swap : (∀ row, ∀ e ∈ component.operations.constraints,
      Expression.eval (rowEnvironment (trace row) data) e = 0) ↔
      ∀ e ∈ component.operations.constraints, ∀ row,
        Expression.eval (rowEnvironment (trace row) data) e = 0 :=
    ⟨fun h e he row => h row e he, fun h row e he => h e he row⟩
  rw [swap]
  refine forall_iff_of_forall₂ ?_ related
  rintro e c ⟨scope, hc⟩
  simp only [AIR.Constraint.Holds, scope, AIR.Scope.Active, forall_const,
    evaluateAt_decode hc statement trace _ data, Option.some.injEq]

/-- The zkc witness of a nonempty Clean table whose declared width is the
artifact's width. -/
def tableTrace (table : Air.Flat.Table F) {height width : Nat}
    (length : table.table.length = height + 1) (widthEq : table.width = width) :
    Fin (height + 1) → Fin width → F :=
  fun row column =>
    have hrow : row.val < table.table.length := lt_of_lt_of_eq row.2 length.symm
    (table.table[row.val]'hrow)[column.val]'(by
      rw [table.uniform_width _ (List.getElem_mem hrow), widthEq]
      exact column.2)

theorem ofFn_tableTrace (table : Air.Flat.Table F) {height width : Nat}
    (length : table.table.length = height + 1) (widthEq : table.width = width)
    (row : Fin (height + 1)) :
    Array.ofFn (tableTrace table length widthEq row) =
      table.table[row.val]'(lt_of_lt_of_eq row.2 length.symm) := by
  have hrow : row.val < table.table.length := lt_of_lt_of_eq row.2 length.symm
  have size : (table.table[row.val]'hrow).size = width := by
    rw [table.uniform_width _ (List.getElem_mem hrow), widthEq]
  apply Array.ext
  · simp [size]
  · intro i _ _
    simp [tableTrace]

/-- Obligation (2) in Clean's own table terms: the zkc relation on the table's
rows is upstream `Air.Flat.Table.Constraints`. -/
theorem table_holds_iff (table : Air.Flat.Table F) {artifact : Artifact}
    (exported : exportComponent table.component = .ok artifact)
    {cs : List (AIR.Constraint F 0 artifact.width)} (decoded : artifact.decode F = some cs)
    {height : Nat} (length : table.table.length = height + 1)
    (widthEq : table.width = artifact.width) (statement : Fin 0 → F) :
    (AIR.family cs height).holds statement (tableTrace table length widthEq) ↔
      table.Constraints := by
  rw [holds_iff exported decoded statement _ table.data]
  simp only [rowEnvironment, ofFn_tableTrace, Air.Flat.Table.Constraints,
    Air.Flat.Table.environment, List.forall_mem_iff_getElem, length]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h row
    exact h row.val row.2

end ZkcClean
