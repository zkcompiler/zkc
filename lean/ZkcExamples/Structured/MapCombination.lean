module

public import ZkcExamples.Structured.MapCombinationViews
public import Zkc.Source.Structured.MapLaws
public import Zkc.Source.Structured.ClosedProjection

@[expose] public section

/-! Independent arithmetic client of the retained map. Helper equations come
from the complete checked source table, including the nested scale calls. -/
namespace ZkcExamples.Structured.MapCombination
open Zkc.Source Zkc.Source.Structured MapCombinationViews
set_option linter.unusedSimpArgs false
set_option smartUnfolding false

private theorem prepend_one {Value : Ty → Type} {types : List Ty} {type : Ty}
    (env : Environment Value types) (values : Values Value [type]) :
    @Eq (Environment Value (type :: types)) (env.prepend values) (env.push (values.get .here)) := by
  cases values with | cons value rest => cases rest; rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    Values (assignment F G) [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons s (.cons a (.cons t (.cons b (.cons unusedRow (.cons unusedScalar .nil)))))

def scalarInputs (s a t b unusedRow unusedScalar : F) :
    Values (assignment F G) [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons s (.cons a (.cons t (.cons b (.cons unusedRow (.cons unusedScalar .nil)))))

theorem scale_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (s a : F) :
    scaleBody.denote (Evaluation.meaning sites table) (Values.cons s (.cons a .nil)).get =
      .done (.cons (s * a) .nil) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option smartUnfolding true in
theorem formula_expansion {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (s a t b unusedRow unusedScalar : F) :
    formulaBody.denote (Evaluation.meaning sites table)
      (scalarInputs s a t b unusedRow unusedScalar).get =
      (invoke table scaleHelper (.cons s (.cons a .nil))).bind fun left =>
        (invoke table scaleHelper (.cons t (.cons b .nil))).bind fun right =>
          .done (.cons (left.get .here - right.get .here + 3) .nil) := by
  simp only [formulaBody, scalarInputs, Region.denote, Evaluation.meaning,
    Evaluation.operation, Op.results, Op.arguments, Operands.eval, Regions.denote, Values.get_cons, Values.get,
    prepend_one, Environment.prepend, Environment.push, PIR.Proc.bind, Nat.cast_ofNat]

theorem scale_equation (s a : F) :
    invoke (program.payload.tables F G).closed scaleHelper (.cons s (.cons a .nil)) =
      .done (.cons (s * a) .nil) :=
  (program.payload.closed_body_view_as scaleDefinition scale_member scaleHelper scale_signature
    scaleBody scale_exact (.cons s (.cons a .nil))).trans (scale_body _ _ s a)

theorem formula_equation (s a t b unusedRow unusedScalar : F) :
    invoke (program.payload.tables F G).closed formulaHelper
      (scalarInputs s a t b unusedRow unusedScalar) =
        .done (.cons (s * a - t * b + 3) .nil) := by
  refine (program.payload.closed_body_view_as formulaDefinition formula_member formulaHelper formula_signature
    formulaBody formula_exact (scalarInputs s a t b unusedRow unusedScalar)).trans ?_
  rw [formula_expansion, scale_equation]
  simp only [PIR.Proc.bind]
  rw [scale_equation]
  rfl

set_option smartUnfolding true in
/-- Every row is checked, including the formula's unused fifth operand. The
interleaved scalar broadcasts retain their original positions. -/
theorem map_equation (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F)
    (small : a.length < indexLimit) (sameB : b.length = a.length)
    (sameUnused : unusedRow.length = a.length) :
    Evaluation.denoteMap (program.payload.tables F G).closed mapSpec
      (inputs s a t b unusedRow unusedScalar) =
        .done (.cons (List.zipWith (fun x y => s * x - t * y + 3) a b) .nil) := by
  let tuple : Nat → Values (assignment F G) [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] := fun index =>
    scalarInputs s (a[index]?.getD 0) t (b[index]?.getD 0)
      (unusedRow[index]?.getD 0) unusedScalar
  let formula : Nat → F := fun index => s * a[index]?.getD 0 - t * b[index]?.getD 0 + 3
  have equation := Evaluation.denoteMap_reference (program.payload.tables F G).closed mapSpec
    (inputs s a t b unusedRow unusedScalar) a.length
    (by change Evaluation.mapShape [a.length, b.length, unusedRow.length] = .returned a.length
        rw [sameB, sameUnused]
        exact Evaluation.mapShape_of_equal _ _ small (by simp)) tuple formula
    (by intro index bound
        have boundB : index < b.length := by rw [sameB]; exact bound
        have boundUnused : index < unusedRow.length := by rw [sameUnused]; exact bound
        simp only [inputs, mapSpec, MapSpec.arguments, Evaluation.mapRowArguments,
          List.getElem?_eq_getElem bound, List.getElem?_eq_getElem boundB,
          List.getElem?_eq_getElem boundUnused, tuple, scalarInputs, Option.getD_some]
        rfl)
    (by intro index _; exact formula_equation _ _ _ _ _ _)
  have ordered : (List.range a.length).map formula =
      List.zipWith (fun x y => s * x - t * y + 3) a b := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_zipWith, sameB, Nat.min_self]
    · intro index leftBound rightBound
      have bound : index < a.length := by simpa only [List.length_map, List.length_range] using leftBound
      have boundB : index < b.length := by rw [sameB]; exact bound
      simp only [List.getElem_map, List.getElem_range, formula,
        List.getElem?_eq_getElem bound, List.getElem?_eq_getElem boundB,
        Option.getD_some, List.getElem_zipWith]
  exact equation.trans (congrArg (fun values => PIR.Proc.done (Values.cons values Values.nil)) ordered)


omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem singleton_return {I : PIR.Signature}
    (process : PIR.Proc I (Values (assignment F G) [.vector "bls12-381.fr"])) :
    process.bind (fun values => .done (Values.singleton (Value := assignment F G) (ty := .vector "bls12-381.fr") (values.get .here))) = process := by
  simp only [Values.singleton_get, PIR.Proc.bind_done]

set_option smartUnfolding true in
theorem map_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    mapBody.denote (Evaluation.meaning sites table) (inputs s a t b unusedRow unusedScalar).get =
      Evaluation.denoteMap table mapSpec (inputs s a t b unusedRow unusedScalar) := by
  simp only [mapBody, inputs, mapSpec, MapSpec.arguments, List.map_cons, List.map_nil, ↓reduceIte, Region.denote, Evaluation.meaning, Evaluation.operation,
    Op.arguments, Op.results, Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_one,
    Environment.prepend, Environment.push, PIR.Proc.bind]
  exact singleton_return _

theorem map_invocation (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    invoke (program.payload.tables F G).closed mapHelper (inputs s a t b unusedRow unusedScalar) =
      Evaluation.denoteMap (program.payload.tables F G).closed mapSpec (inputs s a t b unusedRow unusedScalar) :=
  (program.payload.closed_body_view_as mapDefinition map_member mapHelper map_signature
    mapBody map_exact (inputs s a t b unusedRow unusedScalar)).trans (map_body _ _ s a t b unusedRow unusedScalar)

set_option smartUnfolding true in
theorem wrapper_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    wrapperBody.denote (Evaluation.meaning sites table) (inputs s a t b unusedRow unusedScalar).get =
      (sites.mark "s0").bind (fun _ => invoke table mapHelper (inputs s a t b unusedRow unusedScalar)) := by
  simp only [wrapperBody, inputs, Region.denote, Evaluation.meaning, Evaluation.operation,
    Op.arguments, Op.results, Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_one,
    Environment.prepend, Environment.push, PIR.Proc.bind, PIR.Proc.bind_assoc]
  congr 1
  funext _
  exact singleton_return _

set_option smartUnfolding true in
theorem owner_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    ownerBody.denote (Evaluation.meaning sites table) (inputs s a t b unusedRow unusedScalar).get =
      (sites.mark "s0").bind (fun _ => invoke table wrapperHelper (inputs s a t b unusedRow unusedScalar)) := by
  simp only [ownerBody, inputs, Region.denote, Evaluation.meaning, Evaluation.operation,
    Op.arguments, Op.results, Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_one,
    Environment.prepend, Environment.push, PIR.Proc.bind, PIR.Proc.bind_assoc]
  congr 1
  funext _
  exact singleton_return _

theorem wrapper_invocation (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    invoke (program.payload.tables F G).closed wrapperHelper (inputs s a t b unusedRow unusedScalar) =
      .call (.mark "s0") (fun _ =>
        Evaluation.denoteMap (program.payload.tables F G).closed mapSpec (inputs s a t b unusedRow unusedScalar)) := by
  refine (program.payload.closed_body_view_as wrapperDefinition wrapper_member wrapperHelper wrapper_signature
    wrapperBody wrapper_exact (inputs s a t b unusedRow unusedScalar)).trans ?_
  rw [wrapper_body, map_invocation]
  rfl

/-- The owning protocol requires the unused scalar even for empty rows. -/
theorem missing_unused_scalar (a b : List F) :
    program.participant F G 0 (.cons (some 2) (.cons (some a) (.cons (some 3) (.cons (some b) (.cons (some []) (.cons none .nil)))))) = .halt .incomplete := rfl

/-- The nonowner skips the complete Local call. -/
theorem nonowner_equation :
    program.participant F G 1 (.cons none (.cons none (.cons none (.cons none (.cons none (.cons none .nil)))))) = .done (.cons none .nil) := rfl


private theorem input_scopes : program.payload.entry.inputScopes = [[0], [0], [0], [0], [0], [0]] := rfl
private theorem output_scopes : program.payload.entry.outputScopes = [[0]] := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact source expansion keeps the checked Local helper invocation opaque. -/
theorem observed_expansion (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    program.observed F G 0 (inputs s a t b unusedRow unusedScalar).present =
      .call (.mark "s0") (fun _ =>
        (invoke (program.payload.tables F G).closed wrapperHelper (inputs s a t b unusedRow unusedScalar)).bind
          fun values => .done values.present) := by
  rw [program.observed_body_view entryBody entry_exact 0 (inputs s a t b unusedRow unusedScalar).present,
    input_scopes, output_scopes]
  have input_mask : maskValues 0 [[0], [0], [0], [0], [0], [0]] (inputs (G := G) s a t b unusedRow unusedScalar).present =
      (inputs (G := G) s a t b unusedRow unusedScalar).present := maskValues_single_role 0 _
  have output_mask (values : Values (Component (assignment F G)) [.vector "bls12-381.fr"]) :
      maskValues 0 [[0]] values = values := maskValues_single_role 0 values
  rw [input_mask]
  have env : @Eq (Environment (Component (assignment F G)) [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"])
      (inputs s a t b unusedRow unusedScalar).present.get (fun ref => some ((inputs s a t b unusedRow unusedScalar).get ref)) := by
    funext type ref
    exact Values.get_present _ _
  rw [owner_projection.protocol_table_independent _ _ [], env,
    owner_projection.denote_present _ program.payload.tables_adequate]
  set_option smartUnfolding true in
    rw [owner_body]
    simp only [PIR.Proc.bind_assoc, PIR.Proc.bind, output_mask, PIR.Proc.bind_done, observedSites]


/-- The complete retained protocol preserves both reached source marks. -/
theorem observed_equation (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F)
    (small : a.length < indexLimit) (sameB : b.length = a.length)
    (sameUnused : unusedRow.length = a.length) :
    program.observed F G 0 (inputs s a t b unusedRow unusedScalar).present =
      .call (.mark "s0") (fun _ => .call (.mark "s0")
        (fun _ => .done (.cons (some (List.zipWith (fun x y => s * x - t * y + 3) a b)) .nil))) := by
  rw [observed_expansion]
  rw [wrapper_invocation, map_equation s a t b unusedRow unusedScalar small sameB sameUnused]
  rfl

/-- Full source result for the owner after erasing internal site observations. -/
theorem owner_equation (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F)
    (small : a.length < indexLimit) (sameB : b.length = a.length)
    (sameUnused : unusedRow.length = a.length) :
    program.participant F G 0 (inputs s a t b unusedRow unusedScalar).present =
      .done (.cons (some (List.zipWith (fun x y => s * x - t * y + 3) a b)) .nil) := by
  unfold Program.participant
  rw [observed_equation s a t b unusedRow unusedScalar small sameB sameUnused]
  rfl


/-- The exact source preserves the ordered map shape failure after its marks. -/
theorem owner_shape_failure (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) (reason : PIR.Stop)
    (shape : Evaluation.mapShape [a.length, b.length, unusedRow.length] = .stopped reason) :
    program.participant F G 0 (inputs s a t b unusedRow unusedScalar).present = .halt reason := by
  have stopped := Evaluation.denoteMap_shape_stops (program.payload.tables F G).closed
    mapSpec (inputs s a t b unusedRow unusedScalar) reason shape
  have observed : program.observed F G 0 (inputs s a t b unusedRow unusedScalar).present =
      .call (.mark "s0") (fun _ => .call (.mark "s0") (fun _ => .halt reason)) := by
    rw [observed_expansion]
    rw [wrapper_invocation, stopped]
    rfl
  unfold Program.participant
  rw [observed]
  rfl

end ZkcExamples.Structured.MapCombination
