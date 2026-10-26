module

public import ZkcExamples.Structured.MapCombinationViews
public import Zkc.Source.Structured.CollectLaws
public import Zkc.Source.DeriveRegion
public import ZkcExamples.Structured.MapObservations
public import Zkc.Source.Structured.ClosedProjection

@[expose] public section

/-! Independent arithmetic client of the retained map. Helper equations come
from the complete checked source table, including the nested scale calls. -/
namespace ZkcExamples.Structured.MapCombination
open Zkc.Source Zkc.Source.Structured MapCombinationViews MapCombinationBodies
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding true

private theorem prepend_one {Value : Ty → Type} {types : List Ty} {type : Ty}
    (env : Environment Value types) (values : Values Value [type]) :
    @Eq (Environment Value (type :: types)) (env.prepend values) (env.push (values.get .here)) := by
  cases values with | cons value rest => cases rest; rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    Values (assignment F G) [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons s (.cons a (.cons t (.cons b (.cons unusedRow (.cons unusedScalar .nil)))))

/-- Domain rows precede the broadcasts at the private collection boundary. -/
def collectionInputs (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    Values (assignment F G) mapHelper.inputs :=
  .cons a (.cons b (.cons unusedRow (.cons s (.cons t (.cons unusedScalar .nil)))))

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
    Evaluation.operation, Op.results, Operands.eval, Regions.denote, Values.get_cons, Values.get,
    prepend_one, Environment.push, PIR.Process.bind, Nat.cast_ofNat]

theorem scale_equation (s a : F) :
    invoke (program.payload.tables F G).closed scaleHelper (.cons s (.cons a .nil)) =
      .done (.cons (s * a) .nil) :=
  (program.payload.closed_body_view_as scaleDefinition scale_member scaleHelper scale_signature
    scaleBody scale_shared_raw (.cons s (.cons a .nil))).trans (scale_body _ _ s a)

theorem formula_equation (s a t b unusedRow unusedScalar : F) :
    invoke (program.payload.tables F G).closed formulaHelper
      (scalarInputs s a t b unusedRow unusedScalar) =
        .done (.cons (s * a - t * b + 3) .nil) := by
  refine (program.payload.closed_body_view_as formulaDefinition formula_member formulaHelper formula_signature
    formulaBody formula_shared_raw (scalarInputs s a t b unusedRow unusedScalar)).trans ?_
  rw [formula_expansion, scale_equation]
  simp only [PIR.Process.bind]
  rw [scale_equation]
  rfl

theorem realization_equation (s x t y unusedItem unusedScalar : F) :
    invoke (program.payload.tables F G).closed formulaRealizationHelper
      (scalarInputs s x t y unusedItem unusedScalar) =
      .done (.cons (s * x - t * y + 3) .nil) := by
  rw [program.payload.closed_body_view_as formulaRealizationDefinition formulaRealization_member
    formulaRealizationHelper formulaRealization_signature formulaRealizationBody
    formulaRealization_shared_raw (scalarInputs s x t y unusedItem unusedScalar)]
  have expanded : formulaRealizationBody.denote
      (Evaluation.meaning (observedSites F G) (program.payload.tables F G).closed)
      (scalarInputs s x t y unusedItem unusedScalar).get =
        (invoke (program.payload.tables F G).closed formulaHelper
          (scalarInputs s x t y unusedItem unusedScalar)).bind fun result =>
            .done (.cons (result.get .here) .nil) := by derive_process
  rw [expanded, formula_equation]
  rfl

theorem callback_equation (s x t y unusedItem unusedScalar : F) (a b unusedRow : List F) :
    invoke (program.payload.tables F G).closed mapCallbackHelper
      (.cons x (.cons y (.cons unusedItem (.cons a (.cons b (.cons unusedRow
        (.cons s (.cons t (.cons unusedScalar .nil))))))))) =
      .call (.mark "body") fun _ => .done (.cons (s * x - t * y + 3) .nil) := by
  rw [program.payload.closed_body_view_as mapCallbackDefinition mapCallback_member
    mapCallbackHelper mapCallback_signature mapCallbackBody mapCallback_shared_raw
    (.cons x (.cons y (.cons unusedItem (.cons a (.cons b (.cons unusedRow
      (.cons s (.cons t (.cons unusedScalar .nil)))))))))]
  have expanded : mapCallbackBody.denote
      (Evaluation.meaning (observedSites F G) (program.payload.tables F G).closed)
      (Values.cons x (.cons y (.cons unusedItem (.cons a (.cons b (.cons unusedRow
        (.cons s (.cons t (.cons unusedScalar .nil))))))))).get =
      .call (.mark "body") fun _ =>
        (invoke (program.payload.tables F G).closed formulaRealizationHelper
          (scalarInputs s x t y unusedItem unusedScalar)).bind fun result =>
            .done (.cons (result.get .here) .nil) := by derive_process
  rw [expanded, realization_equation]
  rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem domain_admit (a b unusedRow : List F) (small : a.length < indexLimit)
    (sameB : b.length = a.length) (sameUnused : unusedRow.length = a.length) :
    collectSpec.domain.admit (carriers := uniformCarriers F G)
      (.cons a (.cons b (.cons unusedRow .nil))) =
      .returned (((a.zip b).zip unusedRow).map fun pair =>
        .cons pair.1.1 (.cons pair.1.2 (.cons pair.2 .nil))) := by
  change Finite.continueWith
    (if a.length < indexLimit then
      .returned (a.map fun x => (Values.cons x .nil : Values (assignment F G) [.field "bls12-381.fr"]))
    else .stopped .exhausted) (fun xs =>
      Finite.continueWith
        (if b.length < indexLimit then
          .returned (b.map fun x => (Values.cons x .nil : Values (assignment F G) [.field "bls12-381.fr"]))
        else .stopped .exhausted) (fun ys =>
          Finite.continueWith (zipDomainRows (.cons xs (.cons ys .nil))) (fun first =>
            Finite.continueWith
              (if unusedRow.length < indexLimit then
                .returned (unusedRow.map fun x =>
                  (Values.cons x .nil : Values (assignment F G) [.field "bls12-381.fr"]))
              else .stopped .exhausted) (fun unused =>
                Finite.continueWith (zipDomainRows (.cons first (.cons unused .nil)))
                  (fun rows => .returned rows))))) = _
  simp only [sameB, sameUnused, small, ↓reduceIte, Finite.continueWith, zipDomainRows,
    List.map_map, Values.append, List.length_map, List.length_zip, Nat.min_self,
    List.zip_map, Function.comp_def, Prod.map_fst, Prod.map_snd]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- A mismatch in the first two rows stops before the later row is inspected.
No size hypothesis is needed for that later, unused row. -/
theorem domain_mismatch_before_unused (a b unusedRow : List F)
    (smallA : a.length < indexLimit) (smallB : b.length < indexLimit)
    (different : a.length ≠ b.length) :
    collectSpec.domain.admit (carriers := uniformCarriers F G)
      (.cons a (.cons b (.cons unusedRow .nil))) = .stopped .refused := by
  change Finite.continueWith
    (if a.length < indexLimit then
      .returned (a.map fun x => (Values.cons x .nil : Values (assignment F G) [.field "bls12-381.fr"]))
    else .stopped .exhausted) (fun xs =>
      Finite.continueWith
        (if b.length < indexLimit then
          .returned (b.map fun x => (Values.cons x .nil : Values (assignment F G) [.field "bls12-381.fr"]))
        else .stopped .exhausted) (fun ys =>
          Finite.continueWith (zipDomainRows (.cons xs (.cons ys .nil))) (fun first =>
            Finite.continueWith
              (if unusedRow.length < indexLimit then
                .returned (unusedRow.map fun x =>
                  (Values.cons x .nil : Values (assignment F G) [.field "bls12-381.fr"]))
              else .stopped .exhausted) (fun unused =>
                Finite.continueWith (zipDomainRows (.cons first (.cons unused .nil)))
                  (fun rows => .returned rows))))) = _
  simp only [smallA, smallB, ↓reduceIte, Finite.continueWith, zipDomainRows,
    List.length_map, different]

/-- Every retained row is admitted before callbacks, including the unused row.
Broadcasts are restored to the scalar formula's original argument positions. -/
theorem map_equation (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F)
    (small : a.length < indexLimit) (sameB : b.length = a.length)
    (sameUnused : unusedRow.length = a.length) :
    Evaluation.denoteCollect (program.payload.tables F G).closed collectSpec
      (collectionInputs s a t b unusedRow unusedScalar) =
      (MapObservations.rows (List.zipWith (fun x y => s * x - t * y + 3) a b)).bind
        fun values => .done (.cons values .nil) := by
  have equation := Evaluation.denoteCollect_process (program.payload.tables F G).closed
    collectSpec (.cons a (.cons b (.cons unusedRow .nil)))
    (.cons s (.cons t (.cons unusedScalar .nil))) ((a.zip b).zip unusedRow)
    (fun pair => .cons pair.1.1 (.cons pair.1.2 (.cons pair.2 .nil)))
    (domain_admit a b unusedRow small sameB sameUnused) rfl
    (fun pair => .call (.mark "body") fun _ => .done (s * pair.1.1 - t * pair.1.2 + 3))
    (fun pair => callback_equation s pair.1.1 t pair.1.2 pair.2 unusedScalar a b unusedRow)
  have values : ((a.zip b).zip unusedRow).map (fun pair => s * pair.1.1 - t * pair.1.2 + 3) =
      List.zipWith (fun x y => s * x - t * y + 3) a b := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_zip, List.length_zipWith, sameB, sameUnused, Nat.min_self]
    · intro index leftBound rightBound
      simp only [List.getElem_map, List.getElem_zip, List.getElem_zipWith]
  rw [MapObservations.rows_map ((a.zip b).zip unusedRow)
    (fun pair => s * pair.1.1 - t * pair.1.2 + 3), values] at equation
  exact equation


omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem singleton_return {I : PIR.Signature}
    (process : PIR.Process I (Values (assignment F G) [.vector "bls12-381.fr"])) :
    process.bind (fun values => .done (Values.singleton (Value := assignment F G) (ty := .vector "bls12-381.fr") (values.get .here))) = process := by
  simp only [Values.singleton_get, PIR.Process.bind_done]

set_option smartUnfolding true in
theorem map_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    mapBody.denote (Evaluation.meaning sites table) (collectionInputs s a t b unusedRow unusedScalar).get =
      Evaluation.denoteCollect table collectSpec (collectionInputs s a t b unusedRow unusedScalar) := by
  simp only [mapBody, collectionInputs, collectSpec, Region.denote, Evaluation.meaning, Evaluation.operation,
    Op.results, Operands.eval, Regions.denote, Values.get_cons, prepend_one,
    Environment.push]
  exact singleton_return _

theorem map_invocation (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    invoke (program.payload.tables F G).closed mapHelper (collectionInputs s a t b unusedRow unusedScalar) =
      Evaluation.denoteCollect (program.payload.tables F G).closed collectSpec (collectionInputs s a t b unusedRow unusedScalar) :=
  (program.payload.closed_body_view_as mapDefinition map_member mapHelper map_signature
    mapBody map_shared_raw (collectionInputs s a t b unusedRow unusedScalar)).trans (map_body _ _ s a t b unusedRow unusedScalar)

set_option smartUnfolding true in
theorem wrapper_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    wrapperBody.denote (Evaluation.meaning sites table) (inputs s a t b unusedRow unusedScalar).get =
      (sites.mark "s0").bind (fun _ => invoke table mapHelper (collectionInputs s a t b unusedRow unusedScalar)) := by
  simp only [wrapperBody, inputs, collectionInputs, Region.denote, Evaluation.meaning, Evaluation.operation,
    Op.results, Operands.eval, Regions.denote, Values.get_cons, prepend_one,
    Environment.prepend, Environment.push, PIR.Process.bind, PIR.Process.bind_assoc]
  congr 1
  funext _
  exact singleton_return _

set_option smartUnfolding true in
theorem owner_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    ownerBody.denote (Evaluation.meaning sites table) (inputs s a t b unusedRow unusedScalar).get =
      (sites.mark "s0").bind (fun _ => invoke table wrapperHelper (inputs s a t b unusedRow unusedScalar)) := by
  simp only [ownerBody, inputs, Region.denote, Evaluation.meaning, Evaluation.operation,
    Op.results, Operands.eval, Regions.denote, Values.get_cons, prepend_one,
    Environment.prepend, Environment.push, PIR.Process.bind, PIR.Process.bind_assoc]
  congr 1
  funext _
  exact singleton_return _

theorem wrapper_invocation (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) :
    invoke (program.payload.tables F G).closed wrapperHelper (inputs s a t b unusedRow unusedScalar) =
      .call (.mark "s0") (fun _ =>
        Evaluation.denoteCollect (program.payload.tables F G).closed collectSpec (collectionInputs s a t b unusedRow unusedScalar)) := by
  refine (program.payload.closed_body_view_as wrapperDefinition wrapper_member wrapperHelper wrapper_signature
    wrapperBody wrapper_shared_raw (inputs s a t b unusedRow unusedScalar)).trans ?_
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
    owner_projection.denote_present (program.payload.tables F G)
      program.payload.tables_adequate (inputs s a t b unusedRow unusedScalar).get]
  set_option smartUnfolding true in
    rw [owner_body]
    simp only [PIR.Process.bind, output_mask, PIR.Process.bind_done, observedSites]


/-- The complete retained protocol preserves both reached source marks. -/
theorem observed_equation (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F)
    (small : a.length < indexLimit) (sameB : b.length = a.length)
    (sameUnused : unusedRow.length = a.length) :
    program.observed F G 0 (inputs s a t b unusedRow unusedScalar).present =
      .call (.mark "s0") (fun _ => .call (.mark "s0")
        (fun _ => (MapObservations.rows (List.zipWith (fun x y => s * x - t * y + 3) a b)).bind
          fun values => .done (.cons (some values) .nil))) := by
  rw [observed_expansion]
  rw [wrapper_invocation, map_equation s a t b unusedRow unusedScalar small sameB sameUnused]
  simp only [PIR.Process.bind, PIR.Process.bind_assoc]
  rfl

/-- Full source result for the owner after erasing internal site observations. -/
theorem owner_equation (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F)
    (small : a.length < indexLimit) (sameB : b.length = a.length)
    (sameUnused : unusedRow.length = a.length) :
    program.participant F G 0 (inputs s a t b unusedRow unusedScalar).present =
      .done (.cons (some (List.zipWith (fun x y => s * x - t * y + 3) a b)) .nil) := by
  unfold Program.participant
  rw [observed_equation s a t b unusedRow unusedScalar small sameB sameUnused]
  simp only [PIR.Process.interpret, forgetSites, PIR.Process.bind,
    PIR.Process.interpret_bind, MapObservations.rows_forget]


/-- The exact source preserves the ordered map shape failure after its marks. -/
theorem owner_shape_failure (s : F) (a : List F) (t : F) (b unusedRow : List F) (unusedScalar : F) (reason : PIR.Stop)
    (shape : collectSpec.domain.admit (carriers := uniformCarriers F G)
      (.cons a (.cons b (.cons unusedRow .nil))) = .stopped reason) :
    program.participant F G 0 (inputs s a t b unusedRow unusedScalar).present = .halt reason := by
  have stopped := Evaluation.denoteCollect_admission_stop (program.payload.tables F G).closed
    collectSpec (.cons a (.cons b (.cons unusedRow .nil)))
    (.cons s (.cons t (.cons unusedScalar .nil))) reason shape
  change Evaluation.denoteCollect (program.payload.tables F G).closed collectSpec
    (collectionInputs s a t b unusedRow unusedScalar) = .halt reason at stopped
  have observed : program.observed F G 0 (inputs s a t b unusedRow unusedScalar).present =
      .call (.mark "s0") (fun _ => .call (.mark "s0") (fun _ => .halt reason)) := by
    rw [observed_expansion]
    rw [wrapper_invocation, stopped]
    rfl
  unfold Program.participant
  rw [observed]
  rfl

end ZkcExamples.Structured.MapCombination
