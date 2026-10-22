module

public import ZkcExamples.Structured.MapConstantViews
public import Zkc.Source.Structured.MapLaws
public import Zkc.Source.Structured.ClosedProjection

@[expose] public section

/-! An input-independent formula still checks every retained row shape and
requires all owned inputs. Its formula is derived from the exact Math body. -/
namespace ZkcExamples.Structured.MapConstant
open Zkc.Source Zkc.Source.Structured MapConstantViews
set_option linter.unusedSimpArgs false
set_option smartUnfolding false

private theorem prepend_one {Value : Ty → Type} {types : List Ty} {type : Ty}
    (env : Environment Value types) (values : Values Value [type]) :
    @Eq (Environment Value (type :: types)) (env.prepend values) (env.push (values.get .here)) := by
  cases values with | cons value rest => cases rest; rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (a b : List F) (unusedScalar : F) : Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons a (.cons b (.cons unusedScalar .nil))

theorem formula_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (a b unusedScalar : F) :
    formulaBody.denote (Evaluation.meaning sites table)
      (Values.cons a (.cons b (.cons unusedScalar .nil))).get =
        .done (.cons (7 : F) .nil) := rfl

theorem formula_equation (a b unusedScalar : F) :
    invoke (program.payload.tables F G).closed formulaHelper
      (.cons a (.cons b (.cons unusedScalar .nil))) = .done (.cons (7 : F) .nil) :=
  (program.payload.closed_body_view_as formulaDefinition formula_member formulaHelper formula_signature
    formulaBody formula_exact (.cons a (.cons b (.cons unusedScalar .nil)))).trans
      (formula_body _ _ a b unusedScalar)

/-- Constant results preserve the checked row count, including zero. -/
theorem map_equation (a b : List F) (unusedScalar : F)
    (small : a.length < indexLimit) (sameLength : b.length = a.length) :
    Evaluation.denoteMap (program.payload.tables F G).closed mapSpec (inputs a b unusedScalar) =
      .done (.cons (List.replicate a.length (7 : F)) .nil) := by
  have equation := Evaluation.denoteMap_twoRows_broadcast (program.payload.tables F G).closed
    mapSpec.helperName mapSpec.field a b unusedScalar small sameLength (fun _ _ => (7 : F))
    (fun x y => formula_equation x y unusedScalar)
  have values : List.zipWith (fun (_ _ : F) => (7 : F)) a b = List.replicate a.length 7 := by
    apply List.ext_getElem
    · simp only [List.length_zipWith, List.length_replicate, sameLength, Nat.min_self]
    · intro index leftBound rightBound
      simp only [List.getElem_zipWith, List.getElem_replicate]
  exact equation.trans (congrArg (fun values => PIR.Process.done (Values.cons values Values.nil)) values)


omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem singleton_return {I : PIR.Signature}
    (process : PIR.Process I (Values (assignment F G) [.vector "bls12-381.fr"])) :
    process.bind (fun values => .done (Values.singleton (Value := assignment F G) (ty := .vector "bls12-381.fr") (values.get .here))) = process := by
  simp only [Values.singleton_get, PIR.Process.bind_done]

set_option smartUnfolding true in
theorem map_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (a b : List F) (unusedScalar : F) :
    mapBody.denote (Evaluation.meaning sites table) (inputs a b unusedScalar).get =
      Evaluation.denoteMap table mapSpec (inputs a b unusedScalar) := by
  simp only [mapBody, inputs, mapSpec, MapSpec.arguments, List.map_cons, List.map_nil, ↓reduceIte, Region.denote, Evaluation.meaning, Evaluation.operation,
    Op.arguments, Op.results, Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_one,
    Environment.prepend, Environment.push, PIR.Process.bind]
  exact singleton_return _

theorem map_invocation (a b : List F) (unusedScalar : F) :
    invoke (program.payload.tables F G).closed mapHelper (inputs a b unusedScalar) =
      Evaluation.denoteMap (program.payload.tables F G).closed mapSpec (inputs a b unusedScalar) :=
  (program.payload.closed_body_view_as mapDefinition map_member mapHelper map_signature
    mapBody map_exact (inputs a b unusedScalar)).trans (map_body _ _ a b unusedScalar)

set_option smartUnfolding true in
theorem wrapper_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (a b : List F) (unusedScalar : F) :
    wrapperBody.denote (Evaluation.meaning sites table) (inputs a b unusedScalar).get =
      (sites.mark "s0").bind (fun _ => invoke table mapHelper (inputs a b unusedScalar)) := by
  simp only [wrapperBody, inputs, Region.denote, Evaluation.meaning, Evaluation.operation,
    Op.arguments, Op.results, Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_one,
    Environment.prepend, Environment.push, PIR.Process.bind, PIR.Process.bind_assoc]
  congr 1
  funext _
  exact singleton_return _

set_option smartUnfolding true in
theorem owner_body {I : PIR.Signature} (sites : SiteObservations I)
    (table : Evaluation.Meanings F G I) (a b : List F) (unusedScalar : F) :
    ownerBody.denote (Evaluation.meaning sites table) (inputs a b unusedScalar).get =
      (sites.mark "s0").bind (fun _ => invoke table wrapperHelper (inputs a b unusedScalar)) := by
  simp only [ownerBody, inputs, Region.denote, Evaluation.meaning, Evaluation.operation,
    Op.arguments, Op.results, Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_one,
    Environment.prepend, Environment.push, PIR.Process.bind, PIR.Process.bind_assoc]
  congr 1
  funext _
  exact singleton_return _

theorem wrapper_invocation (a b : List F) (unusedScalar : F) :
    invoke (program.payload.tables F G).closed wrapperHelper (inputs a b unusedScalar) =
      .call (.mark "s0") (fun _ =>
        Evaluation.denoteMap (program.payload.tables F G).closed mapSpec (inputs a b unusedScalar)) := by
  refine (program.payload.closed_body_view_as wrapperDefinition wrapper_member wrapperHelper wrapper_signature
    wrapperBody wrapper_exact (inputs a b unusedScalar)).trans ?_
  rw [wrapper_body, map_invocation]
  rfl

/-- The owning protocol requires the unused scalar even for empty rows. -/
theorem missing_unused_scalar (a b : List F) :
    program.participant F G 0 (.cons (some a) (.cons (some b) (.cons none .nil))) = .halt .incomplete := rfl

/-- The nonowner skips the complete Local call. -/
theorem nonowner_equation :
    program.participant F G 1 (.cons none (.cons none (.cons none .nil))) = .done (.cons none .nil) := rfl


private theorem input_scopes : program.payload.entry.inputScopes = [[0], [0], [0]] := rfl
private theorem output_scopes : program.payload.entry.outputScopes = [[0]] := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact source expansion keeps the checked Local helper invocation opaque. -/
theorem observed_expansion (a b : List F) (unusedScalar : F) :
    program.observed F G 0 (inputs a b unusedScalar).present =
      .call (.mark "s0") (fun _ =>
        (invoke (program.payload.tables F G).closed wrapperHelper (inputs a b unusedScalar)).bind
          fun values => .done values.present) := by
  rw [program.observed_body_view entryBody entry_exact 0 (inputs a b unusedScalar).present,
    input_scopes, output_scopes]
  have input_mask : maskValues 0 [[0], [0], [0]] (inputs (G := G) a b unusedScalar).present =
      (inputs (G := G) a b unusedScalar).present := maskValues_single_role 0 _
  have output_mask (values : Values (Component (assignment F G)) [.vector "bls12-381.fr"]) :
      maskValues 0 [[0]] values = values := maskValues_single_role 0 values
  rw [input_mask]
  have env : @Eq (Environment (Component (assignment F G)) [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"])
      (inputs a b unusedScalar).present.get (fun ref => some ((inputs a b unusedScalar).get ref)) := by
    funext type ref
    exact Values.get_present _ _
  rw [owner_projection.protocol_table_independent _ _ [], env,
    owner_projection.denote_present _ program.payload.tables_adequate]
  set_option smartUnfolding true in
    rw [owner_body]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind, output_mask, PIR.Process.bind_done, observedSites]


/-- The complete retained protocol preserves both reached source marks. -/
theorem observed_equation (a b : List F) (unusedScalar : F)
    (small : a.length < indexLimit) (sameLength : b.length = a.length) :
    program.observed F G 0 (inputs a b unusedScalar).present =
      .call (.mark "s0") (fun _ => .call (.mark "s0")
        (fun _ => .done (.cons (some (List.replicate a.length (7 : F))) .nil))) := by
  rw [observed_expansion]
  rw [wrapper_invocation, map_equation a b unusedScalar small sameLength]
  rfl

/-- Full source result for the owner after erasing internal site observations. -/
theorem owner_equation (a b : List F) (unusedScalar : F)
    (small : a.length < indexLimit) (sameLength : b.length = a.length) :
    program.participant F G 0 (inputs a b unusedScalar).present =
      .done (.cons (some (List.replicate a.length (7 : F))) .nil) := by
  unfold Program.participant
  rw [observed_equation a b unusedScalar small sameLength]
  rfl


/-- The exact source preserves the ordered map shape failure after its marks. -/
theorem owner_shape_failure (a b : List F) (unusedScalar : F) (reason : PIR.Stop)
    (shape : Evaluation.mapShape [a.length, b.length] = .stopped reason) :
    program.participant F G 0 (inputs a b unusedScalar).present = .halt reason := by
  have stopped := Evaluation.denoteMap_shape_stops (program.payload.tables F G).closed
    mapSpec (inputs a b unusedScalar) reason shape
  have observed : program.observed F G 0 (inputs a b unusedScalar).present =
      .call (.mark "s0") (fun _ => .call (.mark "s0") (fun _ => .halt reason)) := by
    rw [observed_expansion]
    rw [wrapper_invocation, stopped]
    rfl
  unfold Program.participant
  rw [observed]
  rfl

end ZkcExamples.Structured.MapConstant
