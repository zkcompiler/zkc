module

public import Zkc.Verification.Installations.Sumcheck.Source.Checks
public import Zkc.IR.Source.Structured.ComponentClosure
public import Zkc.IR.Source.Structured.SumReference
public import Zkc.Applications.IR.Structured.OriginalSumcheckRoots

@[expose] public section
/-! Source-instance controls for both retained roots. The reusable terminal
laws live in OriginalSumcheckChecks without a concrete-root import. -/
set_option autoImplicit false
set_option maxRecDepth 50000
noncomputable section

namespace ZkcExamples.Structured.OriginalSumcheckInstances
open Zkc.Source Zkc.Source.Structured

namespace Small

abbrev collectBindings : MultilinearCollectBodies.Bindings :=
  ⟨"_finite_admission_0",
    "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain",
    "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body",
    "_mathematical_admission_1"⟩

abbrev prefixBindings : MultilinearPrefixBodies.Bindings :=
  ⟨"_finite_admission_3", "_mathematical_admission_2", ⟨"zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402",
    "finite_zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402_s0_domain",
    "finite_zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402_s0_body"⟩⟩

theorem first_bodies : MapFirstContracts.Bodies payload.definitions collectBindings := by
  bind_structured_bodies

theorem prefix_bodies : MapPrefixContracts.Bodies payload.definitions prefixBindings := by
  bind_structured_bodies

theorem terminal_bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions :=
  ⟨prefixBindings, {
    first := ⟨collectBindings, first_bodies⟩
    restriction := prefix_bodies
    check := by bind_structured_bodies
    checkTable := by bind_structured_bodies }⟩

theorem producer_bodies : SumcheckUnitContracts.Bodies payload.definitions where
  first := ⟨collectBindings, first_bodies⟩
  sums := by bind_structured_bodies
  empty := helpers_bound.empty
  append := helpers_bound.append
  values := helpers_bound.values
  width := helpers_bound.width
  «variables» := helpers_bound.«variables»

end Small

namespace Two

abbrev collectBindings : MultilinearCollectBodies.Bindings :=
  ⟨"_finite_admission_0",
    "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain",
    "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body",
    "_mathematical_admission_1"⟩

abbrev prefixBindings : MultilinearPrefixBodies.Bindings :=
  ⟨"_finite_admission_3", "_mathematical_admission_2", ⟨"zkl_742995c5dba6615877ef9df6684411ce6d37b702a1b704411cf4a90c38cfad37",
    "finite_zkl_742995c5dba6615877ef9df6684411ce6d37b702a1b704411cf4a90c38cfad37_s0_domain",
    "finite_zkl_742995c5dba6615877ef9df6684411ce6d37b702a1b704411cf4a90c38cfad37_s0_body"⟩⟩

theorem first_bodies : MapFirstContracts.Bodies payload.definitions collectBindings := by
  bind_structured_bodies

theorem prefix_bodies : MapPrefixContracts.Bodies payload.definitions prefixBindings := by
  bind_structured_bodies

theorem terminal_bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions :=
  ⟨prefixBindings, {
    first := ⟨collectBindings, first_bodies⟩
    restriction := prefix_bodies
    check := by bind_structured_bodies
    checkTable := by bind_structured_bodies }⟩

theorem producer_bodies : SumcheckUnitContracts.Bodies payload.definitions where
  first := ⟨collectBindings, first_bodies⟩
  sums := by bind_structured_bodies
  empty := helpers_bound.empty
  append := helpers_bound.append
  values := helpers_bound.values
  width := helpers_bound.width
  «variables» := helpers_bound.«variables»

end Two

end ZkcExamples.Structured.OriginalSumcheckInstances

namespace ZkcExamples.Structured.OriginalSumcheckRoots.Two
open Zkc.Source Zkc.Source.Structured

abbrev bothBody := Generated.Bindings.TwoSumsInputs.helper25Body

theorem both_body : BodyIn payload.definitions bothHelper bothBody :=
  by bind_structured_bodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
theorem both_present (left right : Bool) :
    combine (OriginalSumcheckLibrary.helpers (F := F) (G := G) payload)
      (.cons (some left) .nil) (.cons (some right) .nil) =
      .done (.cons (some (left && right)) .nil) := by
  let args : Values (assignment F G) bothHelper.inputs := .cons left (.cons right .nil)
  change invoke (OriginalSumcheckLibrary.helpers (F := F) (G := G) payload).toOn.components
    bothHelper args.present = _
  rw [OriginalSumcheckLibrary.helpers_on]
  refine (Evaluation.component_invoke_closed (ringModel F G)
    (interface := OriginalSumcheckLibrary.signature (F := F) (G := G))
    payload.definitions bothHelper args).trans ?_
  have calculation := (ReferenceLibrary.Sum.both (ringModel F G)).invoke
    (helper := bothHelper) payload.definitions payload.linked both_body args trivial
  refine (congrArg (fun process : PIR.Process closedInterface
    (Values (assignment F G) bothHelper.outputs) =>
      (process.interpret (closedLift (I := OriginalSumcheckLibrary.signature (F := F) (G := G)))).bind
        (fun values => .done values.present)) calculation).trans ?_
  cases left <;> rfl

end ZkcExamples.Structured.OriginalSumcheckRoots.Two
