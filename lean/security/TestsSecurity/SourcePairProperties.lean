module

public import ZkcSecurity.Bindings.Source.RootPair
public import ZkcSecurity.Bindings.Sumcheck.SourcePairReduction
public import ZkcSecurityExamples.Sumcheck.SourceRootReference

@[expose] public section

/-! A non-Boolean residual composes through two shared-challenge phases. The
second phase uses the actual first reply; marginal success is insufficient.
These checks also exclude successful stopping; an unowned delivery remains a
concrete unsatisfied membership obligation.
-/
set_option autoImplicit false
namespace TestsSecurity.SourcePairProperties
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Source

def scope : PairScope := ⟨0, 1, [("challenge", "delivery")]⟩
variable {carriers : Carriers}

def drawP (field : String) : PIR.Process (Occurrence.signature carriers) (carriers.Field field) :=
  .call (.action (.receive (.field field) "delivery" 1)) .done

def drawV (field : String) : PIR.Process (Occurrence.signature carriers) (carriers.Field field) :=
  .call (.action (.query "challenge" field (.cons 7 .nil))) fun reply =>
    .call (.action (.send (ty := .field field) "delivery" 0 reply)) fun _ => .done reply

theorem paired_draw (field : String) : Pair scope Eq
    (drawP (carriers := carriers) field) (drawV field) :=
  .challenge field "challenge" "delivery" 0 1 7 ⟨rfl, rfl⟩ (by simp [scope])
    (fun reply => .done rfl)

def secondP (field : String) (first : carriers.Field field) :
    PIR.Process (Occurrence.signature carriers) (carriers.Field field × carriers.Field field) :=
  PIR.Process.call (.action (.send (ty := .field field) "captured" 1 first)) fun _ =>
    (drawP field).bind fun second => .done (first, second)

def secondV (field : String) (_first : carriers.Field field) :
    PIR.Process (Occurrence.signature carriers) (carriers.Field field × carriers.Field field) :=
  PIR.Process.call (.action (.receive (.field field) "captured" 0)) fun received =>
    (drawV field).bind fun second => .done (received, second)

/-- Sequential pairing preserves a captured arbitrary challenge and the next
arbitrary reply as the full residual. Neither is replaced by a success bit. -/
theorem captured_challenge (field : String) : Pair scope Eq
    ((drawP (carriers := carriers) field).bind (secondP field))
    ((drawV field).bind (secondV field)) := by
  apply (paired_draw field).bind
  intro first received same
  subst received
  apply Pair.message (.field field) "captured" 0 1 first rfl ⟨rfl, rfl⟩
  exact (paired_draw field).bind _ _ fun a b same => .done (by rw [same])

/-- The generic installation retains this non-Boolean residual and the entire
common reached state. Coverage remains independent of the source pair law. -/
theorem captured_installed (field : String) (routingP routingV : Original.Routing)
    (laws : Pair.FoldLaws (carriers := carriers) scope routingP routingV)
    (state : Original.State carriers) (finalP finalV : Original.Frames)
    (coveredP : Original.RouteCoverage routingP state.frames finalP
      ((drawP (carriers := carriers) field).bind (secondP field)))
    (coveredV : Original.RouteCoverage routingV state.frames finalV
      ((drawV (carriers := carriers) field).bind (secondV field))) :
    ZkcSecurity.FiatShamir.Readback (fun p v => p.1 = v.1 ∧ p.2 = v.2)
      (Original.fold routingP ((drawP field).bind (secondP field)) state)
      (Original.fold routingV ((drawV field).bind (secondV field)) state) :=
  (captured_challenge field).fold laws state finalP finalV coveredP coveredV

theorem no_stopped_completeness {A B : Type} (Post : A → B → Prop) (reason : PIR.Stop)
    (right : PIR.Process (Occurrence.signature carriers) B) :
    ¬ Pair scope Post (.halt reason) right := by
  intro alleged
  cases alleged

theorem unowned_delivery : ("other", "delivery") ∉ scope.deliveries := by
  simp [scope]

/-- A changed reduction bound cannot satisfy Template.invoke's exact body
association. This is a finite source mismatch, not an attack or search failure. -/
theorem changed_reduction_body :
    (ZkcSecurity.Realizations.Sumcheck.SourceRootReference.reductionAssociation
      ZkcExamples.Structured.SumcheckSourceSelections.Selection.small).definition.raw ≠
    (ZkcExamples.Structured.SumcheckVerifierBodies.reduceBody 3).erase := by
  intro associated
  let limits := fun (body : RawRegion Ty ProtocolOp) => body.operations.filterMap
    (fun op => match op with | .repeat spec _ => some spec.maximum | _ => none)
  have different : limits (ZkcSecurity.Realizations.Sumcheck.SourceRootReference.reductionAssociation
      ZkcExamples.Structured.SumcheckSourceSelections.Selection.small).definition.raw ≠
      limits (ZkcExamples.Structured.SumcheckVerifierBodies.reduceBody 3).erase := by decide +kernel
  exact different (congrArg limits associated)

#print axioms captured_challenge
#print axioms captured_installed
#print axioms ZkcSecurity.Source.publicFoldLaws
#print axioms ZkcSecurity.Source.RootPair.artifacts
#print axioms ZkcSecurity.Realizations.Sumcheck.SourcePair.reduction
end TestsSecurity.SourcePairProperties
