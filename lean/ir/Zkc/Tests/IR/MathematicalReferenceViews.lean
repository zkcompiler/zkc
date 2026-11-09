import Zkc.IR.Source.Structured.ReferenceLaws

/-! Reachable mathematical views preserve complete returns and stopped paths.
The source controls construct and install real body laws without adding the
projected equation to their premises or manufacturing a body association. -/

set_option autoImplicit false

namespace Tests.MathematicalReferenceViews
open Zkc.Source Zkc.Source.Structured

private abbrev replies : PIR.Signature := ⟨Unit, fun _ ↦ Bool⟩

private def sentinelProcess (value : Bool) (reason : PIR.Stop) :
    PIR.Process replies (Option Bool) :=
  .call () fun reply ↦ if reply then .done (some value) else .halt reason

private def sentinelReference (value : Bool) (reason : PIR.Stop) : PIR.Process replies Bool :=
  .call () fun reply ↦ if reply then .done value else .halt reason

/-- The image premise covers both replies, including the stopped branch. -/
theorem sentinel_reachable (value : Bool) (reason : PIR.Stop) :
    PIR.Yields (fun result ↦ some (result.getD false) = result)
      (sentinelProcess value reason) := by
  intro reply
  cases reply <;> trivial

theorem sentinel_projected (value : Bool) (reason : PIR.Stop) :
    (sentinelProcess value reason).bind (fun result ↦ .done (result.getD false)) =
      sentinelReference value reason := by
  change (PIR.Process.call () _ : PIR.Process replies Bool) = .call () _
  congr 1
  funext reply
  cases reply <;> rfl

/-- A globally invalid inverse still reconstructs this complete effect tree. -/
theorem sentinel_reconstructed (value : Bool) (reason : PIR.Stop) :
    sentinelProcess value reason =
      (sentinelReference value reason).bind (fun result ↦ .done (some result)) :=
  PIR.Process.reconstruct_from_reachable_view _ (fun result ↦ result.getD false) some
    (sentinel_reachable value reason) _ (sentinel_projected value reason)

theorem sentinel_has_no_global_inverse :
    ¬ ∀ result : Option Bool, some (result.getD false) = result := by
  intro restores
  have impossible := restores none
  cases impossible

/-- Every stop constructor retains its exact reason, reached state and event
prefix. This includes reject, abort, exhausted, incomplete and refused. -/
theorem reconstructed_stopped_prefix (value : Bool) (reason : PIR.Stop) :
    ((sentinelReference value reason).bind (fun result ↦ .done (some result))).run
      (fun _ (state : Nat) ↦ ⟨.returned false, state + 1, ["reply"]⟩) 3 =
      ⟨.stopped reason, 4, ["reply"]⟩ := rfl

/-- An operation can itself stop; reconstruction also retains that prefix. -/
theorem reconstructed_handler_stop (value : Bool) (reason : PIR.Stop) :
    ((sentinelReference value .reject).bind (fun result ↦ .done (some result))).run
      (fun _ (state : Nat) ↦ ⟨.stopped reason, state + 1, ["blocked"]⟩) 3 =
      ⟨.stopped reason, 4, ["blocked"]⟩ := rfl

private def arbitraryReply : PIR.Process replies Bool := .call () PIR.Process.done

/-- The complete projected equation can hold even for a lossy view. -/
theorem lossy_projected :
    arbitraryReply.bind (fun _ ↦ .done ()) =
      (.call () fun _ ↦ .done () : PIR.Process replies Unit) := rfl

/-- Reversibility for the false reply alone cannot cover arbitrary replies. -/
theorem lossy_reachable_refused :
    ¬ PIR.Yields (fun value ↦ (fun _ : Unit ↦ false) () = value) arbitraryReply := by
  intro reachable
  exact Bool.false_ne_true (reachable true)

theorem lossy_reconstruction_refused :
    arbitraryReply ≠ (.call () fun _ ↦ .done false : PIR.Process replies Bool) := by
  intro same
  have runSame := congrArg (fun process ↦ process.run
    (fun _ (_ : Unit) ↦ ⟨.returned true, (), ([] : List Unit)⟩) ()) same
  have outcomeSame := congrArg PIR.Execution.outcome runSame
  change PIR.Outcome.returned true = .returned false at outcomeSame
  cases outcomeSame

/-- Reachability is vacuous on stops; the projected equation must still
distinguish their reasons. -/
theorem return_only_cannot_change_stop :
    PIR.Yields (fun value : Bool ↦ value = true) (.halt .reject : PIR.Process replies Bool) ∧
      PIR.Yields (fun value : Bool ↦ value = true) (.halt .exhausted : PIR.Process replies Bool) ∧
      (.halt .reject : PIR.Process replies Bool).bind (fun value ↦ .done value) ≠
        .halt .exhausted := by
  exact ⟨True.intro, True.intro, by intro impossible; cases impossible⟩

private def tupleBody : Region dialect [.boolean, .index] [.boolean, .index] :=
  .ret (.cons .here (.cons (.there .here) .nil))

variable (model : DomainModel)

/-- The mathematical view retains the Boolean; the unchanged index is
recovered from actual inputs. No input constraint hides the full equation. -/
def inputDependentLaw : ReferenceLaw model [.boolean, .index] [.boolean, .index] :=
  .ofReachableView tupleBody (fun _ _ ↦ True)
    (View := fun _ ↦ Bool)
    (fun _ values ↦ values.get .here)
    (fun arguments value ↦ .cons value (.cons (arguments.get (.there .here)) .nil))
    (fun arguments ↦ .returned (arguments.get .here))
    (by
      intro _ arguments _
      cases arguments with
      | cons value rest => cases rest with
        | cons index rest => cases rest; rfl)
    (by
      intro _ arguments _
      cases arguments with
      | cons value rest => cases rest with
        | cons index rest => cases rest; rfl)

theorem input_dependent_reference (value : Bool) (index : Nat) :
    (inputDependentLaw model).reference (.cons value (.cons index .nil)) =
      .returned (.cons value (.cons index .nil)) := rfl

theorem premises_unchanged
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (arguments : Values model.Value [.boolean, .index]) :
    (inputDependentLaw model).Requires table arguments = True := rfl

/-- The same view cannot recover the index without its input parameter. -/
theorem input_independent_packing_refused :
    ¬ ∃ pack : Bool → Values model.Value [.boolean, .index],
      ∀ (value : Bool) (index : Nat), pack value = .cons value (.cons index .nil) := by
  rintro ⟨pack, restores⟩
  have impossible := congrArg (fun values ↦ values.get (.there .here))
    ((restores false 0).symm.trans (restores false 1))
  change (0 : Nat) = 1 at impossible
  cases impossible

/-- A mathematical carrier may itself depend on the actual inputs. -/
def dependentCarrierLaw : ReferenceLaw model [.boolean, .index] [.boolean, .index] :=
  .ofReachableView tupleBody (fun _ _ ↦ True)
    (View := fun arguments ↦ Fin (arguments.get (.there .here) + 1))
    (fun _ _ ↦ ⟨0, Nat.zero_lt_succ _⟩)
    (fun arguments _ ↦ arguments)
    (fun _ ↦ .returned ⟨0, Nat.zero_lt_succ _⟩)
    (by
      intro _ arguments _
      cases arguments with
      | cons value rest => cases rest with
        | cons index rest => cases rest; rfl)
    (by
      intro _ arguments _
      rfl)

def stoppedLaw (reason : PIR.Stop) : ReferenceLaw model [.boolean, .index] [.boolean, .index] :=
  .ofReachableView (.stop reason) (fun _ _ ↦ True)
    (View := fun _ ↦ Bool)
    (fun _ values ↦ values.get .here)
    (fun arguments value ↦ .cons value (.cons (arguments.get (.there .here)) .nil))
    (fun _ ↦ .stopped reason)
    (by intros; trivial)
    (by intros; rfl)

theorem stopped_reference (reason : PIR.Stop)
    (arguments : Values model.Value [.boolean, .index]) :
    (stoppedLaw model reason).reference arguments = .stopped reason := rfl

private def tupleDefinition : CheckedDefinition :=
  ⟨"tuple", .math, [.boolean, .index], [.boolean, .index], tupleBody.erase,
    tupleBody, tupleBody.elaborate_erase⟩

private theorem tuple_linked : DeclarationsLinked [] [tupleDefinition] := by
  simp [DeclarationsLinked, tupleDefinition, tupleBody,
    CheckedDefinition.helpers, Region.erase, RawRegion.operations]

/-- Reconstructed laws use the existing exact body association and linked
table. The constructor does not fabricate either installation proof. -/
theorem installed_input_dependent (value : Bool) (index : Nat) :
    invoke ([tupleDefinition].foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      tupleDefinition.helper (.cons value (.cons index .nil)) =
      .done (.cons value (.cons index .nil)) := by
  exact ReferenceLaw.invoke (helper := tupleDefinition.helper)
    (inputDependentLaw model) [tupleDefinition] tuple_linked
    (by exact_body tupleDefinition) (.cons value (.cons index .nil)) trivial

theorem installed_dependent_carrier (value : Bool) (index : Nat) :
    invoke ([tupleDefinition].foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      tupleDefinition.helper (.cons value (.cons index .nil)) =
      .done (.cons value (.cons index .nil)) := by
  exact ReferenceLaw.invoke (helper := tupleDefinition.helper)
    (dependentCarrierLaw model) [tupleDefinition] tuple_linked
    (by exact_body tupleDefinition) (.cons value (.cons index .nil)) trivial

private def stoppedDefinition (reason : PIR.Stop) : CheckedDefinition :=
  let body : Region dialect [.boolean, .index] [.boolean, .index] := .stop reason
  ⟨"stopped", .math, [.boolean, .index], [.boolean, .index], body.erase,
    body, body.elaborate_erase⟩

/-- All stopping outcomes survive actual source installation as well as
construction of the mathematical reference. -/
theorem installed_stopped (reason : PIR.Stop)
    (arguments : Values model.Value [.boolean, .index]) :
    invoke ([stoppedDefinition reason].foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (stoppedDefinition reason).helper arguments = .halt reason := by
  exact ReferenceLaw.invoke (helper := (stoppedDefinition reason).helper)
    (stoppedLaw model reason) [stoppedDefinition reason]
    (by
      simp [DeclarationsLinked, stoppedDefinition, CheckedDefinition.helpers,
        Region.erase, RawRegion.operations])
    (by exact_body stoppedDefinition reason) arguments trivial

/-- The constructor does not associate a different body, even when its ABI
matches the selected helper. -/
theorem wrong_body_refused (reason : PIR.Stop) :
    ¬ BodyIn [tupleDefinition] tupleDefinition.helper (stoppedLaw model reason).body := by
  rintro ⟨definition, member, _, raw⟩
  cases List.mem_singleton.mp member
  change RawRegion.ret [0, 1] = .stop reason at raw
  cases raw

#print axioms PIR.Process.restore_return_of_yields
#print axioms PIR.Process.reconstruct_from_reachable_view
#print axioms ReferenceLaw.ofReachableView
#print axioms installed_input_dependent
#print axioms installed_dependent_carrier
#print axioms installed_stopped
#print axioms lossy_reconstruction_refused

end Tests.MathematicalReferenceViews
