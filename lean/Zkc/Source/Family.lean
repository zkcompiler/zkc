import Zkc.Source.Endpoint

/-! Invocation-selected families. Ingress runs on the actual state; its result
contains the configuration and its bound inputs. No theorem here substitutes an
honest encoder's image for all inputs or grants an endpoint another role's view. -/

set_option autoImplicit false
namespace Zkc.Source.Family
open PIR
variable {Config Raw S E A : Type} {Inputs : Config → Type} {I : Signature}

def run (ingress : Raw → S → Execution S E (Sigma Inputs))
    (member : (config : Config) → Inputs config → Proc I A)
    (handler : Handler I S E) (raw : Raw) (state : S) : Execution S E A :=
  (ingress raw state).follow fun bound residual =>
    (member bound.1 bound.2).run handler residual

/-- Inspectable ingress is ordinary sequencing, so existing phase, return and
call-bound composition laws apply to the whole invocation. -/
theorem run_proc (ingress : Raw → Proc I (Sigma Inputs))
    (member : (config : Config) → Inputs config → Proc I A)
    (handler : Handler I S E) (raw : Raw) (state : S) :
    run (fun raw state => (ingress raw).run handler state) member handler raw state =
      ((ingress raw).bind (fun bound => member bound.1 bound.2)).run handler state :=
  (run_bind handler (ingress raw) (fun bound => member bound.1 bound.2) state).symm

/-- The executed member is selected by the actual successful ingress. Its
residual state and all prior observations are retained. -/
theorem run_selected (ingress : Raw → S → Execution S E (Sigma Inputs))
    (member : (config : Config) → Inputs config → Proc I A)
    (handler : Handler I S E) (raw : Raw) (state residual : S)
    (events : List E) (bound : Sigma Inputs)
    (selected : ingress raw state = ⟨.returned bound, residual, events⟩) :
    run ingress member handler raw state =
      let tail := (member bound.1 bound.2).run handler residual
      ⟨tail.outcome, tail.state, events ++ tail.events⟩ := by
  simp [run, selected, Execution.follow]

theorem run_stopped (ingress : Raw → S → Execution S E (Sigma Inputs))
    (member : (config : Config) → Inputs config → Proc I A)
    (handler : Handler I S E) (raw : Raw) (state residual : S)
    (events : List E) (reason : Stop)
    (failed : ingress raw state = ⟨.stopped reason, residual, events⟩) :
    run ingress member handler raw state = ⟨.stopped reason, residual, events⟩ := by
  simp [run, failed, Execution.follow]

/-- A fixed member has an effect-free constant ingress. It preserves the old
complete execution, not just its successful return value. -/
theorem constant_embedding (program : Proc I A) (handler : Handler I S E) (state : S) :
    run (Config := Unit) (Inputs := fun _ => Unit)
      (fun (_ : Unit) s => ⟨.returned ⟨(), ()⟩, s, []⟩)
      (fun _ _ => program) handler () state = program.run handler state := by
  simp [run, Execution.follow]

/-- Admission is per actual selected configuration and inputs. Each bound
covers every typed reply of that member, not all configurations uniformly. -/
structure Admitted (interaction : Interaction I)
    (member : (config : Config) → Inputs config → Proc I A)
    (contract : (config : Config) → Inputs config → EndpointContract interaction A)
    (allowed : (config : Config) → Inputs config → Prop) : Prop where
  conforms : ∀ config inputs, allowed config inputs →
    Conforms interaction (member config inputs) (contract config inputs).initialPhase
  bounded : ∀ config inputs, allowed config inputs →
    Within (contract config inputs).publicBound (member config inputs)
  returned : ∀ config inputs, allowed config inputs →
    Boundary.Returns interaction (contract config inputs).returned
      (member config inputs) (contract config inputs).initialPhase

/-- Every successful actual ingress establishes readiness in its residual
state. The predicate can include phase, live resources and input representation;
its truth must be proved for this ingress, not inferred from member admission. -/
def SelectsReady (ingress : Raw → S → Execution S E (Sigma Inputs))
    (rawDomain : Raw → S → Prop) (ready : Sigma Inputs → S → Prop) : Prop :=
  ∀ raw state bound, rawDomain raw state →
    (ingress raw state).outcome = .returned bound → ready bound (ingress raw state).state

/-- State-independent selection is a specialization of residual readiness.
Stopped ingress remains an explicit execution result. -/
def Selects (ingress : Raw → S → Execution S E (Sigma Inputs))
    (rawDomain : Raw → S → Prop) (allowed : (config : Config) → Inputs config → Prop) : Prop :=
  SelectsReady ingress rawDomain (fun bound _ => allowed bound.1 bound.2)

/-- Discharge member admission for the selection actually returned by ingress,
not a compatible configuration chosen independently of execution. -/
theorem Admitted.selected (interaction : Interaction I)
    (member : (config : Config) → Inputs config → Proc I A)
    (contract : (config : Config) → Inputs config → EndpointContract interaction A)
    (allowed : (config : Config) → Inputs config → Prop)
    (admitted : Admitted interaction member contract allowed)
    (ingress : Raw → S → Execution S E (Sigma Inputs)) (rawDomain : Raw → S → Prop)
    (selects : Selects ingress rawDomain allowed) (raw : Raw) (state : S)
    (bound : Sigma Inputs) (inDomain : rawDomain raw state)
    (selected : (ingress raw state).outcome = .returned bound) :
    Conforms interaction (member bound.1 bound.2) (contract bound.1 bound.2).initialPhase ∧
    Within (contract bound.1 bound.2).publicBound (member bound.1 bound.2) ∧
    Boundary.Returns interaction (contract bound.1 bound.2).returned
      (member bound.1 bound.2) (contract bound.1 bound.2).initialPhase := by
  have valid := selects raw state bound inDomain selected
  exact ⟨admitted.conforms _ _ valid, admitted.bounded _ _ valid, admitted.returned _ _ valid⟩

/-- Member admission at the phase of the actual successful ingress result.
`enters` is additional to selection validity: ingress may change phase. A
native use also relates `phaseOf` to its actual handler's phase interpretation;
this theorem does not certify ingress itself or infer that representation. -/
theorem Admitted.selected_at (interaction : Interaction I)
    (member : (config : Config) → Inputs config → Proc I A)
    (contract : (config : Config) → Inputs config → EndpointContract interaction A)
    (allowed : (config : Config) → Inputs config → Prop)
    (admitted : Admitted interaction member contract allowed)
    (ingress : Raw → S → Execution S E (Sigma Inputs)) (rawDomain : Raw → S → Prop)
    (selects : Selects ingress rawDomain allowed) (raw : Raw) (state : S)
    (bound : Sigma Inputs) (inDomain : rawDomain raw state)
    (selected : (ingress raw state).outcome = .returned bound)
    (phaseOf : S → interaction.Phase)
    (enters : (contract bound.1 bound.2).initialPhase = phaseOf (ingress raw state).state) :
    Conforms interaction (member bound.1 bound.2) (phaseOf (ingress raw state).state) ∧
    Within (contract bound.1 bound.2).publicBound (member bound.1 bound.2) ∧
    Boundary.Returns interaction (contract bound.1 bound.2).returned
      (member bound.1 bound.2) (phaseOf (ingress raw state).state) := by
  rw [← enters]
  exact admitted.selected interaction member contract allowed ingress rawDomain
    selects raw state bound inDomain selected

/-- A domain-wide readiness proof supplies the actual entry phase and allowed
inputs together. Additional resource or representation facts remain in `ready`.
Native use still relates `phaseOf` to the actual handler's phase interpretation. -/
theorem Admitted.selected_ready (interaction : Interaction I)
    (member : (config : Config) → Inputs config → Proc I A)
    (contract : (config : Config) → Inputs config → EndpointContract interaction A)
    (allowed : (config : Config) → Inputs config → Prop)
    (admitted : Admitted interaction member contract allowed)
    (ingress : Raw → S → Execution S E (Sigma Inputs)) (rawDomain : Raw → S → Prop)
    (ready : Sigma Inputs → S → Prop) (established : SelectsReady ingress rawDomain ready)
    (phaseOf : S → interaction.Phase)
    (valid : ∀ bound residual, ready bound residual → allowed bound.1 bound.2)
    (enters : ∀ bound residual, ready bound residual →
      (contract bound.1 bound.2).initialPhase = phaseOf residual)
    (raw : Raw) (state : S) (bound : Sigma Inputs) (inDomain : rawDomain raw state)
    (selected : (ingress raw state).outcome = .returned bound) :
    ready bound (ingress raw state).state ∧
    Conforms interaction (member bound.1 bound.2) (phaseOf (ingress raw state).state) ∧
    Within (contract bound.1 bound.2).publicBound (member bound.1 bound.2) ∧
    Boundary.Returns interaction (contract bound.1 bound.2).returned
      (member bound.1 bound.2) (phaseOf (ingress raw state).state) := by
  have actual := established raw state bound inDomain selected
  refine ⟨actual, ?_⟩
  apply admitted.selected_at interaction member contract allowed ingress rawDomain
    (fun r s b hr hb => valid b _ (established r s b hr hb)) raw state bound
    inDomain selected phaseOf
  exact enters bound _ actual

/-- Constructive role knowledge on admitted worlds, for the behavior actually
needed by that role; learning the entire configuration is not required. -/
structure Known {World View Behavior : Type} (allowed : World → Prop)
    (view : World → View) (required : World → Behavior) where
  select : View → Behavior
  realizes : ∀ world, allowed world → select (view world) = required world

theorem Known.agree {World View Behavior : Type} {allowed : World → Prop}
    {view : World → View} {required : World → Behavior}
    (known : Known allowed view required) (left right : World)
    (hl : allowed left) (hr : allowed right) (same : view left = view right) :
    required left = required right := by
  rw [← known.realizes left hl, ← known.realizes right hr, same]

end Zkc.Source.Family
