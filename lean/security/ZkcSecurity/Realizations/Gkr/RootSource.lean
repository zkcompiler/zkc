module

public import ZkcSecurity.Realizations.Gkr.Root
public import ZkcSecurity.Realizations.Gkr.SourceAdmission
public import ZkcExamples.Structured.GkrSourceVerifier

public section
noncomputable section

/-! Binding the component route to the actual admitted GKR participant.
The source admission prefix stops on every invalid raw input. On valid inputs,
the registered encoding determines its mathematical circuit and the existing
root theorem supplies soundness through the same all-replies body equation.
Current-source correspondence and compiled producer closure must both be
replayed before a canonical completeness or soundness receipt is registered.
-/

namespace ZkcSecurity.Realizations.Gkr.Source
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations
open Zkc.Polynomial.Multilinear ZkcSecurity.Families.Gkr
open ZkcExamples.Structured
open ZkcSecurity.Obligations OracleComp OracleSpec

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  {width : Nat}

@[expose] def body (runtime : Invocation F) : PIR.Process (Actions F G) (Option Bool) :=
  actualVerifier runtime

/-- Exact all-replies equality, shared by soundness and execution consumers. -/
theorem binding (circuit : Circuit F width) (layers : Nat) (outputs : Table F width)
    (runtime : Invocation F) (represented : Represents circuit layers outputs runtime) :
    body (G := G) runtime = GkrVerifier.verifier {} runtime.handle layers width outputs
      circuit.inputs circuit.add circuit.mul := by
  unfold body actualVerifier GkrSourceAdmission.participant GkrSourceAdmission.inputs
  rw [represented.width_eq, represented.layers_eq]
  exact GkrSourceVerifier.verifier_reads runtime.handle runtime.inputs runtime.outputs runtime.add runtime.mul
    layers runtime.selector width outputs circuit.inputs represented.outputsDecoded represented.inputsDecoded
    circuit.add circuit.mul represented.addShape represented.mulShape represented.addBound represented.mulBound
    represented.addDecoded represented.mulDecoded represented.selectorBound represented.widthBound represented.layersBound

/-- The canonical encoding fixes the circuit and output table before a proof
method is selected. Its checked input policy supplies all representation laws. -/
theorem admitted_binding (runtime : Invocation F) (admitted : runtime.Admitted) :
    body (G := G) runtime = GkrVerifier.verifier {} runtime.handle runtime.layers runtime.width
      runtime.outputTable runtime.encoding.circuit.inputs runtime.encoding.circuit.add
      runtime.encoding.circuit.mul :=
  binding runtime.encoding.circuit runtime.layers runtime.outputTable runtime
    (admitted_represents runtime admitted)

@[expose] def component (circuit : Circuit F width) (layers : Nat) :
    ComponentInterface (Actions F G) (Event F G) (Invocation F) (Option Bool) where
  Parameters := Table F width
  Input := Table F width
  InputWitness := Unit
  Output := Option Bool
  OutputWitness := Unit
  input := .exact fun outputs _ => outputs = circuit.wires layers 0
  output := Root.acceptance
  body := body
  Scope outputs runtime _ := Represents circuit layers outputs runtime
  inputView outputs _ _ := some outputs
  outputView _ _ _ result := some result

/-- The actual explicit guard rejects an oversized machine width; the checked
index helper refuses a mathematical natural outside its machine range. -/
theorem width_refuses (runtime : Invocation F) (outside : 4 < runtime.width) :
    body (G := G) runtime =
      .halt (if runtime.width < indexLimit then .reject else .refused) := by
  have stopped := GkrSourceAdmission.width_refuses (G := G) runtime.inputs runtime.outputs
    runtime.add runtime.mul runtime.layers runtime.selector runtime.width runtime.handle outside
  unfold body actualVerifier
  rw [stopped]
  split <;> rfl

variable [Fintype F] [SampleableType F]

noncomputable opaque soundness (circuit : Circuit F width) (layers : Nat) (context : Context)
    (charge : History F G → Event F G → ENNReal) (charges : Root.Charges {} context width charge) :
    SoundnessContract (component (G := G) circuit layers) context.interface (boundedEscape charge) := by
  intro outputs runtime history represented no
  exact (Root.soundness circuit layers {} runtime.handle context charge charges
    () outputs history trivial no).transport (binding circuit layers outputs runtime represented)

/-- Soundness of the fixed circuit output predicate on the admitted branch.
The full raw-input theorem additionally discharges actual guard refusals. -/
noncomputable def admitted_rejected (runtime : Invocation F) (admitted : runtime.Admitted)
    (context : Context) (charge : History F G → Event F G → ENNReal)
    (charges : Root.Charges {} context runtime.width charge)
    (wrong : ¬ runtime.Correct) (history : History F G) :
    Derivation context.interface (boundedEscape charge)
      (fun _ result => result ≠ some true) history (body runtime) := by
  have no : (Root.component (G := G) runtime.encoding.circuit runtime.layers {} runtime.handle).InputNo
      () runtime.outputTable history := by
    apply ReadbackHolds.some.mpr
    rintro ⟨_, correct⟩
    exact wrong ((admitted_correct_iff runtime admitted).mpr correct)
  exact ((Root.soundness runtime.encoding.circuit runtime.layers {} runtime.handle context charge charges
    () runtime.outputTable history trivial no).consequence
      (fun _ _ no => by
        have rejected := ReadbackHolds.some.mp no
        exact fun accepted => rejected ⟨(), accepted⟩)).transport (admitted_binding runtime admitted)

/-- Soundness for every raw validator input. Invalid inputs halt in their
actual admission prefix; valid inputs use the fixed circuit's root theorem. -/
noncomputable def rejected (runtime : Invocation F) (context : Context)
    (charge : History F G → Event F G → ENNReal)
    (charges : Root.Charges {} context runtime.width charge)
    (wrong : ¬ runtime.Correct) (history : History F G) :
    Derivation context.interface (boundedEscape charge)
      (fun _ result => result ≠ some true) history (body runtime) := by
  by_cases admitted : runtime.Admitted
  · exact admitted_rejected runtime admitted context charge charges wrong history
  · exact invalid_derivation runtime admitted context.interface (boundedEscape charge) _ history

omit [Fintype F] [SampleableType F] in
/-- The very same body binding transports honest runs, failed runs and stops. -/
theorem run_binding {H E : Type} (handler : PIR.Handler (Actions F G) H E) (state : H)
    (circuit : Circuit F width) (layers : Nat) (outputs : Table F width)
    (runtime : Invocation F) (represented : Represents circuit layers outputs runtime) :
    (body runtime).run handler state =
      (GkrVerifier.verifier {} runtime.handle layers width outputs circuit.inputs circuit.add circuit.mul).run
        handler state := congrArg (fun process => process.run handler state)
          (binding circuit layers outputs runtime represented)


end ZkcSecurity.Realizations.Gkr.Source
