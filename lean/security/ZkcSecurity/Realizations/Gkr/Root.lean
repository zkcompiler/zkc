module

public import ZkcSecurity.Realizations.Gkr.Layer
public import ZkcSecurity.Families.Gkr.Output

public section
noncomputable section

namespace ZkcSecurity.Realizations.Gkr.Root
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Construction
open Zkc.Obligations ZkcSecurity.Obligations
open ZkcSecurity.Families.Gkr
open ZkcExamples.Structured
open Zkc.Source.Structured
open OracleComp OracleSpec

variable {F G : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F] {width : Nat}

/-- Every bound is indexed by the actual challenge occurrence. The caller may
use the maximum of these errors or retain a distinct charge for each phase. -/
@[expose] def Charges (ctx : ProtocolContext) (context : Context) (width : Nat)
    (charge : History F G → Event F G → ENNReal) : Prop :=
  (∀ history, 1 / (Fintype.card F : ENNReal) ≤ charge history
    (.challenge (context.query (GkrVerifier.outputSite ctx) (.draw "bls12-381.fr")))) ∧
  (∀ inner, inner = GkrVerifier.leftContext ctx ∨ inner = GkrVerifier.rightContext ctx →
    ∀ history, 2 / (Fintype.card F : ENNReal) ≤ charge history
      (.challenge (context.query (GkrVerifier.challengeSite inner) (.draw "bls12-381.fr")))) ∧
  (∀ history, (width : ENNReal) / Fintype.card F ≤ charge history
    (.challenge (context.query (GkrVerifier.lineChallengeSite ctx) (.draw "bls12-381.fr"))))

@[expose] def acceptance : ClaimRelation (Option Bool) Unit :=
  .exact fun result _ => result = some true

omit [Fintype F] [SampleableType F] in
/-- The final check consumes the zero-layer circuit relation at the actual
returned point. It has no sampler or honest-message premise. -/
theorem terminal_sound (circuit : Circuit F width) :
    (Layer.relation circuit 0).SoundLink acceptance (GkrVerifier.decision width circuit.inputs) := by
  rintro state wrong ⟨_, accepted⟩
  have equal : extension width circuit.inputs (coordinates width state.2.1) = state.2.2 := by
    simpa only [GkrVerifier.decision, Option.some.injEq, decide_eq_true_eq] using accepted
  exact wrong.2 equal.symm

omit [Fintype F] [SampleableType F] in
/-- The same final check accepts a true zero-layer claim. Producer completeness
must establish that this claim is reached by the actual producer. -/
theorem terminal_honest (circuit : Circuit F width) :
    (Layer.relation circuit 0).HonestLink acceptance (GkrVerifier.decision width circuit.inputs) := by
  rintro state ⟨_, _, correct⟩
  refine ⟨(), ?_⟩
  change some (decide (extension width circuit.inputs (coordinates width state.2.1) = state.2.2)) = some true
  have equal : extension width circuit.inputs (coordinates width state.2.1) = state.2.2 := correct.symm
  simp only [equal, decide_true]

@[expose] def component (circuit : Circuit F width) (layers : Nat) (ctx : ProtocolContext) (handle : Nat) :
    ComponentInterface (Actions F G) (Event F G) (Table F width) (Option Bool) where
  Parameters := Unit
  Input := Table F width
  InputWitness := Unit
  Output := Option Bool
  OutputWitness := Unit
  input := .exact fun outputs _ => outputs = circuit.wires layers 0
  output := acceptance
  body outputs := GkrVerifier.verifier ctx handle layers width outputs circuit.inputs circuit.add circuit.mul
  Scope _ _ _ := True
  inputView _ outputs _ := some outputs
  outputView _ _ _ result := some result

noncomputable def output_residual (ctx : ProtocolContext) (handle : Nat) (context : Context)
    (difference : Table F width) (count : Nat) (point : List F)
    (wrong : Output.Differ difference count point)
    (charge : History F G → Event F G → ENNReal)
    (covers : ∀ history, 1 / (Fintype.card F : ENNReal) ≤ charge history
      (.challenge (context.query (GkrVerifier.outputSite ctx) (.draw "bls12-381.fr"))))
    (history : History F G) :
    Derivation context.interface (boundedEscape charge) (fun _ next => Output.Differ difference 0 next)
      history (PIR.repeatN count (GkrVerifier.outputRound ctx handle) point) := by
  induction count generalizing point history with
  | zero => exact .done wrong
  | succ count ih =>
    rw [PIR.repeatN]
    change Derivation context.interface (boundedEscape charge) _ _ (.call (.query (GkrVerifier.outputSite ctx)
      "bls12-381.fr" (.cons handle .nil)) _)
    apply Derivation.query rfl (fun r => ¬ Output.Differ difference count (point ++ [r]))
      ((Output.successor difference count point wrong).trans (covers history))
    intro raw reply decoded outside
    cases Option.some.inj decoded
    apply Derivation.send rfl
    exact ih (point ++ [raw]) (not_not.mp outside) _

/-- Complete multilayer soundness over the actual source presentation. The
generic loop rule consumes opaque layer contracts, including zero layers. -/
noncomputable opaque soundness (circuit : Circuit F width) (layers : Nat) (ctx : ProtocolContext)
    (handle : Nat) (context : Context) (charge : History F G → Event F G → ENNReal)
    (charges : Charges ctx context width charge) :
    SoundnessContract (component (G := G) circuit layers ctx handle)
      context.interface (boundedEscape charge) := by
  intro _ outputs history _ inputNo
  have wrong : outputs ≠ circuit.wires layers 0 := by
    intro equal; exact (ReadbackHolds.some.mp inputNo) ⟨(), equal⟩
  let difference : Table F width := fun bits => outputs bits - circuit.wires layers 0 bits
  have nonzero : ∃ bits, difference bits ≠ 0 := by
    by_contra allZero
    apply wrong
    funext bits
    exact sub_eq_zero.mp (not_not.mp (not_exists.mp allZero bits))
  have outputPrefix := output_residual ctx handle context difference width [] (Output.initial difference nonzero)
    charge charges.1 history
  change Derivation _ _ _ _ ((PIR.repeatN _ _ _).bind _)
  apply outputPrefix.bind
  intro reached point no
  have terminal := Output.terminal difference point no
  have firstNo : (Layer.relation circuit layers).No
      (0, point, extension width outputs (coordinates width point)) := by
    refine ⟨terminal.1, ?_⟩
    intro same
    dsimp only at same
    apply terminal.2
    rw [show difference = (fun bits => outputs bits - circuit.wires layers 0 bits) from rfl,
      extension_sub, same, sub_self]
  unfold GkrVerifier.afterOutputs
  have loop := Derivation.repeatN
    (GkrVerifier.layerStep (G := G) ctx handle width circuit.add circuit.mul)
    (fun _ remaining state => (Layer.relation circuit remaining).No state)
    (fun current remaining state no =>
      ((Layer.soundness circuit remaining ctx handle context charge charges.2.1 charges.2.2)
        () state current no.1 (ReadbackHolds.some.mpr no)).consequence
          (fun _ _ outputNo => ReadbackHolds.some.mp outputNo))
    layers reached (0, point, extension width outputs (coordinates width point)) firstNo
  apply loop.bind
  intro _ final rejected
  apply Derivation.done
  exact ⟨GkrVerifier.decision width circuit.inputs final, rfl, terminal_sound circuit final rejected⟩

end ZkcSecurity.Realizations.Gkr.Root
