module

public import ZkcSecurity.Realizations.Gkr.SourceLayer
public import ZkcSecurity.Families.Gkr.Output

@[expose] public section

/-! Circuit-output falsity through the actual nested source loops. No
producer input restricts these proofs; all messages and histories are arbitrary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.SourceRoot
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Source ZkcSecurity.Families.Gkr
open ZkcExamples.Structured OracleComp OracleSpec
open HonestProducerObserved
variable {F G : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
attribute [local instance] ZkcSecurity.FiatShamir.OccurrenceReading.rawSampleable

def output {width : Nat} (ctx : ProtocolContext) (site : String) (handle start count : Nat)
    (difference : Table F width) (point : List F) (wrong : Output.Differ difference count point)
    (price : ENNReal) (covers : 1 / (Fintype.card F : ENNReal) ≤ price)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ next => Output.Differ difference 0 next) history
      (validatorOutput ctx handle site start count point) := by
  induction count generalizing start point history with
  | zero => exact .done wrong
  | succ count ih =>
    rw [validatorOutput]
    have one : ∀ reached, Derivation PublicProperties.interface (PublicProperties.escape price)
        (fun _ next => Output.Differ difference count next) reached
        (((GkrVerifier.outputRound (G := G) ctx handle point).interpret CommonAdapter.embed).interpret
          Occurrence.actions) := by
      intro reached
      simp only [GkrVerifier.outputRound, GkrVerifier.outputDelivery, PIR.Process.interpret,
        CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
      refine Derivation.query rfl (fun (r : F) => ¬ Output.Differ difference count (point ++ [r]))
        (PublicUniform.bound price _ _ _ _ ((Output.successor difference count point wrong).trans covers) reached) ?_
      intro raw reply decoded outside
      cases Option.some.inj decoded
      exact .send rfl (.done (not_not.mp outside))
    exact (OccurrenceProperties.within site start _ one history).bind _
      (fun reached next valid => ih (start+1) next valid reached)

def layers (ctx : ProtocolContext) (sites : Sites) (handle : Nat) (encoding : CircuitEncoding F)
    (start count : Nat) (state : Nat × List F × F) (wrong : SourceLayer.No encoding.circuit count state)
    (price : ENNReal) (roundBound : 2 / (Fintype.card F : ENNReal) ≤ price)
    (lineBound : (encoding.width : ENNReal) / Fintype.card F ≤ price)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ result => SourceLayer.No encoding.circuit 0 result) history
      (validatorLayers ctx handle sites encoding start count state) := by
  induction count generalizing start state history with
  | zero => exact .done wrong
  | succ count ih =>
    rw [validatorLayers]
    exact (OccurrenceProperties.within sites.layers start _
      (SourceLayer.rejected encoding.circuit count ctx sites.layer handle state wrong price roundBound lineBound)
      history).bind _ (fun reached next valid => ih (start+1) next valid reached)

def rejected (ctx : ProtocolContext) (sites : Sites) (handle : Nat)
    (encoding : CircuitEncoding F) (outputs : List F)
    (wrong : (ofList? encoding.width outputs).getD 0 ≠ encoding.circuit.wires encoding.layers 0)
    (price : ENNReal) (outputBound : 1 / (Fintype.card F : ENNReal) ≤ price)
    (roundBound : 2 / (Fintype.card F : ENNReal) ≤ price)
    (lineBound : (encoding.width : ENNReal) / Fintype.card F ≤ price)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Derivation PublicProperties.interface (PublicProperties.escape price) (fun _ result => result ≠ some true)
      history (validator ctx handle sites encoding outputs) := by
  let difference : Table F encoding.width := fun bits =>
    (ofList? encoding.width outputs).getD 0 bits - encoding.circuit.wires encoding.layers 0 bits
  have nonzero : ∃ bits, difference bits ≠ 0 := by
    by_contra allZero
    apply wrong
    funext bits
    exact sub_eq_zero.mp (not_not.mp (not_exists.mp allZero bits))
  unfold validator
  apply (output ctx sites.output handle 0 encoding.width difference []
    (Output.initial difference nonzero) price outputBound history).bind
  intro reached point no
  have terminal := Output.terminal difference point no
  have initial : SourceLayer.No encoding.circuit encoding.layers
      (0, point, extension encoding.width ((ofList? encoding.width outputs).getD 0)
        (coordinates encoding.width point)) := by
    refine ⟨terminal.1, ?_⟩
    intro same
    dsimp only at same
    apply terminal.2
    rw [show difference = (fun bits => (ofList? encoding.width outputs).getD 0 bits -
      encoding.circuit.wires encoding.layers 0 bits) from rfl, extension_sub, same, sub_self]
  apply (layers ctx sites handle encoding 0 encoding.layers _ initial price roundBound lineBound reached).bind
  intro final state failed
  apply Derivation.done
  intro accepted
  have equal : extension encoding.width encoding.circuit.inputs (coordinates encoding.width state.2.1) = state.2.2 := by
    simpa only [GkrVerifier.decision, Option.some.injEq, decide_eq_true_eq] using accepted
  exact failed.2 equal.symm

#print axioms rejected
end ZkcSecurity.Realizations.Gkr.SourceRoot
