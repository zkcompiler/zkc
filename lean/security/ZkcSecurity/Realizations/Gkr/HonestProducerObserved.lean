module

public import ZkcSecurity.Realizations.Gkr.HonestProducerObservedLayers
public import ZkcSecurity.Realizations.Gkr.HonestProducer

@[expose] public section

/-! Whole honest GKR pair with real nested source iteration observations.
Source body associations are kept explicit, separate from circuit truth. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerObserved
open Zkc Source Structured Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured
open ZkcSecurity.Examples.Components
open ZkcSecurity.FiatShamir HonestProducerComposition HonestProducerOccurrences
open HonestProducerSource

variable {F G : Type} [Field F] [DecidableEq F]

structure Sites where
  output : String
  layers : String
  layer : HonestProducerObservedLayers.Sites

def producerOutput (ctx : ProtocolContext) (site : String) : Nat → Nat → List F →
    PIR.Process (Signature F G) (List F)
  | _, 0, point => .done point
  | index, count + 1, point =>
    (Occurrence.iterations.within site index
      ((output (G := G) ctx 1 point).interpret Occurrence.actions)).bind fun next =>
    producerOutput ctx site (index + 1) count next

def validatorOutput (ctx : ProtocolContext) (handle : Nat) (site : String) : Nat → Nat → List F →
    PIR.Process (Signature F G) (List F)
  | _, 0, point => .done point
  | index, count + 1, point =>
    (Occurrence.iterations.within site index
      (((GkrVerifier.outputRound ctx handle point).interpret CommonAdapter.embed).interpret
        Occurrence.actions)).bind fun next => validatorOutput ctx handle site (index + 1) count next

omit [Field F] [DecidableEq F] in
theorem output_pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) (site : String) (index count : Nat) (point : List F)
    (state : State (F := F) (G := G))
    (routes : ∀ i, HonestProducer.OutputRoutes routing ctx (state.frames ++ [⟨site, i⟩]) handle) :
    Readback (fun left right => ∃ next history,
      left = (next, { state with history := history }) ∧
      right = (next, { state with history := history }) ∧ next.length = point.length + count)
      (Original.fold { routing with mode := .producer } (producerOutput ctx site index count point) state)
      (Original.fold { routing with mode := .validator } (validatorOutput ctx handle site index count point) state) := by
  induction count generalizing index point state with
  | zero => exact .done ⟨point, state.history, rfl, rfl, by omega⟩
  | succ count ih =>
    rw [producerOutput, validatorOutput, Original.fold_bind, Original.fold_bind]
    let entered : State (F := F) (G := G) := { state with frames := state.frames ++ [⟨site, index⟩] }
    have one := HonestProducer.output_pair (F := F) (G := G) routing replacement profile ctx handle 1 point
      entered (routes index)
    simp only [output, PIR.repeatN, PIR.Process.bind_done, HonestProducerPair.validator] at one
    have wrapped := within routing site index state _ _
      (fun left right => ∃ next history,
        left = (next, { state with history := history }) ∧
        right = (next, { state with history := history }) ∧ next.length = point.length + 1)
      (one.mono (by
        rintro left right ⟨next, history, rfl, rfl, size⟩
        exact ⟨rfl, rfl, next, history, rfl, rfl, size⟩))
    apply wrapped.bind
    rintro left right ⟨next, history, rfl, rfl, size⟩
    apply (ih (index + 1) next { state with history := history } routes).mono
    rintro left right ⟨final, history, rfl, rfl, finalSize⟩
    exact ⟨final, history, rfl, rfl, by omega⟩

noncomputable def producerLayers (ctx : ProtocolContext) (sites : Sites) (encoding : CircuitEncoding F) :
    Nat → Nat → List F → PIR.Process (Signature F G) (List F)
  | _, 0, point => .done point
  | index, count + 1, point =>
    (Occurrence.iterations.within sites.layers index
      (HonestProducerObservedLayers.producerLayer ctx sites.layer encoding.circuit
        (encoding.layers - index - 1) index point)).bind fun next =>
    producerLayers ctx sites encoding (index + 1) count next

def validatorLayers (ctx : ProtocolContext) (handle : Nat) (sites : Sites) (encoding : CircuitEncoding F) :
    Nat → Nat → (Nat × List F × F) → PIR.Process (Signature F G) (Nat × List F × F)
  | _, 0, value => .done value
  | index, count + 1, value =>
    (Occurrence.iterations.within sites.layers index
      (HonestProducerObservedLayers.validatorLayer ctx handle encoding.width sites.layer
        encoding.circuit.add encoding.circuit.mul value)).bind fun next =>
    validatorLayers ctx handle sites encoding (index + 1) count next

theorem layers_pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) (sites : Sites) (encoding : CircuitEncoding F)
    (index count : Nat) (counted : index + count = encoding.layers)
    (point : List F) (pointSize : point.length = encoding.width)
    (state : State (F := F) (G := G)) (routes : ∀ i, HonestProducerObservedLayers.Routes routing ctx
      (state.frames ++ [⟨sites.layers, i⟩]) handle sites.layer) :
    Readback (fun left right => ∃ next history,
      left = (next, { state with history := history }) ∧
      right = ((encoding.layers, next, extension encoding.width encoding.circuit.inputs
        (coordinates encoding.width next)), { state with history := history }) ∧ next.length = encoding.width)
      (Original.fold { routing with mode := .producer } (producerLayers ctx sites encoding index count point) state)
      (Original.fold { routing with mode := .validator }
        (validatorLayers ctx handle sites encoding index count
          (index, point, extension encoding.width (encoding.circuit.wires count index)
            (coordinates encoding.width point))) state) := by
  induction count generalizing index point state with
  | zero =>
    apply Readback.done
    refine ⟨point, state.history, rfl, ?_, pointSize⟩
    have same : index = encoding.layers := by omega
    subst index
    rfl
  | succ count ih =>
    have remaining : encoding.layers - index - 1 = count := by omega
    rw [producerLayers, validatorLayers, remaining, Original.fold_bind, Original.fold_bind]
    let entered : State (F := F) (G := G) := { state with frames := state.frames ++ [⟨sites.layers, index⟩] }
    have one := HonestProducerObservedLayers.layer_pair routing replacement profile ctx handle sites.layer
      encoding.circuit count index point pointSize entered (routes index)
    have wrapped := within routing sites.layers index state _ _
      (fun left right => ∃ next history,
        left = (next, { state with history := history }) ∧
        right = ((index + 1, next, extension encoding.width (encoding.circuit.wires count (index + 1))
          (coordinates encoding.width next)), { state with history := history }) ∧ next.length = encoding.width)
      (one.mono (by
        rintro left right ⟨next, history, rfl, rfl, size⟩
        exact ⟨rfl, rfl, next, history, rfl, rfl, size⟩))
    apply wrapped.bind
    rintro left right ⟨next, history, rfl, rfl, nextSize⟩
    exact ih (index + 1) (by omega) next nextSize { state with history := history } routes

noncomputable def producer (ctx : ProtocolContext) (sites : Sites) (encoding : CircuitEncoding F) :
    PIR.Process (Signature F G) (Values (Component (assignment F G)) [.boolean]) :=
  (producerOutput ctx sites.output 0 encoding.width []).bind fun point =>
  (producerLayers ctx sites encoding 0 encoding.layers point).bind fun _ => .done (.cons none .nil)

noncomputable def validator (ctx : ProtocolContext) (handle : Nat) (sites : Sites)
    (encoding : CircuitEncoding F) (outputs : List F) : PIR.Process (Signature F G) (Option Bool) :=
  (validatorOutput ctx handle sites.output 0 encoding.width []).bind fun point =>
  (validatorLayers ctx handle sites encoding 0 encoding.layers
    (0, point, extension encoding.width ((ofList? encoding.width outputs).getD 0)
      (coordinates encoding.width point))).bind fun value =>
  (((PIR.Process.done (GkrVerifier.decision encoding.width encoding.circuit.inputs value)).interpret CommonAdapter.embed).interpret
    Occurrence.actions)

omit [Field F] [DecidableEq F] in
theorem producerOutput_erase (ctx : ProtocolContext) (site : String) (index count : Nat) (point : List F) :
    (producerOutput (G := G) ctx site index count point).interpret Occurrence.erase = output ctx count point := by
  induction count generalizing index point with
  | zero => rfl
  | succ count ih =>
    rw [producerOutput, PIR.Process.interpret_bind,
      IterationObservations.within_interpret _ Occurrence.iterations_erase,
      IterationObservations.silent_within, actions_erase]
    simp only [output, PIR.Process.bind]
    congr 1
    funext r
    exact ih (index + 1) (point ++ [r])

omit [DecidableEq F] in
theorem producerLayers_erase (ctx : ProtocolContext) (sites : Sites) (encoding : CircuitEncoding F)
    (index count : Nat) (point : List F) :
    (producerLayers (G := G) ctx sites encoding index count point).interpret Occurrence.erase =
      layers ctx encoding index count point := by
  induction count generalizing index point with
  | zero => rfl
  | succ count ih =>
    rw [producerLayers, PIR.Process.interpret_bind,
      IterationObservations.within_interpret _ Occurrence.iterations_erase,
      IterationObservations.silent_within, HonestProducerObservedLayers.producerLayer_erase, layers]
    apply congrArg (PIR.Process.bind _)
    funext next
    exact ih (index + 1) next

omit [DecidableEq F] in
theorem producer_erase (ctx : ProtocolContext) (sites : Sites) (encoding : CircuitEncoding F) :
    (producer (G := G) ctx sites encoding).interpret Occurrence.erase = HonestProducerSource.producer ctx encoding := by
  unfold producer HonestProducerSource.producer
  simp only [PIR.Process.interpret_bind, producerOutput_erase, producerLayers_erase, PIR.Process.interpret]

/-- Every challenge and every initial history succeeds for true independent
outputs. No helper law, chosen transcript or oracle behavior is assumed. -/
theorem pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) (sites : Sites) (encoding : CircuitEncoding F) (outputs : List F)
    (correct : encoding.Outputs outputs) (state : State (F := F) (G := G))
    (outputRoutes : ∀ i, HonestProducer.OutputRoutes routing ctx (state.frames ++ [⟨sites.output, i⟩]) handle)
    (layerRoutes : ∀ i, HonestProducerObservedLayers.Routes routing ctx
      (state.frames ++ [⟨sites.layers, i⟩]) handle sites.layer) :
    Readback (fun left right => ∃ history,
      left = (.cons none .nil, { state with history := history }) ∧
      right = (some true, { state with history := history }))
      (Original.fold { routing with mode := .producer } (producer ctx sites encoding) state)
      (Original.fold { routing with mode := .validator } (validator ctx handle sites encoding outputs) state) := by
  unfold producer validator
  rw [correct.2]
  dsimp only [Option.getD]
  rw [Original.fold_bind, Original.fold_bind]
  apply (output_pair routing replacement profile ctx handle sites.output 0 encoding.width [] state outputRoutes).bind
  rintro left right ⟨point, history, rfl, rfl, size⟩
  have pointSize : point.length = encoding.width := by simpa only [List.length_nil, Nat.zero_add] using size
  dsimp only
  rw [Original.fold_bind, Original.fold_bind]
  apply (layers_pair routing replacement profile ctx handle sites encoding 0 encoding.layers (by omega)
    point pointSize { state with history := history } layerRoutes).bind
  rintro left right ⟨next, finalHistory, rfl, rfl, _⟩
  apply Readback.done
  refine ⟨finalHistory, rfl, ?_⟩
  simp only [GkrVerifier.decision, decide_true, PIR.Process.interpret, Original.fold, PIR.Process.interpretState]

end ZkcSecurity.Realizations.Gkr.HonestProducerObserved
