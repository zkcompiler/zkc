module

public import ZkcExamples.Construction.GkrProofInstructions

@[expose] public section

/-! The interactive reading of the compiled GKR verifier is the plain GKR
verifier.

On a well-formed statement (decoded input and output tables, stacked wiring
tables whose blocks decode, and loop counts within the Entry's maxima), the
reading `spec` of the exported instructions, read through the acceptance
output, is `ZkcExamples.Structured.GkrVerifier.verifier` with its qualified
sites (`reading`). Each loop of the export reads as repeated steps of the plain
verifier (`Zkc.Construction.iterate_range_repeatN`): every iteration of a loop
body is one step of the plain process up to transcript histories, which the
reading never inspects (`Zkc.Construction.specK_similar`).
-/

namespace ZkcExamples.Construction.GkrProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcExamples.Structured.GkrSourceLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr

set_option linter.unusedSimpArgs false

/-! ## Loop iterations -/

section Iterations
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (handle : Nat)

/-- One iteration of the output-point loop is one output-point challenge and its
delivery. -/
theorem output_iteration {A : Type} (env : List (Value F G)) (length : env.length = 9) (index : Nat)
    (point : List F) (next : List (Value F G) → PIR.Proc (Actions F G) A) (agree : AgreeUpToHistories next next) :
    specK readingContext handle meanings outputBody (env ++ .index index :: pointValues point)
        (afterIteration [19, 18] next) =
      (GkrVerifier.outputRound {} handle point).bind fun point' => next (pointValues point') := by
  simp only [outputBody, pointValues]
  read_instructions
  simp only [GkrVerifier.outputRound, GkrVerifier.outputDelivery, PIR.Proc.bind]
  try normalize_sites
  refine congrArg (PIR.Proc.call _) (funext fun answer => ?_)
  refine congrArg (PIR.Proc.call _) (funext fun _ => ?_)
  exact agree _ _ rfl

/-- One iteration of the first `Rounds` application's loop is one degree-two
Sumcheck round. -/
theorem left_iteration {A : Type} (env : List (Value F G)) (length : env.length = 17) (index : Nat)
    (state : List F × F) (next : List (Value F G) → PIR.Proc (Actions F G) A)
    (agree : AgreeUpToHistories next next) :
    specK readingContext handle meanings leftBody (env ++ .index index :: claimValues state.1 state.2)
        (afterIteration [49, 53, 48] next) =
      (GkrVerifier.round (GkrVerifier.leftContext {}) handle state).bind fun state' =>
        next (claimValues state'.1 state'.2) := by
  simp only [claimValues]
  rw [leftBody, specK_append]
  simp only [leftBodyA]
  read_instructions
  simp only [GkrVerifier.round, PIR.Proc.bind]
  try normalize_sites
  refine congrArg (PIR.Proc.call _) (funext fun c0 => ?_)
  rw [specK_append]
  simp only [leftBodyB]
  read_instructions
  simp only [GkrVerifier.roundFirst, PIR.Proc.bind]
  try normalize_sites
  refine congrArg (PIR.Proc.call _) (funext fun c1 => ?_)
  rw [specK_append]
  simp only [leftBodyC]
  read_instructions
  simp only [GkrVerifier.roundSecond, PIR.Proc.bind]
  try normalize_sites
  refine congrArg (PIR.Proc.call _) (funext fun c2 => ?_)
  rw [specK_append]
  simp only [leftBodyD]
  read_instructions
  simp only [GkrVerifier.roundCheck]
  by_cases check : state.2 = c0 + c0 + c1 + c2
  · simp only [check, decide_true, ite_true, eq_self, PIR.Proc.bind]
    try normalize_sites
    refine congrArg (PIR.Proc.call _) (funext fun r => ?_)
    simp only [leftBodyE]
    read_instructions
    simp only [GkrVerifier.roundChallenge, PIR.Proc.bind]
    try normalize_sites
    refine congrArg (PIR.Proc.call _) (funext fun _ => ?_)
    exact agree _ _ rfl
  · simp only [check, decide_false, ite_false, PIR.Proc.bind]

/-- One iteration of the second `Rounds` application's loop is one degree-two
Sumcheck round. -/
theorem right_iteration {A : Type} (env : List (Value F G)) (length : env.length = 21) (index : Nat)
    (state : List F × F) (next : List (Value F G) → PIR.Proc (Actions F G) A)
    (agree : AgreeUpToHistories next next) :
    specK readingContext handle meanings rightBody (env ++ .index index :: claimValues state.1 state.2)
        (afterIteration [53, 57, 52] next) =
      (GkrVerifier.round (GkrVerifier.rightContext {}) handle state).bind fun state' =>
        next (claimValues state'.1 state'.2) := by
  simp only [claimValues]
  rw [rightBody, specK_append]
  simp only [rightBodyA]
  read_instructions
  simp only [GkrVerifier.round, PIR.Proc.bind]
  try normalize_sites
  refine congrArg (PIR.Proc.call _) (funext fun c0 => ?_)
  rw [specK_append]
  simp only [rightBodyB]
  read_instructions
  simp only [GkrVerifier.roundFirst, PIR.Proc.bind]
  try normalize_sites
  refine congrArg (PIR.Proc.call _) (funext fun c1 => ?_)
  rw [specK_append]
  simp only [rightBodyC]
  read_instructions
  simp only [GkrVerifier.roundSecond, PIR.Proc.bind]
  try normalize_sites
  refine congrArg (PIR.Proc.call _) (funext fun c2 => ?_)
  rw [specK_append]
  simp only [rightBodyD]
  read_instructions
  simp only [GkrVerifier.roundCheck]
  by_cases check : state.2 = c0 + c0 + c1 + c2
  · simp only [check, decide_true, ite_true, eq_self, PIR.Proc.bind]
    try normalize_sites
    refine congrArg (PIR.Proc.call _) (funext fun r => ?_)
    simp only [rightBodyE]
    read_instructions
    simp only [GkrVerifier.roundChallenge, PIR.Proc.bind]
    try normalize_sites
    refine congrArg (PIR.Proc.call _) (funext fun _ => ?_)
    exact agree _ _ rfl
  · simp only [check, decide_false, ite_false, PIR.Proc.bind]

/-- One iteration of the line coefficients' loop is one further coefficient. -/
theorem coefficient_iteration {A : Type} (env : List (Value F G)) (length : env.length = 30)
    (index : Nat) (coefficients : List F) (next : List (Value F G) → PIR.Proc (Actions F G) A)
    (agree : AgreeUpToHistories next next) :
    specK readingContext handle meanings coefficientBody (env ++ .index index :: pointValues coefficients)
        (afterIteration [38, 37] next) =
      (GkrVerifier.lineCoefficient {} coefficients).bind fun coefficients' =>
        next (pointValues coefficients') := by
  simp only [coefficientBody, pointValues]
  read_instructions
  simp only [GkrVerifier.lineCoefficient, PIR.Proc.bind]
  try normalize_sites
  refine congrArg (PIR.Proc.call _) (funext fun coefficient => ?_)
  exact agree _ _ rfl

/-- One iteration of the layer loop is one layer of the plain verifier: both
`Rounds` applications, the line coefficients, the wiring check and the line
challenge. -/
theorem layer_iteration {A : Type} (values outputs add mul : List F) (layers selector width : Nat)
    (env : List (Value F G)) (rest : List (Value F G))
    (envEq : env = inputs values outputs add mul layers selector width ++ rest) (restLength : rest.length = 5)
    (widthBound : width ≤ 4) (addTables mulTables : Nat → Wiring F width)
    (addShape : add.length = 2 ^ selector * 2 ^ (width + width + width))
    (mulShape : mul.length = 2 ^ selector * 2 ^ (width + width + width))
    (addBound : add.length < indexLimit) (mulBound : mul.length < indexLimit)
    (addDecoded : ∀ layer < layers,
      ofList? (width + width + width) (block add layer (2 ^ (width + width + width))) = some (addTables layer))
    (mulDecoded : ∀ layer < layers,
      ofList? (width + width + width) (block mul layer (2 ^ (width + width + width))) = some (mulTables layer))
    (selectorBound : layers ≤ 2 ^ selector)
    (index : Nat) (state : GkrVerifier.State F) (inside : index < layers)
    (layerEq : state.1 = index) (pointLength : state.2.1.length = width)
    (next : List (Value F G) → PIR.Proc (Actions F G) A) (agree : AgreeUpToHistories next next) :
    specK readingContext handle meanings layerBody (env ++ .index index :: claimValues state.2.1 state.2.2)
        (afterIteration [51, 50, 49] next) =
      (GkrVerifier.layerStep {} handle width addTables mulTables state).bind fun state' =>
        next (claimValues state'.2.1 state'.2.2) := by
  subst envEq
  obtain ⟨layer, point, claim⟩ := state
  simp only at layerEq pointLength
  subst layerEq
  have length : rest.length = 5 := restLength
  have small : width + width + width < 64 := by omega
  have blockSize : 0 < 2 ^ (width + width + width) := by positivity
  have position : layer < 2 ^ selector := by omega
  have addBlock : (block add layer (2 ^ (width + width + width))).length < indexLimit :=
    Nat.lt_of_le_of_lt (by simp [block]) addBound
  have mulBlock : (block mul layer (2 ^ (width + width + width))).length < indexLimit :=
    Nat.lt_of_le_of_lt (by simp [block]) mulBound
  have nextAgree : AgreeUpToHistories (afterIteration [51, 50, 49] next) (afterIteration [51, 50, 49] next) :=
    afterIteration_agree _ agree
  simp only [GkrVerifier.layerStep, GkrVerifier.rounds, PIR.Proc.bind_assoc, claimValues, inputs]
  rw [layerBody, specK_append]
  simp only [layerStart, leftLoop]
  read_instructions
  try simp only [widthBound, ite_true, decide_true]
  rw [iterate_range_repeatN (fun start continuation => specK readingContext handle meanings leftBody start continuation)
    (fun start start' continuation continuation' startSimilar continuationAgree =>
      specK_similar readingContext handle meanings leftBody start start' continuation continuation' startSimilar
        continuationAgree)
    _ _ (fun state : List F × F => claimValues state.1 state.2)
    (GkrVerifier.round (GkrVerifier.leftContext {}) handle) (fun _ _ => True) width ?leftLaw
    (fun _ state _ _ => Yields.mono (round_yields handle _ state.1.length state rfl) fun _ _ => trivial)
    ([], claim) _ _ trivial ?leftSimilar ?leftAgree]
  case leftSimilar => rfl
  case leftLaw =>
    intro index' state' next' _ _ agree'
    exact left_iteration handle _ (by simp [length]) index' state' next' agree'
  case leftAgree =>
    intro final final' finalSimilar
    refine specK_similar readingContext handle meanings _ _ _ _ _ ?_ nextAgree
    simp only [Similar, List.map_cons, List.map_append] at finalSimilar ⊢
    rw [finalSimilar]
  apply (rounds_yields (G := G) handle (GkrVerifier.leftContext {}) width claim).bind_congr
  intro left leftLength
  simp only [GkrVerifier.layerAfterLeft, GkrVerifier.rounds, PIR.Proc.bind_assoc, claimValues]
  rw [specK_append]
  simp only [layerMiddle, rightLoop]
  read_instructions
  try simp only [widthBound, ite_true, decide_true]
  rw [iterate_range_repeatN (fun start continuation => specK readingContext handle meanings rightBody start continuation)
    (fun start start' continuation continuation' startSimilar continuationAgree =>
      specK_similar readingContext handle meanings rightBody start start' continuation continuation' startSimilar
        continuationAgree)
    _ _ (fun state : List F × F => claimValues state.1 state.2)
    (GkrVerifier.round (GkrVerifier.rightContext {}) handle) (fun _ _ => True) width ?rightLaw
    (fun _ state _ _ => Yields.mono (round_yields handle _ state.1.length state rfl) fun _ _ => trivial)
    ([], left.2) _ _ trivial ?rightSimilar ?rightAgree]
  case rightSimilar => rfl
  case rightLaw =>
    intro index' state' next' _ _ agree'
    exact right_iteration handle _ (by simp [length]) index' state' next' agree'
  case rightAgree =>
    intro final final' finalSimilar
    refine specK_similar readingContext handle meanings _ _ _ _ _ ?_ nextAgree
    simp only [Similar, List.map_cons, List.map_append] at finalSimilar ⊢
    rw [finalSimilar]
  apply (rounds_yields (G := G) handle (GkrVerifier.rightContext {}) width left.2).bind_congr
  intro right rightLength
  simp only [GkrVerifier.layerAfterRight, GkrVerifier.layerAfterConstant, PIR.Proc.bind_assoc, PIR.Proc.bind]
  rw [specK_append]
  simp only [layerLine]
  read_instructions
  try normalize_sites
  refine congrArg (PIR.Proc.call _) (funext fun first => ?_)
  simp only [coefficientLoop]
  read_instructions
  try simp only [widthBound, ite_true, decide_true]
  rw [iterate_range_repeatN (fun start continuation => specK readingContext handle meanings coefficientBody start continuation)
    (fun start start' continuation continuation' startSimilar continuationAgree =>
      specK_similar readingContext handle meanings coefficientBody start start' continuation continuation'
        startSimilar continuationAgree)
    _ _ (fun coefficients : List F => pointValues coefficients)
    (GkrVerifier.lineCoefficient {}) (fun index coefficients => coefficients.length = index + 1) width
    ?coefficientLaw ?coefficientPreserved [first] _ _ rfl ?coefficientSimilar ?coefficientAgree]
  case coefficientSimilar => rfl
  case coefficientLaw =>
    intro index' coefficients next' _ _ agree'
    exact coefficient_iteration handle _ (by simp [length]) index' coefficients
      next' agree'
  case coefficientPreserved =>
    intro index' coefficients _ coefficientsLength
    exact lineCoefficient_yields (G := G) _ coefficients coefficientsLength
  case coefficientAgree =>
    intro final final' finalSimilar
    refine specK_similar readingContext handle meanings _ _ _ _ _ ?_ nextAgree
    simp only [Similar, List.map_cons, List.map_append] at finalSimilar ⊢
    rw [finalSimilar]
  have coefficientsYield := Yields.repeatN
    (invariant := fun index (coefficients : List F) => coefficients.length = index + 1)
    (step := GkrVerifier.lineCoefficient (G := G) {})
    (fun index coefficients length => lineCoefficient_yields (G := G) _ coefficients length) width 0 [first] rfl
  apply coefficientsYield.bind_congr
  intro coefficients coefficientsLength
  simp only [Nat.zero_add] at coefficientsLength
  have coefficientsBound : coefficients.length < indexLimit := by
    rw [coefficientsLength]; unfold indexLimit; omega
  have pointsBound : left.1.length < indexLimit := by rw [leftLength]; unfold indexLimit; omega
  have calls :=
    And.intro (call_selectBlock (G := G) add layer selector (2 ^ (width + width + width)) addShape blockSize
      position addBound) <|
    And.intro (call_selectBlock (G := G) mul layer selector (2 ^ (width + width + width)) mulShape blockSize
      position mulBound) <|
    And.intro (call_evaluateWiring (G := G) width _ point left.1 right.1 (addTables layer)
      (addDecoded layer inside) pointLength leftLength rightLength small addBlock) <|
    And.intro (call_evaluateWiring (G := G) width _ point left.1 right.1 (mulTables layer)
      (mulDecoded layer inside) pointLength leftLength rightLength small mulBlock) <|
    And.intro (fun t => call_evaluateCoefficients (G := G) coefficients t coefficientsBound)
      (fun t => call_linePoint (G := G) left.1 right.1 t (by rw [leftLength, rightLength]) pointsBound)
  simp only [pointValues, GkrVerifier.lineCheck, GkrVerifier.wiringValue]
  rw [layerTail, specK_append]
  simp only [layerTailA]
  read_instructions_with_calls
  rw [specK_append]
  simp only [layerTailB]
  read_instructions
  rw [specK_append]
  simp only [layerTailC]
  read_instructions
  by_cases check : right.2 = extension (width + width + width) (addTables layer)
      (coordinates (width + width + width) (point ++ left.1 ++ right.1)) * (first + coefficients.sum) +
    extension (width + width + width) (mulTables layer)
      (coordinates (width + width + width) (point ++ left.1 ++ right.1)) * first * coefficients.sum
  all_goals try simp only [List.append_assoc] at check
  · simp only [check, decide_true, ite_true, eq_self, PIR.Proc.bind]
    try normalize_sites
    refine congrArg (PIR.Proc.call _) (funext fun t => ?_)
    simp only [layerTailD]
    read_instructions_with_calls
    simp only [GkrVerifier.lineDelivery, PIR.Proc.bind]
    try normalize_sites
    refine congrArg (PIR.Proc.call _) (funext fun _ => ?_)
    exact agree _ _ rfl
  · simp only [check, decide_false, ite_false, PIR.Proc.bind]

end Iterations

/-! ## The reading -/

section Finish
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem acceptance_similar {values values' : List (Value F G)} (similar : Similar values values') :
    acceptance values = acceptance values' := by
  unfold acceptance
  rw [acceptancePosition_eq]
  rcases similar.entry 0 with same | ⟨_, _, left, right⟩
  · rw [same]
  · rw [left, right]

/-- The reading's final continuation, read through the acceptance output. -/
def finish (final : List (Value F G)) : PIR.Proc (Actions F G) (Option Bool) :=
  match Zkc.Construction.read final participant.returned with
  | some values => .done (acceptance values)
  | none => .halt .refused

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem finish_agree : AgreeUpToHistories (finish (F := F) (G := G)) finish := by
  intro final final' similar
  unfold finish
  rcases read_similar similar participant.returned with ⟨none, none'⟩ |
    ⟨values, values', found, found', same⟩
  · rw [none, none']
  · rw [found, found']
    dsimp only
    rw [acceptance_similar same]

theorem spec_finish (handle : Nat) (env : List (Value F G)) :
    (spec readingContext handle meanings participant.returned participant.instructions env).bind
        (fun values => .done (acceptance values)) =
      specK readingContext handle meanings participant.instructions env finish := by
  unfold spec
  rw [specK_bind]
  congr 1
  funext final
  unfold finish
  cases Zkc.Construction.read final participant.returned <;> rfl

end Finish

section Reading
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- On a well-formed statement, the interactive reading of the compiled GKR
verifier, read through its acceptance output, is the plain GKR verifier. -/
theorem reading (handle : Nat) (values outputs add mul : List F) (layers selector width : Nat)
    (initial : History F G) (outputsTable inputsTable : Table F width)
    (outputsDecoded : ofList? width outputs = some outputsTable)
    (inputsDecoded : ofList? width values = some inputsTable)
    (addTables mulTables : Nat → Wiring F width)
    (addShape : add.length = 2 ^ selector * 2 ^ (width + width + width))
    (mulShape : mul.length = 2 ^ selector * 2 ^ (width + width + width))
    (addBound : add.length < indexLimit) (mulBound : mul.length < indexLimit)
    (addDecoded : ∀ layer < layers,
      ofList? (width + width + width) (block add layer (2 ^ (width + width + width))) = some (addTables layer))
    (mulDecoded : ∀ layer < layers,
      ofList? (width + width + width) (block mul layer (2 ^ (width + width + width))) = some (mulTables layer))
    (selectorBound : layers ≤ 2 ^ selector) (widthBound : width ≤ 4) (layersBound : layers ≤ 4) :
    (spec readingContext handle meanings participant.returned participant.instructions
        (inputs values outputs add mul layers selector width ++ [.transcript initial])).bind
        (fun result => .done (acceptance result)) =
      GkrVerifier.verifier {} handle layers width outputsTable inputsTable addTables mulTables := by
  have small : width < 64 := by omega
  have tableBound : 2 ^ width < indexLimit := by
    unfold indexLimit
    exact Nat.pow_lt_pow_right (by decide) small
  have outputsBound : outputs.length < indexLimit := by
    rw [ofList?_length _ _ outputsDecoded]; exact tableBound
  have valuesBound : values.length < indexLimit := by
    rw [ofList?_length _ _ inputsDecoded]; exact tableBound
  have length : (0 : Nat) = 0 := rfl
  rw [spec_finish, instructions_eq, topInstructions, specK_append]
  simp only [inputs, topStart, outputLoop]
  read_instructions
  try simp only [widthBound, ite_true, decide_true]
  rw [iterate_range_repeatN (fun start continuation => specK readingContext handle meanings outputBody start continuation)
    (fun start start' continuation continuation' startSimilar continuationAgree =>
      specK_similar readingContext handle meanings outputBody start start' continuation continuation' startSimilar
        continuationAgree)
    _ _ (fun point : List F => pointValues point) (GkrVerifier.outputRound {} handle)
    (fun index point => point.length = index) width ?outputLaw ?outputPreserved [] _ _ rfl ?outputSimilar
    ?outputAgree]
  case outputSimilar => rfl
  case outputLaw =>
    intro index point next _ _ agree
    exact output_iteration handle _ (by simp) index point next agree
  case outputPreserved =>
    intro index point _ pointLength
    exact outputRound_yields handle index point pointLength
  case outputAgree =>
    intro final final' finalSimilar
    refine specK_similar readingContext handle meanings _ _ _ _ _ ?_ finish_agree
    simp only [Similar, List.map_cons, List.map_append] at finalSimilar ⊢
    rw [finalSimilar]
  unfold GkrVerifier.verifier
  have pointsYield := Yields.repeatN (invariant := fun index (point : List F) => point.length = index)
    (step := GkrVerifier.outputRound (G := G) {} handle)
    (fun index point pointLength => outputRound_yields handle index point pointLength) width 0 [] rfl
  apply pointsYield.bind_congr
  intro point pointLength
  simp only [Nat.zero_add] at pointLength
  simp only [GkrVerifier.afterOutputs, pointValues]
  rw [specK_append]
  simp only [topMiddle, layerLoop]
  have calls := call_evaluate (G := G) width outputs point outputsTable outputsDecoded pointLength small
    outputsBound
  read_instructions_with_calls
  try simp only [layersBound, ite_true, decide_true]
  rw [iterate_range_repeatN (fun start continuation => specK readingContext handle meanings layerBody start continuation)
    (fun start start' continuation continuation' startSimilar continuationAgree =>
      specK_similar readingContext handle meanings layerBody start start' continuation continuation' startSimilar
        continuationAgree)
    _ _ (fun state : GkrVerifier.State F => claimValues state.2.1 state.2.2)
    (GkrVerifier.layerStep {} handle width addTables mulTables)
    (fun index state => state.1 = index ∧ state.2.1.length = width) layers ?layerLaw ?layerPreserved
    (0, point, extension width outputsTable (coordinates width point)) _ _ ⟨rfl, pointLength⟩ ?layerSimilar
    ?layerAgree]
  case layerSimilar => rfl
  case layerLaw =>
    intro index state next inside valid agree
    exact layer_iteration handle values outputs add mul layers selector width _ _ rfl
      rfl widthBound
      addTables mulTables addShape mulShape addBound mulBound addDecoded mulDecoded selectorBound index
      state inside valid.1 valid.2 next agree
  case layerPreserved =>
    intro index state _ valid
    exact layerStep_yields handle width addTables mulTables index state valid
  case layerAgree =>
    intro final final' finalSimilar
    refine specK_similar readingContext handle meanings _ _ _ _ _ ?_ finish_agree
    simp only [Similar, List.map_cons, List.map_append] at finalSimilar ⊢
    rw [finalSimilar]
  have statesYield := Yields.repeatN
    (invariant := fun index (state : GkrVerifier.State F) => state.1 = index ∧ state.2.1.length = width)
    (step := GkrVerifier.layerStep (G := G) {} handle width addTables mulTables)
    (fun index state valid => layerStep_yields handle width addTables mulTables index state valid) layers 0
    (0, point, extension width outputsTable (coordinates width point)) ⟨rfl, pointLength⟩
  apply statesYield.bind_congr
  intro final finalValid
  simp only [topTail, claimValues]
  have calls := call_evaluate (G := G) width values final.2.1 inputsTable inputsDecoded finalValid.2 small
    valuesBound
  simp only [GkrVerifier.decision]
  read_instructions_with_calls
  simp only [finish, returned_eq]
  read_instructions
  simp only [acceptance, acceptancePosition_eq, List.getElem?_cons_zero]

end Reading

end ZkcExamples.Construction.GkrProof
