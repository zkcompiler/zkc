module

public import ZkcSecurity.FiatShamir.Composition
public import ZkcSecurity.FiatShamir.Reduction
public import ZkcArkLib.Gkr.Layer
public import ZkcExamples.Structured.GkrVerifierProcess

@[expose] public section

/-! Fiat–Shamir soundness of the plain GKR verifier, with a charge per phase.

The subject is `ZkcExamples.Structured.GkrVerifier.verifier`, the GKR library's
verifier of an admitted statement over the common participant actions; the
original GKR Entry's verifier is this process
(`ZkcExamples.Structured.GkrSourceVerifier.verifier_reads`). Its certificate is a
charged reduction over the transcript interface of the common actions
(`ZkcSecurity.FiatShamir.Typed.Reduction`), composed with `bind`, `repeatN`,
`union` and `receive` from one reduction per phase, each at the error of its own
challenge site (`siteCharge`):

* Output point, `1 / |F|`. While the claimed outputs differ from the circuit's
  outputs, their difference is nonzero at some remaining Boolean coordinates
  (`OutputsDiffer`); a fresh challenge loses that with probability at most
  `1 / |F|`, since the extension is affine in each coordinate.
* Layer Sumcheck, `2 / |F|`. A false layer claim `m ≠ W~_i(r)` is a false claim
  about the sum of the layer's gate polynomial
  (`ZkcSecurity.ArkLib.Gkr.gatePolynomial`), whose rounds keep it false except
  with probability `2 / |F|` each (ArkLib's round lemma at degree two) across
  both `Rounds` applications.
* Line, `width / |F|`. After the wiring check passes on a false complete-point
  claim, the received coefficients describe a polynomial other than the
  restriction of `W~_{i+1}` to the line through the two Sumcheck points, so the
  line challenge makes the next layer's claim true with probability at most
  `width / |F|` (`Zkc.Polynomial.Multilinear.agreements_card_le`).
* Inputs. A false claim about the input layer fails the input check.

Each phase is first a reduction with its own uniform error (`outputCertificate`,
`roundCertificate`, `lineCertificate`), whose doomed queries are all at its
site; `sited` makes it a charged reduction for the site charge.

The adversary budget is weighted (`soundness_charged`): a prover whose queries
charge, on every path, at most `proverCost` with each oracle key charged its
site's error makes claimed outputs other than the circuit's accepted with
probability at most `proverCost` plus the validator's charge. The per-phase
errors improve the bound only through this weighting: a prover with a total of
`Q` queries can place all of them at the most expensive site, so against a
total budget its contribution stays `Q max 2 width / |F|`, and `soundness`
bounds acceptance by `(Q + width + layers (2 width + 1)) max 2 width / |F|`.
-/

set_option autoImplicit false

namespace ZkcSecurity.Examples.GkrFiatShamir
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr
open ZkcSecurity.FiatShamir ZkcSecurity.ArkLib.Gkr
open ZkcExamples.Structured.GkrVerifier
open scoped ENNReal

section Error
variable (F : Type) [Fintype F]

/-- The error per challenge. -/
noncomputable def error (width : Nat) : ENNReal :=
  ((max 2 width : Nat) : ENNReal) / Fintype.card F

theorem error_two (width : Nat) : 2 / (Fintype.card F : ENNReal) ≤ error F width :=
  ENNReal.div_le_div_right (by exact_mod_cast le_max_left 2 width) _

theorem error_width (width : Nat) : (width : ENNReal) / Fintype.card F ≤ error F width :=
  ENNReal.div_le_div_right (by exact_mod_cast le_max_right 2 width) _

theorem error_one (width : Nat) : 1 / (Fintype.card F : ENNReal) ≤ error F width :=
  (ENNReal.div_le_div_right (by norm_num) _).trans (error_two F width)

theorem error_zero (width : Nat) : (0 : ENNReal) ≤ error F width := zero_le

/-- An event over a uniform challenge that holds on at most `count` values has
probability at most `count / |F|`. -/
theorem uniform_event_le [SampleableType F] (event : F → Prop) [DecidablePred event] (count : Nat)
    (small : (Finset.univ.filter event).card ≤ count) :
    Pr{let challenge ← $ᵗ F}[event challenge] ≤ (count : ENNReal) / Fintype.card F := by
  rw [SampleableType.prEvent_uniformSample]
  exact ENNReal.div_le_div_right (by exact_mod_cast small) _

end Error

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- The transcript interface of the common participant actions, with field
challenges read directly from the oracle. -/
abbrev transcript (context : Context) :
    Typed.Interface (Actions F G) (Event F G) (Payload F G) (fun _ => F) :=
  interface context id

/-! ## Charges per challenge site -/

section Charges
variable (ctx : ProtocolContext) (context : Context) (width : Nat)

/-- The charge of a key of the plain verifier's queries: the error of its
challenge site, `1 / |F|` at the output point, `2 / |F|` at a round of either
layer Sumcheck application, `width / |F|` at the line challenge, and nothing at
any other key. A key at sites that coincided is charged the larger error. -/
noncomputable def siteCharge (_ : History F G) : Event F G → ENNReal
  | .challenge origin =>
      max (max (if origin = context.query (outputSite ctx) (.draw "bls12-381.fr") then
            1 / (Fintype.card F : ENNReal) else 0)
          (if origin = context.query (challengeSite (leftContext ctx)) (.draw "bls12-381.fr") ∨
              origin = context.query (challengeSite (rightContext ctx)) (.draw "bls12-381.fr") then
            2 / (Fintype.card F : ENNReal) else 0))
        (if origin = context.query (lineChallengeSite ctx) (.draw "bls12-381.fr") then
          (width : ENNReal) / Fintype.card F else 0)
  | _ => 0

omit [Field F] [DecidableEq F] [SampleableType F] in
theorem siteCharge_le (history : History F G) (event : Event F G) :
    siteCharge (F := F) ctx context width history event ≤ error F width := by
  cases event with
  | challenge origin =>
    refine max_le (max_le ?_ ?_) ?_ <;> split_ifs
    · exact error_one F width
    · exact zero_le
    · exact error_two F width
    · exact zero_le
    · exact error_width F width
    · exact zero_le
  | binding => exact zero_le
  | message => exact zero_le
  | publicBinding => exact zero_le

omit [Field F] [DecidableEq F] [SampleableType F] in
theorem output_charge (history : History F G) :
    1 / (Fintype.card F : ENNReal) ≤ siteCharge (F := F) ctx context width history
      (.challenge (context.query (outputSite ctx) (.draw "bls12-381.fr"))) := by
  refine le_max_of_le_left (le_max_of_le_left ?_)
  simp

omit [Field F] [DecidableEq F] [SampleableType F] in
theorem round_charge (inner : ProtocolContext)
    (side : inner = leftContext ctx ∨ inner = rightContext ctx) (history : History F G) :
    2 / (Fintype.card F : ENNReal) ≤ siteCharge (F := F) ctx context width history
      (.challenge (context.query (challengeSite inner) (.draw "bls12-381.fr"))) := by
  refine le_max_of_le_left (le_max_of_le_right ?_)
  rcases side with rfl | rfl <;> simp

omit [Field F] [DecidableEq F] [SampleableType F] in
theorem line_charge (history : History F G) :
    (width : ENNReal) / Fintype.card F ≤ siteCharge (F := F) ctx context width history
      (.challenge (context.query (lineChallengeSite ctx) (.draw "bls12-381.fr"))) := by
  refine le_max_of_le_right ?_
  simp

end Charges

omit [Field F] [Fintype F] [DecidableEq F] in
/-- A reduction over the common participant actions with a uniform error is a
charged reduction over their transcript interface, with the same doomed
residuals at every history, when the charge at every query of a doomed residual
dominates the error. -/
def sited {A : Type} {final : A → Prop} {error : ENNReal}
    (reduction : Reduction (F := F) (G := G) final error) (context : Context)
    (charge : History F G → Event F G → ENNReal)
    (covers : ∀ process, reduction.doomed process →
      match process with
      | .call (.query site field _) _ =>
          ∀ history, error ≤ charge history (.challenge (context.query site (.draw field)))
      | _ => True) :
    Typed.Reduction (transcript (F := F) (G := G) context) (fun _ value => final value) charge where
  doomed _ process := reduction.doomed process
  step history process member := by
    have step := reduction.step process member
    have charged := covers process member
    match process, step, charged with
    | .done value, step, _ => exact step
    | .halt _, _, _ => trivial
    | .call (.receive ty site sender) next, step, _ => exact fun _ value _ => step value
    | .call (.send site receiver sent) next, step, _ =>
        simp only [Typed.ChargedStepTo, interface]
        cases Payload.ofValue _ sent with
        | none => trivial
        | some payload => exact step
    | .call (.query site field arguments) next, step, charged =>
        refine le_trans (le_of_eq (prEvent_congr _ _ (fun raw => ¬ reduction.doomed (next raw))
          fun raw => ?_)) (step.trans (charged history))
        exact ⟨fun ⟨_, decoded, outside⟩ => by
            cases Option.some.inj decoded
            exact outside,
          fun outside => ⟨_, rfl, outside⟩⟩

/-! ## Output point -/

section Output
variable {width : Nat}

/-- The claimed outputs and the circuit's outputs differ at some Boolean
completion of `point`, whose remaining length is `remaining`. -/
def OutputsDiffer (difference : Table F width) (remaining : Nat) (point : List F) : Prop :=
  point.length + remaining = width ∧
    ∃ suffix : Fin remaining → Bool,
      extension width difference (coordinates width (point ++ List.ofFn (booleanPoint suffix))) ≠ 0

omit [Fintype F] [DecidableEq F] [SampleableType F] in
theorem ofFn_booleanPoint_succ {remaining : Nat} (suffix : Fin (remaining + 1) → Bool) :
    List.ofFn (booleanPoint (F := F) suffix) =
      (if suffix 0 then 1 else 0) :: List.ofFn (booleanPoint (suffix ∘ Fin.succ)) := by
  rw [List.ofFn_succ]
  rfl

/-- A fresh challenge keeps a nonzero difference with probability at least
`1 - 1 / |F|`. -/
theorem outputsDiffer_successor (difference : Table F width) (remaining : Nat) (point : List F)
    (differ : OutputsDiffer difference (remaining + 1) point) :
    Pr{let challenge ← $ᵗ F}[¬ OutputsDiffer difference remaining (point ++ [challenge])] ≤
      1 / (Fintype.card F : ENNReal) := by
  classical
  obtain ⟨sized, suffix, nonzero⟩ := differ
  set tail := List.ofFn (booleanPoint (F := F) (suffix ∘ Fin.succ))
  have short : point.length < width := by omega
  let low := extension width difference (coordinates width (point ++ 0 :: tail))
  let high := extension width difference (coordinates width (point ++ 1 :: tail))
  have pair : ¬ (low = 0 ∧ high = 0) := by
    rintro ⟨lowZero, highZero⟩
    apply nonzero
    rw [ofFn_booleanPoint_succ, extension_insert difference point tail _ short]
    change (1 - _) * low + _ * high = 0
    rw [lowZero, highZero]
    ring
  refine (prEvent_mono _ _ (fun challenge => (1 - challenge) * low + challenge * high = 0)
    (fun challenge escaped => ?_)).trans
    ((uniform_event_le F _ 1 (affine_zeros_card_le low high pair)).trans (by norm_num))
  by_contra notZero
  apply escaped
  refine ⟨by simp; omega, suffix ∘ Fin.succ, ?_⟩
  rw [List.append_assoc, List.singleton_append, extension_insert difference point tail _ short]
  exact notZero

variable (ctx : ProtocolContext) (handle : Nat)

/-- One output-point round, from a difference with `remaining + 1` coordinates
left to one with `remaining` left, at the output point's error `1 / |F|`. -/
noncomputable def outputCertificate (difference : Table F width) (remaining : Nat) :
    Reduction (F := F) (G := G) (OutputsDiffer difference remaining) (1 / (Fintype.card F : ENNReal)) where
  doomed process := ∃ point, OutputsDiffer difference (remaining + 1) point ∧
    (process = outputRound ctx handle point ∨
      ∃ r, OutputsDiffer difference remaining (point ++ [r]) ∧
        (process = outputDelivery ctx point r ∨ process = .done (point ++ [r])))
  step := by
    rintro _ ⟨point, differ, rfl | ⟨r, next, rfl | rfl⟩⟩
    · refine (prEvent_mono _ _ (fun r => ¬ OutputsDiffer difference remaining (point ++ [r]))
        (fun r escaped => ?_)).trans (outputsDiffer_successor difference remaining point differ)
      intro next
      exact escaped ⟨point, differ, .inr ⟨r, next, .inl rfl⟩⟩
    · exact ⟨point, differ, .inr ⟨r, next, .inr rfl⟩⟩
    · exact next

/-- All output-point rounds, charged per site: their final points differ with no
coordinate left. -/
noncomputable def outputsReduction (context : Context) (difference : Table F width) :
    Typed.Reduction (transcript (F := F) (G := G) context) (fun _ point => OutputsDiffer difference 0 point)
      (siteCharge ctx context width) :=
  Typed.Reduction.repeatN (transcript context)
    (invariant := fun _ remaining point => OutputsDiffer difference remaining point)
    (outputRound ctx handle)
    (fun remaining => sited (outputCertificate ctx handle difference remaining) context _
      fun _ ⟨_, _, shape⟩ => by
        rcases shape with rfl | ⟨_, _, rfl | rfl⟩
        · exact fun history => output_charge ctx context width history
        · trivial
        · trivial)
    (fun _ _ point differ => ⟨point, differ, .inl rfl⟩)

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Claimed outputs other than the circuit's differ at the empty point. -/
theorem outputsDiffer_initial (difference : Table F width) (nonzero : ∃ bits, difference bits ≠ 0) :
    OutputsDiffer difference width [] := by
  obtain ⟨bits, nonzero⟩ := nonzero
  refine ⟨by simp, bits, ?_⟩
  rw [List.nil_append, coordinates_ofFn, extension_boolean]
  exact nonzero

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- At a complete point the difference is nonzero. -/
theorem outputsDiffer_final (difference : Table F width) (point : List F)
    (differ : OutputsDiffer difference 0 point) :
    point.length = width ∧ extension width difference (coordinates width point) ≠ 0 := by
  obtain ⟨sized, suffix, nonzero⟩ := differ
  refine ⟨by omega, ?_⟩
  simpa using nonzero

end Output

/-! ## Sumcheck rounds of a layer -/

section Rounds
variable {width : Nat} (statement : _root_.Sumcheck.Spec.OracleStatement F (width + width) 2 ())
  (start : List F)

/-- A false claim at the challenges `start ++ point`, with `remaining` rounds of
this application left. -/
def RoundsFalse (remaining : Nat) (state : List F × F) : Prop :=
  state.1.length + remaining = width ∧ start.length ≤ width ∧
    FalseClaim statement (start ++ state.1) state.2

variable (ctx : ProtocolContext) (handle : Nat)

/-- The residuals of one round from `state`. -/
def RoundResidual (remaining : Nat) (state : List F × F) (process : PIR.Process (Actions F G) (List F × F)) :
    Prop :=
  process = round ctx handle state ∨ (∃ c0, process = roundFirst ctx handle state c0) ∨
    (∃ c0 c1, process = roundSecond ctx handle state c0 c1) ∨
    (∃ c0 c1 c2, process = roundCheck ctx handle state c0 c1 c2) ∨
    ∃ c0 c1 c2 r, RoundsFalse statement start remaining (state.1 ++ [r], c0 + r * (c1 + r * c2)) ∧
      (process = roundChallenge ctx state c0 c1 c2 r ∨
        process = .done (state.1 ++ [r], c0 + r * (c1 + r * c2)))

/-- One degree-two round keeps a false claim false except with probability
`2 / |F|`. -/
noncomputable def roundCertificate (remaining : Nat) :
    Reduction (F := F) (G := G) (RoundsFalse statement start remaining) (2 / (Fintype.card F : ENNReal)) where
  doomed process := ∃ state, RoundsFalse statement start (remaining + 1) state ∧
    RoundResidual statement start ctx handle remaining state process
  step := by
    rintro _ ⟨state, holds, rfl | ⟨c0, rfl⟩ | ⟨c0, c1, rfl⟩ | ⟨c0, c1, c2, rfl⟩ |
      ⟨c0, c1, c2, r, next, rfl | rfl⟩⟩
    · exact fun c0 => ⟨state, holds, .inr (.inl ⟨c0, rfl⟩)⟩
    · exact fun c1 => ⟨state, holds, .inr (.inr (.inl ⟨c0, c1, rfl⟩))⟩
    · exact fun c2 => ⟨state, holds, .inr (.inr (.inr (.inl ⟨c0, c1, c2, rfl⟩)))⟩
    · unfold roundCheck
      split
      · rename_i checked
        obtain ⟨sized, startSize, wrong⟩ := holds
        have bound := falseClaim_successor statement (start ++ state.1) state.2 c0 c1 c2 wrong
          (by simp; omega) checked
        refine (prEvent_mono _ _ _ (fun r escaped => ?_)).trans bound
        intro stays
        apply escaped
        refine ⟨state, ⟨sized, startSize, wrong⟩, .inr (.inr (.inr (.inr ⟨c0, c1, c2, r, ?_, .inl rfl⟩)))⟩
        refine ⟨by simp; omega, startSize, ?_⟩
        rw [← List.append_assoc]
        exact stays
      · trivial
    · exact ⟨state, holds, .inr (.inr (.inr (.inr ⟨c0, c1, c2, r, next, .inr rfl⟩)))⟩
    · exact next

/-- All rounds of one `Rounds` application, at the context `ctx` of the left or
the right application of a layer at `outer`, charged per site. -/
noncomputable def roundsReduction (outer : ProtocolContext) (context : Context)
    (side : ctx = leftContext outer ∨ ctx = rightContext outer) :
    Typed.Reduction (transcript (F := F) (G := G) context) (fun _ state => RoundsFalse statement start 0 state)
      (siteCharge outer context width) :=
  Typed.Reduction.repeatN (transcript context)
    (invariant := fun _ remaining state => RoundsFalse statement start remaining state)
    (round ctx handle)
    (fun remaining => sited (roundCertificate statement start ctx handle remaining) context _
      fun _ ⟨state, _, shape⟩ => by
        rcases shape with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨c0, c1, c2, rfl⟩ | ⟨_, _, _, _, _, rfl | rfl⟩
        · trivial
        · trivial
        · trivial
        · by_cases check : state.2 = c0 + c0 + c1 + c2
          · simp only [roundCheck, check, ↓reduceIte]
            exact fun history => round_charge outer context width ctx side history
          · simp only [roundCheck, check, ↓reduceIte]
        · trivial
        · trivial)
    (fun _ _ state holds => ⟨state, holds, .inl rfl⟩)

theorem rounds_doomed (outer : ProtocolContext) (context : Context)
    (side : ctx = leftContext outer ∨ ctx = rightContext outer) (history : History F G) (claim : F)
    (startSize : start.length ≤ width) (wrong : FalseClaim statement start claim) :
    (roundsReduction (G := G) statement start ctx handle outer context side).doomed history
      (rounds ctx handle width claim) :=
  Typed.Reduction.repeatN_doomed _ _ _ _ history width ([], claim) ⟨by simp, startSize, by simpa using wrong⟩

end Rounds

/-! ## Layers -/

section Layer
variable {width : Nat} (layers : Nat) (inputs : Table F width) (add mul : Nat → Wiring F width)

/-- A false claim about layer `state.1` at its point, with `remaining` layers
below it. -/
def LayerFalse (remaining : Nat) (state : State F) : Prop :=
  state.1 + remaining = layers ∧ state.2.1.length = width ∧
    state.2.2 ≠ extension width (values add mul inputs remaining state.1) (coordinates width state.2.1)

/-- The Sumcheck statement of layer `index` at `point`: its gate polynomial with
the wiring restricted at the point and the values of the layer below, which has
`remaining` layers below it. -/
noncomputable def layerStatement (remaining index : Nat) (point : List F) :
    _root_.Sumcheck.Spec.OracleStatement F (width + width) 2 () :=
  gateStatement (fixPrefix width (add index) (coordinates width point))
    (fixPrefix width (mul index) (coordinates width point)) (values add mul inputs remaining (index + 1))

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- A false layer claim is a false claim about the sum of its gate polynomial. -/
theorem layer_falseClaim (remaining : Nat) (state : State F)
    (holds : LayerFalse layers inputs add mul (remaining + 1) state) :
    FalseClaim (layerStatement inputs add mul remaining state.1 state.2.1) [] state.2.2 := by
  apply falseClaim_initial
  change state.2.2 ≠ ∑ point ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ (width + width),
    MvPolynomial.eval point (gatePolynomial _ _ _)
  rw [gatePolynomial_sum, ← extension_layer]
  exact holds.2.2

/-- The remaining coefficients of a line polynomial with constant term `first`. -/
def CoefficientsFrom (first : F) (count remaining : Nat) (coefficients : List F) : Prop :=
  coefficients.length + remaining = count + 1 ∧ coefficients.head? = some first

variable (ctx : ProtocolContext) (handle : Nat)

/-- One further line coefficient; there is no challenge. -/
noncomputable def coefficientCertificate (first : F) (remaining : Nat) :
    Reduction (F := F) (G := G) (CoefficientsFrom first width remaining) 0 where
  doomed process := ∃ coefficients, CoefficientsFrom first width (remaining + 1) coefficients ∧
    (process = lineCoefficient ctx coefficients ∨ ∃ c, process = .done (coefficients ++ [c]))
  step := by
    rintro _ ⟨coefficients, ⟨sized, head⟩, rfl | ⟨c, rfl⟩⟩
    · exact fun c => ⟨coefficients, ⟨sized, head⟩, .inr ⟨c, rfl⟩⟩
    · refine ⟨by simp; omega, ?_⟩
      cases coefficients with
      | nil => simp at head
      | cons first' rest => simpa using head

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The gate polynomial at the two Sumcheck points is the wiring check's value
at the true values of the layer below. -/
theorem layerStatement_eval (remaining : Nat) (state : State F) (left right : List F)
    (pointSize : state.2.1.length = width) (leftSize : left.length = width)
    (rightSize : right.length = width) :
    MvPolynomial.eval (coordinates (width + width) (left ++ right))
        (layerStatement inputs add mul remaining state.1 state.2.1).val =
      wiringValue
        (extension (width + width + width) (add state.1)
          (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
        (extension (width + width + width) (mul state.1)
          (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
        (extension width (values add mul inputs remaining (state.1 + 1)) (coordinates width left))
        (extension width (values add mul inputs remaining (state.1 + 1)) (coordinates width right)) := by
  change MvPolynomial.eval _ (gatePolynomial _ _ _) = _
  rw [← point_coordinates width left right leftSize rightSize, gatePolynomial_point,
    coordinates_three _ _ _ pointSize leftSize rightSize, extension_fixPrefix, extension_fixPrefix]
  simp only [wiringValue]
  ring

/-- The line challenge: after the wiring check passes on a false complete-point
claim, the next layer's claim is true with probability at most `width / |F|`. -/
theorem line_successor (remaining : Nat) (state : State F) (left right : List F) (claim first : F)
    (coefficients : List F) (holds : LayerFalse layers inputs add mul (remaining + 1) state)
    (leftSize : left.length = width) (rightSize : right.length = width)
    (wrong : MvPolynomial.eval (coordinates (width + width) (left ++ right))
      (layerStatement inputs add mul remaining state.1 state.2.1).val ≠ claim)
    (shape : CoefficientsFrom first width 0 coefficients)
    (checked : claim = wiringValue
      (extension (width + width + width) (add state.1)
        (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
      (extension (width + width + width) (mul state.1)
        (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
      first coefficients.sum) :
    Pr{let t ← $ᵗ F}[¬ LayerFalse layers inputs add mul remaining
        (state.1 + 1, linePoints left right t, powerSum coefficients t)] ≤
      (width : ENNReal) / Fintype.card F := by
  classical
  obtain ⟨index, pointSize, _⟩ := holds
  obtain ⟨sized, head⟩ := shape
  set below := values add mul inputs remaining (state.1 + 1)
  set start := coordinates width left
  set finish := coordinates width right
  have degree : (coefficientPolynomial coefficients).natDegree ≤ width :=
    (coefficientPolynomial_natDegree coefficients).trans (by omega)
  have different : coefficientPolynomial coefficients ≠ linePolynomial width below start finish := by
    intro same
    apply wrong
    have atZero := congrArg (fun polynomial => polynomial.eval 0) same
    have atOne := congrArg (fun polynomial => polynomial.eval 1) same
    simp only [coefficientPolynomial_eval_zero, coefficientPolynomial_eval_one, linePolynomial_zero,
      linePolynomial_one] at atZero atOne
    have firstValue : first = extension width below start := by
      cases coefficients with
      | nil => simp at head
      | cons first' rest =>
          simp only [List.head?_cons, Option.some.injEq] at head
          simpa [head] using atZero
    rw [checked, layerStatement_eval inputs add mul remaining state left right pointSize leftSize rightSize,
      firstValue, atOne]
  refine (prEvent_mono _ _ (fun t => (coefficientPolynomial coefficients).eval t =
      extension width below (linePoint start finish t)) (fun t escaped => ?_)).trans
    (uniform_event_le F _ width (agreements_card_le below start finish _ degree different))
  by_contra notEqual
  apply escaped
  refine ⟨by omega, by simp [linePoints_length, leftSize, rightSize], ?_⟩
  rw [coordinates_linePoints left right t leftSize rightSize, ← coefficientPolynomial_eval]
  exact notEqual

/-- The facts a layer has established when its line check is reached: a false
claim at its two complete Sumcheck points and the received coefficients. -/
def LineReady (remaining : Nat) (state : State F) (left right : List F) (claim first : F)
    (coefficients : List F) : Prop :=
  LayerFalse layers inputs add mul (remaining + 1) state ∧ left.length = width ∧
    right.length = width ∧
    MvPolynomial.eval (coordinates (width + width) (left ++ right))
      (layerStatement inputs add mul remaining state.1 state.2.1).val ≠ claim ∧
    CoefficientsFrom first width 0 coefficients

/-- The wiring check and the line challenge, at the line's error `width / |F|`. -/
noncomputable def lineCertificate (remaining : Nat) :
    Reduction (F := F) (G := G) (LayerFalse layers inputs add mul remaining)
      ((width : ENNReal) / Fintype.card F) where
  doomed process := ∃ state left right claim first coefficients,
    LineReady layers inputs add mul remaining state left right claim first coefficients ∧
    (process = lineCheck ctx handle width (add state.1) (mul state.1) state left right claim first
        coefficients ∨
      ∃ t, LayerFalse layers inputs add mul remaining
          (state.1 + 1, linePoints left right t, powerSum coefficients t) ∧
        (process = lineDelivery ctx state left right coefficients t ∨
          process = .done (state.1 + 1, linePoints left right t, powerSum coefficients t)))
  step := by
    rintro _ ⟨state, left, right, claim, first, coefficients, ready, rfl | ⟨t, next, rfl | rfl⟩⟩
    · unfold lineCheck
      split
      · rename_i checked
        obtain ⟨holds, leftSize, rightSize, wrong, shape⟩ := ready
        refine (prEvent_mono _ _ _ (fun t escaped => ?_)).trans
          (line_successor layers inputs add mul remaining state left right claim first coefficients
            holds leftSize rightSize wrong shape checked)
        intro stays
        exact escaped ⟨state, left, right, claim, first, coefficients,
          ⟨holds, leftSize, rightSize, wrong, shape⟩, .inr ⟨t, stays, .inl rfl⟩⟩
      · trivial
    · exact ⟨state, left, right, claim, first, coefficients, ready, .inr ⟨t, next, .inr rfl⟩⟩
    · exact next

variable (context : Context)

/-- The line polynomial's coefficients, then the wiring check and the line
challenge, charged per site. -/
noncomputable def constantReduction (remaining : Nat) (state : State F) (left right : List F × F)
    (first : F) (ready : LayerFalse layers inputs add mul (remaining + 1) state ∧
      left.1.length = width ∧ right.1.length = width ∧
      MvPolynomial.eval (coordinates (width + width) (left.1 ++ right.1))
        (layerStatement inputs add mul remaining state.1 state.2.1).val ≠ right.2) :
    Typed.Reduction (transcript (F := F) (G := G) context)
      (fun _ next => LayerFalse layers inputs add mul remaining next) (siteCharge ctx context width) :=
  (Typed.Reduction.repeatN (transcript context)
      (invariant := fun _ remaining coefficients => CoefficientsFrom first width remaining coefficients)
      (lineCoefficient ctx)
      (fun remaining => sited (coefficientCertificate ctx first remaining) context _
        fun _ ⟨_, _, shape⟩ => by
          rcases shape with rfl | ⟨_, rfl⟩
          · trivial
          · trivial)
      (fun _ _ coefficients shape => ⟨coefficients, shape, .inl rfl⟩)).bind (transcript context)
    (lineCheck ctx handle width (add state.1) (mul state.1) state left.1 right.1 right.2 first)
    (sited (lineCertificate layers inputs add mul ctx handle remaining) context _
      fun _ ⟨state, left, right, claim, first, coefficients, _, shape⟩ => by
        rcases shape with rfl | ⟨_, _, rfl | rfl⟩
        · by_cases check : claim = wiringValue
              (extension (width + width + width) (add state.1)
                (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
              (extension (width + width + width) (mul state.1)
                (coordinates (width + width + width) (state.2.1 ++ left ++ right)))
              first coefficients.sum
          · simp only [lineCheck, check, ↓reduceIte]
            exact fun history => line_charge ctx context width history
          · simp only [lineCheck, check, ↓reduceIte]
        · trivial
        · trivial)
    (fun _ coefficients shape => ⟨state, left.1, right.1, right.2, first, coefficients,
      ⟨ready.1, ready.2.1, ready.2.2.1, ready.2.2.2, shape⟩, .inl rfl⟩)

theorem constant_doomed (remaining : Nat) (state : State F) (left right : List F × F) (first : F)
    (ready : LayerFalse layers inputs add mul (remaining + 1) state ∧
      left.1.length = width ∧ right.1.length = width ∧
      MvPolynomial.eval (coordinates (width + width) (left.1 ++ right.1))
        (layerStatement inputs add mul remaining state.1 state.2.1).val ≠ right.2) (history : History F G) :
    (constantReduction (G := G) layers inputs add mul ctx handle context remaining state left right first
      ready).doomed history (layerAfterConstant ctx handle width add mul state left right first) :=
  Typed.Reduction.bind_doomed _ _ _ _ _ _ _
    (Typed.Reduction.repeatN_doomed _ _ _ _ history width [first] ⟨by simp; omega, rfl⟩)

/-- The line polynomial's constant term, received at any history, then the rest
of the layer. -/
noncomputable def afterRightReduction (remaining : Nat) (state : State F) (left right : List F × F)
    (ready : LayerFalse layers inputs add mul (remaining + 1) state ∧
      left.1.length = width ∧ right.1.length = width ∧
      MvPolynomial.eval (coordinates (width + width) (left.1 ++ right.1))
        (layerStatement inputs add mul remaining state.1 state.2.1).val ≠ right.2) :
    Typed.Reduction (transcript (F := F) (G := G) context)
      (fun _ next => LayerFalse layers inputs add mul remaining next) (siteCharge ctx context width) :=
  Typed.Reduction.union (transcript context) fun history : History F G =>
    Typed.Reduction.receive (transcript context)
      (operation := .receive scalar (lineConstantSite ctx) (ctx.roles 0)) rfl history
      (layerAfterConstant ctx handle width add mul state left right)
      (fun _ => Typed.Reduction.union (transcript context) fun first : F =>
        constantReduction layers inputs add mul ctx handle context remaining state left right first ready)
      (fun _ first _ => ⟨first, constant_doomed layers inputs add mul ctx handle context remaining state
        left right first ready _⟩)

/-- The second `Rounds` application's result, then the line polynomial. -/
noncomputable def afterLeftReduction (remaining : Nat) (state : State F)
    (holds : LayerFalse layers inputs add mul (remaining + 1) state) (left : List F × F)
    (leftFalse : RoundsFalse (layerStatement inputs add mul remaining state.1 state.2.1) [] 0 left) :
    Typed.Reduction (transcript (F := F) (G := G) context)
      (fun _ next => LayerFalse layers inputs add mul remaining next) (siteCharge ctx context width) :=
  (roundsReduction (layerStatement inputs add mul remaining state.1 state.2.1) left.1 (rightContext ctx)
      handle ctx context (.inr rfl)).bind (transcript context)
    (layerAfterRight ctx handle width add mul state left)
    (Typed.Reduction.union (transcript context) fun (right : {right : List F × F //
        RoundsFalse (layerStatement inputs add mul remaining state.1 state.2.1) left.1 0 right}) =>
      afterRightReduction layers inputs add mul ctx handle context remaining state left right.1
        ⟨holds, by have := leftFalse.1; simpa using this, by have := right.2.1; simpa using this,
          falseClaim_terminal _ _ _ right.2.2.2 (by
            have leftSize := leftFalse.1
            have rightSize := right.2.1
            simp only [List.length_append]
            simp only [Nat.add_zero] at leftSize rightSize
            omega)⟩)
    (fun history right rightFalse => ⟨⟨right, rightFalse⟩, history, .inl ⟨rfl, rfl⟩⟩)

/-- One layer, from a false claim with `remaining + 1` layers below it to one
with `remaining` below it. -/
noncomputable def layerReduction (remaining : Nat) :
    Typed.Reduction (transcript (F := F) (G := G) context)
      (fun _ next => LayerFalse layers inputs add mul remaining next) (siteCharge ctx context width) :=
  Typed.Reduction.union (transcript context) fun (state : {state : State F //
      LayerFalse layers inputs add mul (remaining + 1) state}) =>
    (roundsReduction (layerStatement inputs add mul remaining state.1.1 state.1.2.1) [] (leftContext ctx)
        handle ctx context (.inl rfl)).bind (transcript context)
      (layerAfterLeft ctx handle width add mul state.1)
      (Typed.Reduction.union (transcript context) fun (left : {left : List F × F //
          RoundsFalse (layerStatement inputs add mul remaining state.1.1 state.1.2.1) [] 0 left}) =>
        afterLeftReduction layers inputs add mul ctx handle context remaining state.1 state.2 left.1
          left.2)
      (fun history left leftFalse => ⟨⟨left, leftFalse⟩, Typed.Reduction.bind_doomed _ _ _ _ _ _ _
        (rounds_doomed _ left.1 (rightContext ctx) handle ctx context (.inr rfl) history left.2 (by
          have := leftFalse.1
          simp only [Nat.add_zero] at this
          omega) (by simpa using leftFalse.2.2))⟩)

theorem layer_doomed (remaining : Nat) (state : State F)
    (holds : LayerFalse layers inputs add mul (remaining + 1) state) (history : History F G) :
    (layerReduction (G := G) layers inputs add mul ctx handle context remaining).doomed history
      (layerStep ctx handle width add mul state) :=
  ⟨⟨state, holds⟩, Typed.Reduction.bind_doomed _ _ _ _ _ _ _
    (rounds_doomed _ [] (leftContext ctx) handle ctx context (.inl rfl) history state.2.2 (by simp)
      (layer_falseClaim layers inputs add mul remaining state holds))⟩

/-- All layers: their final claim is a false claim about the inputs. -/
noncomputable def layersReduction :
    Typed.Reduction (transcript (F := F) (G := G) context)
      (fun _ final => LayerFalse layers inputs add mul 0 final) (siteCharge ctx context width) :=
  Typed.Reduction.repeatN (transcript context)
    (invariant := fun _ remaining state => LayerFalse layers inputs add mul remaining state)
    (layerStep ctx handle width add mul) (layerReduction layers inputs add mul ctx handle context)
    (fun history remaining state holds =>
      layer_doomed layers inputs add mul ctx handle context remaining state holds history)

end Layer

/-! ## The verifier -/

section Verifier
variable (ctx : ProtocolContext) (handle layers width : Nat) (outputs inputs : Table F width)
  (add mul : Nat → Wiring F width)

/-- The difference between the claimed outputs and the circuit's outputs. -/
def outputDifference : Table F width :=
  fun bits => outputs bits - values add mul inputs layers 0 bits

/-- The input check rejects a false claim about the inputs. -/
noncomputable def decisionCertificate :
    Reduction (F := F) (G := G) (fun decided : Option Bool => ¬ decided = some true) 0 where
  doomed process := ∃ state, LayerFalse layers inputs add mul 0 state ∧
    process = .done (decision width inputs state)
  step := by
    rintro _ ⟨state, ⟨_, _, wrong⟩, rfl⟩
    change ¬ some (decide (extension width inputs (coordinates width state.2.1) = state.2.2)) = some true
    simp only [Option.some.injEq, decide_eq_true_eq]
    exact fun same => wrong same.symm

variable (context : Context)

/-- The layers from the output claim, then the input check. -/
noncomputable def afterOutputsReduction :
    Typed.Reduction (transcript (F := F) (G := G) context) (fun _ (decided : Option Bool) => ¬ decided = some true)
      (siteCharge ctx context width) :=
  (layersReduction layers inputs add mul ctx handle context).bind (transcript context)
    (fun final => .done (decision width inputs final))
    (sited (decisionCertificate layers width inputs add mul) context _
      fun _ ⟨_, _, same⟩ => by
        rw [same]
        trivial)
    (fun _ final holds => ⟨final, holds, rfl⟩)

/-- The charged reduction of the plain GKR verifier: one reduction per phase,
each at its own site's error. -/
noncomputable def reduction :
    Typed.Reduction (transcript (F := F) (G := G) context) (fun _ (decided : Option Bool) => ¬ decided = some true)
      (siteCharge ctx context width) :=
  (outputsReduction ctx handle context (outputDifference layers width outputs inputs add mul)).bind
    (transcript context) (afterOutputs ctx handle layers width outputs inputs add mul)
    (afterOutputsReduction ctx handle layers width inputs add mul context)
    (fun history point differ => by
      obtain ⟨sized, nonzero⟩ := outputsDiffer_final _ point differ
      refine Typed.Reduction.bind_doomed _ _ _ _ _ _ _
        (Typed.Reduction.repeatN_doomed _ _ _ _ history layers (0, point, _) ⟨by simp, sized, ?_⟩)
      intro same
      apply nonzero
      change extension width (fun bits => outputs bits - values add mul inputs layers 0 bits)
        (coordinates width point) = 0
      rw [extension_sub]
      exact sub_eq_zero.mpr same)

/-- The charged certificate of the plain GKR verifier. -/
noncomputable def certificate :
    Typed.ChargedCertificate (transcript (F := F) (G := G) context) (fun decided : Option Bool => decided = some true)
      (siteCharge ctx context width) :=
  (reduction ctx handle layers width outputs inputs add mul context).toCertificate (transcript context)
    fun _ _ rejects => rejects

theorem verifier_doomed (wrong : outputs ≠ values add mul inputs layers 0) (initial : History F G) :
    (certificate (G := G) ctx handle layers width outputs inputs add mul context).doomed initial
      (verifier ctx handle layers width outputs inputs add mul) := by
  have nonzero : ∃ bits, outputDifference layers width outputs inputs add mul bits ≠ 0 := by
    obtain ⟨bits, different⟩ := Function.ne_iff.mp wrong
    exact ⟨bits, sub_ne_zero.mpr different⟩
  show (reduction ctx handle layers width outputs inputs add mul context).doomed initial
    (verifier ctx handle layers width outputs inputs add mul)
  exact Typed.Reduction.bind_doomed (transcript context)
    (outputsReduction ctx handle context (outputDifference layers width outputs inputs add mul))
    (afterOutputs ctx handle layers width outputs inputs add mul)
    (afterOutputsReduction ctx handle layers width inputs add mul context) _ initial _
    (Typed.Reduction.repeatN_doomed _ _ _ _ initial width [] (outputsDiffer_initial _ nonzero))

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
theorem outputRound_queryBound (point : List F) :
    QueryBound (outputRound (G := G) ctx handle point) 1 :=
  ⟨Nat.one_pos, fun _ => trivial⟩

omit [Fintype F] [SampleableType F] in
theorem round_queryBound (state : List F × F) : QueryBound (round (G := G) ctx handle state) 1 := by
  intro c0 c1 c2
  change QueryBound (roundCheck ctx handle state c0 c1 c2) 1
  unfold roundCheck
  split
  · exact ⟨Nat.one_pos, fun _ => trivial⟩
  · trivial

omit [Fintype F] [SampleableType F] in
theorem layerStep_queryBound (state : State F) :
    QueryBound (layerStep (G := G) ctx handle width add mul state) (width + (width + (0 + 1))) := by
  refine QueryBound.bind _ _ ?_ fun left => ?_
  · unfold rounds
    simpa using QueryBound.repeatN _ (round_queryBound (leftContext ctx) handle) width ([], state.2.2)
  refine QueryBound.bind _ _ ?_ fun right => ?_
  · unfold rounds
    simpa using QueryBound.repeatN _ (round_queryBound (rightContext ctx) handle) width ([], left.2)
  intro first
  refine QueryBound.bind _ _ ?_ fun coefficients => ?_
  · simpa using QueryBound.repeatN (lineCoefficient (G := G) ctx) (each := 0)
      (fun _ _ => trivial) width [first]
  unfold lineCheck
  split
  · exact ⟨Nat.one_pos, fun _ => trivial⟩
  · trivial

omit [Fintype F] [SampleableType F] in
/-- The verifier makes `width + layers (2 width + 1)` challenges. -/
theorem verifier_queryBound :
    QueryBound (verifier (G := G) ctx handle layers width outputs inputs add mul)
      (width + layers * (2 * width + 1)) := by
  have bound := QueryBound.bind _ (afterOutputs (G := G) ctx handle layers width outputs inputs add mul)
    (QueryBound.repeatN _ (outputRound_queryBound ctx handle) width [])
    (second := layers * (width + (width + (0 + 1))) + 0) fun point =>
      QueryBound.bind _ _ (QueryBound.repeatN _ (layerStep_queryBound ctx handle width add mul) layers _)
        fun _ => trivial
  refine QueryBound.mono _ bound (le_of_eq ?_)
  ring

/-- Fiat–Shamir soundness of the plain GKR verifier against a weighted adversary
budget.

Adversary interface: the statement (claimed outputs, inputs, wiring, number of
layers and width) and the initial transcript history are fixed before the
experiment; the prover is an arbitrary oracle computation on the transcript
oracle over all typed histories whose queries charge at most `proverCost` on
every path, each oracle key charged its site's error (`siteCharge`: `1 / |F|`
for an output-point key, `2 / |F|` for a round key of either layer Sumcheck
application, `width / |F|` for a line key, nothing for any other key); the
oracle starts empty and is shared with the transform, whose
`width + layers (2 width + 1)` challenges are charged at most `max 2 width / |F|`
each. Claimed outputs other than the circuit's are accepted with probability at
most `proverCost + (width + layers (2 width + 1)) max 2 width / |F|`. -/
theorem soundness_charged [DecidableEq G] (wrong : outputs ≠ values add mul inputs layers 0)
    (initial : History F G) (prover : OracleComp (FieldOracle F G) (Proof F G)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨Typed.keyCharge (siteCharge (G := G) ctx context width)⟩
      proverCost) :
    Pr{let result ← (simulateQ randomOracle (FiatShamir.experiment context
        (verifier ctx handle layers width outputs inputs add mul) initial prover)).run' ∅}[
      Accepted (· = some true) result.1] ≤
      proverCost + (width + layers * (2 * width + 1)) * error F width := by
  rw [experiment_eq]
  have bound := Typed.soundness_charged (certificate ctx handle layers width outputs inputs add mul context)
    (verifier ctx handle layers width outputs inputs add mul) initial
    (verifier_doomed ctx handle layers width outputs inputs add mul context wrong initial) _
    (Typed.QueryBound.chargedCostBound (transcript context) (siteCharge_le ctx context width) _ _
      (QueryBound.typed context id _ _ (verifier_queryBound ctx handle layers width outputs inputs add mul))
      initial)
    prover proverCost proverBound
  convert bound using 2
  push_cast
  ring

/-- Fiat–Shamir soundness of the plain GKR verifier.

Adversary interface: the statement (claimed outputs, inputs, wiring, number of
layers and width) and the initial transcript history are fixed before the
experiment; the prover is an arbitrary oracle computation on the transcript
oracle over all typed histories with at most `queries` queries on every path;
the oracle starts empty and is shared with the transform, whose
`width + layers (2 width + 1)` challenges are also charged. Claimed outputs other
than the circuit's are accepted with probability at most
`(queries + width + layers (2 width + 1)) max 2 width / |F|`: against a total
query budget every key is charged the largest site error. -/
theorem soundness [DecidableEq G] (context : Context) (wrong : outputs ≠ values add mul inputs layers 0)
    (initial : History F G) (prover : OracleComp (FieldOracle F G) (Proof F G)) (queries : Nat)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (FiatShamir.experiment context
        (verifier ctx handle layers width outputs inputs add mul) initial prover)).run' ∅}[
      Accepted (· = some true) result.1] ≤
      (queries + (width + layers * (2 * width + 1))) * error F width := by
  have bound := soundness_charged ctx handle layers width outputs inputs add mul context wrong initial prover
    (queries * error F width)
    (Typed.worstCaseCostBound_of_isTotalQueryBound _
      (Typed.keyCharge_le (siteCharge_le ctx context width)) prover queries proverBound)
  rwa [add_mul]

end Verifier

end ZkcSecurity.Examples.GkrFiatShamir
