module

public import ZkcArkLib.Examples.Subjects.Sumcheck.Artifacts
public import ZkcArkLib.Examples.Subjects.Sumcheck.Contract
public import ZkcArkLib.Examples.SumcheckFiatShamir

@[expose] public section

/-! Ordinary soundness evidence of the subject `sumcheck`.

**Model relation.** At a static maximum, a policy statement denotes the
well-formed public statement with its vector, claim and round count when the
vector has a table at that count and the count is at most the maximum; the
model statement is false when its claim is not the vector's total
(`relationAt`). The subject's relation is the one at the admitted original's
maximum (`maximum`).

**Family.** The certificate of `SumcheckFiatShamir` for every table and claim
(`DoomedAny`), extended with the runs whose terminal never accepts
(`Rejecting`): the verifier's rounds from any claim followed by a terminal that
returns false or stops whenever the point has the round count's length. A
challenge cannot leave such a run, so its rounds keep it doomed at every
challenge. The certificate and its step obligations hold for every round count.

**Coverage.** At every maximum whose tables fit the index limit (`coversAt`), a
statement the contract counts as false is false in the model when its vector
has a table at an admitted count: the vector is then below the index limit,
where the retained formula is `claim = total`
(`SumcheckContractBindings.public_formula_equation`). Every other statement
denotes no model statement, and its validator is doomed: above the maximum the
admitted original refuses before any action (`importedValidator_excess`), and
at an admitted count a vector without a table runs the rounds and then fails
the terminal's shape check, or stops on a vector beyond the index limit
(`importedValidator_malformed`, `terminal_rejects`, which holds at every count
below the terminal's coordinate bound).

**Charge.** Every original validator makes at most `maximum` challenges
(`original_queryBound`), each charged `1 / |F|`. -/

namespace ZkcSecurity.Examples.Subjects.Sumcheck
open OracleComp
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint ZkcSecurity.FiatShamir
open ZkcExamples.Construction ZkcExamples.Structured
open ZkcSecurity.Examples.SumcheckFiatShamir
open Zkc.Polynomial.Multilinear
open scoped ENNReal

set_option smartUnfolding false

section Rejection
variable {F G : Type} [Field F] [DecidableEq F]

/-- The residual of the rounds followed by a terminal process `k` of the final
point and claim, at each phase of a round. -/
def residualK (ctx : ProtocolContext) (handle : Nat) (k : List F × F → PIR.Process (Actions F G) (Option Bool)) :
    Phase F → PIR.Process (Actions F G) (Option Bool)
  | .round remaining point claim =>
      (PIR.repeatN remaining (verifierRound ctx handle) (point, claim)).bind k
  | .low remaining point claim low =>
      ((afterLow ctx handle (point, claim) low).bind (PIR.repeatN remaining (verifierRound ctx handle))).bind k
  | .high remaining point claim low high =>
      ((afterHigh ctx handle (point, claim) low high).bind (PIR.repeatN remaining (verifierRound ctx handle))).bind k
  | .challenged remaining point claim low high challenge =>
      ((afterChallenge ctx (point, claim) low high challenge).bind
        (PIR.repeatN remaining (verifierRound ctx handle))).bind k

/-- The point of a phase has the length the remaining rounds complete to `count`. -/
def Sized (count : Nat) : Phase F → Prop
  | .round remaining point _ => point.length + remaining = count
  | .low remaining point _ _ => point.length + (remaining + 1) = count
  | .high remaining point _ _ _ => point.length + (remaining + 1) = count
  | .challenged remaining point _ _ _ _ => point.length + (remaining + 1) = count

/-- A terminal that never accepts: a false decision or a stop. -/
def Rejects (process : PIR.Process (Actions F G) (Option Bool)) : Prop :=
  process = .done (some false) ∨ ∃ stop, process = .halt stop

/-- The residuals of the rounds followed by a terminal that never accepts at a
point of the round count's length. -/
def Rejecting (ctx : ProtocolContext) (handle count : Nat)
    (k : List F × F → PIR.Process (Actions F G) (Option Bool)) (process : PIR.Process (Actions F G) (Option Bool)) :
    Prop :=
  (∀ pc : List F × F, pc.1.length = count → Rejects (k pc)) ∧
    ∃ phase, Sized count phase ∧ residualK ctx handle k phase = process

theorem residualK_high_pass (ctx : ProtocolContext) (handle : Nat)
    (k : List F × F → PIR.Process (Actions F G) (Option Bool)) (remaining : Nat) (point : List F)
    (claim low high : F) (checked : claim = low + high) :
    residualK ctx handle k (.high remaining point claim low high) =
      .call (.query (SumcheckVerifierLaws.challengeSite ctx) "bls12-381.fr" (.cons handle .nil))
        fun challenge => residualK ctx handle k (.challenged remaining point claim low high challenge) := by
  simp only [residualK, afterHigh]
  rw [ite_eq_left_of_eq_true _ _ (eq_true checked)]
  rfl

theorem residualK_high_fail (ctx : ProtocolContext) (handle : Nat)
    (k : List F × F → PIR.Process (Actions F G) (Option Bool)) (remaining : Nat) (point : List F)
    (claim low high : F) (failed : ¬ claim = low + high) :
    residualK ctx handle k (.high remaining point claim low high) = .halt .reject := by
  simp only [residualK, afterHigh]
  rw [ite_eq_right_of_eq_false _ _ (eq_false failed)]
  rfl

variable [Fintype F] [SampleableType F]

/-- Every rejecting residual meets its local obligation: a challenge never leaves
the set. -/
theorem rejecting_step (ctx : ProtocolContext) (handle count : Nat)
    (k : List F × F → PIR.Process (Actions F G) (Option Bool)) :
    ∀ process, Rejecting ctx handle count k process →
      Step (Rejecting ctx handle count k) (· = some true) (1 / (Fintype.card F : ENNReal)) process := by
  rintro _ ⟨rejects, phase, sized, rfl⟩
  cases phase with
  | round remaining point claim =>
      cases remaining with
      | zero =>
          have final : residualK ctx handle k (.round 0 point claim) = k (point, claim) := rfl
          rw [final]
          rcases rejects (point, claim) (by simpa [Sized] using sized) with rejected | ⟨stop, halted⟩
          · rw [rejected]
            exact fun accepted => Bool.false_ne_true (Option.some.inj accepted)
          · rw [halted]
            trivial
      | succ remaining =>
          intro low
          exact ⟨rejects, .low remaining point claim low, by simpa [Sized] using sized, rfl⟩
  | low remaining point claim low =>
      intro high
      exact ⟨rejects, .high remaining point claim low high, sized, rfl⟩
  | high remaining point claim low high =>
      by_cases checked : claim = low + high
      · rw [residualK_high_pass ctx handle k remaining point claim low high checked]
        refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun challenge escaped => escaped
          ⟨rejects, .challenged remaining point claim low high challenge, sized, rfl⟩) zero_le
      · rw [residualK_high_fail ctx handle k remaining point claim low high checked]
        trivial
  | challenged remaining point claim low high challenge =>
      exact ⟨rejects, .round remaining (point ++ [challenge]) ((1 - challenge) * low + challenge * high),
        by simp only [Sized, List.length_append, List.length_singleton] at sized ⊢; omega, rfl⟩

/-- The doomed set of the subject's certificate: the residuals of every table
and claim, the refused verifier, and the rejecting runs. -/
def DoomedAll (ctx : ProtocolContext) (handle : Nat) (process : PIR.Process (Actions F G) (Option Bool)) : Prop :=
  DoomedAny ctx handle process ∨ ∃ count k, Rejecting ctx handle count k process

theorem doomedAll_step (ctx : ProtocolContext) (handle : Nat) :
    ∀ process : PIR.Process (Actions F G) (Option Bool), DoomedAll ctx handle process →
      Step (DoomedAll ctx handle) (· = some true) (1 / (Fintype.card F : ENNReal)) process := by
  rintro process (any | ⟨count, k, rejecting⟩)
  · exact Step.mono (fun _ member => .inl member) process (doomedAny_step ctx handle process any)
  · exact Step.mono (fun _ member => .inr ⟨count, k, member⟩) process
      (rejecting_step ctx handle count k process rejecting)

/-- One certificate for the admitted original at every statement. -/
noncomputable def allCertificate (ctx : ProtocolContext) (handle : Nat) :
    RoundByRound (F := F) (G := G) (· = some true) (1 / (Fintype.card F : ENNReal)) :=
  RoundByRound.ofStep (DoomedAll ctx handle) (doomedAll_step ctx handle)

end Rejection

/-- The static maximum round count of the admitted original. -/
abbrev maximum : Nat := SumcheckSourceNormalForms.reduceMaximum

section Original
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The terminal of the admitted original on a vector, at a final point and claim. -/
def terminalK (raw : List F) (pc : List F × F) : PIR.Process (Actions F G) (Option Bool) :=
  ((SumcheckVerifierTerminal.actualOwnedCheck (G := G) SumcheckSourceViews.unit 1 (some raw) (some pc.1)
    (some pc.2)).bind fun outputs => .done (outputs.get .here)).interpret CommonAdapter.project

/-- At an admitted count, the admitted original runs the rounds from the claim
and then its terminal on the vector, whatever the vector. -/
theorem importedValidator_malformed (count : Nat) (admitted : count ≤ maximum) (raw : List F) (claim : F)
    (handle : Nat) :
    importedValidator (G := G) raw claim count handle =
      (PIR.repeatN count (verifierRound SumcheckSourceVerifier.childContext handle) ([], claim)).bind
        (terminalK raw) := by
  rw [importedValidator]
  change ((SumcheckSourceViews.program.participant F G 1
    (SumcheckSourceVerifier.sourceRootInputs (some raw) (some claim) (some count)
      (some handle))).bind fun outputs => .done (outputs.get .here)).interpret
    CommonAdapter.project = _
  rw [SumcheckSourceVerifier.verifier_optional]
  have bounded : count ≤ SumcheckSourceNormalForms.reduceMaximum := admitted
  simp only [SumcheckVerifierPrelude.admittedRounds, SumcheckVerifierPrelude.pendingRounds, bounded, ↓reduceIte]
  rw [SumcheckVerifierLaws.repeat_present SumcheckSourceVerifier.childContext handle count ([], claim)]
  have collapse : ∀ process : PIR.Process (participantInterface F G) (List F × F),
      (((process.bind fun result => PIR.Process.done (some result.1, some result.2)).bind fun pc =>
          SumcheckVerifierTerminal.actualOwnedCheck (G := G) SumcheckSourceViews.unit 1 (some raw) pc.1 pc.2).bind
        fun outputs : Values (Component (assignment F G)) [.boolean] => PIR.Process.done (outputs.get .here)) =
      process.bind fun pc => (SumcheckVerifierTerminal.actualOwnedCheck (G := G) SumcheckSourceViews.unit 1
        (some raw) (some pc.1) (some pc.2)).bind fun outputs => .done (outputs.get .here) := by
    intro process
    rw [PIR.Process.bind_assoc, PIR.Process.bind_assoc]
    rfl
  refine (congrArg (PIR.Process.interpret CommonAdapter.project) (collapse _)).trans ?_
  rw [PIR.Process.interpret_bind, repeatN_interpret]
  simp only [roundPresent_project]
  rfl

/-- At a point of any length below the terminal's coordinate bound, the terminal
on a vector without a table at that length returns false, or stops for a vector
beyond the index limit. -/
theorem terminal_rejects (raw : List F) (count : Nat) (bounded : count < 64)
    (malformed : ofList? count raw = none) (pc : List F × F) (sized : pc.1.length = count) :
    Rejects (terminalK (G := G) raw pc) := by
  have point : pc.1.length < indexLimit := by
    rw [sized]
    exact lt_of_lt_of_le bounded (by decide)
  by_cases bound : raw.length < indexLimit
  · have shape : ¬ ZkcExamples.Structured.PrimitiveLibrary.HasShape raw pc.1.length 1 := by
      rintro ⟨_, _, _, size⟩
      simp only [Nat.div_one, sized] at size
      simp [ofList?, size] at malformed
    left
    unfold terminalK
    rw [SumcheckVerifierTerminal.terminal_malformed 1 raw pc.1 pc.2 bound point shape]
    rfl
  · right
    refine ⟨.exhausted, ?_⟩
    unfold terminalK
    rw [SumcheckVerifierTerminal.terminal_decision]
    have small : pc.1.length < 64 := by omega
    simp only [point, small, bound, ↓reduceIte]
    rfl

/-- Every terminal stops or returns: it makes no challenge. -/
theorem terminal_queryBound (raw : List F) (pc : List F × F) : QueryBound (terminalK (G := G) raw pc) 0 := by
  unfold terminalK
  rw [SumcheckVerifierTerminal.terminal_decision]
  split_ifs <;> trivial

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem residualK_queryBound (ctx : ProtocolContext) (handle : Nat)
    (k : List F × F → PIR.Process (Actions F G) (Option Bool)) (terminal : ∀ pc, QueryBound (k pc) 0) :
    ∀ (remaining : Nat) (point : List F) (claim : F),
      QueryBound (residualK ctx handle k (.round remaining point claim)) remaining := by
  intro remaining
  induction remaining with
  | zero => intro point claim; exact terminal (point, claim)
  | succ remaining ih =>
      intro point claim low high
      by_cases checked : claim = low + high
      · change QueryBound (residualK ctx handle k (.high remaining point claim low high)) (remaining + 1)
        rw [residualK_high_pass ctx handle k remaining point claim low high checked]
        exact ⟨Nat.succ_pos remaining, fun challenge => ih _ _⟩
      · change QueryBound (residualK ctx handle k (.high remaining point claim low high)) (remaining + 1)
        rw [residualK_high_fail ctx handle k remaining point claim low high checked]
        trivial

end Original

/-- The vector, the claim and the round count of a policy statement. -/
def parts {F G : Type} : artifacts.Statement F G → List F × F × Nat
  | .cons raw (.cons claim (.cons rounds .nil)) => (raw, claim, rounds)

/-- At a static maximum, a statement denotes the well-formed public statement
with its vector, claim and round count when the count is at most the maximum;
the model statement is false when its claim is not the vector's total. -/
abbrev relationAt {F G : Type} [Field F] (bound : Nat) : ModelRelation F G artifacts.publics where
  Model := PublicStatement F
  models statement model := parts statement = (model.raw, model.claim, model.count) ∧ model.count ≤ bound
  functional statement model other first second := by
    obtain ⟨first, -⟩ := first
    obtain ⟨second, -⟩ := second
    rw [first] at second
    rcases model with ⟨raw, claim, count, table, decoded⟩
    rcases other with ⟨raw', claim', count', table', decoded'⟩
    simp only [Prod.mk.injEq] at second
    obtain ⟨rawEq, claimEq, countEq⟩ := second
    subst rawEq claimEq countEq
    rw [decoded] at decoded'
    cases decoded'
    rfl
  falseModel model := model.claim ≠ model.raw.sum

/-- The model relation at the admitted original's maximum. -/
abbrev relation {F G : Type} [Field F] : ModelRelation F G artifacts.publics := relationAt maximum

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Fintype F] [SampleableType F] in
theorem original_eq (raw : List F) (claim : F) (rounds : Nat) :
    compiled.original (G := G) (.cons raw (.cons claim (.cons rounds .nil))) 0 =
      importedValidator raw claim rounds 0 :=
  rfl

/-- The certificate for every statement at exactly uniform challenges, each
charged `1 / |F|`. -/
noncomputable def family :
    CertificateFamily (G := G) compiled.context (Regime.exact F) (relation (F := F) (G := G)) where
  validator model := plainFamily 0 model
  charge _ _ := 1 / (Fintype.card F : ENNReal) + 0
  certificate := ((allCertificate (G := G) SumcheckSourceVerifier.childContext 0).balanced compiled.context id
    balanced_id).charged
  doomed model _ falseModel := .inl (plainFamily_doomed 0 model falseModel)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A vector with a table at a count up to a maximum whose tables fit the index
limit is below the index limit. -/
theorem decodes_bounded {bound : Nat} (fits : 2 ^ bound < indexLimit) {raw : List F} {count : Nat}
    (admitted : count ≤ bound) {table : Table F count} (decoded : ofList? count raw = some table) :
    raw.length < indexLimit := by
  have size := (ofList?_isSome_iff (n := count) raw).mp (by rw [decoded]; rfl)
  rw [size]
  exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) admitted) fits

omit [Fintype F] [SampleableType F] in
/-- At every static maximum whose tables fit the index limit, every statement
the contract counts as false is false in the model or denotes no model
statement. -/
theorem coversAt (bound : Nat) (fits : 2 ^ bound < indexLimit) (statement : artifacts.Statement F G)
    (falseStatement : Contract.falseStatement statement) :
    (relationAt (F := F) (G := G) bound).FalseStatement statement ∨
      (relationAt (F := F) (G := G) bound).Unmapped statement := by
  match statement, falseStatement with
  | .cons raw (.cons claim (.cons rounds .nil)), falseStatement =>
      by_cases admitted : rounds ≤ bound
      · cases decoded : ofList? rounds raw with
        | some table =>
            left
            refine ⟨⟨raw, claim, rounds, table, decoded⟩, ⟨rfl, admitted⟩, fun same => falseStatement ?_⟩
            unfold SumcheckContractBindings.PublicTruth
            have truth : decide (claim = raw.sum) = true := decide_eq_true same
            rw [SumcheckContractBindings.public_formula_equation raw claim
              (decodes_bounded fits admitted decoded), truth]
        | none =>
            right
            rintro ⟨raw', claim', count, table, decoded'⟩ ⟨same, _⟩
            simp only [parts, Prod.mk.injEq] at same
            obtain ⟨rawEq, -, countEq⟩ := same
            subst rawEq countEq
            rw [decoded'] at decoded
            cases decoded
      · right
        rintro ⟨raw', claim', count, table, decoded'⟩ ⟨same, small⟩
        simp only [parts, Prod.mk.injEq] at same
        exact admitted (same.2.2 ▸ small)

omit [Fintype F] [SampleableType F] in
/-- Every statement the contract counts as false is false in the model or
denotes no model statement. -/
theorem covers (statement : artifacts.Statement F G) (falseStatement : Contract.falseStatement statement) :
    (relation (F := F) (G := G)).FalseStatement statement ∨ (relation (F := F) (G := G)).Unmapped statement :=
  coversAt maximum (by decide) statement falseStatement

/-- The original validator of a statement that denotes no model statement is
doomed after every initial transcript. -/
theorem unmapped (statement : artifacts.Statement F G) (unmapped : (relation (F := F) (G := G)).Unmapped statement)
    (initial : History F G) :
    (family (F := F) (G := G)).certificate.doomed initial (compiled.original statement 0) := by
  match statement, unmapped with
  | .cons raw (.cons claim (.cons rounds .nil)), unmapped =>
      rw [original_eq]
      by_cases admitted : rounds ≤ maximum
      · have malformed : ofList? rounds raw = none := by
          cases decoded : ofList? rounds raw with
          | none => rfl
          | some table => exact absurd ⟨rfl, admitted⟩ (unmapped ⟨raw, claim, rounds, table, decoded⟩)
        rw [importedValidator_malformed rounds admitted raw claim 0]
        exact .inr ⟨rounds, terminalK raw,
          fun pc sized => terminal_rejects raw rounds (lt_of_le_of_lt admitted (by decide)) malformed pc sized,
          .round rounds [] claim, by simp [Sized], rfl⟩
      · have large : maximum < rounds := Nat.lt_of_not_le admitted
        rw [importedValidator_excess rounds large raw claim 0]
        exact .inl (.inr rfl)

omit [Fintype F] [SampleableType F] in
/-- Every original validator makes at most `maximum` challenges. -/
theorem original_queryBound (statement : artifacts.Statement F G) :
    QueryBound (compiled.original statement 0) maximum := by
  match statement with
  | .cons raw (.cons claim (.cons rounds .nil)) =>
      rw [original_eq]
      by_cases admitted : rounds ≤ maximum
      · rw [importedValidator_malformed rounds admitted raw claim 0]
        exact QueryBound.mono _ (residualK_queryBound SumcheckSourceVerifier.childContext 0 (terminalK raw)
          (terminal_queryBound raw) rounds [] claim) admitted
      · have large : maximum < rounds := Nat.lt_of_not_le admitted
        rw [importedValidator_excess rounds large raw claim 0]
        trivial

/-- The charge of every original validator's challenges. -/
noncomputable def cost : ENNReal := (maximum : ENNReal) * (1 / (Fintype.card F : ENNReal) + 0)

theorem costBound (statement : artifacts.Statement F G) (initial : History F G) :
    Typed.ChargedCostBound (interface (G := G) compiled.context (Regime.exact F).decode)
      (family (F := F) (G := G)).charge (compiled.original statement 0) initial (cost (F := F)) :=
  Typed.QueryBound.chargedCostBound (interface (G := G) compiled.context (Regime.exact F).decode)
    (charge := (family (F := F) (G := G)).charge) (bound := 1 / (Fintype.card F : ENNReal) + 0)
    (fun _ _ => le_rfl) _ maximum (QueryBound.typed _ _ _ maximum (original_queryBound statement)) initial

/-- Ordinary soundness evidence of the Sumcheck proof Entry at a covered endpoint
and a statement form. -/
noncomputable def soundness (endpoint : Semantics) (form : Form) (binding : BindingRequirement form)
    (lowering : LoweringRequirement artifacts compiled F G endpoint) :
    SoundnessEvidence (F := F) (G := G) artifacts endpoint form Contract.falseStatement (Regime.exact F) where
  compiled := compiled
  connection := sourceConnection
  target := .retained Contract.retained ZkcExamples.Structured.SumcheckContractBindings.publicFormula
  claimPinned := Contract.falseStatement_pinned
  handle := 0
  relation := relation
  family := family
  model statement model denotes := by
    match statement, denotes with
    | .cons raw (.cons claim (.cons rounds .nil)), ⟨same, _⟩ =>
        simp only [parts, Prod.mk.injEq] at same
        obtain ⟨rawEq, claimEq, countEq⟩ := same
        subst rawEq claimEq countEq
        rw [original_eq]
        exact importedValidator_family 0 model
  covers := covers
  unmapped := unmapped
  cost _ := cost
  costBound := costBound
  binding := binding
  lowering := lowering
  hypotheses := []

end ZkcSecurity.Examples.Subjects.Sumcheck
