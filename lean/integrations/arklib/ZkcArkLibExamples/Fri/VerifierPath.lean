module

public import ZkcArkLibExamples.Fri.VerifierRound
public import ZkcArkLibExamples.Fri.VerifierTerminalGuard

@[expose] public section

/-! Correspondence of the reached inner Check loop with the ArkLib path.
The registry supplies the physical associations, including the immutable
words behind both same-sort sequences. The certificate contains only
data and lookup facts; no callback or path equation is an input. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.VerifierPath
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource (extension checkedUnit)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open FriCheckRound (roundSite packed advanced nextRows)
open VerifierTerminalGuard (terminalMeaning finalValues coefficientsPort rememberedPort)
open OracleProtocol (concrete)
open Std.Do.Internal (Ensures)

abbrev Store (Aux : Type) := VerifierRound.Runtime model checkedUnit.snapshot checkedUnit.domains checkedUnit.math Aux
abbrev State (Aux : Type) := VerifierRound.State model checkedUnit.snapshot checkedUnit.domains checkedUnit.math Aux

def charged {Aux : Type} (original : Store Aux) (reads : Nat) : Store Aux :=
  {original with queries := original.queries + reads}

def carried {n : Nat} (shift : Octic) (position : Fin (2 ^ n)) (expected : Octic) : FriCheckRound.State model :=
  ⟨expected, position.val, 2 ^ n, shift⟩

/-- Lookup facts for each remaining round. The selections are exactly the
positions used by the source. The next round sees the very same store with
four more reads. All positions of the word share this witness. -/
inductive Registered {Aux : Type} (layers folds : List OracleAnchor) :
    {n r : Nat} → Layers Octic n r → Octic → Nat → Store Aux → Type where
  | final {n : Nat} (cs : List Octic) (shift : Octic) (step : Nat) (store : Store Aux) :
      Registered layers folds (.final (m := n) cs) shift step store
  | fold {n r : Nat} {word : Fin (2 ^ (n + 1)) → Octic} {beta shift : Octic} {rest : Layers Octic n r}
      {step : Nat} {store : Store Aux}
      (layer : VerifierRound.Selection store layers (wrappingAdd step 1) (2 ^ (n + 1)))
      (view : VerifierRound.Selection (charged store 1) folds (wrappingAdd step 1)
        (logicalShiftRight (2 ^ (n + 1)) 1))
      (live : StoredWord.Base (d := extension) store.entries store.self
        (layers.get ⟨wrappingAdd step 1, layer.inside⟩) word store.provider)
      (virtual : VirtualStore.Registered (charged store 1)
        (layers.get ⟨wrappingAdd step 1, layer.inside⟩) (folds.get ⟨wrappingAdd step 1, view.inside⟩)
        word beta shift)
      (tail : Registered layers folds rest (shift * shift) (step + 1) (charged store 4)) :
      Registered layers folds (.fold word beta rest) shift step store

private theorem advanced_eq {n : Nat} (bound : n + 1 ≤ 5) (shift value folded : Octic)
    (position : Fin (2 ^ (n + 1))) :
    advanced (carried shift position value) folded = packed (carried (shift * shift) (lowHalf position) folded) := by
  have rows : 2 ^ (n + 1) < wordModulus := Nat.pow_lt_pow_right (by decide) (by omega)
  have half : logicalShiftRight (2 ^ (n + 1)) 1 = 2 ^ n := by
    rw [logicalShiftRight_of_lt _ (by decide), Nat.mod_eq_of_lt rows]
    simp [Nat.pow_succ]
  simp only [advanced, carried, FriCheckRound.low, nextRows, packed, lowHalf]
  rw [machine_pair_low position.val n (by omega) (position.isLt.trans rows), half]
  rfl

def outcome {Aux : Type} (passes : Bool) (returned : Values (FriBinding.Value model) roundSite.outputs)
    (finalStore : Store Aux) (out : PIR.Outcome (Values (FriBinding.Value model) roundSite.outputs)) (store : Store Aux) : Prop :=
  (if passes then out = .returned returned ∧ store = finalStore else out = .stopped .reject) ∨ out = .stopped .refused

variable {Aux E : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

abbrev handler := PublishedWords.actionM checkedUnit.oracles network choose

def fromStep (context : ProtocolContext) (env : Environment (FriBinding.Value model) roundSite.context)
    (layers folds : List OracleAnchor) (step rounds : Nat) (initial : FriCheckRound.State model) :=
  (Finite.fold (FriCheckRound.framed context layers folds) (List.range' step rounds) (packed initial)).bind
    fun out ↦ roundSite.next.denote (terminalMeaning context) (env.prepend out)

theorem checkPath (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (env : Environment (FriBinding.Value model) roundSite.context) (layers folds : List OracleAnchor)
    {n r : Nat} {transcript : Layers Octic n r} {shift : Octic} {step : Nat} {original : Store Aux}
    (installed : Registered layers folds transcript shift step original)
    (role : original.self = 1) (bound : n ≤ 5) (nonzero : shift ≠ 0)
    (cs : env coefficientsPort = concrete model (.vector extension) transcript.coefficients)
    (fits : transcript.coefficients.length < indexLimit) (pos : Fin (2 ^ n)) (expected : Octic)
    (state : State Aux) (atStore : state.oracle = original) :
    Ensures (fun record ↦ outcome (Phases.path RetainedDomain.root transcript shift pos expected)
      (.cons (env rememberedPort) .nil) (charged original (4 * r)) record.outcome record.state.oracle)
      ((fromStep context env layers folds step r (carried shift pos expected)).runM (handler network choose) state) := by
  induction installed generalizing expected state with
  | @final n coefficients shift step store =>
    change Ensures _ ((roundSite.next.denote (terminalMeaning context)
      (env.prepend (finalValues expected pos.val (2 ^ n) shift))).runM _ state)
    erw [VerifierTerminalGuard.installed context receiver env coefficients cs shift nonzero bound pos fits expected]
    apply OraclePublication.markedOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
      (PublishedWords.publishM choose) _ _ _ (fun _ ↦ Or.inr rfl) store _ state atStore
    intro current kept
    by_cases same : terminal (F := Octic) RetainedDomain.root coefficients shift n pos.val = expected
    · simp only [same, ↓reduceIte]
      apply Zkc.MonadicPostcondition.pure
      left
      simp only [Phases.path, same, decide_true, ↓reduceIte, charged, Nat.mul_zero, Nat.add_zero]
      exact ⟨True.intro, kept⟩
    · simp only [same, ↓reduceIte]
      exact Zkc.MonadicPostcondition.pure _ _ (by simp [outcome, Phases.path, same])
  | @fold n r word beta shift rest step store layer view live virtual tail ih =>
    let nextPos := lowHalf pos
    let folded := foldedValue RetainedDomain.root (word (lowIndex nextPos)) (word (highIndex nextPos))
      shift (n + 1) nextPos.val beta
    let current := carried shift pos expected
    let domain := cosetDomain shift (RetainedDomain.root (n + 1)) nonzero (RetainedDomain.order _ (by omega))
    have geometry := cosetDomain_point RetainedDomain.root shift nonzero (RetainedDomain.order (n + 1) (by omega))
    have foldEq : folded = ProximityGap.foldWord domain word 1 beta nextPos :=
      foldedValue_eq RetainedDomain.root domain shift geometry word beta nextPos
    unfold fromStep
    rw [List.range'_succ, Finite.fold, PIR.Process.bind_assoc, FriCheckRound.framed_packed, PIR.runM_bind]
    by_cases same : word pos = expected
    · let next := packed (carried (shift * shift) nextPos folded)
      let post := fun (out : PIR.Outcome (Values (FriBinding.Value model) roundSite.spec.state)) (s : Store Aux) ↦
        (out = .returned next ∧ s = charged store 4) ∨ out = .stopped .refused
      refine Ensures.bind (P := fun record ↦ post record.outcome record.state.oracle) ?_ ?_
      · apply OraclePublication.iterationOutcomes checkedUnit.oracles (PublishedWords.liftM network)
          PublishedWords.readM (PublishedWords.publishM choose) _ _ _ post (fun _ ↦ Or.inr rfl)
        intro inner kept
        have here : inner.oracle = store := kept.trans atStore
        have result := VerifierRound.matchesFold network choose context receiver step current layers folds
          inner (here ▸ role) (by omega : n + 1 ≤ 63) domain geometry word beta rfl pos.isLt
          (here ▸ layer) (here ▸ view) (here ▸ live) (here ▸ virtual) same
        apply result.weaken
        intro record ok
        rcases ok with ⟨ret, finalStore⟩ | refused
        · left
          have advance : advanced current (ProximityGap.foldWord domain word 1 beta nextPos) = next :=
            (congrArg (fun v : Octic ↦ advanced current v) foldEq.symm).trans (advanced_eq bound shift expected folded pos)
          exact ⟨ret.trans (congrArg PIR.Outcome.returned advance), here ▸ finalStore⟩
        · exact Or.inr refused
      · rintro ⟨out, inner, events⟩ valid
        rcases valid with ⟨rfl, kept⟩ | rfl
        · simp only [PIR.Execution.followM]
          apply Zkc.MonadicPostcondition.map
          · exact ih (by exact role) (by omega) (mul_ne_zero nonzero nonzero) cs fits nextPos folded inner kept
          · intro record ok
            simpa only [Phases.path, same, decide_true, Bool.true_and, charged,
              Nat.mul_succ, Nat.add_assoc, Nat.add_comm 4 (4 * r)] using ok
        · exact Zkc.MonadicPostcondition.pure _ _ (Or.inr rfl)
    · let post := fun (out : PIR.Outcome (Values (FriBinding.Value model) roundSite.spec.state)) (_ : Store Aux) ↦
        out = .stopped .reject ∨ out = .stopped .refused
      refine Ensures.bind (P := fun record ↦ post record.outcome record.state.oracle) ?_ ?_
      · apply OraclePublication.iterationOutcomes checkedUnit.oracles (PublishedWords.liftM network)
          PublishedWords.readM (PublishedWords.publishM choose) _ _ _ post (fun _ ↦ Or.inr rfl)
        intro inner kept
        have here := kept.trans atStore
        exact VerifierRound.rejectsMismatch checkedUnit.oracles network choose context receiver step current
          layers folds inner (here ▸ role) (here ▸ layer) word pos.isLt (here ▸ live) same
      · rintro ⟨out, inner, events⟩ (rfl | rfl)
        · exact Zkc.MonadicPostcondition.pure _ _ (by simp [outcome, Phases.path, same])
        · exact Zkc.MonadicPostcondition.pure _ _ (Or.inr rfl)

/-- The theorem on the actual repeat and its terminal suffix, at a reached
typed environment of the original checker. It gives the ArkLib path's
decision on any registered words, including malicious ones, and keeps the
logical store needed to start another query. -/
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (env : Environment (FriBinding.Value model) roundSite.context) (layers folds : List OracleAnchor)
    {n r : Nat} {transcript : Layers Octic n r} {shift : Octic} {original : Store Aux}
    (registry : Registered layers folds transcript shift 0 original)
    (role : original.self = 1) (bound : n ≤ 5) (rounds : r ≤ roundSite.spec.maximum)
    (nonzero : shift ≠ 0) (cs : env coefficientsPort = concrete model (.vector extension) transcript.coefficients)
    (fits : transcript.coefficients.length < indexLimit) (pos : Fin (2 ^ n)) (expected : Octic)
    (inputs : Operands.eval env roundSite.operands = .cons (concrete model .index r)
      ((packed (carried shift pos expected)).append (FriCheckRound.captures model layers folds)))
    (state : State Aux) (atStore : state.oracle = original) :
    Ensures (fun record ↦ outcome (Phases.path RetainedDomain.root transcript shift pos expected)
      (.cons (env rememberedPort) .nil) (charged original (4 * r)) record.outcome record.state.oracle)
      ((roundSite.region.denote (terminalMeaning context) env).runM (handler network choose) state) := by
  rw [roundSite.denote_region, FriCheckRound.ordered context receiver env r rounds _ layers folds inputs, List.range_eq_range']
  exact checkPath network choose context receiver env layers folds registry role bound nonzero cs fits pos expected state atStore

end ZkcSecurity.ArkLib.Fri.VerifierPath
