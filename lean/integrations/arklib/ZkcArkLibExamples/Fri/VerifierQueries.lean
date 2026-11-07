module

public import ZkcArkLibExamples.Fri.VerifierQuery

@[expose] public section

/-! All sampled positions are checked in order against the same immutable
publications. An early reject or frame refusal skips every later position.
The successful result retains duplicates and the exact number of reads. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.VerifierQueries
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource (extension checkedUnit)
open FriCheckPositions (querySite)
open VerifierPath (Store State charged outcome)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open OracleProtocol (concrete)
open Std.Do.Internal (Ensures)

structure Publication {Aux : Type} {n r : Nat} (store : Store Aux) (source : OracleAnchor)
    (layers folds : List OracleAnchor) (word : Fin (2 ^ (n + 1)) → Octic)
    (beta shift : Octic) (rest : Layers Octic n r) where
  initial : PublishedWords.RegisteredWord (row := .field extension) store.entries store.self source word store.provider
  view : VerifierRound.Selection (charged store 1) folds 0 (logicalShiftRight (2 ^ (n + 1)) 1)
  virtual : VirtualStore.Registered (charged store 1) source (folds.get ⟨0, view.inside⟩) word beta shift
  later : VerifierPath.Registered layers folds rest (shift * shift) 0 (charged store 4)

/-- The source can learn a different cell without changing the published
words. Only the cumulative read count changes between completed queries. -/
noncomputable def Publication.withQueries {Aux : Type} {n r : Nat} {store : Store Aux} {source : OracleAnchor}
    {layers folds : List OracleAnchor} {word : Fin (2 ^ (n + 1)) → Octic} {beta shift : Octic}
    {rest : Layers Octic n r} (pub : Publication store source layers folds word beta shift rest) (q : Nat) :
    Publication {store with queries := q} source layers folds word beta shift rest where
  initial := pub.initial
  view := ⟨pub.view.fits, pub.view.inside, pub.view.visible, pub.view.table, pub.view.lookup,
    pub.view.allowed, pub.view.valid, pub.view.size⟩
  virtual := ⟨pub.virtual.older, pub.virtual.holder, pub.virtual.receivers,
    pub.virtual.live, pub.virtual.allowed, pub.virtual.located⟩
  later := pub.later.withQueries _

def samples {n s : Nat} (positions : Fin s → Fin (2 ^ (n + 1))) : List Nat :=
  List.ofFn fun i ↦ (positions i).val

def packed (xs : List Octic) : Values (FriBinding.Value model) querySite.spec.state :=
  .cons (concrete model (.vector extension) xs) .nil

def captures {n r s : Nat} (source : OracleAnchor) (layers folds : List OracleAnchor)
    (rest : Layers Octic n r) (shift : Octic) (positions : Fin s → Fin (2 ^ (n + 1))) :=
  FriCheckPositions.captured (FriPeeledQuery.captures model layers folds [] shift (2 ^ (n + 1))
    (concrete model (.vector extension) rest.coefficients) r) (samples positions) source

variable {Aux E : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

private theorem orderedQueries {n r s : Nat} (size : n + 1 ≤ 5) (rounds : r ≤ FriCheckRound.roundSite.spec.maximum)
    (count : s ≤ querySite.spec.maximum) (shift : Octic) (nonzero : shift ≠ 0)
    (positions : Fin s → Fin (2 ^ (n + 1))) (word : Fin (2 ^ (n + 1)) → Octic)
    (beta : Octic) (rest : Layers Octic n r) (fits : rest.coefficients.length < indexLimit)
    (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (source : OracleAnchor) (layers folds : List OracleAnchor)
    (ordinals : List (Fin s)) (values : List Octic) (state : State Aux) (role : state.oracle.self = 1)
    (pub : Publication state.oracle source layers folds word beta shift rest) :
    let pass := fun i ↦ Phases.firstPath RetainedDomain.root (.fold word beta rest) shift (positions i)
    Ensures (fun record ↦ outcome (ordinals.all pass) (packed (values ++ ordinals.map (fun i ↦ word (positions i))))
      (charged state.oracle ((4 * (r + 1)) * ordinals.length)) record.outcome record.state.oracle)
      ((Finite.fold (FriCheckPositions.framed context (captures source layers folds rest shift positions))
        (ordinals.map Fin.val) (packed values)).runM (VerifierPath.handler network choose) state) := by
  dsimp only
  induction ordinals generalizing values state with
  | nil =>
    apply Zkc.MonadicPostcondition.pure
    left
    simp [charged]
  | cons i remaining ih =>
    let pass := Phases.firstPath RetainedDomain.root (.fold word beta rest) shift (positions i)
    let cell := word (positions i)
    let reads := 4 * (r + 1)
    let xs := samples positions
    have length : xs.length = s := List.length_ofFn
    let ordinal : Fin xs.length := ⟨i.val, by simpa only [length] using i.isLt⟩
    have sampled : xs[ordinal.val] = (positions i).val := by simp [xs, samples, ordinal]
    have admitted : FriBoundedPositions.Admitted xs := by
      constructor
      · rw [length]
        exact count.trans_lt (by decide)
      · apply List.all_eq_true.mpr
        intro x member
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp member
        simp only [decide_eq_true_eq]
        have bound : 2 ^ (n + 1) < indexLimit := Nat.pow_lt_pow_right (by decide) (by omega)
        exact (positions j).isLt.trans bound
    let cap := FriPeeledQuery.captures model layers folds values shift (2 ^ (n + 1))
      (concrete model (.vector extension) rest.coefficients) r
    have post (current : State Aux) (same : current.oracle = state.oracle) :
        Ensures (fun record ↦ outcome pass (packed (values ++ [cell])) (charged state.oracle reads)
          record.outcome record.state.oracle)
        ((FriCheckPositions.iteration context cap xs i.val source).runM (VerifierPath.handler network choose) current) := by
      have here : Publication current.oracle source layers folds word beta shift rest := same ▸ pub
      have inside : xs[ordinal.val] < 2 ^ (n + 1) := sampled ▸ (positions i).isLt
      have checked := VerifierQuery.installed network choose context receiver xs admitted ordinal source layers folds values
        size rounds shift nonzero word beta rest fits inside current (same ▸ role) here.initial here.view here.virtual here.later
      have coordinate : (⟨xs[ordinal.val], inside⟩ : Fin (2 ^ (n + 1))) = positions i := Fin.ext sampled
      simpa only [coordinate, same, pass, packed, cell, reads, cap, ordinal] using checked
    simp only [List.map_cons, Finite.fold, PIR.runM_bind]
    refine Ensures.bind (P := fun record ↦ outcome pass (packed (values ++ [cell])) (charged state.oracle reads)
      record.outcome record.state.oracle) ?_ ?_
    · apply OraclePublication.iterationOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
        (PublishedWords.publishM choose) querySite.site i.val (FriCheckPositions.iteration context cap xs i.val source)
        (outcome pass (packed (values ++ [cell])) (charged state.oracle reads)) (fun _ ↦ Or.inr rfl) state post
    · rintro ⟨out, next, events⟩ (hit | rfl)
      · cases accepted : pass with
        | true =>
          simp only [accepted, ↓reduceIte] at hit
          rcases hit with ⟨rfl, kept⟩
          simp only [PIR.Execution.followM]
          have here : Publication next.oracle source layers folds word beta shift rest :=
            kept ▸ pub.withQueries _
          have later := ih (values ++ [cell]) next (kept ▸ role) here
          apply Zkc.MonadicPostcondition.map later
          intro result valid
          have all := accepted
          dsimp only [pass] at all
          have charge : charged next.oracle (reads * remaining.length) =
              charged state.oracle (reads * (remaining.length + 1)) := by
            rw [kept]
            simp only [charged, Nat.mul_succ, Nat.add_assoc, Nat.add_comm reads (reads * remaining.length)]
          rw [charge] at valid
          simpa only [List.all_cons, all, Bool.true_and, List.map_cons, List.length_cons,
            List.append_assoc, List.singleton_append, reads, cell] using valid
        | false =>
          simp only [accepted] at hit
          subst out
          apply Zkc.MonadicPostcondition.pure
          left
          simp only [List.all_cons, show Phases.firstPath RetainedDomain.root (.fold word beta rest) shift (positions i) = false
            from accepted, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      · exact Zkc.MonadicPostcondition.pure _ _ (Or.inr rfl)

/-- At the reached outer repeat, the actual verifier checks the complete
mathematical predicate. Its earlier admission prefix establishes the source
operands and the coefficient count; both hypotheses are kept explicit here. -/
theorem installed {n r s : Nat} (size : n + 1 ≤ 5) (rounds : r ≤ FriCheckRound.roundSite.spec.maximum)
    (count : s ≤ querySite.spec.maximum) (shift : Octic) (nonzero : shift ≠ 0)
    (positions : Fin s → Fin (2 ^ (n + 1))) (word : Fin (2 ^ (n + 1)) → Octic)
    (beta : Octic) (rest : Layers Octic n r) (fits : rest.coefficients.length < indexLimit)
    (t : Nat) (exactSize : rest.coefficients.length = 2 ^ t)
    (context : ProtocolContext) (receiver : context.roles 1 = 1) (env : Environment (FriBinding.Value model) querySite.context)
    (source : OracleAnchor) (layers folds : List OracleAnchor)
    (selected : Operands.eval env querySite.operands = .cons (concrete model .index s)
      ((packed []).append (captures source layers folds rest shift positions)))
    (state : State Aux) (role : state.oracle.self = 1)
    (pub : Publication state.oracle source layers folds word beta shift rest) :
    let published := (List.finRange s).map (fun i ↦ word (positions i))
    Ensures (fun record ↦ outcome (Phases.accepts RetainedDomain.root t (.fold word beta rest) shift positions)
      (Values.cons (concrete model .boolean true) (packed published)) (charged state.oracle (4 * (r + 1) * s))
      record.outcome record.state.oracle)
      ((querySite.region.denote (VerifierTerminalGuard.terminalMeaning context) env).runM
        (VerifierPath.handler network choose) state) := by
  dsimp only
  let ordinals := List.finRange s
  let cells := ordinals.map fun i ↦ word (positions i)
  let pass := ordinals.all fun i ↦ Phases.firstPath RetainedDomain.root (.fold word beta rest) shift (positions i)
  let finalStore := charged state.oracle (4 * (r + 1) * s)
  have agrees : Phases.accepts RetainedDomain.root t (.fold word beta rest) shift positions = pass := by
    simp [Phases.accepts, Phases.exactCoefficients, Layers.coefficients, exactSize, pass, ordinals]
  rw [agrees, FriCheckPositions.returnAfterQueries context receiver,
    FriCheckPositions.ordered context receiver env s count _ _ selected, PIR.runM_bind]
  have indices : ordinals.map Fin.val = List.range s := by
    apply List.ext_getElem <;> simp [ordinals]
  have checked := orderedQueries network choose size rounds count shift nonzero positions word beta rest fits
    context receiver source layers folds ordinals [] state role pub
  rw [indices] at checked
  simp only [List.nil_append, show ordinals.length = s from List.length_finRange] at checked
  refine Ensures.bind checked ?_
  rintro ⟨out, next, events⟩ (hit | rfl)
  · cases accepted : pass with
    | true =>
      change (if pass = true then out = .returned (packed cells) ∧ next.oracle = finalStore
        else out = .stopped .reject) at hit
      simp only [accepted, ↓reduceIte] at hit
      rcases hit with ⟨rfl, kept⟩
      simp only [PIR.Execution.followM]
      let output : Values (FriBinding.Value model) querySite.outputs := .cons (concrete model .boolean true) (packed cells)
      let good := outcome (Aux := Aux) true output finalStore
      apply Zkc.MonadicPostcondition.map
      · apply OraclePublication.markedOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
          (PublishedWords.publishM choose) (querySite.continuationMarks context) (.done output) good (fun _ ↦ Or.inr rfl)
          finalStore _ next kept
        intro current kept
        exact Zkc.MonadicPostcondition.pure _ _ (Or.inl ⟨rfl, kept⟩)
      · exact fun _ valid ↦ valid
    | false =>
      change (if pass = true then out = .returned (packed cells) ∧ next.oracle = finalStore
        else out = .stopped .reject) at hit
      simp only [accepted] at hit
      subst out
      exact Zkc.MonadicPostcondition.pure _ _ (Or.inl rfl)
  · exact Zkc.MonadicPostcondition.pure _ _ (Or.inr rfl)

end ZkcSecurity.ArkLib.Fri.VerifierQueries
