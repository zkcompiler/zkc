module

public import ZkcArkLibExamples.Fri.VerifierPath
public import ZkcExamples.Structured.FriPeeledQuery

@[expose] public section

/-! Each completed query of the installed unassociated verifier checks the
ArkLib first path at the position selected by the source. The remembered
value is the cell of its own initial word, including for repeated positions. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.VerifierQuery
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource (extension checkedUnit)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open VerifierPath (Store State charged carried)
open FriCheckRound (roundSite coefficientsPort rememberedPort)
open OracleProtocol (concrete)
open Std.Do.Internal (Ensures)

variable {Aux E : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

private theorem firstFold (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (xs : List Nat) (admitted : FriBoundedPositions.Admitted xs) (ordinal : Fin xs.length)
    (source : OracleAnchor) (layers folds : List OracleAnchor) (values : List Octic)
    (cs : FriBinding.Value model (.vector extension)) (count : Nat)
    {n : Nat} (size : n + 1 ≤ 5) (shift : Octic) (nonzero : shift ≠ 0)
    (word : Fin (2 ^ (n + 1)) → Octic) (beta : Octic) (inside : xs[ordinal.val] < 2 ^ (n + 1))
    (state : State Aux) (role : state.oracle.self = 1)
    (live : PublishedWords.RegisteredWord (row := .field extension) state.oracle.entries state.oracle.self source word state.oracle.provider)
    (view : VerifierRound.Selection (charged state.oracle 1) folds 0 (logicalShiftRight (2 ^ (n + 1)) 1))
    (virtual : VirtualStore.Registered (charged state.oracle 1) source (folds.get ⟨0, view.inside⟩) word beta shift) :
    let pos : Fin (2 ^ (n + 1)) := ⟨xs[ordinal.val], inside⟩
    let low := lowHalf pos
    let folded := foldedValue RetainedDomain.root (word (lowIndex low)) (word (highIndex low)) shift (n + 1) low.val beta
    let cap := FriPeeledQuery.captures model layers folds values shift (2 ^ (n + 1)) cs count
    Ensures (fun record ↦ (∃ env, record.outcome = .returned env ∧
        FriPeeledQuery.reached layers folds values (word pos) cs count (carried shift pos (word pos)) folded env ∧
        record.state.oracle = charged state.oracle 4) ∨ record.outcome = .stopped .refused)
      ((FriPeeledQuery.firstFoldBody.denote (VerifierTerminalGuard.terminalMeaning context)
        (FriCheckPositions.arguments cap xs ordinal.val source).get).runM (VerifierPath.handler network choose) state) := by
  dsimp only
  let pos : Fin (2 ^ (n + 1)) := ⟨xs[ordinal.val], inside⟩
  let low := lowHalf pos
  let domain := cosetDomain shift (RetainedDomain.root (n + 1)) nonzero (RetainedDomain.order _ (by omega))
  have geometry := cosetDomain_point RetainedDomain.root shift nonzero (RetainedDomain.order (n + 1) (by omega))
  have foldEq := foldedValue_eq RetainedDomain.root domain shift geometry word beta low
  let folded := foldedValue RetainedDomain.root (word (lowIndex low)) (word (highIndex low)) shift (n + 1) low.val beta
  let property := fun (out : PIR.Outcome (Values (FriBinding.Value model) roundSite.context)) (store : Store Aux) ↦
    (∃ env, out = .returned env ∧ FriPeeledQuery.reached layers folds values (word pos) cs count
      (carried shift pos (word pos)) folded env ∧ store = charged state.oracle 4) ∨ out = .stopped .refused
  let afterRead := charged state.oracle 1
  let location := FriCheckPositions.initialSite
  let head := FriPeeledQuery.installed context receiver xs admitted ordinal source layers folds values shift
    (2 ^ (n + 1)) cs count
  apply OraclePublication.markedReplyOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
    (PublishedWords.publishM choose) head location (.cons (concrete model (.field extension) (word pos)) .nil)
    state.oracle afterRead (fun current ↦ [.logical (.query (Phases.publishedRequest extension source pos.val
      {location with invocation := current.frame.invocation} []))]) _ property (fun _ ↦ Or.inr rfl) _ state rfl
  · intro current kept
    have base : PublishedWords.RegisteredWord (row := .field extension) current.oracle.entries current.oracle.self source word current.oracle.provider :=
      kept ▸ live
    have atSelf : 1 = current.oracle.self := kept ▸ role.symm
    have law := base.sourceQuery checkedUnit.oracles network choose current pos 1 1 context.roles location
      atSelf (receiver.trans atSelf)
    simp only [kept] at law
    with_unfolding_all exact law
  · intro read checks current atStore
    apply VerifierRound.selectionOutcomes checkedUnit.oracles network choose context receiver afterRead role folds 0
      (logicalShiftRight (2 ^ (n + 1)) 1) (FriPeeledQuery.site 1) (FriPeeledQuery.site 2) view (checks (word pos))
      property (fun _ ↦ Or.inr rfl) _ current atStore
    intro process head current atStore
    have coordinate := VerifierRound.lowCoordinate (by omega : n + 1 ≤ 63) (carried shift pos (word pos)) rfl inside
    change OracleProtocol.AtMarkedCall (OracleProtocol.tableQuery model (.field extension) none _
      (FriCheckRound.low (carried shift pos (word pos))) 1 1 context.roles (FriPeeledQuery.site 3)) _ _ at head
    rw [coordinate] at head
    apply VerifierRound.virtualOutcomes network choose context receiver (by omega) domain shift geometry word beta low
      source (folds.get ⟨0, view.inside⟩) (FriPeeledQuery.site 3) afterRead role virtual head property (fun _ ↦ Or.inr rfl)
      _ current atStore
    intro query finished current kept
    obtain ⟨env, ⟨marks, eqn⟩, args⟩ := finished (ProximityGap.foldWord domain word 1 beta low)
    rw [eqn]
    apply OraclePublication.markedOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
      (PublishedWords.publishM choose) marks (.done env) property (fun _ ↦ Or.inr rfl) _ _ current kept
    intro s finalStore
    apply Zkc.MonadicPostcondition.pure
    refine Or.inl ⟨env, rfl, ?_, finalStore⟩
    rw [show folded = _ from foldEq]
    exact args

/-- This is the whole admitted callback at the current query ordinal. Only
immutable word and view associations and source input bounds are premises.
A valid return appends exactly one cell and accounts for all round reads.
An invalid path cannot return even if earlier marks refuse execution. -/
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (xs : List Nat) (admitted : FriBoundedPositions.Admitted xs) (ordinal : Fin xs.length)
    (source : OracleAnchor) (layers folds : List OracleAnchor) (values : List Octic)
    {n r : Nat} (size : n + 1 ≤ 5) (rounds : r ≤ roundSite.spec.maximum)
    (shift : Octic) (nonzero : shift ≠ 0) (word : Fin (2 ^ (n + 1)) → Octic) (beta : Octic)
    (rest : Layers Octic n r) (fits : rest.coefficients.length < indexLimit)
    (inside : xs[ordinal.val] < 2 ^ (n + 1)) (state : State Aux) (role : state.oracle.self = 1)
    (live : PublishedWords.RegisteredWord (row := .field extension) state.oracle.entries state.oracle.self source word state.oracle.provider)
    (view : VerifierRound.Selection (charged state.oracle 1) folds 0 (logicalShiftRight (2 ^ (n + 1)) 1))
    (virtual : VirtualStore.Registered (charged state.oracle 1) source (folds.get ⟨0, view.inside⟩) word beta shift)
    (registry : VerifierPath.Registered layers folds rest (shift * shift) 0 (charged state.oracle 4)) :
    let pos : Fin (2 ^ (n + 1)) := ⟨xs[ordinal.val], inside⟩
    let cap := FriPeeledQuery.captures model layers folds values shift (2 ^ (n + 1))
      (concrete model (.vector extension) rest.coefficients) r
    Ensures (fun record ↦ VerifierPath.outcome (Phases.firstPath RetainedDomain.root (.fold word beta rest) shift pos)
      (.cons (concrete model (.vector extension) (values ++ [word pos])) .nil)
      (charged state.oracle (4 * (r + 1))) record.outcome record.state.oracle)
      ((FriCheckPositions.iteration context cap xs ordinal.val source).runM (VerifierPath.handler network choose) state) := by
  dsimp only
  let pos : Fin (2 ^ (n + 1)) := ⟨xs[ordinal.val], inside⟩
  let low := lowHalf pos
  let folded := foldedValue RetainedDomain.root (word (lowIndex low)) (word (highIndex low)) shift (n + 1) low.val beta
  unfold FriCheckPositions.iteration
  erw [FriCheckRound.insideQuery.denote_prefix _ FriCheckRound.innerOnSpine _,
    FriPeeledQuery.firstFoldBody_exact, PIR.runM_bind]
  refine Ensures.bind (firstFold network choose context receiver xs admitted ordinal source layers folds values _
    r size shift nonzero word beta inside state role live view virtual) ?_
  rintro ⟨out, current, events⟩ (⟨env, rfl, ⟨inputs, coefficients, remembered⟩, same⟩ | rfl)
  · simp only [PIR.Execution.followM]
    have equation := VerifierPath.advanced_eq size shift (word pos) folded pos
    have args := inputs.trans (congrArg (fun v ↦ Values.cons (concrete model .index r)
      (v.append (FriCheckRound.captures model layers folds))) equation)
    have checked := VerifierPath.installed network choose context receiver env.get layers folds registry role (by omega)
      rounds (mul_ne_zero nonzero nonzero) coefficients fits low folded args current same
    have total : charged (charged state.oracle 4) (4 * r) = charged state.oracle (4 * (r + 1)) := by
      simp only [charged, Nat.mul_succ, Nat.add_assoc, Nat.add_comm 4 (4 * r)]
    rw [remembered, total] at checked
    exact Zkc.MonadicPostcondition.map checked _ (fun _ valid ↦ valid)
  · exact Zkc.MonadicPostcondition.pure _ _ (Or.inr rfl)

end ZkcSecurity.ArkLib.Fri.VerifierQuery
