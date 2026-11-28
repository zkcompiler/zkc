module

public import Zkc.Core.Scheme.Proof.Completeness

@[expose] public section

/-!
Completeness with abort-and-retry (`deploy_complete_retry` and `deploy_complete_retry_nonaborting`)
for non-interactive `.derived` streaming deployments whose prover retries a declared attempt site
(`declaration.retry = some (bound, retrySite)`).

## Architecture
1. **Handler rollback & retry mechanics**:
   - `stack2_again_restore`: `[conP, layP].again` restores the exact transcript state and proof
     buffer recorded at `.begin retrySite` via `restoreAgain`.
   - `attempts_rollback_then_succeed`: if attempts `0 .. k - 1` (`k < bound`) halt inside
     `Handler.inside` with `why.isAbort = true` and attempt `k` returns `(outP, sFinal)`, then
     `attempts` rolls back cleanly on every abort and returns `(outP, sFinal)` with zero trace of
     attempts `0 .. k - 1`.
   - `handler_run_retry_eq_none`: when a role process never emits `.begin`/`.settle` at `retrySite`
     (`ROp.NotMarkAt retrySite`), running under `retryOf M (some (bound, retrySite))` is
     propositionally identical to running under `retryOf M none`.
2. **Three-phase retry automaton (`RetryPhase`: `.before | .inside | .after`)**:
   - Captures in one structural invariant (`Program.RetryWellFormed`):
     - no aborts outside `retrySite` (from `abortsOutsideTarget = []` and `Defs.fnsNoAbort = true`),
     - no nested or repeated `retrySite` (from `Shape.retryAtMostOnce = true`),
     - prover private coins inside `retrySite` lie in `insideCoins`, while outside private coins
       and service requests lie outside `insideCoins` (from `Shape.attemptCoinsExclusive = true`).
3. **Coupled simulation across aborting attempts and the succeeding attempt**:
   - Before `.begin retrySite`: steps prover, verifier, and protocol in lockstep (all `attemptSrc j`
     agree with `source` on non-heard events outside `retrySite`).
   - At `.begin retrySite`:
     - for every `j < k`, `simulate_prover_abort_inside` proves `Handler.inside ... j` halts with
       `((true, why), sAbort)` where `why.isAbort = true` (using `proj_noAbort_contradicts_abort`
       to rule out reaching `.settle retrySite` before aborting);
     - for attempt `k < bound`, `simulate_retry_coupled_inside` steps prover (with `markOwn`
       shifting prover private coins by `.attempt retrySite.key k`) in lockstep with verifier
       until `.settle retrySite`, then hands off directly to `simulate_derived_gen` from
       `Zkc.Core.Scheme.Proof.Completeness`.
-/

namespace Zkc.Core

open LayerBuild

/-! ## Section 1: Generic `Alone` / `Handler` / `attempts` rollback & obliviousness lemmas -/

section RetryMechanics

variable {V : Vocabulary} (M : Model V)

theorem alone_recover_done {source : Source M} {r : Role} {H H' A : Type}
    {p : Process (RSig M) H A} {f : H → Process (RSig M) H' A}
    {a : A} {rec : List (Happened M)}
    (hp : Alone M source r p rec (.returned a)) :
    Alone M source r (p.recover f) rec (.returned a) := by
  generalize hEnd : Ending.returned a = end₁ at hp
  induction hp with
  | done => cases hEnd; exact .done
  | halt => cases hEnd
  | waits => cases hEnd
  | give _ ih => exact .give (ih hEnd)
  | own hsrc _ ih => exact .own hsrc (ih hEnd)
  | hear hsrc _ ih => exact .hear hsrc (ih hEnd)
  | begin _ ih => exact .begin (ih hEnd)
  | settle _ ih => exact .settle (ih hEnd)

theorem alone_recover_halt {source : Source M} {r : Role} {H H' A : Type}
    {p : Process (RSig M) H A} {f : H → Process (RSig M) H' A}
    {h : H} {rec₁ rec₂ : List (Happened M)} {e : Ending A H'}
    (hp : Alone M source r p rec₁ (.stopped h))
    (hf : Alone M source r (f h) rec₂ e) :
    Alone M source r (p.recover f) (rec₁ ++ rec₂) e := by
  generalize hEnd : Ending.stopped h = end₁ at hp
  induction hp with
  | done => cases hEnd
  | halt => cases hEnd; exact hf
  | waits => cases hEnd
  | give _ ih => exact .give (ih hEnd)
  | own hsrc _ ih => exact .own hsrc (ih hEnd)
  | hear hsrc _ ih => exact .hear hsrc (ih hEnd)
  | begin _ ih => exact .begin (ih hEnd)
  | settle _ ih => exact .settle (ih hEnd)

/-- A 2-layer stack `[l₁, l₂]` whose layers both use `restoreAgain` rolls back to the exact entry
state on every retry attempt. -/
theorem stack2_again_restore {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (l₁ l₂ : Layer V hs r ins)
    (hA₁ : l₁.again = restoreAgain l₁.state)
    (hA₂ : l₂.again = restoreAgain l₂.state)
    (i : Nat) (e₁ t₁ : M.Val l₁.state) (e₂ t₂ : M.Val l₂.state) :
    (Stack.handler M fnTable rTable [l₁, l₂]).again i
        (.cons e₁ (.cons e₂ .nil)) (.cons t₁ (.cons t₂ .nil)) =
      .ok (.cons e₁ (.cons e₂ .nil)) := by
  have h1 : l₁.again.denote (localSem M hs.fns fnTable) []
      (Env.positional (.cons i (.cons e₁ (.cons t₁ .nil)))) = .done (.cons e₁ .nil) := by
    rw [hA₁, restoreAgain_denote]
  have h2 : l₂.again.denote (localSem M hs.fns fnTable) []
      (Env.positional (.cons i (.cons e₂ (.cons t₂ .nil)))) = .done (.cons e₂ .nil) := by
    rw [hA₂, restoreAgain_denote]
  have h2' : (Stack.handler M fnTable rTable [l₂]).again i (.cons e₂ .nil) (.cons t₂ .nil) =
      .ok (.cons e₂ .nil) := by
    change (((Layer.handler M fnTable rTable l₂).over
      (Stack.handler M fnTable rTable [])).again i (e₂, .nil) (t₂, .nil)).map
        (fun p => HList.cons p.1 p.2) = _
    dsimp only [Handler.over, Layer.handler]
    rw [h2]; rfl
  change (((Layer.handler M fnTable rTable l₁).over
    (Stack.handler M fnTable rTable [l₂])).again i (e₁, .cons e₂ .nil) (t₁, .cons t₂ .nil)).map
      (fun p => HList.cons p.1 p.2) = _
  dsimp only [Handler.over, Layer.handler]
  rw [h1, h2']; rfl

/-- If attempts `0 .. k - 1` (`k < n`) halt inside the attempt body with `why.isAbort = true` and
attempt `k` returns `out`, then `attempts` rolls back cleanly via `again` and returns `out`. -/
theorem attempts_rollback_then_succeed {σ A : Type} {source : Source M} {r : Role}
    (exhausted : Stop) (again : Nat → σ → σ → Except Stop σ)
    (body : Nat → σ → Process (RSig M) ((Bool × Stop) × σ) (A × σ))
    (entry : σ)
    (hRestore : ∀ i sAbort, again i entry sAbort = .ok entry) :
    ∀ (k n i : Nat) (out : A × σ),
      k < n →
      (∀ j, j < k → ∃ why sAbort rec,
        why.isAbort = true ∧
        Alone M source r (body (i + j) entry) rec (.stopped ((true, why), sAbort))) →
      (∃ rec, Alone M source r (body (i + k) entry) rec (.returned out)) →
      ∃ recAll, Alone M source r (attempts Stop.isAbort exhausted again body entry n i entry)
        recAll (.returned out)
  | 0, n, i, out, hLt, _, ⟨rec, hOk⟩ => by
      cases n with
      | zero => exact absurd hLt (Nat.not_lt_zero _)
      | succ m =>
          refine ⟨rec, ?_⟩
          rw [attempts]
          exact alone_recover_done M hOk
  | k + 1, n, i, out, hLt, hAborts, hOk => by
      cases n with
      | zero => exact absurd hLt (Nat.not_lt_zero _)
      | succ m =>
          have hLtM : k < m := Nat.lt_of_succ_lt_succ hLt
          cases m with
          | zero => exact absurd hLtM (Nat.not_lt_zero _)
          | succ m' =>
              obtain ⟨why0, sAbort0, rec0, hIsAb0, hAl0⟩ := hAborts 0 (Nat.zero_lt_succ k)
              have hAborts' : ∀ j, j < k → ∃ why sAbort rec,
                  why.isAbort = true ∧
                  Alone M source r (body ((i + 1) + j) entry) rec (.stopped ((true, why), sAbort)) := by
                intro j hj
                have h := hAborts (j + 1) (Nat.succ_lt_succ hj)
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
              have hOk' : ∃ rec, Alone M source r (body ((i + 1) + k) entry) rec (.returned out) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hOk
              obtain ⟨recRest, hAlRest⟩ :=
                attempts_rollback_then_succeed exhausted again body entry hRestore
                  k (m' + 1) (i + 1) out hLtM hAborts' hOk'
              refine ⟨rec0 ++ recRest, ?_⟩
              rw [attempts]
              refine alone_recover_halt M hAl0 ?_
              simp only [Bool.true_and, hIsAb0, ↓reduceIte, hRestore]
              exact hAlRest

/-- Effect predicate excluding `.begin` and `.settle` at `target`. -/
def ROp.NotMarkAt (target : Site) : ROp M → Prop
  | .begin at_ => at_.site ≠ target
  | .settle at_ => at_.site ≠ target
  | _ => True

/-- Verifier / post-settle obliviousness: when a role process never emits `.begin` or `.settle` at
`target`, running under `retryOf M (some (bound, target))` is identically equal to running under
`retryOf M none`. -/
theorem handler_run_retry_eq_none {σ A : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) :
    ∀ {p : Program M A} (s : σ),
      p.SafeWith M (fun _ _ => True) (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True) →
      h.run (retryOf M (some (bound, target))) p s = h.run (retryOf M none) p s
  | .done _, _, _ => rfl
  | .halt _, _, _ => rfl
  | .call op k, s, ⟨hOp, hk⟩ => by
      have hBegNone : (retryOf M (some (bound, target))).begins op = none := by
        cases op with
        | «begin» at_ =>
            dsimp only [retryOf]
            exact ite_eq_right hOp
        | _ => rfl
      rw [Handler.run, Handler.run, hBegNone]
      dsimp only [retryOf]
      congr 1; funext out
      exact handler_run_retry_eq_none h bound target out.2 (hk out.1 trivial)

/-! ### Stepping lemmas for `Handler.run` (with retry) and `Handler.inside` -/

theorem handler_run_retry_clause_done {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) (op : ROp M)
    (hNotBeg : (retryOf M (some (bound, target))).begins op = none)
    (k : (RSig M).Reply op → Program M B) (s s' : σ) (reply : (RSig M).Reply op)
    (hStep : h.clause op s = .done (reply, s')) :
    h.run (retryOf M (some (bound, target))) (.call op k) s =
      h.run (retryOf M (some (bound, target))) (k reply) s' := by
  rw [Handler.run, hNotBeg, hStep]; rfl

theorem handler_run_retry_own {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site)
    (gkind : GivenKind V) (hearers : List Role) (at_ : Occurrence)
    (gIns : List V.Ty) (payload : HList M.Val gIns) (τ : V.Ty)
    (k : M.Val τ → Program M B) (s : σ)
    (hPass : h.clause (.own gkind hearers at_ gIns payload τ) s =
      .call (.own gkind hearers at_ gIns payload τ) fun w => .done (w, s)) :
    h.run (retryOf M (some (bound, target))) (.call (.own gkind hearers at_ gIns payload τ) k) s =
      .call (.own gkind hearers at_ gIns payload τ) fun w =>
        h.run (retryOf M (some (bound, target))) (k w) s := by
  rw [Handler.run]; dsimp only [retryOf]; rw [hPass]; rfl

theorem handler_run_retry_begin_other {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) (at_ : Occurrence) (hNe : at_.site ≠ target)
    (k : Nat → Program M B) (s : σ)
    (hPass : h.clause (.begin at_) s = .call (.begin at_) fun n => .done (n, s)) :
    h.run (retryOf M (some (bound, target))) (.call (.begin at_) k) s =
      .call (.begin at_) fun n => h.run (retryOf M (some (bound, target))) (k n) s := by
  have hBeg : (retryOf M (some (bound, target))).begins (.begin at_) = none := by
    dsimp only [retryOf]; exact ite_eq_right hNe
  rw [Handler.run, hBeg, hPass]; rfl

theorem handler_run_retry_begin_target {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) (at_ : Occurrence) (hEq : at_.site = target)
    (k : Nat → Program M B) (s : σ) :
    h.run (retryOf M (some (bound, target))) (.call (.begin at_) k) s =
      attempts Stop.isAbort (.declared .exhausted at_) h.again
        (fun i s' => Handler.inside h (retryOf M (some (bound, target))) i (k i) s') s bound 0 s := by
  have hBeg : (retryOf M (some (bound, target))).begins (.begin at_) =
      some (.declared .exhausted at_, fun i => i) := by
    dsimp only [retryOf]; exact ite_eq_left hEq
  rw [Handler.run, hBeg]; rfl

theorem handler_run_retry_settle {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) (at_ : Occurrence)
    (k : Unit → Program M B) (s : σ)
    (hPass : h.clause (.settle at_) s = .call (.settle at_) fun u => .done (u, s)) :
    h.run (retryOf M (some (bound, target))) (.call (.settle at_) k) s =
      .call (.settle at_) fun u => h.run (retryOf M (some (bound, target))) (k u) s := by
  rw [Handler.run]; dsimp only [retryOf]; rw [hPass]; rfl

theorem handler_inside_clause_done {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) (i : Nat) (op : ROp M)
    (hNotEnd : (retryOf M (some (bound, target))).ends op = none)
    (k : (RSig M).Reply op → Program M B) (s s' : σ) (reply : (RSig M).Reply op)
    (hStep : h.clause op s = .done (reply, s')) :
    Handler.inside h (retryOf M (some (bound, target))) i (.call op k) s =
      Handler.inside h (retryOf M (some (bound, target))) i (k reply) s' := by
  rw [Handler.inside, hNotEnd, hStep]; rfl

theorem handler_inside_pass_private_coin {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) (i : Nat)
    (law : V.LawKey) (at_ : Occurrence) (gIns : List V.Ty) (payload : HList M.Val gIns) (τ : V.Ty)
    (k : M.Val τ → Program M B) (s : σ)
    (hPass : h.clause (.own (.coin law) [] at_ gIns payload τ) s =
      .call (.own (.coin law) [] at_ gIns payload τ) fun v => .done (v, s)) :
    Handler.inside h (retryOf M (some (bound, target))) i
        (.call (.own (.coin law) [] at_ gIns payload τ) k) s =
      .call (.own (.coin law) [] ⟨.attempt target.key i :: at_.path, at_.key⟩ gIns payload τ)
        fun v => Handler.inside h (retryOf M (some (bound, target))) i (k v) s := by
  rw [Handler.inside]; dsimp only [retryOf]; rw [hPass]; rfl

theorem handler_inside_pass_request {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) (i : Nat)
    (svc : Key) (hearers : List Role) (at_ : Occurrence)
    (gIns : List V.Ty) (payload : HList M.Val gIns) (τ : V.Ty)
    (k : M.Val τ → Program M B) (s : σ)
    (hPass : h.clause (.own (.request svc) hearers at_ gIns payload τ) s =
      .call (.own (.request svc) hearers at_ gIns payload τ) fun v => .done (v, s)) :
    Handler.inside h (retryOf M (some (bound, target))) i
        (.call (.own (.request svc) hearers at_ gIns payload τ) k) s =
      .call (.own (.request svc) hearers at_ gIns payload τ)
        fun v => Handler.inside h (retryOf M (some (bound, target))) i (k v) s := by
  rw [Handler.inside]; dsimp only [retryOf]; rw [hPass]; rfl

theorem handler_inside_pass_begin {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) (i : Nat) (at_ : Occurrence)
    (k : Nat → Program M B) (s : σ)
    (hPass : h.clause (.begin at_) s = .call (.begin at_) fun n => .done (n, s)) :
    Handler.inside h (retryOf M (some (bound, target))) i (.call (.begin at_) k) s =
      .call (.begin at_) fun n => Handler.inside h (retryOf M (some (bound, target))) i (k n) s := by
  rw [Handler.inside]; dsimp only [retryOf]; rw [hPass]; rfl

theorem handler_inside_pass_settle_other {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) (i : Nat) (at_ : Occurrence) (hNe : at_.site ≠ target)
    (k : Unit → Program M B) (s : σ)
    (hPass : h.clause (.settle at_) s = .call (.settle at_) fun u => .done (u, s)) :
    Handler.inside h (retryOf M (some (bound, target))) i (.call (.settle at_) k) s =
      .call (.settle at_) fun u => Handler.inside h (retryOf M (some (bound, target))) i (k u) s := by
  have hEnd : (retryOf M (some (bound, target))).ends (.settle at_) = none := by
    dsimp only [retryOf]; exact ite_eq_right hNe
  rw [Handler.inside, hEnd, hPass]; rfl

theorem handler_inside_settle_target {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (bound : Nat) (target : Site) (i : Nat) (at_ : Occurrence) (hEq : at_.site = target)
    (k : Unit → Program M B) (s : σ) :
    Handler.inside h (retryOf M (some (bound, target))) i (.call (.settle at_) k) s =
      (Handler.run h (retryOf M (some (bound, target))) (k ()) s).mapHalt
        fun stop => ((false, stop.1), stop.2) := by
  have hEnd : (retryOf M (some (bound, target))).ends (.settle at_) = some () := by
    dsimp only [retryOf]; exact ite_eq_left hEq
  rw [Handler.inside, hEnd]

end RetryMechanics

/-! ## Section 2: Decidable shape & local-function predicates for retry completeness -/

section ShapePredicates

variable {V : Vocabulary}

mutual
  /-- Whether role `r` participates in any `.attempt` at `target` in the shape. -/
  def Shape.hasAttemptFor (r : Role) (target : Site) (through : List Key) : Shape V → Bool
    | .nil => false
    | .event _ _ _ rest => Shape.hasAttemptFor r target through rest
    | .choice _ _ arms rest =>
        Shapes.hasAttemptFor r target through arms || Shape.hasAttemptFor r target through rest
    | .loop _ _ body rest =>
        Shape.hasAttemptFor r target through body || Shape.hasAttemptFor r target through rest
    | .apply key _ roles inner rest =>
        let innerHas :=
          match (List.range roles.length).filter (fun j => roles.getD j j == r) with
          | [j] => Shape.hasAttemptFor j target (through ++ [key]) inner
          | _ => false
        innerHas || Shape.hasAttemptFor r target through rest
    | .block _ _ body rest =>
        Shape.hasAttemptFor r target through body || Shape.hasAttemptFor r target through rest
    | .guard _ _ _ rest => Shape.hasAttemptFor r target through rest
    | .attempt key who body rest =>
        (decide (⟨through, key⟩ = target) && decide (r ∈ who)) ||
        Shape.hasAttemptFor r target through body ||
        Shape.hasAttemptFor r target through rest

  def Shapes.hasAttemptFor (r : Role) (target : Site) (through : List Key) : Shapes V → Bool
    | .nil => false
    | .cons arm rest =>
        Shape.hasAttemptFor r target through arm || Shapes.hasAttemptFor r target through rest
end

mutual
  /-- Whether every `.attempt` at `target` in the shape is owned by `r` (`r ∈ who`). -/
  def Shape.retryOwnedBy (r : Role) (target : Site) (through : List Key) : Shape V → Bool
    | .nil => true
    | .event _ _ _ rest => Shape.retryOwnedBy r target through rest
    | .choice _ _ arms rest =>
        Shapes.retryOwnedBy r target through arms && Shape.retryOwnedBy r target through rest
    | .loop _ _ body rest =>
        Shape.retryOwnedBy r target through body && Shape.retryOwnedBy r target through rest
    | .apply key _ roles inner rest =>
        let innerOk :=
          match (List.range roles.length).filter (fun j => roles.getD j j == r) with
          | [j] => Shape.retryOwnedBy j target (through ++ [key]) inner
          | _ => true
        innerOk && Shape.retryOwnedBy r target through rest
    | .block _ _ body rest =>
        Shape.retryOwnedBy r target through body && Shape.retryOwnedBy r target through rest
    | .guard _ _ _ rest => Shape.retryOwnedBy r target through rest
    | .attempt key who body rest =>
        (!decide (⟨through, key⟩ = target) || decide (r ∈ who)) &&
        Shape.retryOwnedBy r target through body &&
        Shape.retryOwnedBy r target through rest

  def Shapes.retryOwnedBy (r : Role) (target : Site) (through : List Key) : Shapes V → Bool
    | .nil => true
    | .cons arm rest =>
        Shape.retryOwnedBy r target through arm && Shapes.retryOwnedBy r target through rest
end

mutual
  /-- Whether `target` executes at most once along any path of the shape: it does not appear inside
  a `.loop`, does not nest inside itself, and does not reappear after it settles. -/
  def Shape.retryAtMostOnce (target : Site) (through : List Key) : Shape V → Bool
    | .nil => true
    | .event _ _ _ rest => Shape.retryAtMostOnce target through rest
    | .choice _ _ arms rest =>
        Shapes.retryAtMostOnce target through arms &&
        Shape.retryAtMostOnce target through rest &&
        (!decide (target ∈ Shapes.attemptSites through arms) ||
          !decide (target ∈ Shape.attemptSites through rest))
    | .loop _ _ body rest =>
        !decide (target ∈ Shape.attemptSites through body) &&
        Shape.retryAtMostOnce target through rest
    | .apply key _ _ inner rest =>
        Shape.retryAtMostOnce target (through ++ [key]) inner &&
        Shape.retryAtMostOnce target through rest &&
        (!decide (target ∈ Shape.attemptSites (through ++ [key]) inner) ||
          !decide (target ∈ Shape.attemptSites through rest))
    | .block _ _ body rest =>
        Shape.retryAtMostOnce target through body &&
        Shape.retryAtMostOnce target through rest &&
        (!decide (target ∈ Shape.attemptSites through body) ||
          !decide (target ∈ Shape.attemptSites through rest))
    | .guard _ _ _ rest => Shape.retryAtMostOnce target through rest
    | .attempt key _ body rest =>
        if ⟨through, key⟩ = target then
          !decide (target ∈ Shape.attemptSites through body) &&
          !decide (target ∈ Shape.attemptSites through rest)
        else
          Shape.retryAtMostOnce target through body &&
          Shape.retryAtMostOnce target through rest &&
          (!decide (target ∈ Shape.attemptSites through body) ||
            !decide (target ∈ Shape.attemptSites through rest))

  def Shapes.retryAtMostOnce (target : Site) (through : List Key) : Shapes V → Bool
    | .nil => true
    | .cons arm rest =>
        Shape.retryAtMostOnce target through arm && Shapes.retryAtMostOnce target through rest
end

mutual
  /-- Sites of prover private coins (`.given (.coin _) prover []`) occurring inside `target`. -/
  def Shape.attemptPrivateCoins (prover : Role) (target : Site) (through : List Key)
      (inside : Bool) : Shape V → List Site
    | .nil => []
    | .event key cls _ rest =>
        let here :=
          match cls with
          | .given (.coin _) owner [] =>
              if inside && decide (owner = prover) then [⟨through, key⟩] else []
          | _ => []
        here ++ Shape.attemptPrivateCoins prover target through inside rest
    | .choice _ _ arms rest =>
        Shapes.attemptPrivateCoins prover target through inside arms ++
          Shape.attemptPrivateCoins prover target through inside rest
    | .loop _ _ body rest =>
        Shape.attemptPrivateCoins prover target through inside body ++
          Shape.attemptPrivateCoins prover target through inside rest
    | .apply key _ roles inner rest =>
        let innerSites :=
          match (List.range roles.length).filter (fun j => roles.getD j j == prover) with
          | [j] => Shape.attemptPrivateCoins j target (through ++ [key]) inside inner
          | _ => []
        innerSites ++ Shape.attemptPrivateCoins prover target through inside rest
    | .block _ _ body rest =>
        Shape.attemptPrivateCoins prover target through inside body ++
          Shape.attemptPrivateCoins prover target through inside rest
    | .guard _ _ _ rest => Shape.attemptPrivateCoins prover target through inside rest
    | .attempt key _ body rest =>
        let insideBody := inside || decide (⟨through, key⟩ = target)
        Shape.attemptPrivateCoins prover target through insideBody body ++
          Shape.attemptPrivateCoins prover target through inside rest

  def Shapes.attemptPrivateCoins (prover : Role) (target : Site) (through : List Key)
      (inside : Bool) : Shapes V → List Site
    | .nil => []
    | .cons arm rest =>
        Shape.attemptPrivateCoins prover target through inside arm ++
          Shapes.attemptPrivateCoins prover target through inside rest
end

mutual
  /-- Sites of non-heard events that are NOT prover private coins inside `target`: outside prover
  private coins, non-prover private coins, and all service requests. -/
  def Shape.nonAttemptCoinSites (prover : Role) (target : Site) (through : List Key)
      (inside : Bool) : Shape V → List Site
    | .nil => []
    | .event key cls _ rest =>
        let here :=
          match cls with
          | .given (.coin _) owner [] =>
              if !(inside && decide (owner = prover)) then [⟨through, key⟩] else []
          | .given (.request _) _ _ => [⟨through, key⟩]
          | _ => []
        here ++ Shape.nonAttemptCoinSites prover target through inside rest
    | .choice _ _ arms rest =>
        Shapes.nonAttemptCoinSites prover target through inside arms ++
          Shape.nonAttemptCoinSites prover target through inside rest
    | .loop _ _ body rest =>
        Shape.nonAttemptCoinSites prover target through inside body ++
          Shape.nonAttemptCoinSites prover target through inside rest
    | .apply key _ roles inner rest =>
        let innerSites :=
          match (List.range roles.length).filter (fun j => roles.getD j j == prover) with
          | [j] => Shape.nonAttemptCoinSites j target (through ++ [key]) inside inner
          | _ => Shape.nonAttemptCoinSites roles.length target (through ++ [key]) false inner
        innerSites ++ Shape.nonAttemptCoinSites prover target through inside rest
    | .block _ _ body rest =>
        Shape.nonAttemptCoinSites prover target through inside body ++
          Shape.nonAttemptCoinSites prover target through inside rest
    | .guard _ _ _ rest => Shape.nonAttemptCoinSites prover target through inside rest
    | .attempt key _ body rest =>
        let insideBody := inside || decide (⟨through, key⟩ = target)
        Shape.nonAttemptCoinSites prover target through insideBody body ++
          Shape.nonAttemptCoinSites prover target through inside rest

  def Shapes.nonAttemptCoinSites (prover : Role) (target : Site) (through : List Key)
      (inside : Bool) : Shapes V → List Site
    | .nil => []
    | .cons arm rest =>
        Shape.nonAttemptCoinSites prover target through inside arm ++
          Shapes.nonAttemptCoinSites prover target through inside rest
end

/-- Decidable check that every prover private coin site inside `target` is disjoint from every
non-heard event outside `target`, every non-prover private coin, every heard coin, and every
service request. -/
def Shape.attemptCoinsExclusive (prover : Role) (target : Site) (s : Shape V) : Bool :=
  let inside := s.attemptPrivateCoins prover target [] false
  let others := s.nonAttemptCoinSites prover target [] false
  let evOthers := (s.events [] id).filterMap fun e =>
    match e.cls with
    | .given (.coin _) owner [] => if owner != prover then some e.site else none
    | .given (.coin _) _ (_ :: _) => some e.site
    | .given (.request _) _ _ => some e.site
    | _ => none
  inside.all fun site => !decide (site ∈ others) && !decide (site ∈ evOthers)

mutual
  /-- Whether a local term contains no `.guard` with reason `.abort`. -/
  def Term.localNoAbort {fns : List (FnHeader V)} :
      {Γ : Ctx V.Ty} → {outs : List V.Ty} → Term (localDialect V fns) Γ outs → Bool
    | _, _, .ret _ => true
    | _, _, .op _ _ _ _ rest => Term.localNoAbort rest
    | _, _, .guard _ _ _ _ why rest => decide (why ≠ .abort) && Term.localNoAbort rest
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest =>
        Term.localNoAbort onTrue && Term.localNoAbort onFalse && Term.localNoAbort rest
    | _, _, .cases _ _ _ _ _ arms _ rest =>
        Arms.localNoAbort arms && Term.localNoAbort rest
    | _, _, .loop _ _ _ _ _ _ body _ rest =>
        Term.localNoAbort body && Term.localNoAbort rest
    | _, _, .block _ _ body _ rest =>
        Term.localNoAbort body && Term.localNoAbort rest
    | _, _, .attempt _ _ _ _ body _ rest =>
        Term.localNoAbort body && Term.localNoAbort rest

  def Arms.localNoAbort {fns : List (FnHeader V)} :
      {Γ : Ctx V.Ty} → {mid payloads : List V.Ty} →
      Arms (localDialect V fns) Γ mid payloads → Bool
    | _, _, _, .nil => true
    | _, _, _, .cons _ arm rest => Term.localNoAbort arm && Arms.localNoAbort rest
end

/-- Whether every local function defined in `defs` contains no `.abort` guard. -/
def Defs.fnsNoAbort : {hs : Headers V} → Defs V hs → Bool
  | _, .nil => true
  | _, .fn _ _ body _ rest _ => Term.localNoAbort body && Defs.fnsNoAbort rest
  | _, .protocol _ _ _ _ rest => Defs.fnsNoAbort rest

/-- Shift a `Source` at sites in `insideCoins` by prepending `frame` to the occurrence path,
matching `Process.markOwn M frame` inside attempt `target`. -/
def shiftAttemptSource (M : Model V) (insideCoins : List Site) (frame : Frame)
    (source : Source M) : Source M :=
  fun at_ τ =>
    if at_.site ∈ insideCoins then source ⟨frame :: at_.path, at_.key⟩ τ else source at_ τ

/-- Whether a role program's continuation at `.begin` for `target` is independent of the attempt
counter value `k` relative to `0`. Always holds unconditionally when `k = 0`. -/
def Program.AttemptIndexFree (M : Model V) (target : Site) (k : Nat) {B : Type} :
    Program M B → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.begin at_) cont =>
      (at_.site = target → cont k = cont 0) ∧ ∀ n, Program.AttemptIndexFree M target k (cont n)
  | .call _ cont => ∀ r, Program.AttemptIndexFree M target k (cont r)

theorem Program.attemptIndexFree_zero (M : Model V) (target : Site) {B : Type} :
    ∀ (p : Program M B), Program.AttemptIndexFree M target 0 p
  | .done _ => trivial
  | .halt _ => trivial
  | .call (.begin _) cont => ⟨fun _ => rfl, fun n => attemptIndexFree_zero M target (cont n)⟩
  | .call (.give ..) cont => fun r => attemptIndexFree_zero M target (cont r)
  | .call (.get ..) cont => fun r => attemptIndexFree_zero M target (cont r)
  | .call (.own ..) cont => fun r => attemptIndexFree_zero M target (cont r)
  | .call (.hear ..) cont => fun r => attemptIndexFree_zero M target (cont r)
  | .call (.settle ..) cont => fun r => attemptIndexFree_zero M target (cont r)

end ShapePredicates

/-! ## Section 3: Local no-abort, verifier obliviousness, and the 3-phase `RetryWellFormed` invariant -/

section StructuralInvariants

variable {V : Vocabulary} (M : Model V)

/-! ### 3a. Local operations and `fnsNoAbort` never halt with `.abort` -/

private theorem ownedOp_noAbort {ins res : List V.Ty} (o : OwnedOp V ins res)
    (args : HList M.Val ins) :
    (ownedOp M o args).Every (fun _ _ => True) (fun _ => True) (fun why => why.isAbort = false) := by
  cases o with
  | natAdd | natMul | natPow | natEqual | natLess | boolAnd | boolOr | boolEqual | seqConcat =>
      obtain ⟨_, _, rfl⟩ := HList.two args; trivial
  | boolNot | seqLength | seqFill | seqUnsized | finToNat | finWiden
  | getTuple | getRecord | takeTuple | takeRecord | variant =>
      obtain ⟨_, rfl⟩ := HList.one args; trivial
  | makeSeq | makeTuple | makeRecord => trivial
  | natSub | natDiv | natRem =>
      obtain ⟨_, _, rfl⟩ := HList.two args; simp only [ownedOp]; split <;> trivial
  | seqAt =>
      obtain ⟨_, _, rfl⟩ := HList.two args; simp only [ownedOp]; split <;> trivial
  | seqSlice =>
      obtain ⟨_, _, _, rfl⟩ := HList.three args; simp only [ownedOp]; split <;> trivial
  | seqSized | natBelow | takeSeq =>
      obtain ⟨_, rfl⟩ := HList.one args; simp only [ownedOp]; split <;> trivial

private theorem local_every_bind {A B : Type} {p : Local A} {f : A → Local B}
    {R : Stop → Prop}
    (hp : p.Every (fun _ _ => True) (fun _ => True) R)
    (hf : ∀ a, (f a).Every (fun _ _ => True) (fun _ => True) R) :
    (p.bind f).Every (fun _ _ => True) (fun _ => True) R := by
  cases p with
  | done a => exact hf a
  | halt why => exact hp
  | call op _ => nomatch op

private theorem local_every_iterate {σ : Type} {step : Nat → σ → Local σ} {R : Stop → Prop}
    (hstep : ∀ i s, (step i s).Every (fun _ _ => True) (fun _ => True) R) :
    ∀ (n i : Nat) (s : σ),
      (Process.iterate n step i s).Every (fun _ _ => True) (fun _ => True) R
  | 0, _, _ => trivial
  | n + 1, i, s =>
      local_every_bind (hstep i s) (fun s' => local_every_iterate hstep n (i + 1) s')

mutual
  private theorem term_local_noAbort {fns : List (FnHeader V)} (table : FnTable M fns)
      (hTable : ∀ hdr (c : Member fns hdr) args,
        (table hdr c args).Every (fun _ _ => True) (fun _ => True) (fun why => why.isAbort = false)) :
      ∀ {Γ outs} (t : Term (localDialect V fns) Γ outs) (path : List Frame) (env : Env M.Val Γ),
        Term.localNoAbort t = true →
        (t.denote (localSem M fns table) path env).Every (fun _ _ => True) (fun _ => True)
          (fun why => why.isAbort = false)
    | _, _, .ret _, _, _, _ => trivial
    | _, _, .op key o operands results rest, path, env, hNo => by
        rw [Term.denote_op]
        refine local_every_bind ?_ (fun ys => term_local_noAbort table hTable rest path _ hNo)
        cases o with
        | row key sig known =>
            dsimp only [localSem, localOp]
            cases M.apply key sig known (env.all operands) <;> trivial
        | owned o' => exact ownedOp_noAbort M o' (env.all operands)
        | literal _ _ _ => trivial
        | call callee => exact hTable _ callee (env.all operands)
    | _, _, .guard key w c ok why rest, path, env, hNo => by
        simp only [Term.localNoAbort, Bool.and_eq_true, decide_eq_true_eq] at hNo
        rw [Term.denote_guard]
        cases (localSem M fns table).holds ok (env.get c)
        · show (Stop.declared why ⟨path, key⟩).isAbort = false
          cases why <;> first | rfl | exact absurd rfl hNo.1
        · exact term_local_noAbort table hTable rest path env hNo.2
    | _, _, .choose _ _ c ok _ onTrue onFalse _ rest, path, env, hNo => by
        simp only [Term.localNoAbort, Bool.and_eq_true] at hNo
        rw [Term.denote_choose]
        refine local_every_bind ?_ (fun ys => term_local_noAbort table hTable rest path _ hNo.2)
        cases (localSem M fns table).holds ok (env.get c)
        · exact term_local_noAbort table hTable onFalse path env hNo.1.2
        · exact term_local_noAbort table hTable onTrue path env hNo.1.1
    | _, _, .cases _ _ x ok _ arms _ rest, path, env, hNo => by
        simp only [Term.localNoAbort, Bool.and_eq_true] at hNo
        rw [Term.denote_cases]
        exact local_every_bind
          (arms_local_noAbort table hTable arms path env ((localSem M fns table).pick ok (env.get x)) hNo.1)
          (fun ys => term_local_noAbort table hTable rest path _ hNo.2)
    | _, _, .loop key w times _ initial inputs body _ rest, path, env, hNo => by
        simp only [Term.localNoAbort, Bool.and_eq_true] at hNo
        rw [Term.denote_loop]
        refine local_every_bind ?_ (fun _ => term_local_noAbort table hTable rest path _ hNo.2)
        exact local_every_iterate (fun i st => by
          dsimp only [Semantics.loopStep]
          exact local_every_bind (term_local_noAbort table hTable body (path ++ [.iteration key i]) _ hNo.1)
            (fun _ => trivial)) _ 0 _
    | _, _, .block key number body _ rest, path, env, hNo => by
        simp only [Term.localNoAbort, Bool.and_eq_true] at hNo
        rw [Term.denote_block]
        exact local_every_bind
          (term_local_noAbort table hTable body (path ++ [.iteration key number]) env hNo.1)
          (fun ys => term_local_noAbort table hTable rest path _ hNo.2)
    | _, _, .attempt _ _ _ _ body _ rest, path, env, hNo => by
        simp only [Term.localNoAbort, Bool.and_eq_true] at hNo
        rw [Term.denote_attempt]
        dsimp only [localSem, Process.bind]
        exact local_every_bind
          (term_local_noAbort table hTable body path _ hNo.1)
          (fun ys => term_local_noAbort table hTable rest path _ hNo.2)

  private theorem arms_local_noAbort {fns : List (FnHeader V)} (table : FnTable M fns)
      (hTable : ∀ hdr (c : Member fns hdr) args,
        (table hdr c args).Every (fun _ _ => True) (fun _ => True) (fun why => why.isAbort = false)) :
      ∀ {Γ mid payloads} (arms : Arms (localDialect V fns) Γ mid payloads)
        (path : List Frame) (env : Env M.Val Γ) (p : Pick M.Val payloads),
        Arms.localNoAbort arms = true →
        (arms.denote (localSem M fns table) path env p).Every (fun _ _ => True) (fun _ => True)
          (fun why => why.isAbort = false)
    | _, _, _, .nil, _, _, p, _ => nomatch p
    | _, _, _, .cons _ arm _, path, env, .here _, hNo => by
        simp only [Arms.localNoAbort, Bool.and_eq_true] at hNo
        exact term_local_noAbort table hTable arm path _ hNo.1
    | _, _, _, .cons _ _ rest, path, env, .there p, hNo => by
        simp only [Arms.localNoAbort, Bool.and_eq_true] at hNo
        exact arms_local_noAbort table hTable rest path env p hNo.2
end

private theorem defs_fnTable_noAbort :
    ∀ {hs : Headers V} (defs : Defs V hs),
      Defs.fnsNoAbort defs = true →
      ∀ hdr (c : Member hs.fns hdr) args,
        (Defs.fnTable M defs hdr c args).Every (fun _ _ => True) (fun _ => True)
          (fun why => why.isAbort = false)
  | _, .nil, _, _, c, _ => nomatch c
  | _, .fn _ inputs body _ rest _, hNo, _, c, args => by
      simp only [Defs.fnsNoAbort, Bool.and_eq_true] at hNo
      cases c with
      | head =>
          exact term_local_noAbort M (Defs.fnTable M rest) (defs_fnTable_noAbort rest hNo.2)
            body [] (Env.empty.extend inputs args) hNo.1
      | tail c' => exact defs_fnTable_noAbort rest hNo.2 _ c' args
  | _, .protocol _ _ _ _ rest, hNo, hdr, c, args =>
      defs_fnTable_noAbort rest hNo hdr c args

/-! ### 3b. Role lookup and non-prover site containment helpers -/

private theorem list_nodup_role_inj :
    ∀ {xs : List Role}, xs.Nodup → ∀ {a b : Nat} (ha : a < xs.length) (hb : b < xs.length),
      xs[a] = xs[b] → a = b
  | [], _, _, _, ha, _, _ => absurd ha (Nat.not_lt_zero _)
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | _ :: _, hN, 0, b + 1, _, hb, hEq => by
      simp only [List.nodup_cons] at hN
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
      exact absurd (hEq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hb)) hN.1
  | _ :: _, hN, a + 1, 0, ha, _, hEq => by
      simp only [List.nodup_cons] at hN
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
      exact absurd (hEq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ ha)) hN.1
  | _ :: _, hN, a + 1, b + 1, ha, hb, hEq => by
      simp only [List.nodup_cons] at hN
      simp only [List.getElem_cons_succ] at hEq
      exact congrArg (· + 1) (list_nodup_role_inj hN.2
        (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb) hEq)

private theorem range_filter_getD_eq_singleton (peers : List Role) (distinct : peers.Nodup)
    {j : Nat} (hj : j < peers.length) {r : Role} (hEq : peers[j] = r) :
    (List.range peers.length).filter (fun i => peers.getD i i == r) = [j] := by
  have hSub : ∀ (k : Nat), k ≤ peers.length →
      (List.range k).filter (fun i => peers.getD i i == r) =
        if j < k then [j] else [] := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.filter_append, ih (Nat.le_of_lt hk)]
        have hkLt : k < peers.length := hk
        by_cases hjk : j < k
        · have hPNe : peers[k] ≠ r := fun hPk =>
            (Nat.ne_of_lt hjk) (list_nodup_role_inj distinct hkLt hj (hPk.trans hEq.symm)).symm
          simp [List.getElem?_eq_getElem hkLt, hjk, Nat.lt_succ_of_lt hjk, hPNe]
        · by_cases hEqJK : j = k
          · subst hEqJK
            simp [List.getElem?_eq_getElem hkLt, hjk, hEq]
          · have hNotLt : ¬ j < k + 1 := fun h => hjk (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp h) hEqJK)
            have hPNe : peers[k] ≠ r := fun hPk =>
              hEqJK (list_nodup_role_inj distinct hkLt hj (hPk.trans hEq.symm)).symm
            simp [List.getElem?_eq_getElem hkLt, hjk, hNotLt, hPNe]
  simpa [hj] using hSub peers.length (Nat.le_refl _)

private theorem frame_applications_append_retry (p q : List Frame) :
    Frame.applications (p ++ q) = Frame.applications p ++ Frame.applications q := by
  induction p with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [Frame.applications, ih]

/-! ### 3c. Verifier obliviousness (`roleMeaning_notMarkAt_of_hasAttemptFor_false`) -/

private theorem safeWith_mapR_notMarkAt {B : Type} (ρ : Role → Role) (target : Site) :
    ∀ {p : Program M B},
      p.SafeWith M (fun _ _ => True) (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True) →
      (mapR M ρ p).SafeWith M (fun _ _ => True) (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.give ..) _, ⟨_, hk⟩ => ⟨trivial, fun u _ => safeWith_mapR_notMarkAt ρ target (hk u trivial)⟩
  | .call (.get ..) _, ⟨_, hk⟩ => ⟨trivial, fun u _ => safeWith_mapR_notMarkAt ρ target (hk u trivial)⟩
  | .call (.own ..) _, ⟨_, hk⟩ => ⟨trivial, fun u _ => safeWith_mapR_notMarkAt ρ target (hk u trivial)⟩
  | .call (.hear ..) _, ⟨_, hk⟩ => ⟨trivial, fun u _ => safeWith_mapR_notMarkAt ρ target (hk u trivial)⟩
  | .call (.begin ..) _, ⟨ho, hk⟩ => ⟨ho, fun n _ => safeWith_mapR_notMarkAt ρ target (hk n trivial)⟩
  | .call (.settle ..) _, ⟨ho, hk⟩ => ⟨ho, fun u _ => safeWith_mapR_notMarkAt ρ target (hk u trivial)⟩

private theorem safeWith_iterate_notMarkAt {σ : Type} (target : Site)
    {step : Nat → σ → Program M σ}
    (hstep : ∀ i s, (step i s).SafeWith M (fun _ _ => True) (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True)) :
    ∀ (n i : Nat) (s : σ),
      (Process.iterate n step i s).SafeWith M (fun _ _ => True) (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True)
  | 0, _, _ => trivial
  | n + 1, i, s => by
      simp only [Process.iterate]
      rw [Process.safeWith_bind]
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun s' _ => safeWith_iterate_notMarkAt target hstep n (i + 1) s') (fun _ _ => trivial)
        (hstep i s)

mutual
  private theorem project_notMarkAt {hs : Headers V} (r : Role) (target : Site)
      (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
      (hCallee : ∀ hdr (c : Member hs.protocols hdr) (j : Role) (path : List Frame)
        (args : HList (RV M j) hdr.ins),
        (j ∉ List.range hdr.roles ∨ hdr.shape.hasAttemptFor j target (Frame.applications path) = false) →
        (roles hdr c j path args).SafeWith M (fun _ _ => True) (ROp.NotMarkAt M target)
          (fun _ => True) (fun _ => True)) :
      ∀ {parts : List Role} {Γ outs} (t : Term (protocolDialect V hs) Γ outs)
        (path : List Frame) (env : Env (RV M r) Γ),
        Within parts t →
        (r ∉ parts ∨ (shapeOf t).hasAttemptFor r target (Frame.applications path) = false) →
        ((project r t).denote (roleSem M r fns roles) path env).SafeWith M (fun _ _ => True)
          (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True)
    | _, _, _, .ret _, _, _, _ => fun _ => trivial
    | parts, _, _, .op key o operands results rest, path, env, hW => by
        intro hCond
        rw [project]
        have hCondRest : r ∉ parts ∨ (shapeOf rest).hasAttemptFor r target (Frame.applications path) = false := by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right
            cases o <;> simp only [shapeOf, ProtocolOp.shape, Shape.hasAttemptFor, Bool.or_eq_false_iff] at hHas
            · exact hHas
            · exact hHas
            · exact hHas
            · exact hHas
            · exact hHas.2
        have hRest := fun ys => project_notMarkAt r target fns roles hCallee rest path (env.extend results ys) hW.2 hCondRest
        cases o with
        | compute R op _ types held =>
            dsimp only [ProtocolOp.project]
            split
            · rw [Term.denote_op, Process.safeWith_bind]
              refine Process.safeWith_mono M (P₁ := fun _ => True) (R₁ := fun _ => True)
                (fun _ _ h => h) (fun _ h => h) (fun ys _ => hRest ys) (fun _ _ => trivial) ?_
              dsimp only [roleSem, roleOp]
              rw [Process.safeWith_map]
              exact Process.safeWith_liftLocal M id _ (local_every_true _)
            · rw [Term.denote_op, Process.safeWith_bind]
              dsimp only [roleSem, roleOp]
              exact hRest _
        | narrow R among =>
            dsimp only [ProtocolOp.project]
            split
            · rw [Term.denote_op, Process.safeWith_bind]
              cases env.all operands with | cons _ hNil => cases hNil; dsimp only [roleSem, roleOp]; exact hRest _
            · rw [Term.denote_op, Process.safeWith_bind]
              dsimp only [roleSem, roleOp]
              exact hRest _
        | flow kind giver getters holds unique =>
            dsimp only [ProtocolOp.project]
            split
            · rw [Term.denote_op, Process.safeWith_bind]
              cases env.all operands with
              | cons _ hNil =>
                  cases hNil; dsimp only [roleSem, roleOp]
                  exact ⟨trivial, fun _ _ => hRest _⟩
            · split
              · rw [Term.denote_op, Process.safeWith_bind]
                dsimp only [roleSem, roleOp]
                exact ⟨trivial, fun _ _ => hRest _⟩
              · rw [Term.denote_op, Process.safeWith_bind]
                cases env.all operands with | cons _ hNil => cases hNil; dsimp only [roleSem, roleOp]; exact hRest _
        | given kind owner hearers _ τ _ _ _ =>
            dsimp only [ProtocolOp.project]
            split
            · rename_i hOwnEq; subst hOwnEq
              rw [Term.denote_op, Process.safeWith_bind]
              dsimp only [roleSem, roleOp]
              exact ⟨trivial, fun _ _ => hRest _⟩
            · split
              · rw [Term.denote_op, Process.safeWith_bind]
                dsimp only [roleSem, roleOp]
                exact ⟨trivial, fun _ _ => hRest _⟩
              · rw [Term.denote_op, Process.safeWith_bind]
                dsimp only [roleSem, roleOp]
                exact hRest _
        | @apply hdr callee peers distinct covers _ fits =>
            dsimp only [ProtocolOp.project]
            rw [Term.denote_op, Process.safeWith_bind]
            refine Process.safeWith_mono M (P₁ := fun _ => True) (R₁ := fun _ => True)
              (fun _ _ h => h) (fun _ h => h) (fun ys _ => hRest ys) (fun _ _ => trivial) ?_
            dsimp only [roleSem, roleOp]
            rw [Process.safeWith_map]
            let ρ := RoleMap.ofList peers distinct
            have hApp : Frame.applications (path ++ [.application key]) = Frame.applications path ++ [key] := by
              rw [frame_applications_append_retry]; rfl
            have hInnerCond : ρ.back r ∉ List.range hdr.roles ∨
                hdr.shape.hasAttemptFor (ρ.back r) target (Frame.applications (path ++ [.application key])) = false := by
              by_cases hMem : r ∈ peers
              · obtain ⟨j, hj, hPj⟩ := List.getElem_of_mem hMem
                have hBack : ρ.back r = j := by
                  have hTo := RoleMap.ofList_to peers distinct j hj
                  rw [hPj] at hTo
                  have := congrArg ρ.back hTo
                  rw [ρ.left] at this
                  exact this.symm
                rcases hCond with hOut | hHas
                · exact absurd (hW.1 r hMem) hOut
                · right
                  simp only [shapeOf, ProtocolOp.shape, Shape.hasAttemptFor, Bool.or_eq_false_iff] at hHas
                  rw [range_filter_getD_eq_singleton peers distinct hj hPj] at hHas
                  rw [hBack, hApp]
                  exact hHas.1
              · left
                have hGe := RoleMap.ofList_back peers distinct hMem
                rw [covers] at hGe
                intro hIn
                exact Nat.not_lt.mpr hGe (List.mem_range.mp hIn)
            exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => trivial)
              (fun _ _ => trivial)
              (safeWith_mapR_notMarkAt M ρ.to target (hCallee hdr callee (ρ.back r) _ _ hInnerCond))
    | parts, _, _, .guard key w c ok why rest, path, env, hW => by
        intro hCond
        have hRest := project_notMarkAt r target fns roles hCallee rest path env hW.2 hCond
        rw [project]
        dsimp only [project]
        split
        · rw [Term.denote_guard]
          cases (roleSem M r fns roles).holds _ (env.get c)
          · trivial
          · exact hRest
        · exact hRest
    | parts, _, _, .choose key w c ok gives onTrue onFalse results rest, path, env, hW => by
        intro hCond
        have hCondArms : ∀ (b : Bool), (r ∉ parts ∨ (shapeOf (if b then onTrue else onFalse)).hasAttemptFor r target (Frame.applications path) = false) := by
          intro b
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right
            simp only [shapeOf, Shape.hasAttemptFor, Shapes.hasAttemptFor, Bool.or_false, Bool.or_eq_false_iff] at hHas
            cases b
            · exact hHas.1.2
            · exact hHas.1.1
        have hCondRest : r ∉ parts ∨ (shapeOf rest).hasAttemptFor r target (Frame.applications path) = false := by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right
            simp only [shapeOf, Shape.hasAttemptFor, Shapes.hasAttemptFor, Bool.or_false, Bool.or_eq_false_iff] at hHas
            exact hHas.2
        have hTrue := project_notMarkAt r target fns roles hCallee onTrue path env hW.2.1 (hCondArms true)
        have hFalse := project_notMarkAt r target fns roles hCallee onFalse path env hW.2.2.1 (hCondArms false)
        have hRest := fun ys => project_notMarkAt r target fns roles hCallee rest path (env.extend results ys) hW.2.2.2 hCondRest
        rw [project]
        dsimp only [project]
        split
        · rw [Term.denote_choose, Process.safeWith_bind]
          refine Process.safeWith_mono M (P₁ := fun _ => True) (R₁ := fun _ => True)
            (fun _ _ h => h) (fun _ h => h) (fun ys _ => hRest ys) (fun _ _ => trivial) ?_
          cases (roleSem M r fns roles).holds _ (env.get c)
          · exact hFalse
          · exact hTrue
        · rw [Term.denote_op, Process.safeWith_bind]
          exact hRest _
    | parts, _, _, .cases key w x ok gives arms results rest, path, env, hW => by
        intro hCond
        have hCondArms : r ∉ parts ∨ (shapesOf arms).hasAttemptFor r target (Frame.applications path) = false := by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right; simp only [shapeOf, Shape.hasAttemptFor, Bool.or_eq_false_iff] at hHas; exact hHas.1
        have hCondRest : r ∉ parts ∨ (shapeOf rest).hasAttemptFor r target (Frame.applications path) = false := by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right; simp only [shapeOf, Shape.hasAttemptFor, Bool.or_eq_false_iff] at hHas; exact hHas.2
        have hArms := fun pk => projectArms_notMarkAt r target fns roles hCallee arms path env pk hW.2.1 hCondArms
        have hRest := fun ys => project_notMarkAt r target fns roles hCallee rest path (env.extend results ys) hW.2.2 hCondRest
        rw [project]
        dsimp only [project]
        split
        · rw [Term.denote_cases, Process.safeWith_bind]
          exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
            (fun ys _ => hRest ys) (fun _ _ => trivial) (hArms _)
        · rw [Term.denote_op, Process.safeWith_bind]
          exact hRest _
    | parts, _, _, .loop key w times gives initial inputs body results rest, path, env, hW => by
        intro hCond
        have hCondBody : r ∉ parts ∨ (shapeOf body).hasAttemptFor r target (Frame.applications path) = false := by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right; simp only [shapeOf, Shape.hasAttemptFor, Bool.or_eq_false_iff] at hHas; exact hHas.1
        have hCondRest : r ∉ parts ∨ (shapeOf rest).hasAttemptFor r target (Frame.applications path) = false := by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right; simp only [shapeOf, Shape.hasAttemptFor, Bool.or_eq_false_iff] at hHas; exact hHas.2
        have hBody := fun i env' =>
          project_notMarkAt r target fns roles hCallee body (path ++ [.iteration key i]) env' hW.2.1
            (by rw [frame_applications_append_retry]; simpa [Frame.applications] using hCondBody)
        have hRest := fun ys => project_notMarkAt r target fns roles hCallee rest path (env.extend results ys) hW.2.2 hCondRest
        rw [project]
        dsimp only [project]
        split
        · cases times with
          | fixed n =>
              dsimp only [projectLoop]
              erw [Term.denote_loop, Process.safeWith_bind]
              refine Process.safeWith_mono M (P₁ := fun _ => True) (R₁ := fun _ => True)
                (fun _ _ h => h) (fun _ h => h) (fun _ _ => hRest _) (fun _ _ => trivial) ?_
              exact safeWith_iterate_notMarkAt M target (fun i st => by
                simp only [Semantics.loopStep]
                rw [Process.safeWith_bind]
                exact Process.safeWith_mono M (P₁ := fun _ => True) (R₁ := fun _ => True)
                  (fun _ _ h => h) (fun _ h => h) (fun _ _ => trivial)
                  (fun _ _ => trivial) (hBody i (env.extend inputs (.cons (hide M r (LTy.index w) i) st.1)))) _ 0 _
          | value count ok =>
              dsimp only [projectLoop]
              erw [Term.denote_loop, Process.safeWith_bind]
              refine Process.safeWith_mono M (P₁ := fun _ => True) (R₁ := fun _ => True)
                (fun _ _ h => h) (fun _ h => h) (fun _ _ => hRest _) (fun _ _ => trivial) ?_
              exact safeWith_iterate_notMarkAt M target (fun i st => by
                simp only [Semantics.loopStep]
                rw [Process.safeWith_bind]
                exact Process.safeWith_mono M (P₁ := fun _ => True) (R₁ := fun _ => True)
                  (fun _ _ h => h) (fun _ h => h) (fun _ _ => trivial)
                  (fun _ _ => trivial) (hBody i (env.extend inputs (.cons (hide M r (LTy.index w) i) st.1)))) _ 0 _
        · rw [Term.denote_op, Process.safeWith_bind]
          exact hRest _
    | parts, _, _, .block key number body results rest, path, env, hW => by
        intro hCond
        have hCondBody : r ∉ parts ∨ (shapeOf body).hasAttemptFor r target (Frame.applications path) = false := by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right; simp only [shapeOf, Shape.hasAttemptFor, Bool.or_eq_false_iff] at hHas; exact hHas.1
        have hCondRest : r ∉ parts ∨ (shapeOf rest).hasAttemptFor r target (Frame.applications path) = false := by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right; simp only [shapeOf, Shape.hasAttemptFor, Bool.or_eq_false_iff] at hHas; exact hHas.2
        have hBody := project_notMarkAt r target fns roles hCallee body (path ++ [.iteration key number]) env hW.1
          (by rw [frame_applications_append_retry]; simpa [Frame.applications] using hCondBody)
        have hRest := fun ys => project_notMarkAt r target fns roles hCallee rest path (env.extend results ys) hW.2 hCondRest
        rw [project, Term.denote_block, Process.safeWith_bind]
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun ys _ => hRest ys) (fun _ _ => trivial) hBody
    | parts, _, _, .attempt key w owns inputs body results rest, path, env, hW => by
        intro hCond
        have hCondBody : r ∉ parts ∨ (shapeOf body).hasAttemptFor r target (Frame.applications path) = false := by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right; simp only [shapeOf, Shape.hasAttemptFor, Bool.or_eq_false_iff] at hHas; exact hHas.1.2
        have hCondRest : r ∉ parts ∨ (shapeOf rest).hasAttemptFor r target (Frame.applications path) = false := by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right; simp only [shapeOf, Shape.hasAttemptFor, Bool.or_eq_false_iff] at hHas; exact hHas.2
        have hBody := fun n => project_notMarkAt r target fns roles hCallee body path (env.extend inputs (.cons n .nil)) hW.2.1 hCondBody
        have hRest := fun mids => project_notMarkAt r target fns roles hCallee rest path (env.extend results mids) hW.2.2 hCondRest
        have hMarkNe : r ∈ w → (⟨Frame.applications path, key⟩ : Site) ≠ target := by
          intro hInW hSiteEq
          rcases hCond with hOut | hHas
          · exact hOut (hW.1 r hInW)
          · simp only [shapeOf, Shape.hasAttemptFor, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
              decide_eq_false_iff_not] at hHas
            rcases hHas.1.1 with hNe | hNotW
            · exact hNe hSiteEq
            · exact hNotW hInW
        rw [project, Term.denote_attempt, Process.safeWith_bind]
        have hBodyRest : ∀ n, ((project r body).denote (roleSem M r fns roles) path
              (env.extend inputs (.cons n .nil)) |>.bind fun mids =>
              ((roleSem M r fns roles).settle w key path).bind fun _ =>
                (project r rest).denote (roleSem M r fns roles) path (env.extend results mids)).SafeWith
            M (fun _ _ => True) (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True) := by
          intro n
          rw [Process.safeWith_bind]
          refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
            (fun mids _ => ?_) (fun _ _ => trivial) (hBody n)
          rw [Process.safeWith_bind]
          have hSet : ((roleSem M r fns roles).settle w key path).SafeWith M (fun _ _ => True)
              (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True) := by
            show Process.SafeWith M _ _ _ _ (if r ∈ w then _ else _)
            split
            · rename_i hInW
              exact ⟨hMarkNe hInW, fun _ _ => trivial⟩
            · trivial
          exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
            (fun _ _ => hRest mids) (fun _ _ => trivial) hSet
        have hBeg : ((roleSem M r fns roles).begin w key path).SafeWith M (fun _ _ => True)
            (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True) := by
          show Process.SafeWith M _ _ _ _ (if r ∈ w then _ else _)
          split
          · rename_i hInW
            exact ⟨hMarkNe hInW, fun _ _ => trivial⟩
          · trivial
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun n _ => hBodyRest n) (fun _ _ => trivial) hBeg

  private theorem projectArms_notMarkAt {hs : Headers V} (r : Role) (target : Site)
      (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
      (hCallee : ∀ hdr (c : Member hs.protocols hdr) (j : Role) (path : List Frame)
        (args : HList (RV M j) hdr.ins),
        (j ∉ List.range hdr.roles ∨ hdr.shape.hasAttemptFor j target (Frame.applications path) = false) →
        (roles hdr c j path args).SafeWith M (fun _ _ => True) (ROp.NotMarkAt M target)
          (fun _ => True) (fun _ => True)) :
      ∀ {parts : List Role} {Γ mid payloads} (arms : Arms (protocolDialect V hs) Γ mid payloads)
        (path : List Frame) (env : Env (RV M r) Γ) (p : Pick (RV M r) payloads),
        WithinArms parts arms →
        (r ∉ parts ∨ (shapesOf arms).hasAttemptFor r target (Frame.applications path) = false) →
        ((projectArms r arms).denote (roleSem M r fns roles) path env p).SafeWith M (fun _ _ => True)
          (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True)
    | _, _, _, _, .nil, _, _, p, _ => nomatch p
    | _, _, _, _, .cons _ arm _, path, env, .here _, hW => fun hCond =>
        project_notMarkAt r target fns roles hCallee arm path _ hW.1 (by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right; simp only [shapesOf, Shapes.hasAttemptFor, Bool.or_eq_false_iff] at hHas; exact hHas.1)
    | _, _, _, _, .cons _ _ rest, path, env, .there p, hW => fun hCond =>
        projectArms_notMarkAt r target fns roles hCallee rest path env p hW.2 (by
          rcases hCond with hOut | hHas
          · exact .inl hOut
          · right; simp only [shapesOf, Shapes.hasAttemptFor, Bool.or_eq_false_iff] at hHas; exact hHas.2)
end

private theorem defs_rTable_notMarkAt (target : Site) :
    ∀ {hs : Headers V} (defs : Defs V hs) (hdr : ProtocolHeader V) (c : Member hs.protocols hdr)
      (r : Role) (path : List Frame) (args : HList (RV M r) hdr.ins),
      (r ∉ List.range hdr.roles ∨ hdr.shape.hasAttemptFor r target (Frame.applications path) = false) →
      (Defs.rTable M defs hdr c r path args).SafeWith M (fun _ _ => True) (ROp.NotMarkAt M target)
        (fun _ => True) (fun _ => True)
  | _, .nil, _, c, _, _, _, _ => nomatch c
  | _, .fn _ _ _ _ rest _, hdr, c, r, path, args, hCond =>
      defs_rTable_notMarkAt target rest hdr c r path args hCond
  | _, .protocol hdr inputs body ok rest, _, c, r, path, args, hCond => by
      cases c with
      | head =>
          rw [ok.shaped] at hCond
          exact project_notMarkAt M r target (Defs.fnTable M rest) (Defs.rTable M rest)
            (defs_rTable_notMarkAt target rest) body path (Env.empty.extend inputs args) ok.within hCond
      | tail c' => exact defs_rTable_notMarkAt target rest _ c' r path args hCond

unseal roleMeaning in
/-- If `hdr.shape.hasAttemptFor r target [] = false`, then `roleMeaning` for role `r` never emits
`.begin` or `.settle` at `target`. -/
theorem roleMeaning_notMarkAt_of_hasAttemptFor_false (p : Typed V) {hdr : ProtocolHeader V}
    (callee : Member p.headers.protocols hdr) (r : Role) (args : HList (RV M r) hdr.ins)
    (target : Site) (hHas : hdr.shape.hasAttemptFor r target [] = false) :
    (roleMeaning M p callee r [] args).SafeWith M (fun _ _ => True) (ROp.NotMarkAt M target)
      (fun _ => True) (fun _ => True) :=
  defs_rTable_notMarkAt M target p.defs hdr callee r [] args (.inr hHas)

/-! ### 3d. Three-phase retry well-formedness automaton (`RetryPhase` / `Program.RetryWellFormed`) -/

/-- Phase of the prover's execution relative to the single declared retry attempt `target`. -/
inductive RetryPhase where
  | before
  | inside
  | after
deriving DecidableEq

/-- Unified 3-phase well-formedness invariant on a prover role program `p`:
- `.before`: no abort, private coins & requests `∉ insideCoins`, no `.settle target`, `.begin target`
  transitions to `.inside`.
- `.inside`: aborts allowed, private coins `∈ insideCoins`, requests `∉ insideCoins`, no `.begin target`,
  `.settle target` transitions to `.after`.
- `.after`: no abort, private coins & requests `∉ insideCoins`, neither `.begin target` nor `.settle target`. -/
def Program.RetryWellFormed (target : Site) (insideCoins : List Site) {B : Type} :
    RetryPhase → Program M B → Prop
  | _, .done _ => True
  | .before, .halt why => why.isAbort = false
  | .inside, .halt _ => True
  | .after, .halt why => why.isAbort = false
  | .before, .call (.begin at_) k =>
      if at_.site = target then ∀ n, RetryWellFormed target insideCoins .inside (k n)
      else ∀ n, RetryWellFormed target insideCoins .before (k n)
  | .inside, .call (.begin at_) k =>
      at_.site ≠ target ∧ ∀ n, RetryWellFormed target insideCoins .inside (k n)
  | .after, .call (.begin at_) k =>
      at_.site ≠ target ∧ ∀ n, RetryWellFormed target insideCoins .after (k n)
  | .before, .call (.settle at_) k =>
      at_.site ≠ target ∧ ∀ u, RetryWellFormed target insideCoins .before (k u)
  | .inside, .call (.settle at_) k =>
      if at_.site = target then ∀ u, RetryWellFormed target insideCoins .after (k u)
      else ∀ u, RetryWellFormed target insideCoins .inside (k u)
  | .after, .call (.settle at_) k =>
      at_.site ≠ target ∧ ∀ u, RetryWellFormed target insideCoins .after (k u)
  | .before, .call (.own (.coin _) [] at_ _ _ _) k =>
      at_.site ∉ insideCoins ∧ ∀ v, RetryWellFormed target insideCoins .before (k v)
  | .inside, .call (.own (.coin _) [] at_ _ _ _) k =>
      at_.site ∈ insideCoins ∧ ∀ v, RetryWellFormed target insideCoins .inside (k v)
  | .after, .call (.own (.coin _) [] at_ _ _ _) k =>
      at_.site ∉ insideCoins ∧ ∀ v, RetryWellFormed target insideCoins .after (k v)
  | ph, .call (.own (.request _) _ at_ _ _ _) k =>
      at_.site ∉ insideCoins ∧ ∀ v, RetryWellFormed target insideCoins ph (k v)
  | ph, .call (.own (.coin _) (_ :: _) _ _ _ _) k =>
      ∀ v, RetryWellFormed target insideCoins ph (k v)
  | ph, .call (.give ..) k => ∀ u, RetryWellFormed target insideCoins ph (k u)
  | ph, .call (.get ..) k => ∀ v, RetryWellFormed target insideCoins ph (k v)
  | ph, .call (.hear ..) k => ∀ v, RetryWellFormed target insideCoins ph (k v)

/-- Parameterized version tracking the guaranteed exit phase `onDone : RetryPhase → Prop` so
`Process.bind` composes cleanly across `.before → .after` transitions. -/
def Program.RetryWF (target : Site) (insideCoins : List Site) {B : Type}
    (onDone : RetryPhase → Prop) : RetryPhase → Program M B → Prop
  | ph, .done _ => onDone ph
  | .before, .halt why => why.isAbort = false
  | .inside, .halt _ => True
  | .after, .halt why => why.isAbort = false
  | .before, .call (.begin at_) k =>
      if at_.site = target then ∀ n, RetryWF target insideCoins onDone .inside (k n)
      else ∀ n, RetryWF target insideCoins onDone .before (k n)
  | .inside, .call (.begin at_) k =>
      at_.site ≠ target ∧ ∀ n, RetryWF target insideCoins onDone .inside (k n)
  | .after, .call (.begin at_) k =>
      at_.site ≠ target ∧ ∀ n, RetryWF target insideCoins onDone .after (k n)
  | .before, .call (.settle at_) k =>
      at_.site ≠ target ∧ ∀ u, RetryWF target insideCoins onDone .before (k u)
  | .inside, .call (.settle at_) k =>
      if at_.site = target then ∀ u, RetryWF target insideCoins onDone .after (k u)
      else ∀ u, RetryWF target insideCoins onDone .inside (k u)
  | .after, .call (.settle at_) k =>
      at_.site ≠ target ∧ ∀ u, RetryWF target insideCoins onDone .after (k u)
  | .before, .call (.own (.coin _) [] at_ _ _ _) k =>
      at_.site ∉ insideCoins ∧ ∀ v, RetryWF target insideCoins onDone .before (k v)
  | .inside, .call (.own (.coin _) [] at_ _ _ _) k =>
      at_.site ∈ insideCoins ∧ ∀ v, RetryWF target insideCoins onDone .inside (k v)
  | .after, .call (.own (.coin _) [] at_ _ _ _) k =>
      at_.site ∉ insideCoins ∧ ∀ v, RetryWF target insideCoins onDone .after (k v)
  | ph, .call (.own (.request _) _ at_ _ _ _) k =>
      at_.site ∉ insideCoins ∧ ∀ v, RetryWF target insideCoins onDone ph (k v)
  | ph, .call (.own (.coin _) (_ :: _) _ _ _ _) k =>
      ∀ v, RetryWF target insideCoins onDone ph (k v)
  | ph, .call (.give ..) k => ∀ u, RetryWF target insideCoins onDone ph (k u)
  | ph, .call (.get ..) k => ∀ v, RetryWF target insideCoins onDone ph (k v)
  | ph, .call (.hear ..) k => ∀ v, RetryWF target insideCoins onDone ph (k v)

private theorem retryWF_to_wellFormed {target : Site} {insideCoins : List Site} {B : Type}
    {onDone : RetryPhase → Prop} :
    ∀ {ph : RetryPhase} {p : Program M B},
      Program.RetryWF M target insideCoins onDone ph p →
      Program.RetryWellFormed M target insideCoins ph p
  | _, .done _, _ => trivial
  | .before, .halt _, h => h
  | .inside, .halt _, _ => trivial
  | .after, .halt _, h => h
  | .before, .call (.begin _) k, h => by
      dsimp only [Program.RetryWF, Program.RetryWellFormed] at h ⊢
      split at h <;> simp only [*] at h ⊢ <;> intro n <;> exact retryWF_to_wellFormed (h n)
  | .inside, .call (.begin _) k, ⟨h1, h2⟩ => ⟨h1, fun n => retryWF_to_wellFormed (h2 n)⟩
  | .after, .call (.begin _) k, ⟨h1, h2⟩ => ⟨h1, fun n => retryWF_to_wellFormed (h2 n)⟩
  | .before, .call (.settle _) k, ⟨h1, h2⟩ => ⟨h1, fun u => retryWF_to_wellFormed (h2 u)⟩
  | .inside, .call (.settle _) k, h => by
      dsimp only [Program.RetryWF, Program.RetryWellFormed] at h ⊢
      split at h <;> simp only [*] at h ⊢ <;> intro u <;> exact retryWF_to_wellFormed (h u)
  | .after, .call (.settle _) k, ⟨h1, h2⟩ => ⟨h1, fun u => retryWF_to_wellFormed (h2 u)⟩
  | .before, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_to_wellFormed (h2 v)⟩
  | .inside, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_to_wellFormed (h2 v)⟩
  | .after, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_to_wellFormed (h2 v)⟩
  | ph, .call (.own (.request _) _ _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_to_wellFormed (h2 v)⟩
  | ph, .call (.own (.coin _) (_ :: _) _ _ _ _) k, h => fun v => retryWF_to_wellFormed (h v)
  | ph, .call (.give ..) k, h => fun u => retryWF_to_wellFormed (h u)
  | ph, .call (.get ..) k, h => fun v => retryWF_to_wellFormed (h v)
  | ph, .call (.hear ..) k, h => fun v => retryWF_to_wellFormed (h v)

private theorem retryWF_mono {target : Site} {insideCoins : List Site} {B : Type}
    {P₁ P₂ : RetryPhase → Prop} (hImp : ∀ ph, P₁ ph → P₂ ph) :
    ∀ {ph : RetryPhase} {p : Program M B},
      Program.RetryWF M target insideCoins P₁ ph p →
      Program.RetryWF M target insideCoins P₂ ph p
  | _, .done _, h => hImp _ h
  | .before, .halt _, h => h
  | .inside, .halt _, _ => trivial
  | .after, .halt _, h => h
  | .before, .call (.begin _) k, h => by
      dsimp only [Program.RetryWF] at h ⊢
      split at h <;> simp only [*] at h ⊢ <;> intro n <;> exact retryWF_mono hImp (h n)
  | .inside, .call (.begin _) k, ⟨h1, h2⟩ => ⟨h1, fun n => retryWF_mono hImp (h2 n)⟩
  | .after, .call (.begin _) k, ⟨h1, h2⟩ => ⟨h1, fun n => retryWF_mono hImp (h2 n)⟩
  | .before, .call (.settle _) k, ⟨h1, h2⟩ => ⟨h1, fun u => retryWF_mono hImp (h2 u)⟩
  | .inside, .call (.settle _) k, h => by
      dsimp only [Program.RetryWF] at h ⊢
      split at h <;> simp only [*] at h ⊢ <;> intro u <;> exact retryWF_mono hImp (h u)
  | .after, .call (.settle _) k, ⟨h1, h2⟩ => ⟨h1, fun u => retryWF_mono hImp (h2 u)⟩
  | .before, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_mono hImp (h2 v)⟩
  | .inside, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_mono hImp (h2 v)⟩
  | .after, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_mono hImp (h2 v)⟩
  | ph, .call (.own (.request _) _ _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_mono hImp (h2 v)⟩
  | ph, .call (.own (.coin _) (_ :: _) _ _ _ _) k, h => fun v => retryWF_mono hImp (h v)
  | ph, .call (.give ..) k, h => fun u => retryWF_mono hImp (h u)
  | ph, .call (.get ..) k, h => fun v => retryWF_mono hImp (h v)
  | ph, .call (.hear ..) k, h => fun v => retryWF_mono hImp (h v)

private theorem retryWF_bind {target : Site} {insideCoins : List Site} {A B : Type}
    {P Q : RetryPhase → Prop} {f : A → Program M B} :
    ∀ {ph : RetryPhase} {p : Program M A},
      Program.RetryWF M target insideCoins P ph p →
      (∀ ph' a, P ph' → Program.RetryWF M target insideCoins Q ph' (f a)) →
      Program.RetryWF M target insideCoins Q ph (p.bind f)
  | _, .done a, hp, hf => hf _ a hp
  | .before, .halt _, hp, _ => hp
  | .inside, .halt _, _, _ => trivial
  | .after, .halt _, hp, _ => hp
  | .before, .call (.begin _) k, hp, hf => by
      dsimp only [Process.bind, Program.RetryWF] at hp ⊢
      split at hp <;> simp only [*] at hp ⊢ <;> intro n <;> exact retryWF_bind (hp n) hf
  | .inside, .call (.begin _) k, ⟨h1, h2⟩, hf => ⟨h1, fun n => retryWF_bind (h2 n) hf⟩
  | .after, .call (.begin _) k, ⟨h1, h2⟩, hf => ⟨h1, fun n => retryWF_bind (h2 n) hf⟩
  | .before, .call (.settle _) k, ⟨h1, h2⟩, hf => ⟨h1, fun u => retryWF_bind (h2 u) hf⟩
  | .inside, .call (.settle _) k, hp, hf => by
      dsimp only [Process.bind, Program.RetryWF] at hp ⊢
      split at hp <;> simp only [*] at hp ⊢ <;> intro u <;> exact retryWF_bind (hp u) hf
  | .after, .call (.settle _) k, ⟨h1, h2⟩, hf => ⟨h1, fun u => retryWF_bind (h2 u) hf⟩
  | .before, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩, hf => ⟨h1, fun v => retryWF_bind (h2 v) hf⟩
  | .inside, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩, hf => ⟨h1, fun v => retryWF_bind (h2 v) hf⟩
  | .after, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩, hf => ⟨h1, fun v => retryWF_bind (h2 v) hf⟩
  | ph, .call (.own (.request _) _ _ _ _ _) k, ⟨h1, h2⟩, hf => ⟨h1, fun v => retryWF_bind (h2 v) hf⟩
  | ph, .call (.own (.coin _) (_ :: _) _ _ _ _) k, hp, hf => fun v => retryWF_bind (hp v) hf
  | ph, .call (.give ..) k, hp, hf => fun u => retryWF_bind (hp u) hf
  | ph, .call (.get ..) k, hp, hf => fun v => retryWF_bind (hp v) hf
  | ph, .call (.hear ..) k, hp, hf => fun v => retryWF_bind (hp v) hf

private theorem retryWF_map {target : Site} {insideCoins : List Site} {A B : Type}
    {P : RetryPhase → Prop} (g : A → B) {ph : RetryPhase} {p : Program M A}
    (hp : Program.RetryWF M target insideCoins P ph p) :
    Program.RetryWF M target insideCoins P ph (p.map g) := by
  rw [Process.map_eq_bind]
  exact retryWF_bind M hp (fun _ _ h => h)

private theorem retryWF_mapR {target : Site} {insideCoins : List Site} {B : Type}
    (ρ : Role → Role) {P : RetryPhase → Prop} :
    ∀ {ph : RetryPhase} {p : Program M B},
      Program.RetryWF M target insideCoins P ph p →
      Program.RetryWF M target insideCoins P ph (mapR M ρ p)
  | _, .done _, h => h
  | .before, .halt _, h => h
  | .inside, .halt _, _ => trivial
  | .after, .halt _, h => h
  | .before, .call (.begin _) k, h => by
      dsimp only [mapR, Program.RetryWF] at h ⊢
      split at h <;> simp only [*] at h ⊢ <;> intro n <;> exact retryWF_mapR ρ (h n)
  | .inside, .call (.begin _) k, ⟨h1, h2⟩ => ⟨h1, fun n => retryWF_mapR ρ (h2 n)⟩
  | .after, .call (.begin _) k, ⟨h1, h2⟩ => ⟨h1, fun n => retryWF_mapR ρ (h2 n)⟩
  | .before, .call (.settle _) k, ⟨h1, h2⟩ => ⟨h1, fun u => retryWF_mapR ρ (h2 u)⟩
  | .inside, .call (.settle _) k, h => by
      dsimp only [mapR, Program.RetryWF] at h ⊢
      split at h <;> simp only [*] at h ⊢ <;> intro u <;> exact retryWF_mapR ρ (h u)
  | .after, .call (.settle _) k, ⟨h1, h2⟩ => ⟨h1, fun u => retryWF_mapR ρ (h2 u)⟩
  | .before, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_mapR ρ (h2 v)⟩
  | .inside, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_mapR ρ (h2 v)⟩
  | .after, .call (.own (.coin _) [] _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_mapR ρ (h2 v)⟩
  | ph, .call (.own (.request _) _ _ _ _ _) k, ⟨h1, h2⟩ => ⟨h1, fun v => retryWF_mapR ρ (h2 v)⟩
  | ph, .call (.own (.coin _) (_ :: _) _ _ _ _) k, h => fun v => retryWF_mapR ρ (h v)
  | ph, .call (.give ..) k, h => fun u => retryWF_mapR ρ (h u)
  | ph, .call (.get ..) k, h => fun v => retryWF_mapR ρ (h v)
  | ph, .call (.hear ..) k, h => fun v => retryWF_mapR ρ (h v)

private theorem retryWF_liftLocal {target : Site} {insideCoins : List Site} {A : Type}
    {ph : RetryPhase} :
    ∀ {p : Local A},
      p.Every (fun _ _ => True) (fun _ => True) (fun why => why.isAbort = false) →
      Program.RetryWF M target insideCoins (· = ph) ph (liftLocal (S := RSig M) id p)
  | .done _, _ => rfl
  | .halt _, h => by cases ph <;> first | exact h | trivial
  | .call op _, _ => nomatch op

private theorem retryWF_iterate {target : Site} {insideCoins : List Site} {σ : Type}
    {ph : RetryPhase} {step : Nat → σ → Program M σ}
    (hstep : ∀ i s, Program.RetryWF M target insideCoins (· = ph) ph (step i s)) :
    ∀ (n i : Nat) (s : σ),
      Program.RetryWF M target insideCoins (· = ph) ph (Process.iterate n step i s)
  | 0, _, _ => rfl
  | n + 1, i, s =>
      retryWF_bind M (hstep i s) (fun _ s' hEq => hEq ▸ retryWF_iterate hstep n (i + 1) s')

/-- In `.after`, `RetryWellFormed` guarantees `ROp.NotMarkAt target`, no abort, and all private
coins / service requests outside `insideCoins`. -/
theorem retryWellFormed_after_safe {target : Site} {insideCoins : List Site} {B : Type} :
    ∀ {p : Program M B},
      Program.RetryWellFormed M target insideCoins .after p →
      p.SafeWith M (fun _ _ => True)
        (fun op => ROp.NotMarkAt M target op ∧
          match op with
          | .own (.coin _) [] at_ _ _ _ => at_.site ∉ insideCoins
          | .own (.request _) _ at_ _ _ _ => at_.site ∉ insideCoins
          | _ => True)
        (fun _ => True) (fun why => why.isAbort = false)
  | .done _, _ => trivial
  | .halt _, h => h
  | .call (.begin _) _, ⟨hNe, hk⟩ => ⟨⟨hNe, trivial⟩, fun n _ => retryWellFormed_after_safe (hk n)⟩
  | .call (.settle _) _, ⟨hNe, hk⟩ => ⟨⟨hNe, trivial⟩, fun u _ => retryWellFormed_after_safe (hk u)⟩
  | .call (.own (.coin _) [] _ _ _ _) _, ⟨hOut, hk⟩ => ⟨⟨trivial, hOut⟩, fun v _ => retryWellFormed_after_safe (hk v)⟩
  | .call (.own (.coin _) (_ :: _) _ _ _ _) _, hk => ⟨⟨trivial, trivial⟩, fun v _ => retryWellFormed_after_safe (hk v)⟩
  | .call (.own (.request _) _ _ _ _ _) _, ⟨hOut, hk⟩ => ⟨⟨trivial, hOut⟩, fun v _ => retryWellFormed_after_safe (hk v)⟩
  | .call (.give ..) _, hk => ⟨⟨trivial, trivial⟩, fun u _ => retryWellFormed_after_safe (hk u)⟩
  | .call (.get ..) _, hk => ⟨⟨trivial, trivial⟩, fun v _ => retryWellFormed_after_safe (hk v)⟩
  | .call (.hear ..) _, hk => ⟨⟨trivial, trivial⟩, fun v _ => retryWellFormed_after_safe (hk v)⟩

private def shapeExitPhase (target : Site) (through : List Key) (s : Shape V)
    (ph : RetryPhase) : RetryPhase → Prop :=
  fun ph' =>
    match ph with
    | .before =>
        if target ∈ s.attemptSites through then (ph' = .before ∨ ph' = .after) else ph' = .before
    | .inside => ph' = .inside
    | .after => ph' = .after

private def shapesExitPhase (target : Site) (through : List Key) (ss : Shapes V)
    (ph : RetryPhase) : RetryPhase → Prop :=
  fun ph' =>
    match ph with
    | .before =>
        if target ∈ ss.attemptSites through then (ph' = .before ∨ ph' = .after) else ph' = .before
    | .inside => ph' = .inside
    | .after => ph' = .after

private def phaseInside : RetryPhase → Bool
  | .inside => true
  | _ => false

/-- Helper to combine sequential `shapeExitPhase` transitions when `s₁` and `s₂` never both
contain `target`. -/
private theorem retryWF_seq_combine {target : Site} {insideCoins : List Site} {B : Type}
    {through₁ through₂ : List Key} {s₁ s₂ : Shape V} {ph : RetryPhase}
    {f : RetryPhase → Program M B}
    (hDisj : target ∉ s₁.attemptSites through₁ ∨ target ∉ s₂.attemptSites through₂)
    (hBef : ph = .before → Program.RetryWF M target insideCoins
      (shapeExitPhase target through₂ s₂ .before) .before (f .before))
    (hIns : ph = .inside → Program.RetryWF M target insideCoins
      (shapeExitPhase target through₂ s₂ .inside) .inside (f .inside))
    (hAft : (ph = .after ∨ (ph = .before ∧ target ∈ s₁.attemptSites through₁)) →
      Program.RetryWF M target insideCoins
        (shapeExitPhase target through₂ s₂ .after) .after (f .after)) :
    ∀ ph', shapeExitPhase target through₁ s₁ ph ph' →
      Program.RetryWF M target insideCoins
        (fun ph'' => match ph with
          | .before =>
              if target ∈ s₁.attemptSites through₁ ++ s₂.attemptSites through₂
              then ph'' = .before ∨ ph'' = .after else ph'' = .before
          | .inside => ph'' = .inside
          | .after => ph'' = .after) ph' (f ph') := by
  intro ph' hPh'
  cases ph with
  | inside =>
      dsimp only [shapeExitPhase] at hPh'; subst hPh'
      exact hIns rfl
  | after =>
      dsimp only [shapeExitPhase] at hPh'; subst hPh'
      exact hAft (.inl rfl)
  | before =>
      dsimp only [shapeExitPhase] at hPh'
      by_cases hIn1 : target ∈ s₁.attemptSites through₁
      · rw [ite_eq_left hIn1] at hPh'
        have hNot2 : target ∉ s₂.attemptSites through₂ := hDisj.resolve_left (fun h => h hIn1)
        rcases hPh' with rfl | rfl
        · exact retryWF_mono M (fun p0 hp0 => by
            dsimp only [shapeExitPhase] at hp0
            rw [ite_eq_right hNot2] at hp0
            rw [ite_eq_left (List.mem_append_left _ hIn1)]
            exact .inl hp0) (hBef rfl)
        · exact retryWF_mono M (fun p0 hp0 => by
            dsimp only [shapeExitPhase] at hp0
            rw [ite_eq_left (List.mem_append_left _ hIn1)]
            exact .inr hp0) (hAft (.inr ⟨rfl, hIn1⟩))
      · rw [ite_eq_right hIn1] at hPh'; subst hPh'
        exact retryWF_mono M (fun p0 hp0 => by
          dsimp only [shapeExitPhase] at hp0
          have hIff : target ∈ s₁.attemptSites through₁ ++ s₂.attemptSites through₂ ↔
              target ∈ s₂.attemptSites through₂ := by simp [hIn1]
          by_cases hIn2 : target ∈ s₂.attemptSites through₂
          · rw [ite_eq_left hIn2] at hp0; rw [ite_eq_left (hIff.mpr hIn2)]; exact hp0
          · rw [ite_eq_right hIn2] at hp0; rw [ite_eq_right (fun h => hIn2 (hIff.mp h))]; exact hp0)
          (hBef rfl)

/-- A quiet process (zero calls, zero halts) satisfies `RetryWF` at any phase, preserving the phase. -/
private theorem retryWF_of_quiet {target : Site} {insideCoins : List Site} {B : Type} {ph : RetryPhase} :
    ∀ {p : Program M B},
      p.SafeWith M (fun _ _ => True) (fun _ => False) (fun _ => True) (fun _ => False) →
      Program.RetryWF M target insideCoins (· = ph) ph p
  | .done _, _ => rfl
  | .halt _, h => h.elim
  | .call _ _, h => h.1.elim

private theorem safeWith_quiet_mapR {B : Type} (ρ : Role → Role) :
    ∀ {p : Program M B},
      p.SafeWith M (fun _ _ => True) (fun _ => False) (fun _ => True) (fun _ => False) →
      (mapR M ρ p).SafeWith M (fun _ _ => True) (fun _ => False) (fun _ => True) (fun _ => False)
  | .done _, _ => trivial
  | .halt _, h => h.elim
  | .call _ _, h => h.1.elim

mutual
  private theorem shape_retryAtMostOnce_of_not_mem (target : Site) :
      ∀ (s : Shape V) (th : List Key), target ∉ s.attemptSites th →
        Shape.retryAtMostOnce target th s = true
    | .nil, _, _ => rfl
    | .event _ _ _ rest, th, h => shape_retryAtMostOnce_of_not_mem target rest th h
    | .choice _ _ arms rest, th, h => by
        simp only [Shape.attemptSites, List.mem_append, not_or] at h
        simp [Shape.retryAtMostOnce, shapes_retryAtMostOnce_of_not_mem target arms th h.1,
          shape_retryAtMostOnce_of_not_mem target rest th h.2, h.1]
    | .loop _ _ body rest, th, h => by
        simp only [Shape.attemptSites, List.mem_append, not_or] at h
        simp [Shape.retryAtMostOnce, h.1, shape_retryAtMostOnce_of_not_mem target rest th h.2]
    | .apply k _ _ inner rest, th, h => by
        simp only [Shape.attemptSites, List.mem_append, not_or] at h
        simp [Shape.retryAtMostOnce, shape_retryAtMostOnce_of_not_mem target inner (th ++ [k]) h.1,
          shape_retryAtMostOnce_of_not_mem target rest th h.2, h.1]
    | .block _ _ body rest, th, h => by
        simp only [Shape.attemptSites, List.mem_append, not_or] at h
        simp [Shape.retryAtMostOnce, shape_retryAtMostOnce_of_not_mem target body th h.1,
          shape_retryAtMostOnce_of_not_mem target rest th h.2, h.1]
    | .guard _ _ _ rest, th, h => shape_retryAtMostOnce_of_not_mem target rest th h
    | .attempt k _ body rest, th, h => by
        simp only [Shape.attemptSites, List.mem_cons, List.mem_append, not_or] at h
        have hNe : (⟨th, k⟩ : Site) ≠ target := fun heq => h.1 heq.symm
        simp [Shape.retryAtMostOnce, hNe, shape_retryAtMostOnce_of_not_mem target body th h.2.1,
          shape_retryAtMostOnce_of_not_mem target rest th h.2.2, h.2.1]

  private theorem shapes_retryAtMostOnce_of_not_mem (target : Site) :
      ∀ (ss : Shapes V) (th : List Key), target ∉ ss.attemptSites th →
        Shapes.retryAtMostOnce target th ss = true
    | .nil, _, _ => rfl
    | .cons arm rest, th, h => by
        simp only [Shapes.attemptSites, List.mem_append, not_or] at h
        simp [Shapes.retryAtMostOnce, shape_retryAtMostOnce_of_not_mem target arm th h.1,
          shapes_retryAtMostOnce_of_not_mem target rest th h.2]
end

mutual
  private theorem project_retryWF {hs : Headers V} (r : Role) (target : Site)
      (insideCoins : List Site)
      (fns : FnTable M hs.fns)
      (hFns : ∀ hdr (c : Member hs.fns hdr) args,
        (fns hdr c args).Every (fun _ _ => True) (fun _ => True) (fun why => why.isAbort = false))
      (roles : RTable M hs.protocols)
      (hCallee : ∀ hdr (c : Member hs.protocols hdr) (j : Role) (path : List Frame)
        (args : HList (RV M j) hdr.ins) (ph : RetryPhase),
        (j ∉ List.range hdr.roles →
          (roles hdr c j path args).SafeWith M (fun _ _ => True) (fun _ => False) (fun _ => True) (fun _ => False)) ∧
        (hdr.shape.retryAtMostOnce target (Frame.applications path) = true →
         hdr.shape.retryOwnedBy j target (Frame.applications path) = true →
         (ph ≠ .before → target ∉ hdr.shape.attemptSites (Frame.applications path)) →
         hdr.shape.abortsOutsideTarget target (Frame.applications path) (phaseInside ph) = [] →
         (∀ s ∈ hdr.shape.attemptPrivateCoins j target (Frame.applications path) (phaseInside ph), s ∈ insideCoins) →
         (∀ s ∈ hdr.shape.nonAttemptCoinSites j target (Frame.applications path) (phaseInside ph), s ∉ insideCoins) →
         Program.RetryWF M target insideCoins
           (shapeExitPhase target (Frame.applications path) hdr.shape ph) ph (roles hdr c j path args))) :
      ∀ {parts : List Role} {Γ outs} (t : Term (protocolDialect V hs) Γ outs)
        (path : List Frame) (env : Env (RV M r) Γ) (ph : RetryPhase),
        Within parts t →
        (r ∉ parts →
          ((project r t).denote (roleSem M r fns roles) path env).SafeWith M
            (fun _ _ => True) (fun _ => False) (fun _ => True) (fun _ => False)) ∧
        ((shapeOf t).retryAtMostOnce target (Frame.applications path) = true →
         (shapeOf t).retryOwnedBy r target (Frame.applications path) = true →
         (ph ≠ .before → target ∉ (shapeOf t).attemptSites (Frame.applications path)) →
         (shapeOf t).abortsOutsideTarget target (Frame.applications path) (phaseInside ph) = [] →
         (∀ s ∈ (shapeOf t).attemptPrivateCoins r target (Frame.applications path) (phaseInside ph), s ∈ insideCoins) →
         (∀ s ∈ (shapeOf t).nonAttemptCoinSites r target (Frame.applications path) (phaseInside ph), s ∉ insideCoins) →
         Program.RetryWF M target insideCoins
           (shapeExitPhase target (Frame.applications path) (shapeOf t) ph) ph
           ((project r t).denote (roleSem M r fns roles) path env))
    | _, _, _, .ret _, _, _, ph, _ =>
        ⟨fun _ => trivial, fun _ _ _ _ _ _ => by cases ph <;> simp [project, Term.denote_ret, Program.RetryWF, shapeExitPhase, shapeOf, Shape.attemptSites]⟩
    | parts, _, _, .op key o operands results rest, path, env, ph, hW => by
        have hRestAll := fun env' ph' =>
          project_retryWF r target insideCoins fns hFns roles hCallee rest path env' ph' hW.2
        refine ⟨?_, ?_⟩
        · intro hOut
          rw [project]
          cases o with
          | compute R op _ types held =>
              dsimp only [ProtocolOp.project]
              split
              · rename_i hInR; exact absurd (hW.1 r hInR) hOut
              · rw [Term.denote_op, Process.safeWith_bind]
                dsimp only [roleSem, roleOp]
                exact (hRestAll _ ph).1 hOut
          | narrow R among =>
              dsimp only [ProtocolOp.project]
              split
              · rw [Term.denote_op, Process.safeWith_bind]
                cases env.all operands with | cons _ hNil => cases hNil; dsimp only [roleSem, roleOp]; exact (hRestAll _ ph).1 hOut
              · rw [Term.denote_op, Process.safeWith_bind]
                dsimp only [roleSem, roleOp]
                exact (hRestAll _ ph).1 hOut
          | flow kind giver getters holds unique =>
              dsimp only [ProtocolOp.project]
              split
              · rename_i hEq; exact absurd (hEq ▸ hW.1.1) hOut
              · split
                · rename_i hInG; exact absurd (hW.1.2 r hInG) hOut
                · rw [Term.denote_op, Process.safeWith_bind]
                  cases env.all operands with | cons _ hNil => cases hNil; dsimp only [roleSem, roleOp]; exact (hRestAll _ ph).1 hOut
          | given kind owner hearers _ τ _ _ _ =>
              dsimp only [ProtocolOp.project]
              split
              · rename_i hEq; exact absurd (hEq ▸ hW.1.1) hOut
              · split
                · rename_i hInH; exact absurd (hW.1.2 r hInH) hOut
                · rw [Term.denote_op, Process.safeWith_bind]
                  dsimp only [roleSem, roleOp]
                  exact (hRestAll _ ph).1 hOut
          | @apply hdr callee peers distinct covers _ fits =>
              dsimp only [ProtocolOp.project]
              rw [Term.denote_op, Process.safeWith_bind]
              refine Process.safeWith_mono M (P₁ := fun _ => True) (R₁ := fun _ => False)
                (fun _ _ h => h) (fun _ h => h)
                (fun ys _ => (hRestAll (env.extend results ys) ph).1 hOut) (fun _ h => h) ?_
              dsimp only [roleSem, roleOp]
              rw [Process.safeWith_map]
              let ρ := RoleMap.ofList peers distinct
              have hNotMem : r ∉ peers := fun hm => hOut (hW.1 r hm)
              have hGe := RoleMap.ofList_back peers distinct hNotMem
              rw [covers] at hGe
              have hNotInR : ρ.back r ∉ List.range hdr.roles := fun hm =>
                Nat.not_lt.mpr hGe (List.mem_range.mp hm)
              exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
                (fun _ _ => trivial) (fun _ h => h)
                (safeWith_quiet_mapR M ρ.to ((hCallee hdr callee (ρ.back r) _ _ ph).1 hNotInR))
        · intro hOnce hOwned hNotBef hAb hInC hOutC
          rw [project]
          cases o with
          | compute R op _ types held =>
              simp only [shapeOf, ProtocolOp.shape] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
              dsimp only [ProtocolOp.project]
              split
              · rw [Term.denote_op]
                refine retryWF_bind M (P := (· = ph)) ?_ (fun ph' ys hEq => ?_)
                · dsimp only [roleSem, roleOp]
                  refine retryWF_map M _ (retryWF_liftLocal M ?_)
                  cases op with
                  | row k sig kn => dsimp only [localOp]; cases M.apply k sig kn _ <;> trivial
                  | owned o' => exact ownedOp_noAbort M o' _
                  | literal _ _ _ => trivial
                  | call c => exact hFns _ c _
                · subst hEq
                  exact (hRestAll _ ph').2 hOnce hOwned hNotBef hAb hInC hOutC
              · rw [Term.denote_op]
                dsimp only [roleSem, roleOp, Process.bind]
                exact (hRestAll _ ph).2 hOnce hOwned hNotBef hAb hInC hOutC
          | narrow R among =>
              simp only [shapeOf, ProtocolOp.shape] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
              dsimp only [ProtocolOp.project]
              split
              · rw [Term.denote_op]
                cases env.all operands with
                | cons _ hNil =>
                    cases hNil; dsimp only [roleSem, roleOp, Process.bind]
                    exact (hRestAll _ ph).2 hOnce hOwned hNotBef hAb hInC hOutC
              · rw [Term.denote_op]
                dsimp only [roleSem, roleOp, Process.bind]
                exact (hRestAll _ ph).2 hOnce hOwned hNotBef hAb hInC hOutC
          | flow kind giver getters holds unique =>
              simp only [shapeOf, ProtocolOp.shape, Shape.retryAtMostOnce, Shape.retryOwnedBy, Shape.attemptSites,
                Shape.abortsOutsideTarget, Shape.attemptPrivateCoins, Shape.nonAttemptCoinSites,
                List.nil_append] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
              dsimp only [ProtocolOp.project]
              split
              · rw [Term.denote_op]
                cases env.all operands with
                | cons _ hNil =>
                    cases hNil; dsimp only [roleSem, roleOp, Process.bind]
                    exact fun _ => (hRestAll _ ph).2 hOnce hOwned hNotBef hAb hInC hOutC
              · split
                · rw [Term.denote_op]
                  dsimp only [roleSem, roleOp, Process.bind]
                  exact fun _ => (hRestAll _ ph).2 hOnce hOwned hNotBef hAb hInC hOutC
                · rw [Term.denote_op]
                  cases env.all operands with
                  | cons _ hNil =>
                      cases hNil; dsimp only [roleSem, roleOp, Process.bind]
                      exact (hRestAll _ ph).2 hOnce hOwned hNotBef hAb hInC hOutC
          | given gkind owner hearers _ τ _ _ _ =>
              simp only [shapeOf, ProtocolOp.shape, Shape.retryAtMostOnce, Shape.retryOwnedBy, Shape.attemptSites,
                Shape.abortsOutsideTarget, Shape.attemptPrivateCoins, Shape.nonAttemptCoinSites] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
              have hInCR : ∀ s ∈ (shapeOf rest).attemptPrivateCoins r target (Frame.applications path) (phaseInside ph), s ∈ insideCoins :=
                fun s hs => hInC s (List.mem_append_right _ hs)
              have hOutCR : ∀ s ∈ (shapeOf rest).nonAttemptCoinSites r target (Frame.applications path) (phaseInside ph), s ∉ insideCoins :=
                fun s hs => hOutC s (List.mem_append_right _ hs)
              dsimp only [ProtocolOp.project]
              split
              · rename_i hOwnEq
                subst hOwnEq
                rw [Term.denote_op]
                dsimp only [roleSem, roleOp, Process.bind]
                cases gkind with
                | coin law =>
                    cases hearers with
                    | nil =>
                        cases ph with
                        | before =>
                            refine ⟨?_, fun _ => (hRestAll _ .before).2 hOnce hOwned hNotBef hAb hInCR hOutCR⟩
                            exact hOutC _ (List.mem_append_left _ (by simp [phaseInside, Occurrence.site]))
                        | inside =>
                            refine ⟨?_, fun _ => (hRestAll _ .inside).2 hOnce hOwned hNotBef hAb hInCR hOutCR⟩
                            exact hInC _ (List.mem_append_left _ (by simp [phaseInside, Occurrence.site]))
                        | after =>
                            refine ⟨?_, fun _ => (hRestAll _ .after).2 hOnce hOwned hNotBef hAb hInCR hOutCR⟩
                            exact hOutC _ (List.mem_append_left _ (by simp [phaseInside, Occurrence.site]))
                    | cons _ _ => exact fun _ => (hRestAll _ ph).2 hOnce hOwned hNotBef hAb hInCR hOutCR
                | request svc =>
                    refine ⟨?_, fun _ => (hRestAll _ ph).2 hOnce hOwned hNotBef hAb hInCR hOutCR⟩
                    exact hOutC _ (List.mem_append_left _ List.mem_cons_self)
              · split
                · rw [Term.denote_op]
                  dsimp only [roleSem, roleOp, Process.bind]
                  exact fun _ => (hRestAll _ ph).2 hOnce hOwned hNotBef hAb hInCR hOutCR
                · rw [Term.denote_op]
                  dsimp only [roleSem, roleOp, Process.bind]
                  exact (hRestAll _ ph).2 hOnce hOwned hNotBef hAb hInCR hOutCR
          | @apply hdr callee peers distinct covers _ fits =>
              simp only [shapeOf, ProtocolOp.shape, Shape.retryAtMostOnce, Shape.retryOwnedBy, Shape.attemptSites,
                Shape.abortsOutsideTarget, Shape.attemptPrivateCoins, Shape.nonAttemptCoinSites,
                Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
                List.append_eq_nil_iff] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
              dsimp only [ProtocolOp.project]
              rw [Term.denote_op]
              let ρ := RoleMap.ofList peers distinct
              have hApp : Frame.applications (path ++ [.application key]) = Frame.applications path ++ [key] := by
                rw [frame_applications_append_retry]; rfl
              have hNotBefI : ph ≠ .before → target ∉ hdr.shape.attemptSites (Frame.applications path ++ [key]) :=
                fun hne hm => hNotBef hne (List.mem_append_left _ hm)
              have hNotBefR : ph ≠ .before → target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
                fun hne hm => hNotBef hne (List.mem_append_right _ hm)
              have hInCR : ∀ s ∈ (shapeOf rest).attemptPrivateCoins r target (Frame.applications path) (phaseInside ph), s ∈ insideCoins :=
                fun s hs => hInC s (List.mem_append_right _ hs)
              have hOutCR : ∀ s ∈ (shapeOf rest).nonAttemptCoinSites r target (Frame.applications path) (phaseInside ph), s ∉ insideCoins :=
                fun s hs => hOutC s (List.mem_append_right _ hs)
              by_cases hMem : r ∈ peers
              · obtain ⟨j, hj, hPj⟩ := List.getElem_of_mem hMem
                have hBack : ρ.back r = j := by
                  have hTo := RoleMap.ofList_to peers distinct j hj
                  rw [hPj] at hTo
                  have := congrArg ρ.back hTo; rw [ρ.left] at this; exact this.symm
                have hFilt := range_filter_getD_eq_singleton peers distinct hj hPj
                rw [hFilt] at hOwned hInC hOutC
                have hInCI : ∀ s ∈ hdr.shape.attemptPrivateCoins j target (Frame.applications path ++ [key]) (phaseInside ph), s ∈ insideCoins :=
                  fun s hs => hInC s (List.mem_append_left _ hs)
                have hOutCI : ∀ s ∈ hdr.shape.nonAttemptCoinSites j target (Frame.applications path ++ [key]) (phaseInside ph), s ∉ insideCoins :=
                  fun s hs => hOutC s (List.mem_append_left _ hs)
                have hCallWF := (hCallee hdr callee (ρ.back r) (path ++ [.application key])
                  (enterAll M ρ r (fitAllRV M fits (env.all operands))) ph).2
                  (by rw [hApp]; exact hOnce.1.1)
                  (by rw [hBack, hApp]; exact hOwned.1)
                  (by rw [hApp]; exact hNotBefI)
                  (by rw [hApp]; exact hAb.1)
                  (by rw [hBack, hApp]; exact hInCI)
                  (by rw [hBack, hApp]; exact hOutCI)
                rw [hApp] at hCallWF
                refine retryWF_bind M (retryWF_map M _ (retryWF_mapR M ρ.to hCallWF)) ?_
                intro ph' ys hPh'
                refine retryWF_mono M (fun ph'' hPh'' => by
                  cases ph <;> simp only [shapeExitPhase, Shape.attemptSites, List.mem_append] at hPh'' ⊢ <;> exact hPh'')
                  (retryWF_seq_combine M (insideCoins := insideCoins) (s₁ := hdr.shape) (s₂ := shapeOf rest)
                    (f := fun _ => Term.denote (roleSem M r fns roles) (project r rest) path (env.extend results ys))
                    hOnce.2
                    (fun hB => by subst hB; exact (hRestAll (env.extend results ys) .before).2 hOnce.1.2 hOwned.2 (fun h => absurd rfl h) hAb.2 hInCR hOutCR)
                    (fun hI => by subst hI; exact (hRestAll (env.extend results ys) .inside).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR)
                    (fun hA => by
                      rcases hA with rfl | ⟨rfl, hInI⟩
                      · exact (hRestAll (env.extend results ys) .after).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR
                      · have hNotR : target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
                          hOnce.2.resolve_left (fun h => h hInI)
                        exact (hRestAll (env.extend results ys) .after).2 hOnce.1.2 hOwned.2 (fun _ => hNotR) hAb.2 hInCR hOutCR)
                    ph' hPh')
              · have hGe := RoleMap.ofList_back peers distinct hMem
                rw [covers] at hGe
                have hNotInR : ρ.back r ∉ List.range hdr.roles := fun hm =>
                  Nat.not_lt.mpr hGe (List.mem_range.mp hm)
                have hQuiet := (hCallee hdr callee (ρ.back r) (path ++ [.application key])
                  (enterAll M ρ r (fitAllRV M fits (env.all operands))) ph).1 hNotInR
                have hCallWF : Program.RetryWF M target insideCoins (· = ph) ph
                    ((mapR M ρ.to (roles hdr callee (ρ.back r) (path ++ [.application key])
                      (enterAll M ρ r (fitAllRV M fits (env.all operands))))).map (leaveAll M ρ r)) :=
                  retryWF_map M (leaveAll M ρ r) (retryWF_of_quiet M (safeWith_quiet_mapR M ρ.to hQuiet))
                refine retryWF_bind M hCallWF (fun ph' ys hEq => ?_)
                subst hEq
                exact retryWF_mono M (fun p0 hp0 => by
                  cases ph' with
                  | inside => exact hp0
                  | after => exact hp0
                  | before =>
                      dsimp only [shapeExitPhase] at hp0 ⊢
                      by_cases hInR : target ∈ (shapeOf rest).attemptSites (Frame.applications path)
                      · rw [ite_eq_left hInR] at hp0
                        have hInBoth : target ∈ (Shape.apply key hdr.key peers hdr.shape (shapeOf rest)).attemptSites (Frame.applications path) :=
                          List.mem_append_right _ hInR
                        rw [ite_eq_left hInBoth]; exact hp0
                      · rw [ite_eq_right hInR] at hp0
                        by_cases hInBoth : target ∈ (Shape.apply key hdr.key peers hdr.shape (shapeOf rest)).attemptSites (Frame.applications path)
                        · rw [ite_eq_left hInBoth]; exact .inl hp0
                        · rw [ite_eq_right hInBoth]; exact hp0)
                  ((hRestAll _ ph').2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR)
    | parts, _, _, .guard key w c ok why rest, path, env, ph, hW => by
        have hRestAll := project_retryWF r target insideCoins fns hFns roles hCallee rest path env ph hW.2
        refine ⟨?_, ?_⟩
        · intro hOut
          rw [project]; dsimp only [project]
          split
          · rename_i hInW; exact absurd (hW.1 r hInW) hOut
          · exact hRestAll.1 hOut
        · intro hOnce hOwned hNotBef hAb hInC hOutC
          simp only [shapeOf, Shape.retryAtMostOnce, Shape.retryOwnedBy, Shape.attemptSites, Shape.abortsOutsideTarget,
            Shape.attemptPrivateCoins, Shape.nonAttemptCoinSites, List.append_eq_nil_iff] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
          rw [project]; dsimp only [project]
          split
          · rw [Term.denote_guard]
            cases (roleSem M r fns roles).holds _ (env.get c)
            · cases ph with
              | inside => trivial
              | before =>
                  show (Stop.declared why ⟨path, key⟩).isAbort = false
                  cases why with
                  | abort =>
                      have hHere := hAb.1
                      simp [phaseInside] at hHere
                  | reject | exhausted | refused => rfl
              | after =>
                  show (Stop.declared why ⟨path, key⟩).isAbort = false
                  cases why with
                  | abort =>
                      have hHere := hAb.1
                      simp [phaseInside] at hHere
                  | reject | exhausted | refused => rfl
            · exact hRestAll.2 hOnce hOwned hNotBef hAb.2 hInC hOutC
          · exact hRestAll.2 hOnce hOwned hNotBef hAb.2 hInC hOutC
    | parts, _, _, .choose key w c ok gives onTrue onFalse results rest, path, env, ph, hW => by
        have hTAll := fun ph' => project_retryWF r target insideCoins fns hFns roles hCallee onTrue path env ph' hW.2.1
        have hFAll := fun ph' => project_retryWF r target insideCoins fns hFns roles hCallee onFalse path env ph' hW.2.2.1
        have hRAll := fun env' ph' => project_retryWF r target insideCoins fns hFns roles hCallee rest path env' ph' hW.2.2.2
        refine ⟨?_, ?_⟩
        · intro hOut
          rw [project]; dsimp only [project]
          split
          · rename_i hInW; exact absurd (hW.1 r hInW) hOut
          · rw [Term.denote_op, Process.safeWith_bind]
            exact (hRAll _ ph).1 hOut
        · intro hOnce hOwned hNotBef hAb hInC hOutC
          simp only [shapeOf, Shape.retryAtMostOnce, Shapes.retryAtMostOnce, Shape.retryOwnedBy, Shapes.retryOwnedBy,
            Shape.attemptSites, Shapes.attemptSites, Shape.abortsOutsideTarget, Shapes.abortsOutsideTarget,
            Shape.attemptPrivateCoins, Shapes.attemptPrivateCoins,
            Shape.nonAttemptCoinSites, Shapes.nonAttemptCoinSites,
            List.append_nil, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
            decide_eq_false_iff_not, List.append_eq_nil_iff] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
          have hNotBefT : ph ≠ .before → target ∉ (shapeOf onTrue).attemptSites (Frame.applications path) :=
            fun hne hm => hNotBef hne (List.mem_append_left _ (List.mem_append_left _ hm))
          have hNotBefF : ph ≠ .before → target ∉ (shapeOf onFalse).attemptSites (Frame.applications path) :=
            fun hne hm => hNotBef hne (List.mem_append_left _ (List.mem_append_right _ hm))
          have hNotBefR : ph ≠ .before → target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
            fun hne hm => hNotBef hne (List.mem_append_right _ hm)
          have hInCT := fun s hs => hInC s (List.mem_append_left _ (List.mem_append_left _ hs))
          have hInCF := fun s hs => hInC s (List.mem_append_left _ (List.mem_append_right _ hs))
          have hInCR := fun s hs => hInC s (List.mem_append_right _ hs)
          have hOutCT := fun s hs => hOutC s (List.mem_append_left _ (List.mem_append_left _ hs))
          have hOutCF := fun s hs => hOutC s (List.mem_append_left _ (List.mem_append_right _ hs))
          have hOutCR := fun s hs => hOutC s (List.mem_append_right _ hs)
          rw [project]; dsimp only [project]
          split
          · rw [Term.denote_choose]
            refine retryWF_bind M (P := shapesExitPhase target (Frame.applications path)
                (.cons (shapeOf onTrue) (.cons (shapeOf onFalse) .nil)) ph) ?_ ?_
            · cases (roleSem M r fns roles).holds _ (env.get c)
              · exact retryWF_mono M (fun p0 hp0 => by
                  cases ph with
                  | inside => exact hp0
                  | after => exact hp0
                  | before =>
                      simp only [shapeExitPhase, shapesExitPhase, Shapes.attemptSites, List.append_nil,
                        List.mem_append] at hp0 ⊢
                      by_cases hInF : target ∈ (shapeOf onFalse).attemptSites (Frame.applications path)
                      · simp only [hInF, or_true, ite_true] at hp0 ⊢; exact hp0
                      · simp only [hInF, or_false, ite_false] at hp0 ⊢
                        by_cases hInT : target ∈ (shapeOf onTrue).attemptSites (Frame.applications path)
                        · simp only [hInT, ite_true]; exact .inl hp0
                        · simp only [hInT, ite_false]; exact hp0)
                  ((hFAll ph).2 hOnce.1.1.2 hOwned.1.2 hNotBefF hAb.1.2 hInCF hOutCF)
              · exact retryWF_mono M (fun p0 hp0 => by
                  cases ph with
                  | inside => exact hp0
                  | after => exact hp0
                  | before =>
                      simp only [shapeExitPhase, shapesExitPhase, Shapes.attemptSites, List.append_nil,
                        List.mem_append] at hp0 ⊢
                      by_cases hInT : target ∈ (shapeOf onTrue).attemptSites (Frame.applications path)
                      · simp only [hInT, true_or, ite_true] at hp0 ⊢; exact hp0
                      · simp only [hInT, false_or, ite_false] at hp0 ⊢
                        by_cases hInF : target ∈ (shapeOf onFalse).attemptSites (Frame.applications path)
                        · simp only [hInF, ite_true]; exact .inl hp0
                        · simp only [hInF, ite_false]; exact hp0)
                  ((hTAll ph).2 hOnce.1.1.1 hOwned.1.1 hNotBefT hAb.1.1 hInCT hOutCT)
            · intro ph' ys hPh'
              have hArmsDisj : target ∉ ((shapeOf onTrue).attemptSites (Frame.applications path) ++
                  (shapeOf onFalse).attemptSites (Frame.applications path)) ∨
                  target ∉ (shapeOf rest).attemptSites (Frame.applications path) := hOnce.2
              cases ph with
              | inside =>
                  dsimp only [shapesExitPhase] at hPh'; subst hPh'
                  exact (hRAll _ .inside).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR
              | after =>
                  dsimp only [shapesExitPhase] at hPh'; subst hPh'
                  exact (hRAll _ .after).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR
              | before =>
                  simp only [shapesExitPhase, Shapes.attemptSites, List.append_nil] at hPh'
                  by_cases hInA : target ∈ (shapeOf onTrue).attemptSites (Frame.applications path) ++
                      (shapeOf onFalse).attemptSites (Frame.applications path)
                  · simp only [hInA, ite_true] at hPh'
                    have hNotR : target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
                      hArmsDisj.resolve_left (fun h => h hInA)
                    rcases hPh' with rfl | rfl
                    · exact retryWF_mono M (fun p0 hp0 => by
                        simp only [shapeExitPhase, Shape.attemptSites, Shapes.attemptSites, List.append_nil,
                          List.mem_append, List.mem_append.mp hInA, hNotR, true_or, ite_true, ite_false] at hp0 ⊢
                        exact .inl hp0)
                        ((hRAll _ .before).2 hOnce.1.2 hOwned.2 (fun h => absurd rfl h) hAb.2 hInCR hOutCR)
                    · exact retryWF_mono M (fun p0 hp0 => by
                        simp only [shapeExitPhase, Shape.attemptSites, Shapes.attemptSites, List.append_nil,
                          List.mem_append, List.mem_append.mp hInA, true_or, ite_true] at hp0 ⊢
                        exact .inr hp0)
                        ((hRAll _ .after).2 hOnce.1.2 hOwned.2 (fun _ => hNotR) hAb.2 hInCR hOutCR)
                  · simp only [hInA, ite_false] at hPh'; subst hPh'
                    have hNotT : target ∉ (shapeOf onTrue).attemptSites (Frame.applications path) :=
                      fun h => hInA (List.mem_append_left _ h)
                    have hNotF : target ∉ (shapeOf onFalse).attemptSites (Frame.applications path) :=
                      fun h => hInA (List.mem_append_right _ h)
                    exact retryWF_mono M (fun p0 hp0 => by
                      simp only [shapeExitPhase, Shape.attemptSites, Shapes.attemptSites, List.append_nil,
                        List.mem_append, hNotT, hNotF, false_or] at hp0 ⊢
                      exact hp0)
                      ((hRAll _ .before).2 hOnce.1.2 hOwned.2 (fun h => absurd rfl h) hAb.2 hInCR hOutCR)
          · rw [Term.denote_op]
            dsimp only [roleSem, roleOp, Process.bind]
            exact retryWF_mono M (fun p0 hp0 => by
              cases ph with
              | inside => exact hp0
              | after => exact hp0
              | before =>
                  simp only [shapeExitPhase, Shape.attemptSites, Shapes.attemptSites, List.append_nil,
                    List.mem_append] at hp0 ⊢
                  by_cases hInR : target ∈ (shapeOf rest).attemptSites (Frame.applications path)
                  · simp only [hInR, or_true, ite_true] at hp0 ⊢; exact hp0
                  · simp only [hInR, or_false, ite_false] at hp0 ⊢
                    by_cases hInA : target ∈ (shapeOf onTrue).attemptSites (Frame.applications path) ∨
                        target ∈ (shapeOf onFalse).attemptSites (Frame.applications path)
                    · simp only [hInA, ite_true]; exact .inl hp0
                    · simp only [hInA, ite_false]; exact hp0)
              ((hRAll _ ph).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR)
    | parts, _, _, .cases key w x ok gives arms results rest, path, env, ph, hW => by
        have hAAll := fun p' => projectArms_retryWF r target insideCoins fns hFns roles hCallee arms path env p' ph hW.2.1
        have hRAll := fun env' ph' => project_retryWF r target insideCoins fns hFns roles hCallee rest path env' ph' hW.2.2
        refine ⟨?_, ?_⟩
        · intro hOut
          rw [project]; dsimp only [project]
          split
          · rename_i hInW; exact absurd (hW.1 r hInW) hOut
          · rw [Term.denote_op, Process.safeWith_bind]
            exact (hRAll _ ph).1 hOut
        · intro hOnce hOwned hNotBef hAb hInC hOutC
          simp only [shapeOf, Shape.retryAtMostOnce, Shape.retryOwnedBy, Shape.attemptSites, Shape.abortsOutsideTarget,
            Shape.attemptPrivateCoins, Shape.nonAttemptCoinSites,
            Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
            List.append_eq_nil_iff] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
          have hNotBefA : ph ≠ .before → target ∉ (shapesOf arms).attemptSites (Frame.applications path) :=
            fun hne hm => hNotBef hne (List.mem_append_left _ hm)
          have hNotBefR : ph ≠ .before → target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
            fun hne hm => hNotBef hne (List.mem_append_right _ hm)
          have hInCA := fun s hs => hInC s (List.mem_append_left _ hs)
          have hInCR := fun s hs => hInC s (List.mem_append_right _ hs)
          have hOutCA := fun s hs => hOutC s (List.mem_append_left _ hs)
          have hOutCR := fun s hs => hOutC s (List.mem_append_right _ hs)
          rw [project]; dsimp only [project]
          split
          · rw [Term.denote_cases]
            refine retryWF_bind M ((hAAll _).2 hOnce.1.1 hOwned.1 hNotBefA hAb.1 hInCA hOutCA) ?_
            intro ph' ys hPh'
            cases ph with
            | inside =>
                dsimp only [shapesExitPhase] at hPh'; subst hPh'
                exact (hRAll _ .inside).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR
            | after =>
                dsimp only [shapesExitPhase] at hPh'; subst hPh'
                exact (hRAll _ .after).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR
            | before =>
                dsimp only [shapesExitPhase] at hPh'
                by_cases hInA : target ∈ (shapesOf arms).attemptSites (Frame.applications path)
                · rw [ite_eq_left hInA] at hPh'
                  have hNotR : target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
                    hOnce.2.resolve_left (fun h => h hInA)
                  rcases hPh' with rfl | rfl
                  · exact retryWF_mono M (fun p0 hp0 => by
                      simp only [shapeExitPhase, Shape.attemptSites, List.mem_append, hInA, hNotR,
                        true_or, ite_true, ite_false] at hp0 ⊢
                      exact .inl hp0)
                      ((hRAll _ .before).2 hOnce.1.2 hOwned.2 (fun h => absurd rfl h) hAb.2 hInCR hOutCR)
                  · exact retryWF_mono M (fun p0 hp0 => by
                      simp only [shapeExitPhase, Shape.attemptSites, List.mem_append, hInA,
                        true_or, ite_true] at hp0 ⊢
                      exact .inr hp0)
                      ((hRAll _ .after).2 hOnce.1.2 hOwned.2 (fun _ => hNotR) hAb.2 hInCR hOutCR)
                · rw [ite_eq_right hInA] at hPh'; subst hPh'
                  exact retryWF_mono M (fun p0 hp0 => by
                    simp only [shapeExitPhase, Shape.attemptSites, List.mem_append, hInA, false_or] at hp0 ⊢
                    exact hp0)
                    ((hRAll _ .before).2 hOnce.1.2 hOwned.2 (fun h => absurd rfl h) hAb.2 hInCR hOutCR)
          · rw [Term.denote_op]
            dsimp only [roleSem, roleOp, Process.bind]
            exact retryWF_mono M (fun p0 hp0 => by
              cases ph with
              | inside => exact hp0
              | after => exact hp0
              | before =>
                  simp only [shapeExitPhase, Shape.attemptSites, List.mem_append] at hp0 ⊢
                  by_cases hInR : target ∈ (shapeOf rest).attemptSites (Frame.applications path)
                  · simp only [hInR, or_true, ite_true] at hp0 ⊢; exact hp0
                  · simp only [hInR, or_false, ite_false] at hp0 ⊢
                    by_cases hInA : target ∈ (shapesOf arms).attemptSites (Frame.applications path)
                    · simp only [hInA, ite_true]; exact .inl hp0
                    · simp only [hInA, ite_false]; exact hp0)
              ((hRAll _ ph).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR)
    | parts, _, _, .loop key w times gives initial inputs body results rest, path, env, ph, hW => by
        have hBAll := fun i env' =>
          project_retryWF r target insideCoins fns hFns roles hCallee body (path ++ [.iteration key i]) env' ph hW.2.1
        have hRAll := fun env' =>
          project_retryWF r target insideCoins fns hFns roles hCallee rest path env' ph hW.2.2
        refine ⟨?_, ?_⟩
        · intro hOut
          rw [project]; dsimp only [project]
          split
          · rename_i hInW; exact absurd (hW.1 r hInW) hOut
          · rw [Term.denote_op, Process.safeWith_bind]
            exact (hRAll _).1 hOut
        · intro hOnce hOwned hNotBef hAb hInC hOutC
          simp only [shapeOf, Shape.retryAtMostOnce, Shape.retryOwnedBy, Shape.attemptSites, Shape.abortsOutsideTarget,
            Shape.attemptPrivateCoins, Shape.nonAttemptCoinSites,
            Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
            List.append_eq_nil_iff] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
          have hNotInB : target ∉ (shapeOf body).attemptSites (Frame.applications path) := hOnce.1
          have hOnceB : (shapeOf body).retryAtMostOnce target (Frame.applications path) = true :=
            shape_retryAtMostOnce_of_not_mem target (shapeOf body) (Frame.applications path) hNotInB
          have hNotBefR : ph ≠ .before → target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
            fun hne hm => hNotBef hne (List.mem_append_right _ hm)
          have hInCB := fun s hs => hInC s (List.mem_append_left _ hs)
          have hInCR := fun s hs => hInC s (List.mem_append_right _ hs)
          have hOutCB := fun s hs => hOutC s (List.mem_append_left _ hs)
          have hOutCR := fun s hs => hOutC s (List.mem_append_right _ hs)
          rw [project]; dsimp only [project]
          split
          · cases times with
            | fixed n =>
                dsimp only [projectLoop]
                erw [Term.denote_loop]
                refine retryWF_bind M (P := (· = ph)) ?_ (fun ph' st hEq => ?_)
                · exact retryWF_iterate M (ph := ph) (fun i st => by
                    simp only [Semantics.loopStep]
                    have hApp : Frame.applications (path ++ [.iteration key i]) = Frame.applications path := by
                      rw [frame_applications_append_retry]; simp [Frame.applications]
                    have hBW := (hBAll i (env.extend inputs (.cons (hide M r (LTy.index w) i) st.1))).2
                      (by rw [hApp]; exact hOnceB) (by rw [hApp]; exact hOwned.1)
                      (fun _ => by rw [hApp]; exact hNotInB) (by rw [hApp]; exact hAb.1)
                      (by rw [hApp]; exact hInCB) (by rw [hApp]; exact hOutCB)
                    refine retryWF_bind M (retryWF_mono M (fun p0 hp0 => by
                      rw [hApp] at hp0
                      cases ph with
                      | inside => exact hp0
                      | after => exact hp0
                      | before => dsimp only [shapeExitPhase] at hp0; rw [ite_eq_right hNotInB] at hp0; exact hp0) hBW)
                      (fun p0 _ hp0 => hp0)) _ 0 _
                · cases hEq
                  exact retryWF_mono M (fun p0 hp0 => by
                    cases ph with
                    | inside => exact hp0
                    | after => exact hp0
                    | before =>
                        simp only [shapeExitPhase, Shape.attemptSites, List.mem_append, hNotInB, false_or] at hp0 ⊢
                        exact hp0)
                    ((hRAll _).2 hOnce.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR)
            | value count ok =>
                dsimp only [projectLoop]
                erw [Term.denote_loop]
                refine retryWF_bind M (P := (· = ph)) ?_ (fun ph' st hEq => ?_)
                · exact retryWF_iterate M (ph := ph) (fun i st => by
                    simp only [Semantics.loopStep]
                    have hApp : Frame.applications (path ++ [.iteration key i]) = Frame.applications path := by
                      rw [frame_applications_append_retry]; simp [Frame.applications]
                    have hBW := (hBAll i (env.extend inputs (.cons (hide M r (LTy.index w) i) st.1))).2
                      (by rw [hApp]; exact hOnceB) (by rw [hApp]; exact hOwned.1)
                      (fun _ => by rw [hApp]; exact hNotInB) (by rw [hApp]; exact hAb.1)
                      (by rw [hApp]; exact hInCB) (by rw [hApp]; exact hOutCB)
                    refine retryWF_bind M (retryWF_mono M (fun p0 hp0 => by
                      rw [hApp] at hp0
                      cases ph with
                      | inside => exact hp0
                      | after => exact hp0
                      | before => dsimp only [shapeExitPhase] at hp0; rw [ite_eq_right hNotInB] at hp0; exact hp0) hBW)
                      (fun p0 _ hp0 => hp0)) _ 0 _
                · cases hEq
                  exact retryWF_mono M (fun p0 hp0 => by
                    cases ph with
                    | inside => exact hp0
                    | after => exact hp0
                    | before =>
                        simp only [shapeExitPhase, Shape.attemptSites, List.mem_append, hNotInB, false_or] at hp0 ⊢
                        exact hp0)
                    ((hRAll _).2 hOnce.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR)
          · rw [Term.denote_op]
            dsimp only [roleSem, roleOp, Process.bind]
            exact retryWF_mono M (fun p0 hp0 => by
              cases ph with
              | inside => exact hp0
              | after => exact hp0
              | before =>
                  simp only [shapeExitPhase, Shape.attemptSites, List.mem_append, hNotInB, false_or] at hp0 ⊢
                  exact hp0)
              ((hRAll _).2 hOnce.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR)
    | parts, _, _, .block key number body results rest, path, env, ph, hW => by
        have hApp : Frame.applications (path ++ [.iteration key number]) = Frame.applications path := by
          rw [frame_applications_append_retry]; simp [Frame.applications]
        have hBAll := project_retryWF r target insideCoins fns hFns roles hCallee body
          (path ++ [.iteration key number]) env ph hW.1
        have hRAll := fun env' ph' =>
          project_retryWF r target insideCoins fns hFns roles hCallee rest path env' ph' hW.2
        refine ⟨?_, ?_⟩
        · intro hOut
          rw [project, Term.denote_block, Process.safeWith_bind]
          exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
            (fun ys _ => (hRAll _ ph).1 hOut) (fun _ h => h) (hBAll.1 hOut)
        · intro hOnce hOwned hNotBef hAb hInC hOutC
          simp only [shapeOf, Shape.retryAtMostOnce, Shape.retryOwnedBy, Shape.attemptSites, Shape.abortsOutsideTarget,
            Shape.attemptPrivateCoins, Shape.nonAttemptCoinSites,
            Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
            List.append_eq_nil_iff] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
          have hNotBefB : ph ≠ .before → target ∉ (shapeOf body).attemptSites (Frame.applications path) :=
            fun hne hm => hNotBef hne (List.mem_append_left _ hm)
          have hNotBefR : ph ≠ .before → target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
            fun hne hm => hNotBef hne (List.mem_append_right _ hm)
          have hInCB := fun s hs => hInC s (List.mem_append_left _ hs)
          have hInCR := fun s hs => hInC s (List.mem_append_right _ hs)
          have hOutCB := fun s hs => hOutC s (List.mem_append_left _ hs)
          have hOutCR := fun s hs => hOutC s (List.mem_append_right _ hs)
          rw [project, Term.denote_block]
          have hBW := hBAll.2 (by rw [hApp]; exact hOnce.1.1) (by rw [hApp]; exact hOwned.1) (by rw [hApp]; exact hNotBefB)
            (by rw [hApp]; exact hAb.1) (by rw [hApp]; exact hInCB) (by rw [hApp]; exact hOutCB)
          rw [hApp] at hBW
          refine retryWF_bind M hBW (fun ph' ys hPh' => ?_)
          refine retryWF_mono M (fun ph'' hPh'' => by
            cases ph <;> simp only [shapeExitPhase, Shape.attemptSites, List.mem_append] at hPh'' ⊢ <;> exact hPh'')
            (retryWF_seq_combine M (insideCoins := insideCoins) (s₁ := shapeOf body) (s₂ := shapeOf rest)
              (f := fun _ => Term.denote (roleSem M r fns roles) (project r rest) path (env.extend results ys))
              hOnce.2
              (fun hB => by subst hB; exact (hRAll (env.extend results ys) .before).2 hOnce.1.2 hOwned.2 (fun h => absurd rfl h) hAb.2 hInCR hOutCR)
              (fun hI => by subst hI; exact (hRAll (env.extend results ys) .inside).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR)
              (fun hA => by
                rcases hA with rfl | ⟨rfl, hInB⟩
                · exact (hRAll (env.extend results ys) .after).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR
                · have hNotR : target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
                    hOnce.2.resolve_left (fun h => h hInB)
                  exact (hRAll (env.extend results ys) .after).2 hOnce.1.2 hOwned.2 (fun _ => hNotR) hAb.2 hInCR hOutCR)
              ph' hPh')
    | parts, _, _, .attempt key w owns inputs body results rest, path, env, ph, hW => by
        have hBAll := fun env' ph' =>
          project_retryWF r target insideCoins fns hFns roles hCallee body path env' ph' hW.2.1
        have hRAll := fun env' ph' =>
          project_retryWF r target insideCoins fns hFns roles hCallee rest path env' ph' hW.2.2
        refine ⟨?_, ?_⟩
        · intro hOut
          rw [project, Term.denote_attempt]
          have hNotW : r ∉ w := fun hm => hOut (hW.1 r hm)
          have hBeg : (roleSem M r fns roles).begin w key path = .done (hide M r (LTy.index w) 0) := by
            dsimp only [roleSem]; exact ite_eq_right hNotW
          rw [hBeg]
          dsimp only [Process.bind]
          rw [Process.safeWith_bind]
          refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun mids _ => ?_) (fun _ h => h)
            ((hBAll _ ph).1 hOut)
          rw [ite_eq_right hNotW]
          exact (hRAll _ ph).1 hOut
        · intro hOnce hOwned hNotBef hAb hInC hOutC
          simp only [shapeOf, Shape.retryAtMostOnce, Shape.retryOwnedBy, Shape.attemptSites, Shape.abortsOutsideTarget,
            Shape.attemptPrivateCoins, Shape.nonAttemptCoinSites,
            Bool.and_eq_true, List.append_eq_nil_iff] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
          rw [project, Term.denote_attempt]
          by_cases hIsT : (⟨Frame.applications path, key⟩ : Site) = target
          · -- This attempt IS `target`!
            have hPhBef : ph = .before := by
              cases ph with
              | before => rfl
              | inside => exact absurd (by rw [← hIsT]; exact List.mem_cons_self) (hNotBef (by decide))
              | after => exact absurd (by rw [← hIsT]; exact List.mem_cons_self) (hNotBef (by decide))
            subst hPhBef
            rw [ite_eq_left hIsT] at hOnce
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hOnce
            have hInBodyTrue : (phaseInside .before || decide (⟨Frame.applications path, key⟩ = target)) = true := by
              simp [phaseInside, hIsT]
            rw [hInBodyTrue] at hAb hInC hOutC
            have hOnceB := shape_retryAtMostOnce_of_not_mem target (shapeOf body) (Frame.applications path) hOnce.1
            have hOnceR := shape_retryAtMostOnce_of_not_mem target (shapeOf rest) (Frame.applications path) hOnce.2
            have hInCB := fun s hs => hInC s (List.mem_append_left _ hs)
            have hInCR := fun s hs => hInC s (List.mem_append_right _ hs)
            have hOutCB := fun s hs => hOutC s (List.mem_append_left _ hs)
            have hOutCR := fun s hs => hOutC s (List.mem_append_right _ hs)
            have hInW : r ∈ w := by
              have h := hOwned.1.1
              simp [hIsT] at h
              exact h
            have hBeg : (roleSem M r fns roles).begin w key path =
                .call (.begin ⟨path, key⟩) (fun n => .done (hide M r (LTy.index w) n)) := by
              dsimp only [roleSem]; exact ite_eq_left hInW
            rw [hBeg]
            simp only [Process.bind, Program.RetryWF, Occurrence.site, hIsT, ite_true]
            intro n
            have hBW := (hBAll (env.extend inputs (.cons (hide M r (LTy.index w) n) .nil)) .inside).2
              hOnceB hOwned.1.2 (fun _ => hOnce.1) hAb.1 hInCB hOutCB
            refine retryWF_bind M hBW (fun ph1 mids hPh1 => ?_)
            dsimp only [shapeExitPhase] at hPh1; subst hPh1
            rw [ite_eq_left hInW]
            simp only [Process.bind, Program.RetryWF, Occurrence.site, hIsT, ite_true]
            intro _
            have hRW := (hRAll (env.extend results mids) .after).2
              hOnceR hOwned.2 (fun _ => hOnce.2) hAb.2 hInCR hOutCR
            exact retryWF_mono M (fun ph2 hPh2 => by
              simp only [shapeExitPhase, Shape.attemptSites, List.mem_cons, hIsT.symm, true_or, ite_true] at hPh2 ⊢
              exact .inr hPh2) hRW
          · -- This attempt is NOT `target`!
            rw [ite_eq_right hIsT] at hOnce
            simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hOnce
            have hInBodyEq : (phaseInside ph || decide (⟨Frame.applications path, key⟩ = target)) = phaseInside ph := by
              simp [hIsT]
            rw [hInBodyEq] at hAb hInC hOutC
            have hNotBefB : ph ≠ .before → target ∉ (shapeOf body).attemptSites (Frame.applications path) :=
              fun hne hm => hNotBef hne (List.mem_cons_of_mem _ (List.mem_append_left _ hm))
            have hNotBefR : ph ≠ .before → target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
              fun hne hm => hNotBef hne (List.mem_cons_of_mem _ (List.mem_append_right _ hm))
            have hInCB := fun s hs => hInC s (List.mem_append_left _ hs)
            have hInCR := fun s hs => hInC s (List.mem_append_right _ hs)
            have hOutCB := fun s hs => hOutC s (List.mem_append_left _ hs)
            have hOutCR := fun s hs => hOutC s (List.mem_append_right _ hs)
            have hBegWF : Program.RetryWF M target insideCoins (· = ph) ph
                ((roleSem M r fns roles).begin w key path) := by
              dsimp only [roleSem]
              split
              · cases ph with
                | before => simp only [Program.RetryWF, Occurrence.site, hIsT, ite_false]; intro _; trivial
                | inside => exact ⟨hIsT, fun _ => rfl⟩
                | after => exact ⟨hIsT, fun _ => rfl⟩
              · exact rfl
            have hSetWF : ∀ ph1, Program.RetryWF M target insideCoins (· = ph1) ph1
                ((roleSem M r fns roles).settle w key path) := by
              intro ph1
              dsimp only [roleSem]
              split
              · cases ph1 with
                | before => exact ⟨hIsT, fun _ => rfl⟩
                | inside => simp only [Program.RetryWF, Occurrence.site, hIsT, ite_false]; intro _; trivial
                | after => exact ⟨hIsT, fun _ => rfl⟩
              · exact rfl
            refine retryWF_bind M hBegWF (fun ph0 n hPh0 => ?_)
            cases hPh0
            have hBW := (hBAll (env.extend inputs (.cons n .nil)) ph).2 hOnce.1.1 hOwned.1.2 hNotBefB hAb.1 hInCB hOutCB
            refine retryWF_bind M hBW (fun ph1 mids hPh1 => ?_)
            refine retryWF_bind M (hSetWF ph1) (fun ph2 _ hPh2 => ?_)
            cases hPh2
            refine retryWF_mono M (fun ph3 hPh3 => ?_)
              (retryWF_seq_combine M (insideCoins := insideCoins) (s₁ := shapeOf body) (s₂ := shapeOf rest)
                (f := fun _ => Term.denote (roleSem M r fns roles) (project r rest) path (env.extend results mids))
                hOnce.2
                (fun hB => by subst hB; exact (hRAll (env.extend results mids) .before).2 hOnce.1.2 hOwned.2 (fun h => absurd rfl h) hAb.2 hInCR hOutCR)
                (fun hI => by subst hI; exact (hRAll (env.extend results mids) .inside).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR)
                (fun hA => by
                  rcases hA with rfl | ⟨rfl, hInB⟩
                  · exact (hRAll (env.extend results mids) .after).2 hOnce.1.2 hOwned.2 hNotBefR hAb.2 hInCR hOutCR
                  · have hNotR : target ∉ (shapeOf rest).attemptSites (Frame.applications path) :=
                      hOnce.2.resolve_left (fun h => h hInB)
                    exact (hRAll (env.extend results mids) .after).2 hOnce.1.2 hOwned.2 (fun _ => hNotR) hAb.2 hInCR hOutCR)
                ph1 hPh1)
            cases ph with
            | inside => exact hPh3
            | after => exact hPh3
            | before =>
                simp only [shapeExitPhase, Shape.attemptSites, List.mem_cons, Ne.symm hIsT, false_or] at hPh3 ⊢
                exact hPh3

  private theorem projectArms_retryWF {hs : Headers V} (r : Role) (target : Site)
      (insideCoins : List Site)
      (fns : FnTable M hs.fns)
      (hFns : ∀ hdr (c : Member hs.fns hdr) args,
        (fns hdr c args).Every (fun _ _ => True) (fun _ => True) (fun why => why.isAbort = false))
      (roles : RTable M hs.protocols)
      (hCallee : ∀ hdr (c : Member hs.protocols hdr) (j : Role) (path : List Frame)
        (args : HList (RV M j) hdr.ins) (ph : RetryPhase),
        (j ∉ List.range hdr.roles →
          (roles hdr c j path args).SafeWith M (fun _ _ => True) (fun _ => False) (fun _ => True) (fun _ => False)) ∧
        (hdr.shape.retryAtMostOnce target (Frame.applications path) = true →
         hdr.shape.retryOwnedBy j target (Frame.applications path) = true →
         (ph ≠ .before → target ∉ hdr.shape.attemptSites (Frame.applications path)) →
         hdr.shape.abortsOutsideTarget target (Frame.applications path) (phaseInside ph) = [] →
         (∀ s ∈ hdr.shape.attemptPrivateCoins j target (Frame.applications path) (phaseInside ph), s ∈ insideCoins) →
         (∀ s ∈ hdr.shape.nonAttemptCoinSites j target (Frame.applications path) (phaseInside ph), s ∉ insideCoins) →
         Program.RetryWF M target insideCoins
           (shapeExitPhase target (Frame.applications path) hdr.shape ph) ph (roles hdr c j path args))) :
      ∀ {parts : List Role} {Γ mid payloads} (arms : Arms (protocolDialect V hs) Γ mid payloads)
        (path : List Frame) (env : Env (RV M r) Γ) (p : Pick (RV M r) payloads) (ph : RetryPhase),
        WithinArms parts arms →
        (r ∉ parts →
          ((projectArms r arms).denote (roleSem M r fns roles) path env p).SafeWith M
            (fun _ _ => True) (fun _ => False) (fun _ => True) (fun _ => False)) ∧
        ((shapesOf arms).retryAtMostOnce target (Frame.applications path) = true →
         (shapesOf arms).retryOwnedBy r target (Frame.applications path) = true →
         (ph ≠ .before → target ∉ (shapesOf arms).attemptSites (Frame.applications path)) →
         (shapesOf arms).abortsOutsideTarget target (Frame.applications path) (phaseInside ph) = [] →
         (∀ s ∈ (shapesOf arms).attemptPrivateCoins r target (Frame.applications path) (phaseInside ph), s ∈ insideCoins) →
         (∀ s ∈ (shapesOf arms).nonAttemptCoinSites r target (Frame.applications path) (phaseInside ph), s ∉ insideCoins) →
         Program.RetryWF M target insideCoins
           (shapesExitPhase target (Frame.applications path) (shapesOf arms) ph) ph
           ((projectArms r arms).denote (roleSem M r fns roles) path env p))
    | _, _, _, _, .nil, _, _, p, _, _ => nomatch p
    | parts, _, _, _, .cons inputs arm rest, path, env, .here a, ph, hW => by
        dsimp only [projectArms, Arms.denote]
        have hArm := project_retryWF r target insideCoins fns hFns roles hCallee arm path
          (env.extend inputs (.cons a .nil)) ph hW.1
        refine ⟨hArm.1, fun hOnce hOwned hNotBef hAb hInC hOutC => ?_⟩
        simp only [shapesOf, Shapes.retryAtMostOnce, Shapes.retryOwnedBy, Shapes.attemptSites, Shapes.abortsOutsideTarget,
          Shapes.attemptPrivateCoins, Shapes.nonAttemptCoinSites, Bool.and_eq_true,
          List.append_eq_nil_iff] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
        have hAW := hArm.2 hOnce.1 hOwned.1 (fun hne hm => hNotBef hne (List.mem_append_left _ hm)) hAb.1
          (fun s hs => hInC s (List.mem_append_left _ hs)) (fun s hs => hOutC s (List.mem_append_left _ hs))
        exact retryWF_mono M (fun p0 hp0 => by
          cases ph with
          | inside => exact hp0
          | after => exact hp0
          | before =>
              simp only [shapeExitPhase, shapesExitPhase, Shapes.attemptSites, List.mem_append] at hp0 ⊢
              by_cases hInA : target ∈ (shapeOf arm).attemptSites (Frame.applications path)
              · simp only [hInA, true_or, ite_true] at hp0 ⊢; exact hp0
              · simp only [hInA, false_or, ite_false] at hp0 ⊢
                by_cases hInR : target ∈ (shapesOf rest).attemptSites (Frame.applications path)
                · simp only [hInR, ite_true]; exact .inl hp0
                · simp only [hInR, ite_false]; exact hp0) hAW
    | parts, _, _, _, .cons _ arm rest, path, env, .there p, ph, hW => by
        dsimp only [projectArms, Arms.denote]
        have hRest := projectArms_retryWF r target insideCoins fns hFns roles hCallee rest path env p ph hW.2
        refine ⟨hRest.1, fun hOnce hOwned hNotBef hAb hInC hOutC => ?_⟩
        simp only [shapesOf, Shapes.retryAtMostOnce, Shapes.retryOwnedBy, Shapes.attemptSites, Shapes.abortsOutsideTarget,
          Shapes.attemptPrivateCoins, Shapes.nonAttemptCoinSites, Bool.and_eq_true,
          List.append_eq_nil_iff] at hOnce hOwned hNotBef hAb hInC hOutC ⊢
        have hRW := hRest.2 hOnce.2 hOwned.2 (fun hne hm => hNotBef hne (List.mem_append_right _ hm)) hAb.2
          (fun s hs => hInC s (List.mem_append_right _ hs)) (fun s hs => hOutC s (List.mem_append_right _ hs))
        exact retryWF_mono M (fun p0 hp0 => by
          cases ph with
          | inside => exact hp0
          | after => exact hp0
          | before =>
              simp only [shapesExitPhase, Shapes.attemptSites, List.mem_append] at hp0 ⊢
              by_cases hInR : target ∈ (shapesOf rest).attemptSites (Frame.applications path)
              · simp only [hInR, or_true, ite_true] at hp0 ⊢; exact hp0
              · simp only [hInR, or_false, ite_false] at hp0 ⊢
                by_cases hInA : target ∈ (shapeOf arm).attemptSites (Frame.applications path)
                · simp only [hInA, ite_true]; exact .inl hp0
                · simp only [hInA, ite_false]; exact hp0) hRW
end

private theorem defs_rTable_retryWF (target : Site) (insideCoins : List Site) :
    ∀ {hs : Headers V} (defs : Defs V hs),
      Defs.fnsNoAbort defs = true →
      ∀ (hdr : ProtocolHeader V) (c : Member hs.protocols hdr) (j : Role)
        (path : List Frame) (args : HList (RV M j) hdr.ins) (ph : RetryPhase),
        (j ∉ List.range hdr.roles →
          (Defs.rTable M defs hdr c j path args).SafeWith M (fun _ _ => True) (fun _ => False) (fun _ => True) (fun _ => False)) ∧
        (hdr.shape.retryAtMostOnce target (Frame.applications path) = true →
         hdr.shape.retryOwnedBy j target (Frame.applications path) = true →
         (ph ≠ .before → target ∉ hdr.shape.attemptSites (Frame.applications path)) →
         hdr.shape.abortsOutsideTarget target (Frame.applications path) (phaseInside ph) = [] →
         (∀ s ∈ hdr.shape.attemptPrivateCoins j target (Frame.applications path) (phaseInside ph), s ∈ insideCoins) →
         (∀ s ∈ hdr.shape.nonAttemptCoinSites j target (Frame.applications path) (phaseInside ph), s ∉ insideCoins) →
         Program.RetryWF M target insideCoins
           (shapeExitPhase target (Frame.applications path) hdr.shape ph) ph
           (Defs.rTable M defs hdr c j path args))
  | _, .nil, _, _, c, _, _, _, _ => nomatch c
  | _, .fn _ _ _ _ rest _, hNo, hdr, c, j, path, args, ph => by
      simp only [Defs.fnsNoAbort, Bool.and_eq_true] at hNo
      exact defs_rTable_retryWF target insideCoins rest hNo.2 hdr c j path args ph
  | _, .protocol hdr inputs body ok rest, hNo, _, c, j, path, args, ph => by
      cases c with
      | head =>
          rw [ok.shaped]
          exact project_retryWF M j target insideCoins
            (Defs.fnTable M rest) (defs_fnTable_noAbort M rest hNo)
            (Defs.rTable M rest) (defs_rTable_retryWF target insideCoins rest hNo)
            body path (Env.empty.extend inputs args) ph ok.within
      | tail c' => exact defs_rTable_retryWF target insideCoins rest hNo _ c' j path args ph

unseal roleMeaning in
/-- Top-level 3-phase well-formedness theorem for the prover's role program. -/
theorem roleMeaning_retryWellFormed (p : Typed V) {hdr : ProtocolHeader V}
    (callee : Member p.headers.protocols hdr) (prover : Role) (args : HList (RV M prover) hdr.ins)
    (target : Site)
    (hFns : Defs.fnsNoAbort p.defs = true)
    (hOnce : hdr.shape.retryAtMostOnce target [] = true)
    (hOwned : hdr.shape.retryOwnedBy prover target [] = true)
    (hAb : hdr.shape.abortsOutsideTarget target [] false = [])
    (hExcl : hdr.shape.attemptCoinsExclusive prover target = true) :
    Program.RetryWellFormed M target (hdr.shape.attemptPrivateCoins prover target [] false) .before
      (roleMeaning M p callee prover [] args) := by
  have hOut : ∀ s ∈ hdr.shape.nonAttemptCoinSites prover target [] false,
      s ∉ hdr.shape.attemptPrivateCoins prover target [] false := by
    intro s hs hIn
    unfold Shape.attemptCoinsExclusive at hExcl
    have hAll := List.all_eq_true.mp hExcl s hIn
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hAll
    exact hAll.1 hs
  exact retryWF_to_wellFormed M
    ((defs_rTable_retryWF M target (hdr.shape.attemptPrivateCoins prover target [] false)
      p.defs hFns hdr callee prover [] args .before).2
      hOnce hOwned (fun h => absurd rfl h) hAb (fun _ hs => hs) hOut)

/-- Consequence of `Shape.attemptCoinsExclusive`: every non-prover private coin, every heard coin,
and every service request occurring in `s.events [] id` has its site outside `attemptPrivateCoins`. -/
theorem attemptCoinsExclusive_ev_notin (prover : Role) (target : Site) (s : Shape V)
    (hExcl : s.attemptCoinsExclusive prover target = true)
    {e : ShapeEvent V} (hMem : e ∈ s.events [] id) :
    match e.cls with
    | .given (.coin _) owner [] =>
        owner ≠ prover → e.site ∉ s.attemptPrivateCoins prover target [] false
    | .given (.coin _) _ (_ :: _) =>
        e.site ∉ s.attemptPrivateCoins prover target [] false
    | .given (.request _) _ _ =>
        e.site ∉ s.attemptPrivateCoins prover target [] false
    | _ => True := by
  have hDisj : ∀ site ∈ s.attemptPrivateCoins prover target [] false,
      site ∉ (s.events [] id).filterMap (fun ev =>
        match ev.cls with
        | .given (.coin _) owner [] => if owner != prover then some ev.site else none
        | .given (.coin _) _ (_ :: _) => some ev.site
        | .given (.request _) _ _ => some ev.site
        | _ => none) := by
    intro site hIn
    unfold Shape.attemptCoinsExclusive at hExcl
    have hAll := List.all_eq_true.mp hExcl site hIn
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hAll
    exact hAll.2
  cases hCls : e.cls with
  | flow _ _ _ => trivial
  | given gkind owner hearers =>
      cases gkind with
      | coin law =>
          cases hearers with
          | nil =>
              intro hNe hIn
              refine hDisj e.site hIn (List.mem_filterMap.mpr ⟨e, hMem, ?_⟩)
              rw [hCls]; simp [bne_iff_ne, hNe]
          | cons h0 hs =>
              intro hIn
              refine hDisj e.site hIn (List.mem_filterMap.mpr ⟨e, hMem, ?_⟩)
              rw [hCls]
      | request svc =>
          intro hIn
          refine hDisj e.site hIn (List.mem_filterMap.mpr ⟨e, hMem, ?_⟩)
          rw [hCls]

end StructuralInvariants

/-! ## Section 4: Coupled retry simulation and `deploy_complete_retry` -/

section RetrySimulation

variable {V : Vocabulary} (M : Model V)

/-! ### 4a. `Protocol.NoSitesIn`, source-agreement helpers, and step helpers -/

private theorem alone_eq_proc {σ A : Type} {source : Source M} {r : Role}
    {p₁ p₂ : Process (RSig M) σ A} {rec : List (Happened M)} {e : Ending A σ}
    (hEq : p₁ = p₂) (h : Alone M source r p₂ rec e) : Alone M source r p₁ rec e :=
  hEq ▸ h

private theorem eqRec_symm_eqRec {α : Type} {F : α → Type} {a b : α} (h : a = b) (x : F a) :
    h.symm ▸ (h ▸ x : F b) = x := by
  subst h; rfl

private theorem patchSource_ne_ty (source : Source M) (target : Occurrence) (τ₀ : V.Ty)
    (v₀ : M.Val τ₀) {τ : V.Ty} (hne : τ ≠ τ₀) :
    patchSource M source target τ₀ v₀ target τ = source target τ := by
  unfold patchSource
  exact dite_eq_right (fun h => hne h.2)

/-- Protocol never executes a `.given` event whose site lies in `bad`. -/
def Protocol.NoSitesIn (bad : List Site) {A : Type} : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.flow ..) k => ∀ u, Protocol.NoSitesIn bad (k u)
  | .call (.given _ _ _ at_ _ _ _) k => at_.site ∉ bad ∧ ∀ v, Protocol.NoSitesIn bad (k v)

private theorem lawful_of_agree_sites {bad : List Site} {s₁ s₂ : Source M}
    (hAg : ∀ at_ τ, at_.site ∉ bad → s₁ at_ τ = s₂ at_ τ) :
    ∀ {A : Type} {p : Protocol M A},
      Protocol.NoSitesIn M bad p → Lawful M s₁ p → Lawful M s₂ p := by
  intro A p
  induction p with
  | done _ => intro _ _; trivial
  | halt _ => intro _ _; trivial
  | call op k ih =>
      cases op with
      | flow _ _ _ _ _ _ => intro hNo hL; exact ih () (hNo ()) hL
      | given _ _ _ at_ _ _ _ =>
          intro ⟨hOut, hNo⟩ hL v hv
          obtain ⟨hAl, hLk⟩ := hL v ((hAg at_ _ hOut).trans hv)
          exact ⟨hAl, ih v (hNo v) hLk⟩

private theorem lawfulPrivate_of_agree_sites {bad : List Site} {s₁ s₂ : Source M}
    (hAg : ∀ at_ τ, at_.site ∉ bad → s₁ at_ τ = s₂ at_ τ) :
    ∀ {A : Type} {p : Protocol M A},
      Protocol.NoSitesIn M bad p → LawfulPrivate M s₁ p → LawfulPrivate M s₂ p := by
  intro A p
  induction p with
  | done _ => intro _ _; trivial
  | halt _ => intro _ _; trivial
  | call op k ih =>
      cases op with
      | flow _ _ _ _ _ _ => intro hNo hL; exact ih () (hNo ()) hL
      | given gkind _ hearers at_ _ _ _ =>
          intro ⟨hOut, hNo⟩ hL
          cases gkind with
          | coin _ =>
              cases hearers with
              | cons _ _ => exact fun v hAl => ih v (hNo v) (hL v hAl)
              | nil =>
                  intro v hv
                  obtain ⟨hAl, hLk⟩ := hL v ((hAg at_ _ hOut).trans hv)
                  exact ⟨hAl, ih v (hNo v) hLk⟩
          | request _ =>
              intro v hv
              obtain ⟨hAl, hLk⟩ := hL v ((hAg at_ _ hOut).trans hv)
              exact ⟨hAl, ih v (hNo v) hLk⟩

private theorem fed_of_agree_sites {bad : List Site} {s₁ s₂ : Source M}
    (hAg : ∀ at_ τ, at_.site ∉ bad → s₁ at_ τ = s₂ at_ τ) :
    ∀ {A : Type} {p : Protocol M A},
      Protocol.NoSitesIn M bad p → Fed M s₁ p → Fed M s₂ p := by
  intro A p
  induction p with
  | done _ => intro _ _; trivial
  | halt _ => intro _ _; trivial
  | call op k ih =>
      cases op with
      | flow _ _ _ _ _ _ => intro hNo hF; exact ih () (hNo ()) hF
      | given gkind _ hearers at_ _ _ _ =>
          intro ⟨hOut, hNo⟩ hF
          cases gkind with
          | coin _ =>
              cases hearers with
              | cons _ _ => exact fun v hAl => ih v (hNo v) (hF v hAl)
              | nil =>
                  obtain ⟨v, hv, hFk⟩ := hF
                  exact ⟨v, (hAg at_ _ hOut).symm.trans hv, ih v (hNo v) hFk⟩
          | request _ =>
              obtain ⟨v, hv, hFk⟩ := hF
              exact ⟨v, (hAg at_ _ hOut).symm.trans hv, ih v (hNo v) hFk⟩

private theorem grun_of_agree_sites {bad : List Site} {s₁ s₂ : Source M}
    (hAg : ∀ at_ τ, at_.site ∉ bad → s₁ at_ τ = s₂ at_ τ) :
    ∀ {A : Type} {p : Protocol M A} {evs : List (Event M)} {e : GEnd A},
      Protocol.NoSitesIn M bad p → GRun M s₁ p evs e → GRun M s₂ p evs e
  | _, _, _, _, _, .done => .done
  | _, _, _, _, _, .halt => .halt
  | _, _, _, _, hNo, .flow hR => .flow (grun_of_agree_sites hAg (hNo ()) hR)
  | _, _, _, _, hNo, .given hSrc hR =>
      .given ((hAg _ _ hNo.1).symm.trans hSrc) (grun_of_agree_sites hAg (hNo.2 _) hR)

private theorem proj_after_noSitesIn {prover : Role} {target : Site} {shape : Shape V}
    (hExcl : shape.attemptCoinsExclusive prover target = true)
    {A BP : Type} {postP : A → BP → Prop} {p : Protocol M A} {qP : Program M BP}
    (hPP : Proj M prover postP p qP)
    (hSafe : qP.SafeWith M (fun _ _ => True)
      (fun op => ROp.NotMarkAt M target op ∧
        match op with
        | .own (.coin _) [] at_ _ _ _ => at_.site ∉ shape.attemptPrivateCoins prover target [] false
        | .own (.request _) _ at_ _ _ _ => at_.site ∉ shape.attemptPrivateCoins prover target [] false
        | _ => True)
      (fun _ => True) (fun why => why.isAbort = false))
    (hPShape : Protocol.MatchesShape M (shape.events [] id) p) :
    Protocol.NoSitesIn M (shape.attemptPrivateCoins prover target [] false) p := by
  induction hPP with
  | done _ => trivial
  | stopsHere _ => trivial
  | stopsElsewhere _ => trivial
  | gave _ _ ih => intro _; exact ih (hSafe.2 () trivial) (hPShape.2 ())
  | got _ _ _ ih => intro _; exact ih (hSafe.2 _ trivial) (hPShape.2 ())
  | passed _ _ _ ih => intro _; exact ih hSafe (hPShape.2 ())
  | begins _ ih => exact ih (hSafe.2 0 trivial) hPShape
  | settles _ ih => exact ih (hSafe.2 () trivial) hPShape
  | @owned gkind hearers at_ gIns payload τ k k' _ ih =>
      refine ⟨?_, fun v => ih v (hSafe.2 v trivial) (hPShape.2 v)⟩
      cases gkind with
      | coin law =>
          cases hearers with
          | nil => exact hSafe.1.2
          | cons h0 hs =>
              obtain ⟨e, he, hSite, _, hCls⟩ := hPShape.1
              have hEv := attemptCoinsExclusive_ev_notin prover target shape hExcl he
              rw [hCls] at hEv
              exact hSite ▸ hEv
      | request svc => exact hSafe.1.2
  | @heard gkind owner hearers at_ gIns payload τ k k' hNe _ _ ih =>
      refine ⟨?_, fun v => ih v (hSafe.2 v trivial) (hPShape.2 v)⟩
      obtain ⟨e, he, hSite, _, hCls⟩ := hPShape.1
      have hEv := attemptCoinsExclusive_ev_notin prover target shape hExcl he
      rw [hCls] at hEv
      cases gkind with
      | coin law =>
          cases hearers with
          | nil => exact hSite ▸ hEv hNe
          | cons h0 hs => exact hSite ▸ hEv
      | request svc => exact hSite ▸ hEv
  | @unheard gkind owner hearers at_ gIns payload τ q k hNe _ _ ih =>
      refine ⟨?_, fun v => ih v hSafe (hPShape.2 v)⟩
      obtain ⟨e, he, hSite, _, hCls⟩ := hPShape.1
      have hEv := attemptCoinsExclusive_ev_notin prover target shape hExcl he
      rw [hCls] at hEv
      cases gkind with
      | coin law =>
          cases hearers with
          | nil => exact hSite ▸ hEv hNe
          | cons h0 hs => exact hSite ▸ hEv
      | request svc => exact hSite ▸ hEv

/-- Unified prover+verifier clause stepping for a prover→verifier `.flow` event under a streaming
`.derived` deployment (handles both absorbed and elided-absorb messages uniformly). -/
private theorem derived_step_flow {enc : VocabEncoder V} {d : Deployed V} {suite : ModuleRef}
    {layout : Layout} {stateTy suiteUnitTy unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false}
    {absRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key}
    {conP0 : Layer V d.admitted.program.headers prover d.entry.ins}
    {conV0 : Layer V d.admitted.program.headers verifier d.entry.ins}
    {layP0 : Layer V d.admitted.program.headers prover d.entry.ins}
    {layV0 : Layer V d.admitted.program.headers verifier d.entry.ins}
    (hCPSt : conP0.state = stateTy) (hCVSt : conV0.state = stateTy)
    (hLPSt : layP0.state = .seq unitTy none) (hLVSt : layV0.state = streamStateTy unitTy)
    (hLayDecl : d.declaration.layout = some layout) (hLayLaw : d.LayoutLawful M)
    (hCC : buildConstructionClauses.go enc d.admitted suite stateTy suiteUnitTy absRef prover verifier
      declKey (d.entry.shape.events [] id) 0
      (d.entry.shape.eventsWithAbsorb prover verifier [] id false) =
      .ok (hCPSt ▸ conP0.clauses, hCVSt ▸ conV0.clauses))
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hLPSt ▸ layP0.clauses, hLVSt ▸ layV0.clauses))
    {kind : FlowKind} {getters : List Role} {at_ : Occurrence} {τ : V.Ty} {x : M.Val τ}
    (hMsgV : M.Valid τ x) {st : M.Val stateTy} {buf : List (M.Val unitTy)}
    (hStV : M.Valid stateTy st) (hBufV : ∀ u ∈ buf, M.Valid unitTy u)
    {eP : ShapeEvent V} (hEP : eP ∈ d.entry.shape.events [] id)
    (hSiteP : eP.site = at_.site) (hTyP : eP.τ = τ) (hVin : verifier ∈ getters)
    (hClsP : eP.cls = .flow kind prover getters) :
    let fnTable := Defs.fnTable M d.admitted.program.defs
    let rTable := Defs.rTable M d.admitted.program.defs
    ∃ (st' : M.Val stateTy) (chunk : List (M.Val unitTy)),
      M.Valid stateTy st' ∧
      (∀ u ∈ chunk, M.Valid unitTy u) ∧
      (Stack.handler M fnTable rTable [conP0, layP0]).clause
        (.give kind getters at_ τ x)
        (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) =
        .done ((), .cons (hCPSt.symm ▸ st') (.cons (hLPSt.symm ▸ (buf ++ chunk)) .nil)) ∧
      (∀ (restBuf : List (M.Val unitTy)), (∀ u ∈ restBuf, M.Valid unitTy u) →
        (Stack.handler M fnTable rTable [conV0, layV0]).clause
          (.get kind prover at_ τ)
          (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ chunk ++ restBuf, (buf.length, ()))) .nil)) =
          .done (x, .cons (hCVSt.symm ▸ st')
            (.cons (hLVSt.symm ▸ (buf ++ chunk ++ restBuf, (buf.length + chunk.length, ()))) .nil))) := by
  cases conP0 with | mk cPL cPSt cPT cPG cPCl cPA cPS cPF =>
  cases conV0 with | mk cVL cVSt cVT cVG cVCl cVA cVS cVF =>
  cases layP0 with | mk lPL lPSt lPT lPG lPCl lPA lPS lPF =>
  cases layV0 with | mk lVL lVSt lVT lVG lVCl lVA lVS lVF =>
  dsimp only at hCPSt hCVSt hLPSt hLVSt
  subst cPSt; subst cVSt; subst lPSt; subst lVSt
  dsimp only at hCC hSL ⊢
  let events := d.entry.shape.events [] id
  let eventsAbs := d.entry.shape.eventsWithAbsorb prover verifier [] id false
  have hFst : eventsAbs.map Prod.fst = events :=
    eventsWithAbsorb_fst prover verifier [] id false d.entry.shape
  have hEPInAbs : ∃ bP, (eP, bP) ∈ eventsAbs := by
    have hM : eP ∈ eventsAbs.map Prod.fst := hFst.symm ▸ hEP
    obtain ⟨⟨e₀, b₀⟩, hIn, hEq⟩ := List.mem_map.mp hM
    dsimp only at hEq; subst hEq; exact ⟨b₀, hIn⟩
  obtain ⟨needP, hNeedP⟩ := hEPInAbs
  have hAtEta : (⟨at_.path, at_.site.key⟩ : Occurrence) = at_ := by cases at_; rfl
  obtain ⟨wRef, chunk, hWFind, hWD, hChV, hLayPAns⟩ :=
    streaming_layout_answer_prover_flow M 0 events (fun _ h => h) hSL
      kind getters at_ τ x buf hMsgV
      ⟨eP, hEP, hSiteP, hTyP, hVin, hClsP⟩
  cases needP with
  | true =>
      obtain ⟨encP, encVal, st', hEncFindP, hEncD, hAbsD, hSt'V, hConPAns⟩ :=
        construction_clauses_answer_prover_flow_abs M 0 eventsAbs hCC
          kind getters at_ τ x st hMsgV hStV ⟨eP, hNeedP, hSiteP, hTyP, hClsP⟩
      rw [hAtEta] at hConPAns
      obtain ⟨encV, hEncFindV, hConVAns⟩ :=
        construction_clauses_answer_verifier_flow_abs M 0 eventsAbs hCC
          kind at_ τ st ⟨eP, hNeedP, hSiteP, hTyP, getters, hVin, hClsP⟩
      rw [hAtEta] at hConVAns
      have hEncEq : encP = encV := Option.some.inj (hEncFindP.symm.trans hEncFindV)
      subst hEncEq
      refine ⟨st', chunk, hSt'V, hChV, ?_, ?_⟩
      · exact stack2_clause_step M (Defs.fnTable M d.admitted.program.defs)
          (Defs.rTable M d.admitted.program.defs)
          ⟨cPL, stateTy, cPT, cPG, cPCl, cPA, cPS, cPF⟩
          ⟨lPL, .seq unitTy none, lPT, lPG, lPCl, lPA, lPS, lPF⟩
          _ _ st st' buf (buf ++ chunk) () () _ hConPAns hLayPAns rfl
      · intro restBuf hRestV
        obtain ⟨rRef, hRFind, hLayVAns⟩ :=
          streaming_layout_answer_verifier_flow M 0 events hSL
            kind at_ τ (buf ++ chunk ++ restBuf) buf.length
            ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
        have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind hRFind hMsgV hBufV hRestV hWD
        have hLayVDone := hLayVAns x (buf.length + chunk.length) hRD
        have hKV :
            ((((liftLocal (S := RSig M) id (encP.eval M (Defs.fnTable M d.admitted.program.defs) (.cons x .nil))).bind fun enc0 =>
              (liftLocal (S := RSig M) id (absRef.eval M (Defs.fnTable M d.admitted.program.defs)
                (.cons st (.cons (msgLabel at_.site) (.cons enc0.single .nil))))).map
                fun nextSt => aloneIn M verifier (.cons x nextSt)).mapHalt
                  fun why => (why, st)).map fun out =>
              let values := HList.split [τ] (aloneOut M verifier out)
              (values.1.single, values.2.single)) = .done (x, st') := by
          rw [hEncD]
          simp only [liftLocal_done, Process.bind, HList.single]
          rw [hAbsD]
          simp only [liftLocal_done, Process.map, Process.mapHalt, aloneOut_aloneIn, HList.split]
        exact stack2_clause_step M (Defs.fnTable M d.admitted.program.defs)
          (Defs.rTable M d.admitted.program.defs)
          ⟨cVL, stateTy, cVT, cVG, cVCl, cVA, cVS, cVF⟩
          ⟨lVL, streamStateTy unitTy, lVT, lVG, lVCl, lVA, lVS, lVF⟩
          _ _ st st' (buf ++ chunk ++ restBuf, (buf.length, ()))
          (buf ++ chunk ++ restBuf, (buf.length + chunk.length, ()))
          x x _ hConVAns hLayVDone hKV
  | false =>
      have hNoAbs : ∀ e' b', (e', b') ∈ eventsAbs → e'.site = at_.site → e'.τ = τ →
          (∃ gs, verifier ∈ gs ∧ e'.cls = .flow kind prover gs) → b' = false := by
        intro e' b' hIn hS hT ⟨gs, hVg, hC⟩
        exact eventsWithAbsorb_flow_consistent prover verifier [] id false d.entry.shape
          hIn hNeedP (hS.trans hSiteP.symm) (hT.trans hTyP.symm) hC hVg hClsP hVin
      obtain ⟨hUnmP, hUnmV⟩ :=
        construction_clauses_unmatched_elided_flow M 0 eventsAbs hCC kind getters at_ τ x hNoAbs
      have hConPPass : Clause.answer M (Defs.fnTable M d.admitted.program.defs)
          (Defs.rTable M d.admitted.program.defs) cPCl (.give kind getters at_ τ x) st =
          .call (.give kind getters at_ τ x) fun reply => .done (reply, st) :=
        clause_answer_unmatched_all M _ _ _ st cPCl hUnmP
      have hConVPass : Clause.answer M (Defs.fnTable M d.admitted.program.defs)
          (Defs.rTable M d.admitted.program.defs) cVCl (.get kind prover at_ τ) st =
          .call (.get kind prover at_ τ) fun reply => .done (reply, st) :=
        clause_answer_unmatched_all M _ _ _ st cVCl hUnmV
      refine ⟨st, chunk, hStV, hChV, ?_, ?_⟩
      · exact stack2_clause_step M (Defs.fnTable M d.admitted.program.defs)
          (Defs.rTable M d.admitted.program.defs)
          ⟨cPL, stateTy, cPT, cPG, cPCl, cPA, cPS, cPF⟩
          ⟨lPL, .seq unitTy none, lPT, lPG, lPCl, lPA, lPS, lPF⟩
          _ _ st st buf (buf ++ chunk) () () _ hConPPass hLayPAns rfl
      · intro restBuf hRestV
        obtain ⟨rRef, hRFind, hLayVAns⟩ :=
          streaming_layout_answer_verifier_flow M 0 events hSL
            kind at_ τ (buf ++ chunk ++ restBuf) buf.length
            ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
        have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind hRFind hMsgV hBufV hRestV hWD
        have hLayVDone := hLayVAns x (buf.length + chunk.length) hRD
        exact stack2_clause_step M (Defs.fnTable M d.admitted.program.defs)
          (Defs.rTable M d.admitted.program.defs)
          ⟨cVL, stateTy, cVT, cVG, cVCl, cVA, cVS, cVF⟩
          ⟨lVL, streamStateTy unitTy, lVT, lVG, lVCl, lVA, lVS, lVF⟩
          _ _ st st (buf ++ chunk ++ restBuf, (buf.length, ()))
          (buf ++ chunk ++ restBuf, (buf.length + chunk.length, ()))
          x x _ hConVPass hLayVDone rfl

/-- Unified prover+verifier clause stepping for a heard coin (`owner = verifier`, `prover ∈ hearers`,
non-empty hearers) under a streaming `.derived` deployment (handles both carried and uncarried draws
uniformly, returning `chunk = []` when uncarried). -/
private theorem derived_step_heard_coin {enc : VocabEncoder V} {d : Deployed V} {suite : ModuleRef}
    {sessionTag : Option (List Nat)} {layout : Layout} {stateTy suiteUnitTy unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false}
    {absRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key}
    {conP0 : Layer V d.admitted.program.headers prover d.entry.ins}
    {conV0 : Layer V d.admitted.program.headers verifier d.entry.ins}
    {layP0 : Layer V d.admitted.program.headers prover d.entry.ins}
    {layV0 : Layer V d.admitted.program.headers verifier d.entry.ins}
    (hCPSt : conP0.state = stateTy) (hCVSt : conV0.state = stateTy)
    (hLPSt : layP0.state = .seq unitTy none) (hLVSt : layV0.state = streamStateTy unitTy)
    (hConDecl : d.declaration.construction = .derived suite sessionTag)
    (hLayDecl : d.declaration.layout = some layout)
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M)
    (hCC : buildConstructionClauses.go enc d.admitted suite stateTy suiteUnitTy absRef prover verifier
      declKey (d.entry.shape.events [] id) 0
      (d.entry.shape.eventsWithAbsorb prover verifier [] id false) =
      .ok (hCPSt ▸ conP0.clauses, hCVSt ▸ conV0.clauses))
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hLPSt ▸ layP0.clauses, hLVSt ▸ layV0.clauses))
    {law : V.LawKey} {h0 : Role} {hs : List Role} {at_ : Occurrence} {τ : V.Ty}
    {st : M.Val stateTy} {buf : List (M.Val unitTy)}
    (hStV : M.Valid stateTy st) (hBufV : ∀ u ∈ buf, M.Valid unitTy u)
    {eV : ShapeEvent V} (hEV : eV ∈ d.entry.shape.events [] id)
    (hSiteV : eV.site = at_.site) (hTyV : eV.τ = τ) (hPin : prover ∈ h0 :: hs)
    (hClsV : eV.cls = .given (.coin law) verifier (h0 :: hs)) :
    let fnTable := Defs.fnTable M d.admitted.program.defs
    let rTable := Defs.rTable M d.admitted.program.defs
    ∃ (coin : M.Val τ) (st' : M.Val stateTy) (chunk : List (M.Val unitTy)),
      M.Valid τ coin ∧
      Allows M (.coin law) [] .nil τ coin ∧
      at_.site ∈ d.entry.shape.heardCoins ∧
      M.Valid stateTy st' ∧
      (∀ u ∈ chunk, M.Valid unitTy u) ∧
      (Stack.handler M fnTable rTable [conP0, layP0]).clause
        (.hear (.coin law) verifier at_ τ)
        (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) =
        .done (coin, .cons (hCPSt.symm ▸ st') (.cons (hLPSt.symm ▸ (buf ++ chunk)) .nil)) ∧
      (∀ (restBuf : List (M.Val unitTy)), (∀ u ∈ restBuf, M.Valid unitTy u) →
        (Stack.handler M fnTable rTable [conV0, layV0]).clause
          (.own (.coin law) (h0 :: hs) at_ [] .nil τ)
          (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ chunk ++ restBuf, (buf.length, ()))) .nil)) =
          .done (coin, .cons (hCVSt.symm ▸ st')
            (.cons (hLVSt.symm ▸ (buf ++ chunk ++ restBuf, (buf.length + chunk.length, ()))) .nil))) := by
  cases conP0 with | mk cPL cPSt cPT cPG cPCl cPA cPS cPF =>
  cases conV0 with | mk cVL cVSt cVT cVG cVCl cVA cVS cVF =>
  cases layP0 with | mk lPL lPSt lPT lPG lPCl lPA lPS lPF =>
  cases layV0 with | mk lVL lVSt lVT lVG lVCl lVA lVS lVF =>
  dsimp only at hCPSt hCVSt hLPSt hLVSt
  subst cPSt; subst cVSt; subst lPSt; subst lVSt
  dsimp only at hCC hSL ⊢
  let events := d.entry.shape.events [] id
  let eventsAbs := d.entry.shape.eventsWithAbsorb prover verifier [] id false
  have hFst : eventsAbs.map Prod.fst = events :=
    eventsWithAbsorb_fst prover verifier [] id false d.entry.shape
  have hEVAbs : ∃ p ∈ eventsAbs, p.1 = eV := by
    have hM : eV ∈ eventsAbs.map Prod.fst := hFst.symm ▸ hEV
    obtain ⟨p, hp, hEq⟩ := List.mem_map.mp hM
    exact ⟨p, hp, hEq⟩
  obtain ⟨pV, hpV, hpVEq⟩ := hEVAbs
  have hSuf0 : ∀ k p, eventsAbs[k]? = some p → events[0 + k]? = some p.1 := by
    intro k p hk; rw [Nat.zero_add, ← hFst, List.getElem?_map, hk]; rfl
  obtain ⟨idxP, ⟨ePSite, ePCls, ePτ⟩, derP, coinP, stP', hIdxP, hSiteP, hTyP,
    ⟨hsP, hPinP, hClsP⟩, hDerFindP, hDerDP, hCoinPV, hStP'V, hConPAns⟩ :=
    construction_clauses_answer_prover_coin M 0 eventsAbs hSuf0 hCC
      law at_ τ st hStV
      ⟨pV, hpV, hpVEq.symm ▸ hSiteV, hpVEq.symm ▸ hTyV, h0 :: hs, hPin, hpVEq.symm ▸ hClsV⟩
  obtain ⟨idxV, ⟨eV'Site, eV'Cls, eV'τ⟩, derV, coinV, stV', hIdxV, hSiteV', hTyV',
    hClsV', hLawV', hDerFindV, hDerDV, hCoinVV, hStV'V, hConVAns⟩ :=
    construction_clauses_answer_verifier_coin M 0 eventsAbs hSuf0 hCC
      law (h0 :: hs) at_ τ st hStV
      ⟨pV, hpV, hpVEq.symm ▸ hSiteV, hpVEq.symm ▸ hTyV, hPin, hpVEq.symm ▸ hClsV⟩
  dsimp only at hSiteP hTyP hClsP hSiteV' hTyV' hClsV'
  subst ePτ; subst eV'τ
  have hDerEq : derP = derV := Option.some.inj (hDerFindP.symm.trans hDerFindV)
  subst hDerEq
  have hEvalEq : Process.done (HList.cons coinP (HList.cons stP' HList.nil)) =
      .done (.cons coinV (.cons stV' .nil)) := hDerDP.symm.trans hDerDV
  cases hEvalEq
  have hAllowsCoin : Allows M (.coin law) [] .nil τ coinP :=
    suiteLawful_allows M hConDecl hSuiteLaw hDerFindV
      (List.mem_of_getElem? hIdxV) hClsV' rfl hLawV' hStV (drawLabel_bytes at_.site) hDerDV
  have hAtHeard : at_.site ∈ d.entry.shape.heardCoins := by
    rw [← hSiteV']
    exact mem_heardCoins_of_event (List.mem_of_getElem? hIdxV) hClsV'
  have hToldSiteP : (⟨at_.path, drawToldKey events idxP⟩ : Occurrence).site =
      ⟨ePSite.through, drawToldKey events (0 + idxP)⟩ := by
    simpa using site_told_from_match hSiteP (k := drawToldKey events idxP)
  have hToldSiteV : (⟨at_.path, drawToldKey events idxV⟩ : Occurrence).site =
      ⟨eV'Site.through, drawToldKey events (0 + idxV)⟩ := by
    simpa using site_told_from_match hSiteV' (k := drawToldKey events idxV)
  have hCarryP := streaming_layout_answer_told M 0 events (fun _ h => h) hSL
    idxP ⟨ePSite, ePCls, τ⟩ hIdxP law hsP ⟨at_.path, drawToldKey events idxP⟩
    coinP hClsP hPinP hToldSiteP hCoinPV
  have hCarryV := streaming_layout_answer_told M 0 events (fun _ h => h) hSL
    idxV ⟨eV'Site, eV'Cls, τ⟩ hIdxV law (h0 :: hs) ⟨at_.path, drawToldKey events idxV⟩
    coinP hClsV' hPin hToldSiteV hCoinPV
  by_cases hCar : at_.site ∈ layout.carry
  · have hCarP : ePSite ∈ layout.carry := hSiteP.symm ▸ hCar
    have hCarV : eV'Site ∈ layout.carry := hSiteV'.symm ▸ hCar
    rw [ite_eq_left hCarP] at hCarryP
    rw [ite_eq_left hCarV] at hCarryV
    obtain ⟨wRef, _, _, chunk, hWFind, _, _, hWD, hChV, hLayPAns, _⟩ := hCarryP
    obtain ⟨_, rRef, eqRef, _, _, hRFind, hEqFind, _, _, _, hLayVAns⟩ := hCarryV
    refine ⟨coinP, stP', chunk, hCoinPV, hAllowsCoin, hAtHeard, hStP'V, hChV, ?_, ?_⟩
    · exact stack2_clause_step M (Defs.fnTable M d.admitted.program.defs)
        (Defs.rTable M d.admitted.program.defs)
        ⟨cPL, stateTy, cPT, cPG, cPCl, cPA, cPS, cPF⟩
        ⟨lPL, .seq unitTy none, lPT, lPG, lPCl, lPA, lPS, lPF⟩
        _ _ st stP' buf (buf ++ chunk) () coinP _ hConPAns (hLayPAns buf) rfl
    · intro restBuf hRestV
      have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind hRFind hCoinPV hBufV hRestV hWD
      have hEqD := layoutLawful_equal_refl M hLayDecl hLayLaw hEqFind hCoinPV
      have hLayVDone := hLayVAns (buf ++ chunk ++ restBuf) buf.length (buf.length + chunk.length) hRD hEqD
      exact stack2_clause_step M (Defs.fnTable M d.admitted.program.defs)
        (Defs.rTable M d.admitted.program.defs)
        ⟨cVL, stateTy, cVT, cVG, cVCl, cVA, cVS, cVF⟩
        ⟨lVL, streamStateTy unitTy, lVT, lVG, lVCl, lVA, lVS, lVF⟩
        _ _ st stP' (buf ++ chunk ++ restBuf, (buf.length, ()))
        (buf ++ chunk ++ restBuf, (buf.length + chunk.length, ()))
        () coinP _ hConVAns hLayVDone rfl
  · have hCarP : ePSite ∉ layout.carry := hSiteP.symm ▸ hCar
    have hCarV : eV'Site ∉ layout.carry := hSiteV'.symm ▸ hCar
    rw [ite_eq_right hCarP] at hCarryP
    rw [ite_eq_right hCarV] at hCarryV
    refine ⟨coinP, stP', [], hCoinPV, hAllowsCoin, hAtHeard, hStP'V, (fun _ h => nomatch h), ?_, ?_⟩
    · simpa [List.append_nil] using stack2_clause_step M (Defs.fnTable M d.admitted.program.defs)
        (Defs.rTable M d.admitted.program.defs)
        ⟨cPL, stateTy, cPT, cPG, cPCl, cPA, cPS, cPF⟩
        ⟨lPL, .seq unitTy none, lPT, lPG, lPCl, lPA, lPS, lPF⟩
        _ _ st stP' buf buf () coinP _ hConPAns (hCarryP.1 buf) rfl
    · intro restBuf _
      simpa [List.append_nil, List.length_nil, Nat.add_zero] using
        stack2_clause_step M (Defs.fnTable M d.admitted.program.defs)
          (Defs.rTable M d.admitted.program.defs)
          ⟨cVL, stateTy, cVT, cVG, cVCl, cVA, cVS, cVF⟩
          ⟨lVL, streamStateTy unitTy, lVT, lVG, lVCl, lVA, lVS, lVF⟩
          _ _ st stP' (buf ++ restBuf, (buf.length, ())) (buf ++ restBuf, (buf.length, ()))
          () coinP _ hConVAns (hCarryV.2 (buf ++ restBuf) buf.length) rfl

/-- Step an aborting-attempt specification past a non-heard `.given` event (private coin or request),
handling both `at_.site ∈ heardCoins` and `at_.site ∉ heardCoins` unconditionally. -/
private theorem step_aborts_given {A : Type} {prover : Role} {heardCoins : List Site}
    {src : Source M} {gkind : GivenKind V} {owner : Role} {hearers : List Role}
    {at_ : Occurrence} {gIns : List V.Ty} {payload : HList M.Val gIns} {τ : V.Ty}
    {k : M.Val τ → Protocol M A} {v : M.Val τ}
    (hSrc : src at_ τ = some v) (hAl : Allows M gkind gIns payload τ v)
    (hOccK : Protocol.OccsIn M (· ≠ at_) (k v))
    (hAborts : ∀ source₁, Lawful M source₁ (.call (.given gkind owner hearers at_ gIns payload τ) k) →
      (∀ at' τ', at'.site ∉ heardCoins → source₁ at' τ' = src at' τ') →
      ∃ evs who why, GRun M source₁ (.call (.given gkind owner hearers at_ gIns payload τ) k) evs (.stopped who why) ∧
        prover ∈ who ∧ why.isAbort = true) :
    ∀ source₁, Lawful M source₁ (k v) →
      (∀ at' τ', at'.site ∉ heardCoins → source₁ at' τ' = src at' τ') →
      ∃ evs who why, GRun M source₁ (k v) evs (.stopped who why) ∧
        prover ∈ who ∧ why.isAbort = true := by
  intro source₁ hL₁ hAg₁
  by_cases hInH : at_.site ∈ heardCoins
  · let src₂ := patchSource M source₁ at_ τ v
    have hAg12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = src₂ at' τ' :=
      fun at' τ' hne => (patchSource_ne M source₁ at_ τ v hne τ').symm
    have hL₂ : Lawful M src₂ (.call (.given gkind owner hearers at_ gIns payload τ) k) := by
      intro w hw
      dsimp only [src₂] at hw; rw [patchSource_self] at hw; cases hw
      exact ⟨hAl, lawful_of_agree M hAg12 hOccK hL₁⟩
    have hAg₂ : ∀ at' τ', at'.site ∉ heardCoins → src₂ at' τ' = src at' τ' := by
      intro at' τ' hNotIn
      have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hInH)
      dsimp only [src₂]; rw [patchSource_ne M source₁ at_ τ v hne τ']
      exact hAg₁ at' τ' hNotIn
    obtain ⟨evs, who, why, hRun₂, hInWho, hIsAb⟩ := hAborts src₂ hL₂ hAg₂
    cases hRun₂ with
    | given hS2 hRk =>
        dsimp only [src₂] at hS2; rw [patchSource_self] at hS2; cases hS2
        exact ⟨_, who, why, grun_of_agree M (fun at' τ' hne => (hAg12 at' τ' hne).symm) hOccK hRk, hInWho, hIsAb⟩
  · have hS1 : source₁ at_ τ = some v := (hAg₁ at_ τ hInH).trans hSrc
    have hL₂ : Lawful M source₁ (.call (.given gkind owner hearers at_ gIns payload τ) k) := by
      intro w hw; rw [hS1] at hw; cases hw; exact ⟨hAl, hL₁⟩
    obtain ⟨evs, who, why, hRun₁, hInWho, hIsAb⟩ := hAborts source₁ hL₂ hAg₁
    cases hRun₁ with
    | given hS1' hRk =>
        rw [hS1] at hS1'; cases hS1'
        exact ⟨_, who, why, hRk, hInWho, hIsAb⟩

/-- Step an aborting-attempt specification past a heard coin event via `patchSource`. -/
private theorem step_aborts_heard_coin {A : Type} {prover : Role} {heardCoins : List Site}
    {src : Source M} {law : V.LawKey} {owner : Role} {hearers : List Role}
    {at_ : Occurrence} {τ : V.Ty} {k : M.Val τ → Protocol M A} {coin : M.Val τ}
    (hAtH : at_.site ∈ heardCoins) (hAl : Allows M (.coin law) [] .nil τ coin)
    (hOccK : Protocol.OccsIn M (· ≠ at_) (k coin))
    (hAborts : ∀ source₁, Lawful M source₁ (.call (.given (.coin law) owner hearers at_ [] .nil τ) k) →
      (∀ at' τ', at'.site ∉ heardCoins → source₁ at' τ' = src at' τ') →
      ∃ evs who why, GRun M source₁ (.call (.given (.coin law) owner hearers at_ [] .nil τ) k) evs (.stopped who why) ∧
        prover ∈ who ∧ why.isAbort = true) :
    ∀ source₁, Lawful M source₁ (k coin) →
      (∀ at' τ', at'.site ∉ heardCoins → source₁ at' τ' = src at' τ') →
      ∃ evs who why, GRun M source₁ (k coin) evs (.stopped who why) ∧
        prover ∈ who ∧ why.isAbort = true := by
  intro source₁ hL₁ hAg₁
  let src₂ := patchSource M source₁ at_ τ coin
  have hAg12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = src₂ at' τ' :=
    fun at' τ' hne => (patchSource_ne M source₁ at_ τ coin hne τ').symm
  have hL₂ : Lawful M src₂ (.call (.given (.coin law) owner hearers at_ [] .nil τ) k) := by
    intro w hw
    dsimp only [src₂] at hw; rw [patchSource_self] at hw; cases hw
    exact ⟨hAl, lawful_of_agree M hAg12 hOccK hL₁⟩
  have hAg₂ : ∀ at' τ', at'.site ∉ heardCoins → src₂ at' τ' = src at' τ' := by
    intro at' τ' hNotIn
    have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtH)
    dsimp only [src₂]; rw [patchSource_ne M source₁ at_ τ coin hne τ']
    exact hAg₁ at' τ' hNotIn
  obtain ⟨evs, who, why, hRun₂, hInWho, hIsAb⟩ := hAborts src₂ hL₂ hAg₂
  cases hRun₂ with
  | given hS2 hRk =>
      dsimp only [src₂] at hS2; rw [patchSource_self] at hS2; cases hS2
      exact ⟨_, who, why, grun_of_agree M (fun at' τ' hne => (hAg12 at' τ' hne).symm) hOccK hRk, hInWho, hIsAb⟩

/-- Step a no-halt specification past a non-heard `.given` event (private coin or request). -/
private theorem step_noHalt_given {A : Type} {heardCoins : List Site}
    {src : Source M} {gkind : GivenKind V} {owner : Role} {hearers : List Role}
    {at_ : Occurrence} {gIns : List V.Ty} {payload : HList M.Val gIns} {τ : V.Ty}
    {k : M.Val τ → Protocol M A} {v : M.Val τ}
    (hSrc : src at_ τ = some v) (hAl : Allows M gkind gIns payload τ v)
    (hOccK : Protocol.OccsIn M (· ≠ at_) (k v))
    (hNoHalt : ∀ source₁, Lawful M source₁ (.call (.given gkind owner hearers at_ gIns payload τ) k) →
      (∀ at' τ', at'.site ∉ heardCoins → source₁ at' τ' = src at' τ') →
      ∀ e, GExec M source₁ (.call (.given gkind owner hearers at_ gIns payload τ) k) e → ∃ a, e = .returned a) :
    ∀ source₁, Lawful M source₁ (k v) →
      (∀ at' τ', at'.site ∉ heardCoins → source₁ at' τ' = src at' τ') →
      ∀ e, GExec M source₁ (k v) e → ∃ a, e = .returned a := by
  intro source₁ hL₁ hAg₁ e ⟨evs₁, hRun₁⟩
  by_cases hInH : at_.site ∈ heardCoins
  · let src₂ := patchSource M source₁ at_ τ v
    have hAg12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = src₂ at' τ' :=
      fun at' τ' hne => (patchSource_ne M source₁ at_ τ v hne τ').symm
    have hL₂ : Lawful M src₂ (.call (.given gkind owner hearers at_ gIns payload τ) k) := by
      intro w hw; dsimp only [src₂] at hw; rw [patchSource_self] at hw; cases hw
      exact ⟨hAl, lawful_of_agree M hAg12 hOccK hL₁⟩
    have hAg₂ : ∀ at' τ', at'.site ∉ heardCoins → src₂ at' τ' = src at' τ' := by
      intro at' τ' hNotIn
      have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hInH)
      dsimp only [src₂]; rw [patchSource_ne M source₁ at_ τ v hne τ']
      exact hAg₁ at' τ' hNotIn
    exact hNoHalt src₂ hL₂ hAg₂ e ⟨_, .given (patchSource_self M source₁ at_ τ v) (grun_of_agree M hAg12 hOccK hRun₁)⟩
  · have hS1 : source₁ at_ τ = some v := (hAg₁ at_ τ hInH).trans hSrc
    have hL₂ : Lawful M source₁ (.call (.given gkind owner hearers at_ gIns payload τ) k) := by
      intro w hw; rw [hS1] at hw; cases hw; exact ⟨hAl, hL₁⟩
    exact hNoHalt source₁ hL₂ hAg₁ e ⟨_, .given hS1 hRun₁⟩

/-- Step a no-halt specification past a heard coin event via `patchSource`. -/
private theorem step_noHalt_heard_coin {A : Type} {heardCoins : List Site}
    {src : Source M} {law : V.LawKey} {owner : Role} {hearers : List Role}
    {at_ : Occurrence} {τ : V.Ty} {k : M.Val τ → Protocol M A} {coin : M.Val τ}
    (hAtH : at_.site ∈ heardCoins) (hAl : Allows M (.coin law) [] .nil τ coin)
    (hOccK : Protocol.OccsIn M (· ≠ at_) (k coin))
    (hNoHalt : ∀ source₁, Lawful M source₁ (.call (.given (.coin law) owner hearers at_ [] .nil τ) k) →
      (∀ at' τ', at'.site ∉ heardCoins → source₁ at' τ' = src at' τ') →
      ∀ e, GExec M source₁ (.call (.given (.coin law) owner hearers at_ [] .nil τ) k) e → ∃ a, e = .returned a) :
    ∀ source₁, Lawful M source₁ (k coin) →
      (∀ at' τ', at'.site ∉ heardCoins → source₁ at' τ' = src at' τ') →
      ∀ e, GExec M source₁ (k coin) e → ∃ a, e = .returned a := by
  intro source₁ hL₁ hAg₁ e ⟨evs₁, hRun₁⟩
  let src₂ := patchSource M source₁ at_ τ coin
  have hAg12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = src₂ at' τ' :=
    fun at' τ' hne => (patchSource_ne M source₁ at_ τ coin hne τ').symm
  have hL₂ : Lawful M src₂ (.call (.given (.coin law) owner hearers at_ [] .nil τ) k) := by
    intro w hw; dsimp only [src₂] at hw; rw [patchSource_self] at hw; cases hw
    exact ⟨hAl, lawful_of_agree M hAg12 hOccK hL₁⟩
  have hAg₂ : ∀ at' τ', at'.site ∉ heardCoins → src₂ at' τ' = src at' τ' := by
    intro at' τ' hNotIn
    have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtH)
    dsimp only [src₂]; rw [patchSource_ne M source₁ at_ τ coin hne τ']
    exact hAg₁ at' τ' hNotIn
  exact hNoHalt src₂ hL₂ hAg₂ e ⟨_, .given (patchSource_self M source₁ at_ τ coin) (grun_of_agree M hAg12 hOccK hRun₁)⟩

/-! ### 4b. Post-settle no-abort contradiction (`after_noAbort_contradicts_abort`) -/

/-- Once the prover has settled `target` (entering `.after`, where `why.isAbort = false` for all
reachable halts), a protocol that must abort at the prover on every lawful source agreeing with
`src` outside `heardCoins` yields a contradiction. -/
private theorem after_noAbort_contradicts_abort {enc : VocabEncoder V} {d : Deployed V}
    {suite : ModuleRef} {sessionTag : Option (List Nat)} {layout : Layout}
    {stateTy suiteUnitTy unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {absRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {conP0 : Layer V d.admitted.program.headers prover d.entry.ins}
    {conV0 : Layer V d.admitted.program.headers verifier d.entry.ins}
    {layP0 : Layer V d.admitted.program.headers prover d.entry.ins}
    {layV0 : Layer V d.admitted.program.headers verifier d.entry.ins}
    (hCPSt : conP0.state = stateTy) (hCVSt : conV0.state = stateTy)
    (hLPSt : layP0.state = .seq unitTy none) (hLVSt : layV0.state = streamStateTy unitTy)
    (hConDecl : d.declaration.construction = .derived suite sessionTag)
    (hLayDecl : d.declaration.layout = some layout)
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M)
    (hCC : buildConstructionClauses.go enc d.admitted suite stateTy suiteUnitTy absRef prover verifier
      declKey (d.entry.shape.events [] id) 0
      (d.entry.shape.eventsWithAbsorb prover verifier [] id false) =
      .ok (hCPSt ▸ conP0.clauses, hCVSt ▸ conV0.clauses))
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hLPSt ▸ layP0.clauses, hLVSt ▸ layV0.clauses)) :
    ∀ {A BP BV : Type} (p : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (qP : Program M BP) (qV : Program M BV)
      (st : M.Val stateTy) (src : Source M),
      M.Valid stateTy st →
      Proj M prover postP p qP →
      Proj M verifier postV p qV →
      qP.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      qP.SafeWith M (fun _ _ => True) (ROp.MatchesShape M prover (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      qV.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      qP.SafeWith M (fun _ _ => True) (fun _ => True) (fun _ => True) (fun w => w.isAbort = false) →
      Protocol.MatchesShape M (d.entry.shape.events [] id) p →
      Protocol.UniqueOccs M p →
      LawfulPrivate M src p →
      Fed M src p →
      (∀ source₁, Lawful M source₁ p →
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = src at' τ') →
        ∃ evs who why, GRun M source₁ p evs (.stopped who why) ∧ prover ∈ who ∧ why.isAbort = true) →
      False := by
  let events := d.entry.shape.events [] id
  let eventsAbs := d.entry.shape.eventsWithAbsorb prover verifier [] id false
  have hFst : eventsAbs.map Prod.fst = events :=
    eventsWithAbsorb_fst prover verifier [] id false d.entry.shape
  have hEventDisc : ∀ e ∈ events,
      match e.cls with
      | .flow _ giver getters =>
          (giver = prover ∧ verifier ∈ getters) ∨
          (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
      | .given (.coin law) owner hearers =>
          (owner = verifier ∧ prover ∈ hearers ∧
            ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
          hearers = []
      | .given (.request _) owner hearers =>
          (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
    intro e he
    rw [← hFst] at he
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp he
    exact construction_event_disc 0 eventsAbs hCC p0 hp0
  intro A BP BV p
  induction p with
  | done a =>
      intro _ _ _ _ _ src _ _ _ _ _ _ _ _ _ _ _ hAborts
      obtain ⟨_, _, _, hRun, _, _⟩ := hAborts src trivial (fun _ _ _ => rfl)
      cases hRun
  | halt payload =>
      intro postP postV qP qV st src hStV hPP hPV hSP hShP hShV hNoAb hPShape hUniq hLP hFed hAborts
      obtain ⟨_, who, why, hRun, hInWho, hIsAb⟩ := hAborts src trivial (fun _ _ _ => rfl)
      cases hRun
      generalize hH : Process.halt (who, why) = p0 at hPP
      induction hPP with
      | stopsHere _ => cases hH; exact absurd hIsAb (by rw [hNoAb]; decide)
      | stopsElsewhere hOut => cases hH; exact absurd hInWho hOut
      | begins _ ihP => exact ihP (hSP.2 0 trivial) (hShP.2 0 trivial) (hNoAb.2 0 trivial) hH
      | settles _ ihP => exact ihP (hSP.2 () trivial) (hShP.2 () trivial) (hNoAb.2 () trivial) hH
      | _ => cases hH
  | call op k ih =>
      intro postP postV qP qV st src hStV hPP hPV hSP hShP hShV hNoAb hPShape hUniq hLP hFed hAborts
      generalize hP0 : Process.call op k = p0 at hPP
      induction hPP with
      | begins _ ihP =>
          exact ihP (hSP.2 0 trivial) (hShP.2 0 trivial) (hNoAb.2 0 trivial) hP0
      | settles _ ihP =>
          exact ihP (hSP.2 () trivial) (hShP.2 () trivial) (hNoAb.2 () trivial) hP0
      | done _ => cases hP0
      | stopsHere _ => cases hP0
      | stopsElsewhere _ => cases hP0
      | @gave kind getters at_ τ x kG kP' _ hPP' =>
          cases hP0
          obtain ⟨eP, hEP, hSiteP, hTyP, hClsP⟩ := hShP.1
          have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
          have hVin : verifier ∈ getters := by
            rcases hDisc with ⟨_, hV⟩ | ⟨hNotP, _, _, _⟩
            · exact hV
            · exact absurd rfl hNotP
          obtain ⟨st', _, hSt'V, _, _, _⟩ :=
            derived_step_flow M hCPSt hCVSt hLPSt hLVSt hLayDecl hLayLaw hCC hSL
              hSP.1 (buf := []) hStV (fun _ h => nomatch h) hEP hSiteP hTyP hVin hClsP
          generalize hPV0 : (Process.call (GOp.flow kind prover getters at_ τ x) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | begins _ ihV => exact ihV (hShV.2 0 trivial) hPV0
          | settles _ ihV => exact ihV (hShV.2 () trivial) hPV0
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | gave _ _ => cases hPV0; exact absurd rfl hNe
          | passed _ hVOut _ => cases hPV0; exact absurd hVin hVOut
          | got _ _ hPV' =>
              cases hPV0
              exact ih () _ _ st' src hSt'V hPP' hPV' (hSP.2 () trivial) (hShP.2 () trivial)
                (hShV.2 _ trivial) (hNoAb.2 () trivial) (hPShape.2 ()) (hUniq ()).2 hLP hFed
                (fun s₁ hL₁ hAg₁ => by
                  obtain ⟨_, who, why, hR, hW, hA⟩ := hAborts s₁ hL₁ hAg₁
                  cases hR with | flow hR' => exact ⟨_, who, why, hR', hW, hA⟩)
          | _ => cases hPV0
      | got hGNeP hPIn _ =>
          cases hP0
          obtain ⟨eP, hEP, _, _, _, _, hPin', hClsP⟩ := hShP.1
          have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
          rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, hNotP, _⟩
          · exact absurd hEqP hGNeP
          · exact absurd hPin' hNotP
      | @passed kind giver getters at_ τ x kG _ hGNeP _ hPP' =>
          cases hP0
          generalize hPV0 : (Process.call (GOp.flow kind giver getters at_ τ x) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | begins _ ihV => exact ihV (hShV.2 0 trivial) hPV0
          | settles _ ihV => exact ihV (hShV.2 () trivial) hPV0
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | gave _ _ =>
              cases hPV0
              obtain ⟨eV, hEV, _, _, hClsV⟩ := hShV.1
              have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
              rcases hDisc with ⟨hEqP, _⟩ | ⟨_, hNotV, _, _⟩
              · exact absurd hEqP.symm hNe
              · exact absurd rfl hNotV
          | got _ hVin _ =>
              cases hPV0
              obtain ⟨eV, hEV, _, _, _, _, hVin', hClsV⟩ := hShV.1
              have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
              rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, _, hNotV⟩
              · exact absurd hEqP hGNeP
              · exact absurd hVin' hNotV
          | passed _ _ hPV' =>
              cases hPV0
              exact ih () _ _ st src hStV hPP' hPV' hSP hShP hShV hNoAb (hPShape.2 ()) (hUniq ()).2 hLP hFed
                (fun s₁ hL₁ hAg₁ => by
                  obtain ⟨_, who, why, hR, hW, hA⟩ := hAborts s₁ hL₁ hAg₁
                  cases hR with | flow hR' => exact ⟨_, who, why, hR', hW, hA⟩)
          | _ => cases hPV0
      | @owned gkind hearers at_ gIns payload τ kG kP' hPP' =>
          cases hP0
          obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          have hNotH : (∃ law, gkind = .coin law ∧ hearers = []) ∨
              (∃ svc, gkind = .request svc ∧ verifier ∉ hearers) := by
            cases gkind with
            | coin law =>
                rcases hDisc with ⟨hOwV, _, _⟩ | hNil
                · exact absurd hOwV hNe
                · exact .inl ⟨law, rfl, hNil⟩
            | request svc =>
                exact .inr ⟨svc, rfl, hDisc.2.resolve_left hNe⟩
          generalize hPV0 : (Process.call (GOp.given gkind prover hearers at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | begins _ ihV => exact ihV (hShV.2 0 trivial) hPV0
          | settles _ ihV => exact ihV (hShV.2 () trivial) hPV0
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | owned _ => cases hPV0; exact absurd rfl hNe
          | heard _ hVin _ =>
              cases hPV0
              rcases hNotH with ⟨_, _, rfl⟩ | ⟨_, _, hOut⟩
              · cases hVin
              · exact absurd hVin hOut
          | unheard _ _ hPV' =>
              cases hPV0
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact ih v (kP' v) _ st src hStV (hPP' v) (hPV' v) (hSP.2 v (allows_valid M hAl))
                  (hShP.2 v trivial) hShV (hNoAb.2 v trivial) (hPShape.2 v) (hUniq v).2 hLP' hFed'
                  (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact ih v (kP' v) _ st src hStV (hPP' v) (hPV' v) (hSP.2 v (allows_valid M hAl))
                  (hShP.2 v trivial) hShV (hNoAb.2 v trivial) (hPShape.2 v) (hUniq v).2 hLP' hFed'
                  (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)
          | _ => cases hPV0
      | @heard gkind owner hearers at_ gIns payload τ kG kP' hOwNe hPin hPP' =>
          cases hP0
          obtain ⟨eG, hEG, hSiteG, hTyG, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          cases gkind with
          | request svc => exact absurd hPin (hDisc.1.resolve_left hOwNe)
          | coin law =>
              rcases hDisc with ⟨hOwV, _, sig, hLaw, _, hSigIns⟩ | hNil
              · cases hOwV
                have hNonEmpty : ∃ h0 hs, hearers = h0 :: hs := by
                  cases hearers with
                  | nil => cases hPin
                  | cons h0 hs => exact ⟨h0, hs, rfl⟩
                obtain ⟨h0, hs, hHCons⟩ := hNonEmpty
                subst hHCons
                generalize hPV0 : (Process.call (GOp.given (.coin law) verifier (h0 :: hs) at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
                induction hPV with
                | begins _ ihV => exact ihV (hShV.2 0 trivial) hPV0
                | settles _ ihV => exact ihV (hShV.2 () trivial) hPV0
                | done _ => cases hPV0
                | stopsHere _ => cases hPV0
                | stopsElsewhere _ => cases hPV0
                | heard hNeS _ _ => cases hPV0; exact absurd rfl hNeS
                | unheard hNeS _ _ => cases hPV0; exact absurd rfl hNeS
                | owned hPV' =>
                    cases hPV0
                    obtain ⟨eV, hEV, hSiteV, hTyV, hClsV, hTypedV⟩ := hShV.1
                    have hGInsNil : gIns = [] := by
                      obtain ⟨s, hsLaw, hsIns, _⟩ := hTypedV
                      rw [hLaw] at hsLaw; cases hsLaw; rw [← hsIns, hSigIns]
                    subst hGInsNil; cases payload
                    obtain ⟨coin, st', _, hCoinV, hAl, hAtH, hSt'V, _, _, _⟩ :=
                      derived_step_heard_coin M hCPSt hCVSt hLPSt hLVSt hConDecl hLayDecl hSuiteLaw hLayLaw
                        hCC hSL (buf := []) hStV (fun _ h => nomatch h) hEV hSiteV hTyV hPin hClsV
                    exact ih coin (kP' coin) _ st' src hSt'V (hPP' coin) (hPV' coin)
                      (hSP.2 coin hCoinV) (hShP.2 coin trivial) (hShV.2 coin trivial)
                      (hNoAb.2 coin trivial) (hPShape.2 coin) (hUniq coin).2
                      (hLP coin hAl) (hFed coin hAl)
                      (step_aborts_heard_coin M hAtH hAl (hUniq coin).1 hAborts)
                | _ => cases hPV0
              · subst hNil; cases hPin
      | @unheard gkind owner hearers at_ gIns payload τ kG q hOwNe hNotIn hPP' =>
          cases hP0
          obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          have hNotH : (∃ law, gkind = .coin law ∧ hearers = []) ∨
              (∃ svc, gkind = .request svc ∧ (owner = verifier ∨ verifier ∉ hearers)) := by
            cases gkind with
            | coin law =>
                rcases hDisc with ⟨_, hPin', _⟩ | hNil
                · exact absurd hPin' hNotIn
                · exact .inl ⟨law, rfl, hNil⟩
            | request svc => exact .inr ⟨svc, rfl, hDisc.2⟩
          generalize hPV0 : (Process.call (GOp.given gkind owner hearers at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | begins _ ihV => exact ihV (hShV.2 0 trivial) hPV0
          | settles _ ihV => exact ihV (hShV.2 () trivial) hPV0
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | owned hPV' =>
              cases hPV0
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact ih v q _ st src hStV (hPP' v) (hPV' v) hSP hShP (hShV.2 v trivial) hNoAb
                  (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact ih v q _ st src hStV (hPP' v) (hPV' v) hSP hShP (hShV.2 v trivial) hNoAb
                  (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)
          | heard _ hVin _ =>
              cases hPV0
              rcases hNotH with ⟨_, _, rfl⟩ | ⟨_, _, hVO⟩
              · cases hVin
              · exact absurd hVin (hVO.resolve_left (by assumption))
          | unheard _ _ hPV' =>
              cases hPV0
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact ih v q _ st src hStV (hPP' v) (hPV' v) hSP hShP hShV hNoAb
                  (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact ih v q _ st src hStV (hPP' v) (hPV' v) hSP hShP hShV hNoAb
                  (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)

          | _ => cases hPV0
/-! ### 4c. Aborting attempt simulation inside `Handler.inside` (`simulate_prover_abort_inside`) -/

private theorem simulate_prover_abort_inside {enc : VocabEncoder V} {d : Deployed V}
    {suite : ModuleRef} {sessionTag : Option (List Nat)} {layout : Layout}
    {stateTy suiteUnitTy unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {absRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {conP0 : Layer V d.admitted.program.headers prover d.entry.ins}
    {conV0 : Layer V d.admitted.program.headers verifier d.entry.ins}
    {layP0 : Layer V d.admitted.program.headers prover d.entry.ins}
    {layV0 : Layer V d.admitted.program.headers verifier d.entry.ins}
    (hCPSt : conP0.state = stateTy) (hCVSt : conV0.state = stateTy)
    (hLPSt : layP0.state = .seq unitTy none) (hLVSt : layV0.state = streamStateTy unitTy)
    (hConDecl : d.declaration.construction = .derived suite sessionTag)
    (hLayDecl : d.declaration.layout = some layout)
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M)
    (hCC : buildConstructionClauses.go enc d.admitted suite stateTy suiteUnitTy absRef prover verifier
      declKey (d.entry.shape.events [] id) 0
      (d.entry.shape.eventsWithAbsorb prover verifier [] id false) =
      .ok (hCPSt ▸ conP0.clauses, hCVSt ▸ conV0.clauses))
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hLPSt ▸ layP0.clauses, hLVSt ▸ layV0.clauses))
    (bound : Nat) (target : Site) (j : Nat) :
    let insideCoins := d.entry.shape.attemptPrivateCoins prover target [] false
    let fnTable := Defs.fnTable M d.admitted.program.defs
    let rTable := Defs.rTable M d.admitted.program.defs
    let hP := Stack.handler M fnTable rTable [conP0, layP0]
    ∀ {A BP BV : Type} (p : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (qP : Program M BP) (qV : Program M BV)
      (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M),
      M.Valid stateTy st → (∀ u ∈ buf, M.Valid unitTy u) →
      Proj M prover postP p qP → Proj M verifier postV p qV →
      qP.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      qP.SafeWith M (fun _ _ => True) (ROp.MatchesShape M prover (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      qV.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      Program.RetryWellFormed M target insideCoins .inside qP →
      Protocol.MatchesShape M (d.entry.shape.events [] id) p →
      Protocol.UniqueOccs M p →
      LawfulPrivate M (shiftAttemptSource M insideCoins (.attempt target.key j) source) p →
      Fed M (shiftAttemptSource M insideCoins (.attempt target.key j) source) p →
      (∀ source₁, Lawful M source₁ p →
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
          source₁ at' τ' = shiftAttemptSource M insideCoins (.attempt target.key j) source at' τ') →
        ∃ evs who why, GRun M source₁ p evs (.stopped who why) ∧ prover ∈ who ∧ why.isAbort = true) →
      ∃ why sAbort rec,
        why.isAbort = true ∧
        Alone M source prover
          (Handler.inside hP (retryOf M (some (bound, target))) j qP
            (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
          rec (.stopped ((true, why), sAbort)) := by
  intro insideCoins fnTable rTable hP
  let events := d.entry.shape.events [] id
  let eventsAbs := d.entry.shape.eventsWithAbsorb prover verifier [] id false
  have hFst : eventsAbs.map Prod.fst = events :=
    eventsWithAbsorb_fst prover verifier [] id false d.entry.shape
  have hPassP : ∀ op (st : M.Val stateTy) (buf : List (M.Val unitTy)),
      ROp.IsClosed M op →
      hP.clause op (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) =
        .call op fun reply => .done (reply, .cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) := by
    intro op st buf hCl
    have hCU := construction_clauses_unmatched_closed M 0 eventsAbs hCC op hCl
    have hLU := streaming_layout_unmatched_closed M 0 events hSL op hCl
    cases conP0 with | mk cPL cPSt cPT cPG cPCl cPA cPS cPF =>
    cases layP0 with | mk lPL lPSt lPT lPG lPCl lPA lPS lPF =>
    dsimp only at hCPSt hLPSt; subst cPSt; subst lPSt
    exact stack2_clause_pass M fnTable rTable
      ⟨cPL, stateTy, cPT, cPG, cPCl, cPA, cPS, cPF⟩
      ⟨lPL, .seq unitTy none, lPT, lPG, lPCl, lPA, lPS, lPF⟩ op st buf
      (clause_answer_unmatched_all M fnTable rTable op st cPCl hCU.1)
      (clause_answer_unmatched_all M fnTable rTable op buf lPCl hLU.1)
  have hEventDisc : ∀ e ∈ events,
      match e.cls with
      | .flow _ giver getters =>
          (giver = prover ∧ verifier ∈ getters) ∨
          (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
      | .given (.coin law) owner hearers =>
          (owner = verifier ∧ prover ∈ hearers ∧
            ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
          hearers = []
      | .given (.request _) owner hearers =>
          (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
    intro e he
    rw [← hFst] at he
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp he
    exact construction_event_disc 0 eventsAbs hCC p0 hp0
  intro A BP BV p
  induction p with
  | done a =>
      intro _ _ _ _ _ _ source _ _ _ _ _ _ _ _ _ _ _ _ hAborts
      obtain ⟨_, _, _, hRun, _, _⟩ := hAborts (shiftAttemptSource M insideCoins (.attempt target.key j) source)
        trivial (fun _ _ _ => rfl)
      cases hRun
  | halt payload =>
      intro postP postV qP qV st buf source hStV hBufV hPP hPV hSP hShP hShV hRWF hPShape hUniq hLP hFed hAborts
      obtain ⟨_, who, why, hRun, hInWho, hIsAb⟩ :=
        hAborts (shiftAttemptSource M insideCoins (.attempt target.key j) source) trivial (fun _ _ _ => rfl)
      cases hRun
      generalize hH : Process.halt (who, why) = p0 at hPP
      induction hPP with
      | stopsHere _ =>
          cases hH
          exact ⟨why, _, [], hIsAb, by simpa [Handler.inside] using Alone.halt⟩
      | stopsElsewhere hOut => cases hH; exact absurd hInWho hOut
      | @begins at_ _ kP' _ ihP =>
          obtain ⟨why', sAb, rec, hAb', hAl⟩ := ihP (hSP.2 0 trivial) (hShP.2 0 trivial) (hRWF.2 0) hH
          exact ⟨why', sAb, .began prover at_ :: rec, hAb', by
            rw [handler_inside_pass_begin M hP bound target j at_ kP' _ (hPassP _ st buf trivial)]
            exact .begin hAl⟩
      | @settles at_ _ kP' hPP' ihP =>
          by_cases hIsT : at_.site = target
          · dsimp only [Program.RetryWellFormed] at hRWF
            rw [ite_eq_left hIsT] at hRWF
            have hAft := retryWellFormed_after_safe M (hRWF ())
            have hNoAb := Process.safeWith_mono M (fun _ _ h => h) (fun _ _ => trivial)
              (fun _ _ => trivial) (fun _ h => h) hAft
            exact False.elim (after_noAbort_contradicts_abort M hNe hCPSt hCVSt hLPSt hLVSt
              hConDecl hLayDecl hSuiteLaw hLayLaw hCC hSL _ (kP' ()) qV st
              (shiftAttemptSource M insideCoins (.attempt target.key j) source) hStV
              hPP' (hH ▸ hPV) (hSP.2 () trivial) (hShP.2 () trivial) hShV hNoAb
              (hH ▸ hPShape) (hH ▸ hUniq) (hH ▸ hLP) (hH ▸ hFed) (hH ▸ hAborts))
          · dsimp only [Program.RetryWellFormed] at hRWF
            rw [ite_eq_right hIsT] at hRWF
            obtain ⟨why', sAb, rec, hAb', hAl⟩ := ihP (hSP.2 () trivial) (hShP.2 () trivial) (hRWF ()) hH
            exact ⟨why', sAb, .settled prover at_ :: rec, hAb', by
              rw [handler_inside_pass_settle_other M hP bound target j at_ hIsT kP' _ (hPassP _ st buf trivial)]
              exact .settle hAl⟩
      | _ => cases hH
  | call op k ih =>
      intro postP postV qP qV st buf source hStV hBufV hPP hPV hSP hShP hShV hRWF hPShape hUniq hLP hFed hAborts
      let attemptSrc := shiftAttemptSource M insideCoins (.attempt target.key j) source
      generalize hP0 : Process.call op k = p0 at hPP
      induction hPP with
      | @begins at_ _ kP' _ ihP =>
          obtain ⟨why', sAb, rec, hAb', hAl⟩ := ihP (hSP.2 0 trivial) (hShP.2 0 trivial) (hRWF.2 0) hP0
          exact ⟨why', sAb, .began prover at_ :: rec, hAb', by
            rw [handler_inside_pass_begin M hP bound target j at_ kP' _ (hPassP _ st buf trivial)]
            exact .begin hAl⟩
      | @settles at_ _ kP' hPP' ihP =>
          by_cases hIsT : at_.site = target
          · dsimp only [Program.RetryWellFormed] at hRWF
            rw [ite_eq_left hIsT] at hRWF
            have hAft := retryWellFormed_after_safe M (hRWF ())
            have hNoAb := Process.safeWith_mono M (fun _ _ h => h) (fun _ _ => trivial)
              (fun _ _ => trivial) (fun _ h => h) hAft
            exact False.elim (after_noAbort_contradicts_abort M hNe hCPSt hCVSt hLPSt hLVSt
              hConDecl hLayDecl hSuiteLaw hLayLaw hCC hSL _ (kP' ()) qV st attemptSrc hStV
              hPP' (hP0 ▸ hPV) (hSP.2 () trivial) (hShP.2 () trivial) hShV hNoAb
              (hP0 ▸ hPShape) (hP0 ▸ hUniq) (hP0 ▸ hLP) (hP0 ▸ hFed) (hP0 ▸ hAborts))
          · dsimp only [Program.RetryWellFormed] at hRWF
            rw [ite_eq_right hIsT] at hRWF
            obtain ⟨why', sAb, rec, hAb', hAl⟩ := ihP (hSP.2 () trivial) (hShP.2 () trivial) (hRWF ()) hP0
            exact ⟨why', sAb, .settled prover at_ :: rec, hAb', by
              rw [handler_inside_pass_settle_other M hP bound target j at_ hIsT kP' _ (hPassP _ st buf trivial)]
              exact .settle hAl⟩
      | done _ => cases hP0
      | stopsHere _ => cases hP0
      | stopsElsewhere _ => cases hP0
      | @gave kind getters at_ τ x kG kP' _ hPP' =>
          cases hP0
          obtain ⟨eP, hEP, hSiteP, hTyP, hClsP⟩ := hShP.1
          have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
          have hVin : verifier ∈ getters := by
            rcases hDisc with ⟨_, hV⟩ | ⟨hNotP, _, _, _⟩
            · exact hV
            · exact absurd rfl hNotP
          obtain ⟨st', chunk, hSt'V, hChV, hStepP, _⟩ :=
            derived_step_flow M hCPSt hCVSt hLPSt hLVSt hLayDecl hLayLaw hCC hSL
              hSP.1 hStV hBufV hEP hSiteP hTyP hVin hClsP
          have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := fun u hu =>
            (List.mem_append.mp hu).elim (hBufV u) (hChV u)
          generalize hPV0 : (Process.call (GOp.flow kind prover getters at_ τ x) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | begins _ ihV => exact ihV (hShV.2 0 trivial) hPV0
          | settles _ ihV => exact ihV (hShV.2 () trivial) hPV0
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | gave _ _ => cases hPV0; exact absurd rfl hNe
          | passed _ hVOut _ => cases hPV0; exact absurd hVin hVOut
          | got _ _ hPV' =>
              cases hPV0
              obtain ⟨why', sAb, rec, hAb', hAl⟩ :=
                ih () (kP' ()) _ st' (buf ++ chunk) source hSt'V hBufChV hPP' hPV'
                  (hSP.2 () trivial) (hShP.2 () trivial) (hShV.2 x trivial) (hRWF ())
                  (hPShape.2 ()) (hUniq ()).2 hLP hFed
                  (fun s₁ hL₁ hAg₁ => by
                    obtain ⟨_, who, why, hR, hW, hA⟩ := hAborts s₁ hL₁ hAg₁
                    cases hR with | flow hR' => exact ⟨_, who, why, hR', hW, hA⟩)
              exact ⟨why', sAb, rec, hAb',
                alone_eq_proc M (handler_inside_clause_done M hP bound target j (.give kind getters at_ τ x) rfl kP' _ _ () hStepP) hAl⟩
          | _ => cases hPV0
      | got hGNeP hPIn _ =>
          cases hP0
          obtain ⟨eP, hEP, _, _, _, _, hPin', hClsP⟩ := hShP.1
          have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
          rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, hNotP, _⟩
          · exact absurd hEqP hGNeP
          · exact absurd hPin' hNotP
      | @passed kind giver getters at_ τ x kG _ hGNeP _ hPP' =>
          cases hP0
          generalize hPV0 : (Process.call (GOp.flow kind giver getters at_ τ x) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | begins _ ihV => exact ihV (hShV.2 0 trivial) hPV0
          | settles _ ihV => exact ihV (hShV.2 () trivial) hPV0
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | gave _ _ =>
              cases hPV0
              obtain ⟨eV, hEV, _, _, hClsV⟩ := hShV.1
              have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
              rcases hDisc with ⟨hEqP, _⟩ | ⟨_, hNotV, _, _⟩
              · exact absurd hEqP.symm hNe
              · exact absurd rfl hNotV
          | got _ hVin _ =>
              cases hPV0
              obtain ⟨eV, hEV, _, _, _, _, hVin', hClsV⟩ := hShV.1
              have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
              rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, _, hNotV⟩
              · exact absurd hEqP hGNeP
              · exact absurd hVin' hNotV
          | passed _ _ hPV' =>
              cases hPV0
              exact ih () _ _ st buf source hStV hBufV hPP' hPV' hSP hShP hShV hRWF
                (hPShape.2 ()) (hUniq ()).2 hLP hFed
                (fun s₁ hL₁ hAg₁ => by
                  obtain ⟨_, who, why, hR, hW, hA⟩ := hAborts s₁ hL₁ hAg₁
                  cases hR with | flow hR' => exact ⟨_, who, why, hR', hW, hA⟩)
          | _ => cases hPV0
      | @owned gkind hearers at_ gIns payload τ kG kP' hPP' =>
          cases hP0
          obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          have hNotH : (∃ law, gkind = .coin law ∧ hearers = []) ∨
              (∃ svc, gkind = .request svc ∧ verifier ∉ hearers) := by
            cases gkind with
            | coin law =>
                rcases hDisc with ⟨hOwV, _, _⟩ | hNil
                · exact absurd hOwV hNe
                · exact .inl ⟨law, rfl, hNil⟩
            | request svc => exact .inr ⟨svc, rfl, hDisc.2.resolve_left hNe⟩
          generalize hPV0 : (Process.call (GOp.given gkind prover hearers at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | begins _ ihV => exact ihV (hShV.2 0 trivial) hPV0
          | settles _ ihV => exact ihV (hShV.2 () trivial) hPV0
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | owned _ => cases hPV0; exact absurd rfl hNe
          | heard _ hVin _ =>
              cases hPV0
              rcases hNotH with ⟨_, _, rfl⟩ | ⟨_, _, hOut⟩
              · cases hVin
              · exact absurd hVin hOut
          | unheard _ _ hPV' =>
              cases hPV0
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                have hInC : at_.site ∈ insideCoins := hRWF.1
                have hSrcSh : source ⟨.attempt target.key j :: at_.path, at_.key⟩ τ = some v := by
                  have h := hvSrc
                  dsimp only [attemptSrc, shiftAttemptSource] at h
                  rwa [ite_eq_left hInC] at h
                obtain ⟨why', sAb, rec, hAb', hAlP⟩ :=
                  ih v (kP' v) _ st buf source hStV hBufV (hPP' v) (hPV' v)
                    (hSP.2 v (allows_valid M hAl)) (hShP.2 v trivial) hShV (hRWF.2 v)
                    (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)
                exact ⟨why', sAb, _, hAb', by
                  rw [handler_inside_pass_private_coin M hP bound target j law at_ gIns payload τ kP' _
                    (hPassP _ st buf trivial)]
                  exact .own hSrcSh hAlP⟩
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                have hOutC : at_.site ∉ insideCoins := hRWF.1
                have hSrcEq : source at_ τ = some v := by
                  have h := hvSrc
                  dsimp only [attemptSrc, shiftAttemptSource] at h
                  rwa [ite_eq_right hOutC] at h
                obtain ⟨why', sAb, rec, hAb', hAlP⟩ :=
                  ih v (kP' v) _ st buf source hStV hBufV (hPP' v) (hPV' v)
                    (hSP.2 v (allows_valid M hAl)) (hShP.2 v trivial) hShV (hRWF.2 v)
                    (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)
                exact ⟨why', sAb, _, hAb', by
                  rw [handler_inside_pass_request M hP bound target j svc hearers at_ gIns payload τ kP' _
                    (hPassP _ st buf trivial)]
                  exact .own hSrcEq hAlP⟩
          | _ => cases hPV0
      | @heard gkind owner hearers at_ gIns payload τ kG kP' hOwNe hPin hPP' =>
          cases hP0
          obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          cases gkind with
          | request svc => exact absurd hPin (hDisc.1.resolve_left hOwNe)
          | coin law =>
              rcases hDisc with ⟨hOwV, _, sig, hLaw, _, hSigIns⟩ | hNil
              · cases hOwV
                have hNonEmpty : ∃ h0 hs, hearers = h0 :: hs := by
                  cases hearers with
                  | nil => cases hPin
                  | cons h0 hs => exact ⟨h0, hs, rfl⟩
                obtain ⟨h0, hs, hHCons⟩ := hNonEmpty
                subst hHCons
                generalize hPV0 : (Process.call (GOp.given (.coin law) verifier (h0 :: hs) at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
                induction hPV with
                | begins _ ihV => exact ihV (hShV.2 0 trivial) hPV0
                | settles _ ihV => exact ihV (hShV.2 () trivial) hPV0
                | done _ => cases hPV0
                | stopsHere _ => cases hPV0
                | stopsElsewhere _ => cases hPV0
                | heard hNeS _ _ => cases hPV0; exact absurd rfl hNeS
                | unheard hNeS _ _ => cases hPV0; exact absurd rfl hNeS
                | owned hPV' =>
                    cases hPV0
                    obtain ⟨eV, hEV, hSiteV, hTyV, hClsV, hTypedV⟩ := hShV.1
                    have hGInsNil : gIns = [] := by
                      obtain ⟨s, hsLaw, hsIns, _⟩ := hTypedV
                      rw [hLaw] at hsLaw; cases hsLaw; rw [← hsIns, hSigIns]
                    subst hGInsNil; cases payload
                    obtain ⟨coin, st', chunk, hCoinV, hAl, hAtH, hSt'V, hChV, hStepP, _⟩ :=
                      derived_step_heard_coin M hCPSt hCVSt hLPSt hLVSt hConDecl hLayDecl hSuiteLaw hLayLaw
                        hCC hSL hStV hBufV hEV hSiteV hTyV hPin hClsV
                    have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := fun u hu =>
                      (List.mem_append.mp hu).elim (hBufV u) (hChV u)
                    obtain ⟨why', sAb, rec, hAb', hAlP⟩ :=
                      ih coin (kP' coin) _ st' (buf ++ chunk) source hSt'V hBufChV (hPP' coin) (hPV' coin)
                        (hSP.2 coin hCoinV) (hShP.2 coin trivial) (hShV.2 coin trivial) (hRWF coin)
                        (hPShape.2 coin) (hUniq coin).2 (hLP coin hAl) (hFed coin hAl)
                        (step_aborts_heard_coin M hAtH hAl (hUniq coin).1 hAborts)
                    exact ⟨why', sAb, rec, hAb',
                      alone_eq_proc M (handler_inside_clause_done M hP bound target j (.hear (.coin law) verifier at_ τ) rfl kP' _ _ coin hStepP) hAlP⟩
                | _ => cases hPV0
              · subst hNil; cases hPin
      | @unheard gkind owner hearers at_ gIns payload τ kG q hOwNe hNotIn hPP' =>
          cases hP0
          obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          have hNotH : (∃ law, gkind = .coin law ∧ hearers = []) ∨
              (∃ svc, gkind = .request svc ∧ (owner = verifier ∨ verifier ∉ hearers)) := by
            cases gkind with
            | coin law =>
                rcases hDisc with ⟨_, hPin', _⟩ | hNil
                · exact absurd hPin' hNotIn
                · exact .inl ⟨law, rfl, hNil⟩
            | request svc => exact .inr ⟨svc, rfl, hDisc.2⟩
          generalize hPV0 : (Process.call (GOp.given gkind owner hearers at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | begins _ ihV => exact ihV (hShV.2 0 trivial) hPV0
          | settles _ ihV => exact ihV (hShV.2 () trivial) hPV0
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | owned hPV' =>
              cases hPV0
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact ih v q _ st buf source hStV hBufV (hPP' v) (hPV' v) hSP hShP (hShV.2 v trivial)
                  hRWF (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact ih v q _ st buf source hStV hBufV (hPP' v) (hPV' v) hSP hShP (hShV.2 v trivial)
                  hRWF (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)
          | heard _ hVin _ =>
              cases hPV0
              rcases hNotH with ⟨_, _, rfl⟩ | ⟨_, _, hVO⟩
              · cases hVin
              · exact absurd hVin (hVO.resolve_left (by assumption))
          | unheard _ _ hPV' =>
              cases hPV0
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact ih v q _ st buf source hStV hBufV (hPP' v) (hPV' v) hSP hShP hShV
                  hRWF (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact ih v q _ st buf source hStV hBufV (hPP' v) (hPV' v) hSP hShP hShV
                  hRWF (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_aborts_given M hvSrc hAl (hUniq v).1 hAborts)

          | _ => cases hPV0
/-! ### 4d. Coupled simulation inside attempt `k` (`simulate_retry_coupled_inside`) -/

private theorem simulate_retry_coupled_inside {enc : VocabEncoder V} {d : Deployed V}
    {suite : ModuleRef} {sessionTag : Option (List Nat)} {layout : Layout}
    {stateTy suiteUnitTy unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {absRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    (conP0 : Layer V d.admitted.program.headers prover d.entry.ins)
    (conV0 : Layer V d.admitted.program.headers verifier d.entry.ins)
    (layP0 : Layer V d.admitted.program.headers prover d.entry.ins)
    (layV0 : Layer V d.admitted.program.headers verifier d.entry.ins)
    (hCPSt : conP0.state = stateTy) (hCVSt : conV0.state = stateTy)
    (hLPSt : layP0.state = .seq unitTy none) (hLVSt : layV0.state = streamStateTy unitTy)
    (hConDecl : d.declaration.construction = .derived suite sessionTag)
    (hLayDecl : d.declaration.layout = some layout)
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M)
    (hCC : buildConstructionClauses.go enc d.admitted suite stateTy suiteUnitTy absRef prover verifier
      declKey (d.entry.shape.events [] id) 0
      (d.entry.shape.eventsWithAbsorb prover verifier [] id false) =
      .ok (hCPSt ▸ conP0.clauses, hCVSt ▸ conV0.clauses))
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hLPSt ▸ layP0.clauses, hLVSt ▸ layV0.clauses))
    (bound : Nat) (target : Site) (kIdx : Nat)
    (hExcl : d.entry.shape.attemptCoinsExclusive prover target = true) :
    let insideCoins := d.entry.shape.attemptPrivateCoins prover target [] false
    let fnTable := Defs.fnTable M d.admitted.program.defs
    let rTable := Defs.rTable M d.admitted.program.defs
    let hP := Stack.handler M fnTable rTable [conP0, layP0]
    let hV := Stack.handler M fnTable rTable [conV0, layV0]
    ∀ {A BP BV : Type} (p : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (qP : Program M BP) (qV : Program M BV)
      (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M),
      M.Valid stateTy st → (∀ u ∈ buf, M.Valid unitTy u) →
      Proj M prover postP p qP → Proj M verifier postV p qV →
      qP.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      qV.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      qP.SafeWith M (fun _ _ => True) (ROp.MatchesShape M prover (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      qV.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      Program.RetryWellFormed M target insideCoins .inside qP →
      Protocol.MatchesShape M (d.entry.shape.events [] id) p →
      Protocol.UniqueOccs M p →
      LawfulPrivate M (shiftAttemptSource M insideCoins (.attempt target.key kIdx) source) p →
      Fed M (shiftAttemptSource M insideCoins (.attempt target.key kIdx) source) p →
      (∀ source₁, Lawful M source₁ p →
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
          source₁ at' τ' = shiftAttemptSource M insideCoins (.attempt target.key kIdx) source at' τ') →
        ∀ e, GExec M source₁ p e → ∃ a, e = .returned a) →
      ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
        (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
        (∀ u ∈ suffix, M.Valid unitTy u) ∧
        Alone M source prover
          (Handler.inside hP (retryOf M (some (bound, target))) kIdx qP
            (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
          recP (.returned (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ suffix)) .nil))) ∧
        (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
          ∃ recV, Alone M source verifier
            (hV.run (retryOf M none) qV
              (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
            recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
              (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
        postP a outP ∧ postV a outV ∧
        Lawful M source' p ∧
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
          source' at' τ' = shiftAttemptSource M insideCoins (.attempt target.key kIdx) source at' τ') ∧
        GExec M source' p (.returned a) := by
  intro insideCoins fnTable rTable hP hV
  let events := d.entry.shape.events [] id
  let eventsAbs := d.entry.shape.eventsWithAbsorb prover verifier [] id false
  have hFst : eventsAbs.map Prod.fst = events :=
    eventsWithAbsorb_fst prover verifier [] id false d.entry.shape
  have hPassP : ∀ op (st : M.Val stateTy) (buf : List (M.Val unitTy)),
      ROp.IsClosed M op →
      hP.clause op (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) =
        .call op fun reply => .done (reply, .cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) := by
    intro op st buf hCl
    have hCU := construction_clauses_unmatched_closed M 0 eventsAbs hCC op hCl
    have hLU := streaming_layout_unmatched_closed M 0 events hSL op hCl
    cases conP0 with | mk cPL cPSt cPT cPG cPCl cPA cPS cPF =>
    cases layP0 with | mk lPL lPSt lPT lPG lPCl lPA lPS lPF =>
    dsimp only at hCPSt hLPSt; subst cPSt; subst lPSt
    exact stack2_clause_pass M fnTable rTable
      ⟨cPL, stateTy, cPT, cPG, cPCl, cPA, cPS, cPF⟩
      ⟨lPL, .seq unitTy none, lPT, lPG, lPCl, lPA, lPS, lPF⟩ op st buf
      (clause_answer_unmatched_all M fnTable rTable op st cPCl hCU.1)
      (clause_answer_unmatched_all M fnTable rTable op buf lPCl hLU.1)
  have hPassV : ∀ op (st : M.Val stateTy) (lst : M.Val (streamStateTy unitTy)),
      ROp.IsClosed M op →
      hV.clause op (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ lst) .nil)) =
        .call op fun reply => .done (reply, .cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ lst) .nil)) := by
    intro op st lst hCl
    have hCU := construction_clauses_unmatched_closed M 0 eventsAbs hCC op hCl
    have hLU := streaming_layout_unmatched_closed M 0 events hSL op hCl
    cases conV0 with | mk cVL cVSt cVT cVG cVCl cVA cVS cVF =>
    cases layV0 with | mk lVL lVSt lVT lVG lVCl lVA lVS lVF =>
    dsimp only at hCVSt hLVSt; subst cVSt; subst lVSt
    exact stack2_clause_pass M fnTable rTable
      ⟨cVL, stateTy, cVT, cVG, cVCl, cVA, cVS, cVF⟩
      ⟨lVL, streamStateTy unitTy, lVT, lVG, lVCl, lVA, lVS, lVF⟩ op st lst
      (clause_answer_unmatched_all M fnTable rTable op st cVCl hCU.2)
      (clause_answer_unmatched_all M fnTable rTable op lst lVCl hLU.2)
  have hEventDisc : ∀ e ∈ events,
      match e.cls with
      | .flow _ giver getters =>
          (giver = prover ∧ verifier ∈ getters) ∨
          (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
      | .given (.coin law) owner hearers =>
          (owner = verifier ∧ prover ∈ hearers ∧
            ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
          hearers = []
      | .given (.request _) owner hearers =>
          (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
    intro e he
    rw [← hFst] at he
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp he
    exact construction_event_disc 0 eventsAbs hCC p0 hp0
  -- Handoff helper at `.settle target` → delegates directly to `simulate_derived_gen`!
  have hHandoffAfter : ∀ {A BP BV : Type} (p0 : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (qP0 : Program M BP) (qV0 : Program M BV)
      (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M),
      let attemptSrc := shiftAttemptSource M insideCoins (.attempt target.key kIdx) source
      M.Valid stateTy st → (∀ u ∈ buf, M.Valid unitTy u) →
      Proj M prover postP p0 qP0 → Proj M verifier postV p0 qV0 →
      qP0.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      qV0.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      qP0.SafeWith M (fun _ _ => True) (ROp.MatchesShape M prover events) (fun _ => True) (fun _ => True) →
      qV0.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier events) (fun _ => True) (fun _ => True) →
      Program.RetryWellFormed M target insideCoins .after qP0 →
      Protocol.MatchesShape M events p0 → Protocol.UniqueOccs M p0 →
      LawfulPrivate M attemptSrc p0 → Fed M attemptSrc p0 →
      (∀ source₁, Lawful M source₁ p0 →
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = attemptSrc at' τ') →
        ∀ e, GExec M source₁ p0 e → ∃ a, e = .returned a) →
      ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
        (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
        (∀ u ∈ suffix, M.Valid unitTy u) ∧
        Alone M source prover
          ((hP.run (retryOf M (some (bound, target))) qP0
            (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil))).mapHalt
              fun stop => ((false, stop.1), stop.2))
          recP (.returned (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ suffix)) .nil))) ∧
        (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
          ∃ recV, Alone M source verifier
            (hV.run (retryOf M none) qV0
              (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
            recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
              (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
        postP a outP ∧ postV a outV ∧
        Lawful M source' p0 ∧
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source' at' τ' = attemptSrc at' τ') ∧
        GExec M source' p0 (.returned a) := by
    intro A BP BV p0 postP postV qP0 qV0 st buf source attemptSrc hStV hBufV hPP0 hPV0
      hSP0 hSV0 hShP0 hShV0 hAfter hPShape0 hUniq0 hLP0 hFed0 hNoHalt0
    have hAftSafe := retryWellFormed_after_safe M hAfter
    have hNotMark : qP0.SafeWith M (fun _ _ => True) (ROp.NotMarkAt M target) (fun _ => True) (fun _ => True) :=
      Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h.1) (fun _ _ => trivial) (fun _ _ => trivial) hAftSafe
    have hNoInside : Protocol.NoSitesIn M insideCoins p0 :=
      proj_after_noSitesIn M hExcl hPP0 hAftSafe hPShape0
    have hAgOut : ∀ at' τ', at'.site ∉ insideCoins → attemptSrc at' τ' = source at' τ' := by
      intro at' τ' hOut; dsimp only [attemptSrc, shiftAttemptSource]; exact ite_eq_right hOut
    have hLPSrc : LawfulPrivate M source p0 := lawfulPrivate_of_agree_sites M hAgOut hNoInside hLP0
    have hFedSrc : Fed M source p0 := fed_of_agree_sites M hAgOut hNoInside hFed0
    have hNoHaltSrc : ∀ source₁, Lawful M source₁ p0 →
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
        ∀ e, GExec M source₁ p0 e → ∃ a, e = .returned a := by
      intro source₁ hL₁ hAg₁ e ⟨evs₁, hRun₁⟩
      let src₂ : Source M := fun at' τ' => if at'.site ∈ insideCoins then attemptSrc at' τ' else source₁ at' τ'
      have hAg12 : ∀ at' τ', at'.site ∉ insideCoins → source₁ at' τ' = src₂ at' τ' := by
        intro at' τ' hOut; dsimp only [src₂]; rw [ite_eq_right hOut]
      have hL₂ : Lawful M src₂ p0 := lawful_of_agree_sites M hAg12 hNoInside hL₁
      have hAg₂ : ∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → src₂ at' τ' = attemptSrc at' τ' := by
        intro at' τ' hNotH
        dsimp only [src₂]
        by_cases hInC : at'.site ∈ insideCoins
        · rw [ite_eq_left hInC]
        · rw [ite_eq_right hInC, hAg₁ at' τ' hNotH, ← hAgOut at' τ' hInC]
      exact hNoHalt0 src₂ hL₂ hAg₂ e ⟨evs₁, grun_of_agree_sites M hAg12 hNoInside hRun₁⟩
    let adapter2 : ProverAdapter M prover false events
        (castStack2Handler M fnTable rTable conP0 layP0 hCPSt hLPSt) := {
      σ := HList M.Val [conP0.state, layP0.state]
      h := hP
      Inv := fun s st1 buf1 => s = .cons (hCPSt.symm ▸ st1) (.cons (hLPSt.symm ▸ buf1) .nil)
      passMark := fun op s hM => by
        obtain ⟨s1, s2, rfl⟩ := HList.two s
        have hCl : ROp.IsClosed M op := by rcases hM with hM | hM <;> rw [hM] <;> trivial
        let s1' : M.Val stateTy := hCPSt ▸ s1
        let s2' : M.Val (.seq unitTy none) := hLPSt ▸ s2
        have h := hPassP op s1' s2' hCl
        have h1 : hCPSt.symm ▸ s1' = s1 := eqRec_symm_eqRec (F := M.Val) hCPSt s1
        have h2 : hLPSt.symm ▸ s2' = s2 := eqRec_symm_eqRec (F := M.Val) hLPSt s2
        rw [h1, h2] at h; exact h
      passClosed := fun op s st1 buf1 hInv hCl _ _ => by subst hInv; exact hPassP op st1 buf1 hCl
      stepBelow := fun op s st1 buf1 st' buf' reply hInv _ hBase => by
        subst hInv
        refine ⟨.cons (hCPSt.symm ▸ st') (.cons (hLPSt.symm ▸ buf') .nil), rfl, ?_⟩
        cases conP0; cases layP0; dsimp only at hCPSt hLPSt; subst hCPSt; subst hLPSt
        exact hBase
      stepSampled := fun h => by cases h
    }
    obtain ⟨a, outP, outV, sP', finalSt, suffix, recP, src', hInv', hSufV, hAlP, hAlV,
      hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
      simulate_derived_gen M hNe (d := d) (hCPSt ▸ conP0.clauses) (hCVSt ▸ conV0.clauses)
        (hLPSt ▸ layP0.clauses) (hLVSt ▸ layV0.clauses)
        conP0 conV0 layP0 layV0 hCPSt hCVSt hLPSt hLVSt rfl rfl rfl rfl
        hConDecl hLayDecl hSuiteLaw hLayLaw hCC hSL false adapter2
        p0 qP0 qV0 (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) st buf source
        rfl hStV hBufV hPP0 hPV0 hSP0 hSV0 hShP0 hShV0 hPShape0 hUniq0
        (lawfulPrivate_to_lawfulFor_false M hLPSrc) (fed_to_fedFor_false M hFedSrc) hNoHaltSrc
    subst hInv'
    let src'' : Source M := fun at' τ' => if at'.site ∈ insideCoins then attemptSrc at' τ' else src' at' τ'
    have hAgSrc'' : ∀ at' τ', at'.site ∉ insideCoins → src' at' τ' = src'' at' τ' := by
      intro at' τ' hOut; dsimp only [src'']; rw [ite_eq_right hOut]
    refine ⟨a, outP, outV, finalSt, suffix, recP, src'', hSufV, ?_, hAlV, hPostP, hPostV,
      lawful_of_agree_sites M hAgSrc'' hNoInside hLSrc', ?_,
      ⟨evs', grun_of_agree_sites M hAgSrc'' hNoInside hRun'⟩⟩
    · have hRunEq := handler_run_retry_eq_none M hP bound target
        (HList.cons (hCPSt.symm ▸ st) (HList.cons (hLPSt.symm ▸ buf) HList.nil) : HList M.Val (Stack.States [conP0, layP0]))
        hNotMark
      rw [hRunEq]
      exact alone_mapHalt M hAlP
    · intro at' τ' hNotH
      dsimp only [src'']
      by_cases hInC : at'.site ∈ insideCoins
      · rw [ite_eq_left hInC]
      · rw [ite_eq_right hInC, hAgSrc' at' τ' hNotH, ← hAgOut at' τ' hInC]
  intro A BP BV p
  induction p with
  | done a =>
      intro postP postV qP qV st buf source hStV hBufV hPP hPV hSP hSV hShP hShV hRWF hPShape hUniq hLP hFed hNoHalt
      let attemptSrc := shiftAttemptSource M insideCoins (.attempt target.key kIdx) source
      generalize hP0 : Process.done a = p0 at hPP
      induction hPP with
      | @begins at_ _ kP' _ ihP =>
          obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
            ihP (hSP.2 0 trivial) (hShP.2 0 trivial) (hRWF.2 0) hP0
          exact ⟨a', outP, outV, fSt, suf, .began prover at_ :: recP, src', h1, by
            rw [handler_inside_pass_begin M hP bound target kIdx at_ kP' _ (hPassP _ st buf trivial)]
            exact .begin h2, h3, h4, h5, h6, h7, h8⟩
      | @settles at_ _ kP' hPP' ihP =>
          by_cases hIsT : at_.site = target
          · dsimp only [Program.RetryWellFormed] at hRWF
            rw [ite_eq_left hIsT] at hRWF
            obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
              hHandoffAfter _ (kP' ()) qV st buf source hStV hBufV hPP' (hP0 ▸ hPV)
                (hSP.2 () trivial) hSV (hShP.2 () trivial) hShV (hRWF ())
                (hP0 ▸ hPShape) (hP0 ▸ hUniq) (hP0 ▸ hLP) (hP0 ▸ hFed) (hP0 ▸ hNoHalt)
            refine ⟨a', outP, outV, fSt, suf, recP, src', h1, ?_, h3, h4, h5, h6, h7, h8⟩
            exact alone_eq_proc M (handler_inside_settle_target M hP bound target kIdx at_ hIsT kP' _) h2
          · dsimp only [Program.RetryWellFormed] at hRWF
            rw [ite_eq_right hIsT] at hRWF
            obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
              ihP (hSP.2 () trivial) (hShP.2 () trivial) (hRWF ()) hP0
            exact ⟨a', outP, outV, fSt, suf, .settled prover at_ :: recP, src', h1, by
              rw [handler_inside_pass_settle_other M hP bound target kIdx at_ hIsT kP' _ (hPassP _ st buf trivial)]
              exact .settle h2, h3, h4, h5, h6, h7, h8⟩
      | done hPostP =>
          cases hP0
          generalize hPV0 : Process.done a = pv0 at hPV
          induction hPV with
          | @begins at_ _ kV' _ ihV =>
              obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
              exact ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.began verifier at_ :: recV, by
                  rw [stack_run_begin M hV at_ kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | @settles at_ _ kV' _ ihV =>
              obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
              exact ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.settled verifier at_ :: recV, by
                  rw [stack_run_settle M hV at_ kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | done hPostV =>
              cases hPV0
              exact ⟨a, _, _, st, [], [], attemptSrc, (fun _ h => nomatch h),
                by simpa [Handler.inside] using Alone.done,
                fun post _ => ⟨[], by simpa [Handler.run] using Alone.done⟩,
                hPostP, hPostV, trivial, (fun _ _ _ => rfl), ⟨[], .done⟩⟩
          | _ => cases hPV0
      | _ => cases hP0
  | halt payload =>
      intro _ _ _ _ _ _ source _ _ _ _ _ _ _ _ _ _ _ _ _ hNoHalt
      obtain ⟨_, hContra⟩ := hNoHalt (shiftAttemptSource M insideCoins (.attempt target.key kIdx) source)
        trivial (fun _ _ _ => rfl) (.stopped payload.1 payload.2) ⟨[], .halt⟩
      cases hContra
  | call op k ih =>
      intro postP postV qP qV st buf source hStV hBufV hPP hPV hSP hSV hShP hShV hRWF hPShape hUniq hLP hFed hNoHalt
      let attemptSrc := shiftAttemptSource M insideCoins (.attempt target.key kIdx) source
      generalize hP0 : Process.call op k = p0 at hPP
      induction hPP with
      | @begins at_ _ kP' _ ihP =>
          obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
            ihP (hSP.2 0 trivial) (hShP.2 0 trivial) (hRWF.2 0) hP0
          exact ⟨a, outP, outV, fSt, suf, .began prover at_ :: recP, src', h1, by
            rw [handler_inside_pass_begin M hP bound target kIdx at_ kP' _ (hPassP _ st buf trivial)]
            exact .begin h2, h3, h4, h5, h6, h7, h8⟩
      | @settles at_ _ kP' hPP' ihP =>
          by_cases hIsT : at_.site = target
          · dsimp only [Program.RetryWellFormed] at hRWF
            rw [ite_eq_left hIsT] at hRWF
            obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
              hHandoffAfter _ (kP' ()) qV st buf source hStV hBufV hPP' (hP0 ▸ hPV)
                (hSP.2 () trivial) hSV (hShP.2 () trivial) hShV (hRWF ())
                (hP0 ▸ hPShape) (hP0 ▸ hUniq) (hP0 ▸ hLP) (hP0 ▸ hFed) (hP0 ▸ hNoHalt)
            refine ⟨a, outP, outV, fSt, suf, recP, src', h1, ?_, h3, h4, h5, h6, h7, h8⟩
            exact alone_eq_proc M (handler_inside_settle_target M hP bound target kIdx at_ hIsT kP' _) h2
          · dsimp only [Program.RetryWellFormed] at hRWF
            rw [ite_eq_right hIsT] at hRWF
            obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
              ihP (hSP.2 () trivial) (hShP.2 () trivial) (hRWF ()) hP0
            exact ⟨a, outP, outV, fSt, suf, .settled prover at_ :: recP, src', h1, by
              rw [handler_inside_pass_settle_other M hP bound target kIdx at_ hIsT kP' _ (hPassP _ st buf trivial)]
              exact .settle h2, h3, h4, h5, h6, h7, h8⟩
      | done _ => cases hP0
      | stopsHere _ => cases hP0
      | stopsElsewhere _ => cases hP0
      | @gave kind getters at_ τ x kG kP' _ hPP' ihUnused =>
          clear ihUnused
          cases hP0
          obtain ⟨eP, hEP, hSiteP, hTyP, hClsP⟩ := hShP.1
          have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
          have hVin : verifier ∈ getters := by
            rcases hDisc with ⟨_, hV⟩ | ⟨hNotP, _, _, _⟩
            · exact hV
            · exact absurd rfl hNotP
          have hMsgV : M.Valid τ x := hSP.1
          obtain ⟨st', chunk, hSt'V, hChV, hStepP, hStepV⟩ :=
            derived_step_flow M hCPSt hCVSt hLPSt hLVSt hLayDecl hLayLaw hCC hSL
              hMsgV hStV hBufV hEP hSiteP hTyP hVin hClsP
          have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := fun u hu =>
            (List.mem_append.mp hu).elim (hBufV u) (hChV u)
          generalize hPV0 : (Process.call (GOp.flow kind prover getters at_ τ x) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | @begins atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.began verifier atV :: recV, by
                  rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | @settles atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.settled verifier atV :: recV, by
                  rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | gave _ _ => cases hPV0; exact absurd rfl hNe
          | passed _ hVOut _ => cases hPV0; exact absurd hVin hVOut
          | got _ _ hPV' =>
              cases hPV0
              obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                ih () (kP' ()) _ st' (buf ++ chunk) source hSt'V hBufChV hPP' hPV'
                  (hSP.2 () trivial) (hSV.2 x hMsgV) (hShP.2 () trivial) (hShV.2 x trivial) (hRWF ())
                  (hPShape.2 ()) (hUniq ()).2 hLP hFed
                  (fun s₁ hL₁ hAg₁ e ⟨evs₁, hR₁⟩ => hNoHalt s₁ hL₁ hAg₁ e ⟨_, .flow hR₁⟩)
              refine ⟨a, outP, outV, fSt, chunk ++ suf', recP, src',
                (fun u hu => (List.mem_append.mp hu).elim (hChV u) (hSufV u)), ?_, ?_,
                hPostP, hPostV, hLSrc', hAgSrc', ⟨_, .flow hRun'⟩⟩
              · exact alone_eq_proc M (handler_inside_clause_done M hP bound target kIdx (.give kind getters at_ τ x) rfl kP' _ _ () hStepP)
                  (by simpa [List.append_assoc] using hAlP)
              · intro post hPost
                have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := fun u hu =>
                  (List.mem_append.mp hu).elim (hSufV u) (hPost u)
                obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                refine ⟨recV, ?_⟩
                have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                  simp [List.append_assoc]
                have hBufEq2 : buf ++ chunk ++ (suf' ++ post) = (buf ++ chunk) ++ suf' ++ post := by
                  simp [List.append_assoc]
                have hLenEq : buf.length + (chunk ++ suf').length = (buf ++ chunk).length + suf'.length := by
                  simp [List.length_append, Nat.add_assoc]
                rw [hBufEq]
                refine alone_eq_proc M (stack_run_clause_done M _ _ _ _ _ _ (hStepV (suf' ++ post) hSufPostV)) ?_
                rw [hLenEq, hBufEq2, ← List.length_append]
                exact hAlV'
          | _ => cases hPV0
      | got hGNeP hPIn _ =>
          cases hP0
          obtain ⟨eP, hEP, _, _, _, _, hPin', hClsP⟩ := hShP.1
          have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
          rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, hNotP, _⟩
          · exact absurd hEqP hGNeP
          · exact absurd hPin' hNotP
      | @passed kind giver getters at_ τ x kG _ hGNeP _ hPP' ihUnused =>
          clear ihUnused
          cases hP0
          generalize hPV0 : (Process.call (GOp.flow kind giver getters at_ τ x) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | @begins atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.began verifier atV :: recV, by
                  rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | @settles atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.settled verifier atV :: recV, by
                  rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | gave _ _ =>
              cases hPV0
              obtain ⟨eV, hEV, _, _, hClsV⟩ := hShV.1
              have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
              rcases hDisc with ⟨hEqP, _⟩ | ⟨_, hNotV, _, _⟩
              · exact absurd hEqP.symm hNe
              · exact absurd rfl hNotV
          | got _ hVin _ =>
              cases hPV0
              obtain ⟨eV, hEV, _, _, _, _, hVin', hClsV⟩ := hShV.1
              have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
              rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, _, hNotV⟩
              · exact absurd hEqP hGNeP
              · exact absurd hVin' hNotV
          | passed _ _ hPV' =>
              cases hPV0
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨evs', hRun'⟩⟩ :=
                ih () _ _ st buf source hStV hBufV hPP' hPV' hSP hSV hShP hShV hRWF
                  (hPShape.2 ()) (hUniq ()).2 hLP hFed
                  (fun s₁ hL₁ hAg₁ e ⟨evs₁, hR₁⟩ => hNoHalt s₁ hL₁ hAg₁ e ⟨_, .flow hR₁⟩)
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨_, .flow hRun'⟩⟩
          | _ => cases hPV0
      | @owned gkind hearers at_ gIns payload τ kG kP' hPP' ihUnused =>
          clear ihUnused
          cases hP0
          obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          have hNotH : (∃ law, gkind = .coin law ∧ hearers = []) ∨
              (∃ svc, gkind = .request svc ∧ verifier ∉ hearers) := by
            cases gkind with
            | coin law =>
                rcases hDisc with ⟨hOwV, _, _⟩ | hNil
                · exact absurd hOwV hNe
                · exact .inl ⟨law, rfl, hNil⟩
            | request svc => exact .inr ⟨svc, rfl, hDisc.2.resolve_left hNe⟩
          generalize hPV0 : (Process.call (GOp.given gkind prover hearers at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | @begins atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.began verifier atV :: recV, by
                  rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | @settles atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.settled verifier atV :: recV, by
                  rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | owned _ => cases hPV0; exact absurd rfl hNe
          | heard _ hVin _ =>
              cases hPV0
              rcases hNotH with ⟨_, _, rfl⟩ | ⟨_, _, hOut⟩
              · cases hVin
              · exact absurd hVin hOut
          | unheard _ _ hPV' =>
              cases hPV0
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                have hInC : at_.site ∈ insideCoins := hRWF.1
                have hSrcSh : source ⟨.attempt target.key kIdx :: at_.path, at_.key⟩ τ = some v := by
                  have h := hvSrc; dsimp only [attemptSrc, shiftAttemptSource] at h; rwa [ite_eq_left hInC] at h
                obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                  ih v (kP' v) _ st buf source hStV hBufV (hPP' v) (hPV' v)
                    (hSP.2 v (allows_valid M hAl)) hSV (hShP.2 v trivial) hShV (hRWF.2 v)
                    (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_noHalt_given M hvSrc hAl (hUniq v).1 hNoHalt)
                let src'' := patchSource M src' at_ τ v
                have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                  fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                have hAlP' : ∃ recP', Alone M source prover
                    (hP.inside (retryOf M (some (bound, target))) kIdx
                      (.call (.own (.coin law) [] at_ gIns payload τ) kP')
                      (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
                    recP' (.returned (outP, .cons (hCPSt.symm ▸ fSt) (.cons (hLPSt.symm ▸ (buf ++ suf)) .nil))) :=
                  ⟨_, by
                    rw [handler_inside_pass_private_coin M hP bound target kIdx law at_ gIns payload τ kP' _
                      (hPassP _ st buf trivial)]
                    exact .own hSrcSh hAlP⟩
                obtain ⟨recP', hAlP'⟩ := hAlP'
                refine ⟨a, outP, outV, fSt, suf, recP', src'', hSufV, hAlP', hAlV, hPostP, hPostV, ?_, ?_,
                  ⟨_, .given (patchSource_self M src' at_ τ v) (grun_of_agree M hAgP (hUniq v).1 hRun')⟩⟩
                · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                  exact ⟨hAl, lawful_of_agree M hAgP (hUniq v).1 hLSrc'⟩
                · intro at' τ' hNotH'
                  by_cases hEqAt : at' = at_
                  · subst at'
                    by_cases hEqT : τ' = τ
                    · subst hEqT; dsimp only [src'']; rw [patchSource_self]; exact hvSrc.symm
                    · dsimp only [src'']; rw [patchSource_ne_ty M src' at_ τ v hEqT]; exact hAgSrc' at_ τ' hNotH'
                  · dsimp only [src'']; rw [patchSource_ne M src' at_ τ v hEqAt τ']; exact hAgSrc' at' τ' hNotH'
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                have hOutC : at_.site ∉ insideCoins := hRWF.1
                have hSrcEq : source at_ τ = some v := by
                  have h := hvSrc; dsimp only [attemptSrc, shiftAttemptSource] at h; rwa [ite_eq_right hOutC] at h
                obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                  ih v (kP' v) _ st buf source hStV hBufV (hPP' v) (hPV' v)
                    (hSP.2 v (allows_valid M hAl)) hSV (hShP.2 v trivial) hShV (hRWF.2 v)
                    (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_noHalt_given M hvSrc hAl (hUniq v).1 hNoHalt)
                let src'' := patchSource M src' at_ τ v
                have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                  fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                have hAlP' : ∃ recP', Alone M source prover
                    (hP.inside (retryOf M (some (bound, target))) kIdx
                      (.call (.own (.request svc) hearers at_ gIns payload τ) kP')
                      (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
                    recP' (.returned (outP, .cons (hCPSt.symm ▸ fSt) (.cons (hLPSt.symm ▸ (buf ++ suf)) .nil))) :=
                  ⟨_, by
                    rw [handler_inside_pass_request M hP bound target kIdx svc hearers at_ gIns payload τ kP' _
                      (hPassP _ st buf trivial)]
                    exact .own hSrcEq hAlP⟩
                obtain ⟨recP', hAlP'⟩ := hAlP'
                refine ⟨a, outP, outV, fSt, suf, recP', src'', hSufV, hAlP', hAlV, hPostP, hPostV, ?_, ?_,
                  ⟨_, .given (patchSource_self M src' at_ τ v) (grun_of_agree M hAgP (hUniq v).1 hRun')⟩⟩
                · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                  exact ⟨hAl, lawful_of_agree M hAgP (hUniq v).1 hLSrc'⟩
                · intro at' τ' hNotH'
                  by_cases hEqAt : at' = at_
                  · subst at'
                    by_cases hEqT : τ' = τ
                    · subst hEqT; dsimp only [src'']; rw [patchSource_self]; exact hvSrc.symm
                    · dsimp only [src'']; rw [patchSource_ne_ty M src' at_ τ v hEqT]; exact hAgSrc' at_ τ' hNotH'
                  · dsimp only [src'']; rw [patchSource_ne M src' at_ τ v hEqAt τ']; exact hAgSrc' at' τ' hNotH'
          | _ => cases hPV0
      | @heard gkind owner hearers at_ gIns payload τ kG kP' hOwNe hPin hPP' ihUnused =>
          clear ihUnused
          cases hP0
          obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          cases gkind with
          | request svc => exact absurd hPin (hDisc.1.resolve_left hOwNe)
          | coin law =>
              rcases hDisc with ⟨hOwV, _, sig, hLaw, _, hSigIns⟩ | hNil
              · cases hOwV
                have hNonEmpty : ∃ h0 hs, hearers = h0 :: hs := by
                  cases hearers with
                  | nil => cases hPin
                  | cons h0 hs => exact ⟨h0, hs, rfl⟩
                obtain ⟨h0, hs, hHCons⟩ := hNonEmpty
                subst hHCons
                generalize hPV0 : (Process.call (GOp.given (.coin law) verifier (h0 :: hs) at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
                induction hPV with
                | @begins atV _ kV' _ ihV =>
                    obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                      ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
                    exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                      let ⟨recV, hAlV⟩ := h3 post hPost
                      ⟨.began verifier atV :: recV, by
                        rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                      h4, h5, h6, h7, h8⟩
                | @settles atV _ kV' _ ihV =>
                    obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                      ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
                    exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                      let ⟨recV, hAlV⟩ := h3 post hPost
                      ⟨.settled verifier atV :: recV, by
                        rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                      h4, h5, h6, h7, h8⟩
                | done _ => cases hPV0
                | stopsHere _ => cases hPV0
                | stopsElsewhere _ => cases hPV0
                | heard hNeS _ _ => cases hPV0; exact absurd rfl hNeS
                | unheard hNeS _ _ => cases hPV0; exact absurd rfl hNeS
                | owned hPV' =>
                    cases hPV0
                    obtain ⟨eV, hEV, hSiteV, hTyV, hClsV, hTypedV⟩ := hShV.1
                    have hGInsNil : gIns = [] := by
                      obtain ⟨s, hsLaw, hsIns, _⟩ := hTypedV
                      rw [hLaw] at hsLaw; cases hsLaw; rw [← hsIns, hSigIns]
                    subst hGInsNil; cases payload
                    obtain ⟨coin, st', chunk, hCoinV, hAl, hAtH, hSt'V, hChV, hStepP, hStepV⟩ :=
                      derived_step_heard_coin M hCPSt hCVSt hLPSt hLVSt hConDecl hLayDecl hSuiteLaw hLayLaw
                        hCC hSL hStV hBufV hEV hSiteV hTyV hPin hClsV
                    have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := fun u hu =>
                      (List.mem_append.mp hu).elim (hBufV u) (hChV u)
                    obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                      ih coin (kP' coin) _ st' (buf ++ chunk) source hSt'V hBufChV (hPP' coin) (hPV' coin)
                        (hSP.2 coin hCoinV) (hSV.2 coin hCoinV) (hShP.2 coin trivial) (hShV.2 coin trivial)
                        (hRWF coin) (hPShape.2 coin) (hUniq coin).2 (hLP coin hAl) (hFed coin hAl)
                        (step_noHalt_heard_coin M hAtH hAl (hUniq coin).1 hNoHalt)
                    let src'' := patchSource M src' at_ τ coin
                    have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                      fun at' τ' hne => (patchSource_ne M src' at_ τ coin hne τ').symm
                    refine ⟨a, outP, outV, fSt, chunk ++ suf', recP, src'',
                      (fun u hu => (List.mem_append.mp hu).elim (hChV u) (hSufV u)), ?_, ?_,
                      hPostP, hPostV, ?_, ?_,
                      ⟨_, .given (patchSource_self M src' at_ τ coin) (grun_of_agree M hAgP (hUniq coin).1 hRun')⟩⟩
                    · exact alone_eq_proc M (handler_inside_clause_done M hP bound target kIdx (.hear (.coin law) verifier at_ τ) rfl kP' _ _ coin hStepP)
                        (by simpa [List.append_assoc] using hAlP)
                    · intro post hPost
                      have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := fun u hu =>
                        (List.mem_append.mp hu).elim (hSufV u) (hPost u)
                      obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                      refine ⟨recV, ?_⟩
                      have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                        simp [List.append_assoc]
                      have hBufEq2 : buf ++ chunk ++ (suf' ++ post) = (buf ++ chunk) ++ suf' ++ post := by
                        simp [List.append_assoc]
                      have hLenEq : buf.length + (chunk ++ suf').length = (buf ++ chunk).length + suf'.length := by
                        simp [List.length_append, Nat.add_assoc]
                      rw [hBufEq]
                      refine alone_eq_proc M (stack_run_clause_done M _ _ _ _ _ _ (hStepV (suf' ++ post) hSufPostV)) ?_
                      rw [hLenEq, hBufEq2, ← List.length_append]
                      exact hAlV'
                    · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                      exact ⟨hAl, lawful_of_agree M hAgP (hUniq coin).1 hLSrc'⟩
                    · intro at' τ' hNotH'
                      have hne : at' ≠ at_ := fun heq => hNotH' (heq ▸ hAtH)
                      dsimp only [src'']; rw [patchSource_ne M src' at_ τ coin hne τ']; exact hAgSrc' at' τ' hNotH'
                | _ => cases hPV0
              · subst hNil; cases hPin
      | @unheard gkind owner hearers at_ gIns payload τ kG q hOwNe hNotIn hPP' ihUnused =>
          clear ihUnused
          cases hP0
          obtain ⟨eG, hEG, hSiteG, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          have hNotH : (∃ law, gkind = .coin law ∧ hearers = []) ∨
              (∃ svc, gkind = .request svc ∧ (owner = verifier ∨ verifier ∉ hearers)) := by
            cases gkind with
            | coin law =>
                rcases hDisc with ⟨_, hPin', _⟩ | hNil
                · exact absurd hPin' hNotIn
                · exact .inl ⟨law, rfl, hNil⟩
            | request svc => exact .inr ⟨svc, rfl, hDisc.2⟩
          have hOutC : at_.site ∉ insideCoins := by
            have hEv := attemptCoinsExclusive_ev_notin prover target d.entry.shape hExcl hEG
            rw [hClsG] at hEv
            rcases hNotH with ⟨_, rfl, rfl⟩ | ⟨_, rfl, _⟩
            · exact hSiteG ▸ hEv hOwNe
            · exact hSiteG ▸ hEv
          generalize hPV0 : (Process.call (GOp.given gkind owner hearers at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | @begins atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.began verifier atV :: recV, by
                  rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | @settles atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.settled verifier atV :: recV, by
                  rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | @owned _ _ _ _ _ _ _ kV' hPV' =>
              cases hPV0
              have hStepV : ∀ v, (hLP' : LawfulPrivate M attemptSrc (kG v)) → (hFed' : Fed M attemptSrc (kG v)) →
                  (hvSrc : attemptSrc at_ τ = some v) → (hAl : Allows M gkind gIns payload τ v) →
                  (hCl : ROp.IsClosed M (.own gkind hearers at_ gIns payload τ)) →
                  ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
                    (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
                    (∀ u ∈ suffix, M.Valid unitTy u) ∧
                    Alone M source prover
                      (Handler.inside hP (retryOf M (some (bound, target))) kIdx q
                        (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
                      recP (.returned (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ suffix)) .nil))) ∧
                    (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
                      ∃ recV, Alone M source verifier
                        (hV.run (retryOf M none) (.call (.own gkind hearers at_ gIns payload τ) kV')
                          (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
                        recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
                          (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
                    postP a outP ∧ postV a outV ∧
                    Lawful M source' (.call (.given gkind verifier hearers at_ gIns payload τ) kG) ∧
                    (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source' at' τ' = attemptSrc at' τ') ∧
                    GExec M source' (.call (.given gkind verifier hearers at_ gIns payload τ) kG) (.returned a) := by
                intro v hLP' hFed' hvSrc hAl hCl
                have hSrcEq : source at_ τ = some v := by
                  have h := hvSrc; dsimp only [attemptSrc, shiftAttemptSource] at h; rwa [ite_eq_right hOutC] at h
                obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                  ih v q (kV' v) st buf source hStV hBufV (hPP' v) (hPV' v)
                    hSP (hSV.2 v (allows_valid M hAl)) hShP (hShV.2 v trivial) hRWF
                    (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_noHalt_given M hvSrc hAl (hUniq v).1 hNoHalt)
                let src'' := patchSource M src' at_ τ v
                have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                  fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                refine ⟨a, outP, outV, fSt, suf, recP, src'', hSufV, hAlP, ?_, hPostP, hPostV, ?_, ?_,
                  ⟨_, .given (patchSource_self M src' at_ τ v) (grun_of_agree M hAgP (hUniq v).1 hRun')⟩⟩
                · intro post hPost
                  obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                  exact ⟨_, by rw [stack_run_own M hV _ _ _ _ _ _ kV' _ (hPassV _ st _ hCl)]; exact .own hSrcEq hAlV'⟩
                · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                  exact ⟨hAl, lawful_of_agree M hAgP (hUniq v).1 hLSrc'⟩
                · intro at' τ' hNotH'
                  by_cases hEqAt : at' = at_
                  · subst at'
                    by_cases hEqT : τ' = τ
                    · subst hEqT; dsimp only [src'']; rw [patchSource_self]; exact hvSrc.symm
                    · dsimp only [src'']; rw [patchSource_ne_ty M src' at_ τ v hEqT]; exact hAgSrc' at_ τ' hNotH'
                  · dsimp only [src'']; rw [patchSource_ne M src' at_ τ v hEqAt τ']; exact hAgSrc' at' τ' hNotH'
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact hStepV v hLP' hFed' hvSrc hAl trivial
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact hStepV v hLP' hFed' hvSrc hAl trivial
          | heard _ hVin _ =>
              cases hPV0
              rcases hNotH with ⟨_, _, rfl⟩ | ⟨_, _, hVO⟩
              · cases hVin
              · exact absurd hVin (hVO.resolve_left (by assumption))
          | @unheard _ _ _ _ _ _ _ _ qV' _ _ hPV' =>
              cases hPV0
              have hStepU : ∀ v, (hLP' : LawfulPrivate M attemptSrc (kG v)) → (hFed' : Fed M attemptSrc (kG v)) →
                  (hvSrc : attemptSrc at_ τ = some v) → (hAl : Allows M gkind gIns payload τ v) →
                  ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
                    (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
                    (∀ u ∈ suffix, M.Valid unitTy u) ∧
                    Alone M source prover
                      (Handler.inside hP (retryOf M (some (bound, target))) kIdx q
                        (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
                      recP (.returned (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ suffix)) .nil))) ∧
                    (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
                      ∃ recV, Alone M source verifier
                        (hV.run (retryOf M none) qV'
                          (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
                        recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
                          (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
                    postP a outP ∧ postV a outV ∧
                    Lawful M source' (.call (.given gkind owner hearers at_ gIns payload τ) kG) ∧
                    (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source' at' τ' = attemptSrc at' τ') ∧
                    GExec M source' (.call (.given gkind owner hearers at_ gIns payload τ) kG) (.returned a) := by
                intro v hLP' hFed' hvSrc hAl
                obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                  ih v q qV' st buf source hStV hBufV (hPP' v) (hPV' v) hSP hSV hShP hShV hRWF
                    (hPShape.2 v) (hUniq v).2 hLP' hFed' (step_noHalt_given M hvSrc hAl (hUniq v).1 hNoHalt)
                let src'' := patchSource M src' at_ τ v
                have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                  fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                refine ⟨a, outP, outV, fSt, suf, recP, src'', hSufV, hAlP, hAlV, hPostP, hPostV, ?_, ?_,
                  ⟨_, .given (patchSource_self M src' at_ τ v) (grun_of_agree M hAgP (hUniq v).1 hRun')⟩⟩
                · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                  exact ⟨hAl, lawful_of_agree M hAgP (hUniq v).1 hLSrc'⟩
                · intro at' τ' hNotH'
                  by_cases hEqAt : at' = at_
                  · subst at'
                    by_cases hEqT : τ' = τ
                    · subst hEqT; dsimp only [src'']; rw [patchSource_self]; exact hvSrc.symm
                    · dsimp only [src'']; rw [patchSource_ne_ty M src' at_ τ v hEqT]; exact hAgSrc' at_ τ' hNotH'
                  · dsimp only [src'']; rw [patchSource_ne M src' at_ τ v hEqAt τ']; exact hAgSrc' at' τ' hNotH'
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact hStepU v hLP' hFed' hvSrc hAl
              · obtain ⟨v, hvSrc, hFed'⟩ := hFed
                obtain ⟨hAl, hLP'⟩ := hLP v hvSrc
                exact hStepU v hLP' hFed' hvSrc hAl

          | _ => cases hPV0
/-! ### 4e. Coupled simulation before `.begin target` (`simulate_retry_coupled_before`) -/

private theorem simulate_retry_coupled_before {enc : VocabEncoder V} {d : Deployed V}
    {suite : ModuleRef} {sessionTag : Option (List Nat)} {layout : Layout}
    {stateTy suiteUnitTy unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {absRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    (conP0 : Layer V d.admitted.program.headers prover d.entry.ins)
    (conV0 : Layer V d.admitted.program.headers verifier d.entry.ins)
    (layP0 : Layer V d.admitted.program.headers prover d.entry.ins)
    (layV0 : Layer V d.admitted.program.headers verifier d.entry.ins)
    (hCPSt : conP0.state = stateTy) (hCVSt : conV0.state = stateTy)
    (hLPSt : layP0.state = .seq unitTy none) (hLVSt : layV0.state = streamStateTy unitTy)
    (hCPA : conP0.again = restoreAgain conP0.state)
    (hLPA : layP0.again = restoreAgain layP0.state)
    (hConDecl : d.declaration.construction = .derived suite sessionTag)
    (hLayDecl : d.declaration.layout = some layout)
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M)
    (hCC : buildConstructionClauses.go enc d.admitted suite stateTy suiteUnitTy absRef prover verifier
      declKey (d.entry.shape.events [] id) 0
      (d.entry.shape.eventsWithAbsorb prover verifier [] id false) =
      .ok (hCPSt ▸ conP0.clauses, hCVSt ▸ conV0.clauses))
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hLPSt ▸ layP0.clauses, hLVSt ▸ layV0.clauses))
    (bound : Nat) (target : Site) (kIdx : Nat) (hKLt : kIdx < bound)
    (hExcl : d.entry.shape.attemptCoinsExclusive prover target = true) :
    let insideCoins := d.entry.shape.attemptPrivateCoins prover target [] false
    let fnTable := Defs.fnTable M d.admitted.program.defs
    let rTable := Defs.rTable M d.admitted.program.defs
    let hP := Stack.handler M fnTable rTable [conP0, layP0]
    let hV := Stack.handler M fnTable rTable [conV0, layV0]
    ∀ {A BP BV : Type} (p : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (qP : Program M BP) (qV : Program M BV)
      (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M),
      M.Valid stateTy st → (∀ u ∈ buf, M.Valid unitTy u) →
      Proj M prover postP p qP → Proj M verifier postV p qV →
      qP.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      qV.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      qP.SafeWith M (fun _ _ => True) (ROp.MatchesShape M prover (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      qV.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      Program.RetryWellFormed M target insideCoins .before qP →
      (∀ j, j ≤ kIdx → Program.AttemptIndexFree M target j qP) →
      Protocol.MatchesShape M (d.entry.shape.events [] id) p →
      Protocol.UniqueOccs M p →
      (∀ j, j < kIdx → LawfulPrivate M (shiftAttemptSource M insideCoins (.attempt target.key j) source) p) →
      (∀ j, j < kIdx → Fed M (shiftAttemptSource M insideCoins (.attempt target.key j) source) p) →
      (∀ j, j < kIdx →
        ∀ source₁, Lawful M source₁ p →
          (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
            source₁ at' τ' = shiftAttemptSource M insideCoins (.attempt target.key j) source at' τ') →
          ∃ evs who why, GRun M source₁ p evs (.stopped who why) ∧ prover ∈ who ∧ why.isAbort = true) →
      LawfulPrivate M (shiftAttemptSource M insideCoins (.attempt target.key kIdx) source) p →
      Fed M (shiftAttemptSource M insideCoins (.attempt target.key kIdx) source) p →
      (∀ source₁, Lawful M source₁ p →
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
          source₁ at' τ' = shiftAttemptSource M insideCoins (.attempt target.key kIdx) source at' τ') →
        ∀ e, GExec M source₁ p e → ∃ a, e = .returned a) →
      ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
        (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
        (∀ u ∈ suffix, M.Valid unitTy u) ∧
        Alone M source prover
          (hP.run (retryOf M (some (bound, target))) qP
            (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
          recP (.returned (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ suffix)) .nil))) ∧
        (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
          ∃ recV, Alone M source verifier
            (hV.run (retryOf M none) qV
              (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
            recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
              (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
        postP a outP ∧ postV a outV ∧
        Lawful M source' p ∧
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
          source' at' τ' = shiftAttemptSource M insideCoins (.attempt target.key kIdx) source at' τ') ∧
        GExec M source' p (.returned a) := by
  intro insideCoins fnTable rTable hP hV
  let events := d.entry.shape.events [] id
  let eventsAbs := d.entry.shape.eventsWithAbsorb prover verifier [] id false
  have hFst : eventsAbs.map Prod.fst = events :=
    eventsWithAbsorb_fst prover verifier [] id false d.entry.shape
  have hPassP : ∀ op (st : M.Val stateTy) (buf : List (M.Val unitTy)),
      ROp.IsClosed M op →
      hP.clause op (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) =
        .call op fun reply => .done (reply, .cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) := by
    intro op st buf hCl
    have hCU := construction_clauses_unmatched_closed M 0 eventsAbs hCC op hCl
    have hLU := streaming_layout_unmatched_closed M 0 events hSL op hCl
    cases conP0 with | mk cPL cPSt cPT cPG cPCl cPA cPS cPF =>
    cases layP0 with | mk lPL lPSt lPT lPG lPCl lPA lPS lPF =>
    dsimp only at hCPSt hLPSt; subst cPSt; subst lPSt
    exact stack2_clause_pass M fnTable rTable
      ⟨cPL, stateTy, cPT, cPG, cPCl, cPA, cPS, cPF⟩
      ⟨lPL, .seq unitTy none, lPT, lPG, lPCl, lPA, lPS, lPF⟩ op st buf
      (clause_answer_unmatched_all M fnTable rTable op st cPCl hCU.1)
      (clause_answer_unmatched_all M fnTable rTable op buf lPCl hLU.1)
  have hPassV : ∀ op (st : M.Val stateTy) (lst : M.Val (streamStateTy unitTy)),
      ROp.IsClosed M op →
      hV.clause op (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ lst) .nil)) =
        .call op fun reply => .done (reply, .cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ lst) .nil)) := by
    intro op st lst hCl
    have hCU := construction_clauses_unmatched_closed M 0 eventsAbs hCC op hCl
    have hLU := streaming_layout_unmatched_closed M 0 events hSL op hCl
    cases conV0 with | mk cVL cVSt cVT cVG cVCl cVA cVS cVF =>
    cases layV0 with | mk lVL lVSt lVT lVG lVCl lVA lVS lVF =>
    dsimp only at hCVSt hLVSt; subst cVSt; subst lVSt
    exact stack2_clause_pass M fnTable rTable
      ⟨cVL, stateTy, cVT, cVG, cVCl, cVA, cVS, cVF⟩
      ⟨lVL, streamStateTy unitTy, lVT, lVG, lVCl, lVA, lVS, lVF⟩ op st lst
      (clause_answer_unmatched_all M fnTable rTable op st cVCl hCU.2)
      (clause_answer_unmatched_all M fnTable rTable op lst lVCl hLU.2)
  have hEventDisc : ∀ e ∈ events,
      match e.cls with
      | .flow _ giver getters =>
          (giver = prover ∧ verifier ∈ getters) ∨
          (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
      | .given (.coin law) owner hearers =>
          (owner = verifier ∧ prover ∈ hearers ∧
            ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
          hearers = []
      | .given (.request _) owner hearers =>
          (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
    intro e he
    rw [← hFst] at he
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp he
    exact construction_event_disc 0 eventsAbs hCC p0 hp0
  -- Helper at `.begin target`: runs rollback across `0 .. kIdx - 1` then coupled inside at `kIdx`!
  have hEnterTarget : ∀ {A BP BV : Type} (p0 : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (at_ : Occurrence) (hIsT : at_.site = target) (kP' : Nat → Program M BP) (qV0 : Program M BV)
      (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M),
      let attemptSrc := fun i => shiftAttemptSource M insideCoins (.attempt target.key i) source
      M.Valid stateTy st → (∀ u ∈ buf, M.Valid unitTy u) →
      Proj M prover postP p0 (kP' 0) → Proj M verifier postV p0 qV0 →
      (∀ n, (kP' n).SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined)) →
      qV0.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      (∀ n, (kP' n).SafeWith M (fun _ _ => True) (ROp.MatchesShape M prover events) (fun _ => True) (fun _ => True)) →
      qV0.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier events) (fun _ => True) (fun _ => True) →
      (∀ n, Program.RetryWellFormed M target insideCoins .inside (kP' n)) →
      (∀ j, j ≤ kIdx → kP' j = kP' 0) →
      Protocol.MatchesShape M events p0 → Protocol.UniqueOccs M p0 →
      (∀ j, j < kIdx → LawfulPrivate M (attemptSrc j) p0) →
      (∀ j, j < kIdx → Fed M (attemptSrc j) p0) →
      (∀ j, j < kIdx →
        ∀ source₁, Lawful M source₁ p0 →
          (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = attemptSrc j at' τ') →
          ∃ evs who why, GRun M source₁ p0 evs (.stopped who why) ∧ prover ∈ who ∧ why.isAbort = true) →
      LawfulPrivate M (attemptSrc kIdx) p0 →
      Fed M (attemptSrc kIdx) p0 →
      (∀ source₁, Lawful M source₁ p0 →
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = attemptSrc kIdx at' τ') →
        ∀ e, GExec M source₁ p0 e → ∃ a, e = .returned a) →
      ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
        (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
        (∀ u ∈ suffix, M.Valid unitTy u) ∧
        Alone M source prover
          (hP.run (retryOf M (some (bound, target))) (.call (.begin at_) kP')
            (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
          recP (.returned (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ suffix)) .nil))) ∧
        (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
          ∃ recV, Alone M source verifier
            (hV.run (retryOf M none) qV0
              (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
            recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
              (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
        postP a outP ∧ postV a outV ∧
        Lawful M source' p0 ∧
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source' at' τ' = attemptSrc kIdx at' τ') ∧
        GExec M source' p0 (.returned a) := by
    intro A BP BV p0 postP postV at_ hIsT kP' qV0 st buf source attemptSrc
      hStV hBufV hPP0 hPV0 hSP' hSV0 hShP' hShV0 hRWF' hIdxEq hPShape0 hUniq0
      hLPAb hFedAb hAborts hLPK hFedK hNoHaltK
    have hKProj : Proj M prover postP p0 (kP' kIdx) := by
      rw [hIdxEq kIdx (Nat.le_refl _)]; exact hPP0
    obtain ⟨a, outP, outV, finalSt, suffix, recK, src', hSufV, hAlK, hAlV, hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
      simulate_retry_coupled_inside M hNe conP0 conV0 layP0 layV0 hCPSt hCVSt hLPSt hLVSt
        hConDecl hLayDecl hSuiteLaw hLayLaw hCC hSL bound target kIdx hExcl
        p0 (kP' kIdx) qV0 st buf source hStV hBufV hKProj hPV0
        (hSP' kIdx) hSV0 (hShP' kIdx) hShV0 (hRWF' kIdx) hPShape0 hUniq0 hLPK hFedK hNoHaltK
    have hAbInside : ∀ j, j < kIdx → ∃ why sAbort rec,
        why.isAbort = true ∧
        Alone M source prover
          (Handler.inside hP (retryOf M (some (bound, target))) (0 + j) (kP' (0 + j))
            (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
          rec (.stopped ((true, why), sAbort)) := by
      intro j hj
      rw [Nat.zero_add]
      have hJProj : Proj M prover postP p0 (kP' j) := by
        rw [hIdxEq j (Nat.le_of_lt hj)]; exact hPP0
      exact simulate_prover_abort_inside M hNe hCPSt hCVSt hLPSt hLVSt
        hConDecl hLayDecl hSuiteLaw hLayLaw hCC hSL bound target j
        p0 (kP' j) qV0 st buf source hStV hBufV hJProj hPV0
        (hSP' j) (hShP' j) hShV0 (hRWF' j) hPShape0 hUniq0
        (hLPAb j hj) (hFedAb j hj) (hAborts j hj)
    have hRestore : ∀ i sAbort,
        hP.again i (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) sAbort =
          .ok (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)) := by
      intro i sAbort
      obtain ⟨t1, t2, rfl⟩ := HList.two sAbort
      exact stack2_again_restore M fnTable rTable conP0 layP0 hCPA hLPA i _ t1 _ t2
    obtain ⟨recAll, hAlAll⟩ := attempts_rollback_then_succeed M (.declared .exhausted at_) hP.again
      (fun i s' => Handler.inside hP (retryOf M (some (bound, target))) i (kP' i) s')
      (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil))
      hRestore kIdx bound 0
      (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ suffix)) .nil))
      hKLt hAbInside ⟨recK, by simpa using hAlK⟩
    refine ⟨a, outP, outV, finalSt, suffix, recAll, src', hSufV, ?_, hAlV, hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩
    have hBegEq := handler_run_retry_begin_target M hP bound target at_ hIsT kP'
      (HList.cons (hCPSt.symm ▸ st) (HList.cons (hLPSt.symm ▸ buf) HList.nil) : HList M.Val (Stack.States [conP0, layP0]))
    rw [hBegEq]
    exact hAlAll
  intro A BP BV p
  induction p with
  | done a =>
      intro postP postV qP qV st buf source hStV hBufV hPP hPV hSP hSV hShP hShV hRWF hIdxFree
        hPShape hUniq hLPAb hFedAb hAborts hLPK hFedK hNoHaltK
      let attemptSrc := fun i => shiftAttemptSource M insideCoins (.attempt target.key i) source
      generalize hP0 : Process.done a = p0 at hPP
      induction hPP with
      | @begins at_ _ kP' hPP' ihP =>
          by_cases hIsT : at_.site = target
          · dsimp only [Program.RetryWellFormed] at hRWF; rw [ite_eq_left hIsT] at hRWF
            exact hEnterTarget _ at_ hIsT kP' qV st buf source hStV hBufV hPP' (hP0 ▸ hPV)
              (fun n => hSP.2 n trivial) hSV (fun n => hShP.2 n trivial) hShV hRWF
              (fun j hj => (hIdxFree j hj).1 hIsT) (hP0 ▸ hPShape) (hP0 ▸ hUniq)
              (hP0 ▸ hLPAb) (hP0 ▸ hFedAb) (hP0 ▸ hAborts) (hP0 ▸ hLPK) (hP0 ▸ hFedK) (hP0 ▸ hNoHaltK)
          · dsimp only [Program.RetryWellFormed] at hRWF; rw [ite_eq_right hIsT] at hRWF
            obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
              ihP (hSP.2 0 trivial) (hShP.2 0 trivial) (hRWF 0) (fun j hj => (hIdxFree j hj).2 0) hP0
            exact ⟨a', outP, outV, fSt, suf, .began prover at_ :: recP, src', h1, by
              rw [handler_run_retry_begin_other M hP bound target at_ hIsT kP' _ (hPassP _ st buf trivial)]
              exact .begin h2, h3, h4, h5, h6, h7, h8⟩
      | @settles at_ _ kP' _ ihP =>
          obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
            ihP (hSP.2 () trivial) (hShP.2 () trivial) (hRWF.2 ()) (fun j hj => hIdxFree j hj ()) hP0
          exact ⟨a', outP, outV, fSt, suf, .settled prover at_ :: recP, src', h1, by
            rw [handler_run_retry_settle M hP bound target at_ kP' _ (hPassP _ st buf trivial)]
            exact .settle h2, h3, h4, h5, h6, h7, h8⟩
      | done hPostP =>
          cases hP0
          generalize hPV0 : Process.done a = pv0 at hPV
          induction hPV with
          | @begins atV _ kV' _ ihV =>
              obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
              exact ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.began verifier atV :: recV, by
                  rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | @settles atV _ kV' _ ihV =>
              obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
              exact ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.settled verifier atV :: recV, by
                  rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | done hPostV =>
              cases hPV0
              exact ⟨a, _, _, st, [], [], attemptSrc kIdx, (fun _ h => nomatch h),
                by simpa [Handler.run] using Alone.done,
                fun post _ => ⟨[], by simpa [Handler.run] using Alone.done⟩,
                hPostP, hPostV, trivial, (fun _ _ _ => rfl), ⟨[], .done⟩⟩
          | _ => cases hPV0
      | _ => cases hP0
  | halt payload =>
      intro _ _ _ _ _ _ source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNoHaltK
      obtain ⟨_, hContra⟩ := hNoHaltK (shiftAttemptSource M insideCoins (.attempt target.key kIdx) source)
        trivial (fun _ _ _ => rfl) (.stopped payload.1 payload.2) ⟨[], .halt⟩
      cases hContra
  | call op k ih =>
      intro postP postV qP qV st buf source hStV hBufV hPP hPV hSP hSV hShP hShV hRWF hIdxFree
        hPShape hUniq hLPAb hFedAb hAborts hLPK hFedK hNoHaltK
      let attemptSrc := fun i => shiftAttemptSource M insideCoins (.attempt target.key i) source
      generalize hP0 : Process.call op k = p0 at hPP
      induction hPP with
      | @begins at_ _ kP' hPP' ihP =>
          by_cases hIsT : at_.site = target
          · dsimp only [Program.RetryWellFormed] at hRWF; rw [ite_eq_left hIsT] at hRWF
            exact hEnterTarget _ at_ hIsT kP' qV st buf source hStV hBufV hPP' (hP0 ▸ hPV)
              (fun n => hSP.2 n trivial) hSV (fun n => hShP.2 n trivial) hShV hRWF
              (fun j hj => (hIdxFree j hj).1 hIsT) (hP0 ▸ hPShape) (hP0 ▸ hUniq)
              (hP0 ▸ hLPAb) (hP0 ▸ hFedAb) (hP0 ▸ hAborts) (hP0 ▸ hLPK) (hP0 ▸ hFedK) (hP0 ▸ hNoHaltK)
          · dsimp only [Program.RetryWellFormed] at hRWF; rw [ite_eq_right hIsT] at hRWF
            obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
              ihP (hSP.2 0 trivial) (hShP.2 0 trivial) (hRWF 0) (fun j hj => (hIdxFree j hj).2 0) hP0
            exact ⟨a, outP, outV, fSt, suf, .began prover at_ :: recP, src', h1, by
              rw [handler_run_retry_begin_other M hP bound target at_ hIsT kP' _ (hPassP _ st buf trivial)]
              exact .begin h2, h3, h4, h5, h6, h7, h8⟩
      | @settles at_ _ kP' _ ihP =>
          obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
            ihP (hSP.2 () trivial) (hShP.2 () trivial) (hRWF.2 ()) (fun j hj => hIdxFree j hj ()) hP0
          exact ⟨a, outP, outV, fSt, suf, .settled prover at_ :: recP, src', h1, by
            rw [handler_run_retry_settle M hP bound target at_ kP' _ (hPassP _ st buf trivial)]
            exact .settle h2, h3, h4, h5, h6, h7, h8⟩
      | done _ => cases hP0
      | stopsHere _ => cases hP0
      | stopsElsewhere _ => cases hP0
      | @gave kind getters at_ τ x kG kP' _ hPP' ihUnused =>
          clear ihUnused
          cases hP0
          obtain ⟨eP, hEP, hSiteP, hTyP, hClsP⟩ := hShP.1
          have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
          have hVin : verifier ∈ getters := by
            rcases hDisc with ⟨_, hV⟩ | ⟨hNotP, _, _, _⟩
            · exact hV
            · exact absurd rfl hNotP
          have hMsgV : M.Valid τ x := hSP.1
          obtain ⟨st', chunk, hSt'V, hChV, hStepP, hStepV⟩ :=
            derived_step_flow M hCPSt hCVSt hLPSt hLVSt hLayDecl hLayLaw hCC hSL
              hMsgV hStV hBufV hEP hSiteP hTyP hVin hClsP
          have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := fun u hu =>
            (List.mem_append.mp hu).elim (hBufV u) (hChV u)
          generalize hPV0 : (Process.call (GOp.flow kind prover getters at_ τ x) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | @begins atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.began verifier atV :: recV, by
                  rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | @settles atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.settled verifier atV :: recV, by
                  rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | gave _ _ => cases hPV0; exact absurd rfl hNe
          | passed _ hVOut _ => cases hPV0; exact absurd hVin hVOut
          | got _ _ hPV' =>
              cases hPV0
              obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                ih () (kP' ()) _ st' (buf ++ chunk) source hSt'V hBufChV hPP' hPV'
                  (hSP.2 () trivial) (hSV.2 x hMsgV) (hShP.2 () trivial) (hShV.2 x trivial)
                  (hRWF ()) (fun j hj => hIdxFree j hj ()) (hPShape.2 ()) (hUniq ()).2
                  hLPAb hFedAb
                  (fun j hj s₁ hL₁ hAg₁ => by
                    obtain ⟨_, who, why, hR, hW, hA⟩ := hAborts j hj s₁ hL₁ hAg₁
                    cases hR with | flow hR' => exact ⟨_, who, why, hR', hW, hA⟩)
                  hLPK hFedK
                  (fun s₁ hL₁ hAg₁ e ⟨evs₁, hR₁⟩ => hNoHaltK s₁ hL₁ hAg₁ e ⟨_, .flow hR₁⟩)
              refine ⟨a, outP, outV, fSt, chunk ++ suf', recP, src',
                (fun u hu => (List.mem_append.mp hu).elim (hChV u) (hSufV u)), ?_, ?_,
                hPostP, hPostV, hLSrc', hAgSrc', ⟨_, .flow hRun'⟩⟩
              · exact alone_eq_proc M (handler_run_retry_clause_done M hP bound target (.give kind getters at_ τ x) rfl kP' _ _ () hStepP)
                  (by simpa [List.append_assoc] using hAlP)
              · intro post hPost
                have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := fun u hu =>
                  (List.mem_append.mp hu).elim (hSufV u) (hPost u)
                obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                refine ⟨recV, ?_⟩
                have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                  simp [List.append_assoc]
                have hBufEq2 : buf ++ chunk ++ (suf' ++ post) = (buf ++ chunk) ++ suf' ++ post := by
                  simp [List.append_assoc]
                have hLenEq : buf.length + (chunk ++ suf').length = (buf ++ chunk).length + suf'.length := by
                  simp [List.length_append, Nat.add_assoc]
                rw [hBufEq]
                refine alone_eq_proc M (stack_run_clause_done M _ _ _ _ _ _ (hStepV (suf' ++ post) hSufPostV)) ?_
                rw [hLenEq, hBufEq2, ← List.length_append]
                exact hAlV'
          | _ => cases hPV0
      | got hGNeP hPIn _ =>
          cases hP0
          obtain ⟨eP, hEP, _, _, _, _, hPin', hClsP⟩ := hShP.1
          have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
          rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, hNotP, _⟩
          · exact absurd hEqP hGNeP
          · exact absurd hPin' hNotP
      | @passed kind giver getters at_ τ x kG _ hGNeP _ hPP' ihUnused =>
          clear ihUnused
          cases hP0
          generalize hPV0 : (Process.call (GOp.flow kind giver getters at_ τ x) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | @begins atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.began verifier atV :: recV, by
                  rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | @settles atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.settled verifier atV :: recV, by
                  rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | gave _ _ =>
              cases hPV0
              obtain ⟨eV, hEV, _, _, hClsV⟩ := hShV.1
              have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
              rcases hDisc with ⟨hEqP, _⟩ | ⟨_, hNotV, _, _⟩
              · exact absurd hEqP.symm hNe
              · exact absurd rfl hNotV
          | got _ hVin _ =>
              cases hPV0
              obtain ⟨eV, hEV, _, _, _, _, hVin', hClsV⟩ := hShV.1
              have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
              rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, _, hNotV⟩
              · exact absurd hEqP hGNeP
              · exact absurd hVin' hNotV
          | passed _ _ hPV' =>
              cases hPV0
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨evs', hRun'⟩⟩ :=
                ih () _ _ st buf source hStV hBufV hPP' hPV' hSP hSV hShP hShV hRWF hIdxFree
                  (hPShape.2 ()) (hUniq ()).2 hLPAb hFedAb
                  (fun j hj s₁ hL₁ hAg₁ => by
                    obtain ⟨_, who, why, hR, hW, hA⟩ := hAborts j hj s₁ hL₁ hAg₁
                    cases hR with | flow hR' => exact ⟨_, who, why, hR', hW, hA⟩)
                  hLPK hFedK
                  (fun s₁ hL₁ hAg₁ e ⟨evs₁, hR₁⟩ => hNoHaltK s₁ hL₁ hAg₁ e ⟨_, .flow hR₁⟩)
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨_, .flow hRun'⟩⟩
          | _ => cases hPV0
      | @owned gkind hearers at_ gIns payload τ kG kP' hPP' ihUnused =>
          clear ihUnused
          cases hP0
          obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          have hNotH : (∃ law, gkind = .coin law ∧ hearers = []) ∨
              (∃ svc, gkind = .request svc ∧ verifier ∉ hearers) := by
            cases gkind with
            | coin law =>
                rcases hDisc with ⟨hOwV, _, _⟩ | hNil
                · exact absurd hOwV hNe
                · exact .inl ⟨law, rfl, hNil⟩
            | request svc => exact .inr ⟨svc, rfl, hDisc.2.resolve_left hNe⟩
          generalize hPV0 : (Process.call (GOp.given gkind prover hearers at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | @begins atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.began verifier atV :: recV, by
                  rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | @settles atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.settled verifier atV :: recV, by
                  rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | owned _ => cases hPV0; exact absurd rfl hNe
          | heard _ hVin _ =>
              cases hPV0
              rcases hNotH with ⟨_, _, rfl⟩ | ⟨_, _, hOut⟩
              · cases hVin
              · exact absurd hVin hOut
          | @unheard _ _ _ _ _ _ _ _ qV' _ _ hPV' =>
              cases hPV0
              have hStepOwn : (hOutC : at_.site ∉ insideCoins) →
                  (hCl : ROp.IsClosed M (.own gkind hearers at_ gIns payload τ)) →
                  ∀ v, (hvSrcK : attemptSrc kIdx at_ τ = some v) →
                  (hAl : Allows M gkind gIns payload τ v) →
                  (hLPK' : LawfulPrivate M (attemptSrc kIdx) (kG v)) →
                  (hFedK' : Fed M (attemptSrc kIdx) (kG v)) →
                  (∀ j, j < kIdx → LawfulPrivate M (attemptSrc j) (kG v) ∧ Fed M (attemptSrc j) (kG v)) →
                  ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
                    (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
                    (∀ u ∈ suffix, M.Valid unitTy u) ∧
                    Alone M source prover
                      (hP.run (retryOf M (some (bound, target))) (.call (.own gkind hearers at_ gIns payload τ) kP')
                        (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
                      recP (.returned (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ suffix)) .nil))) ∧
                    (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
                      ∃ recV, Alone M source verifier
                        (hV.run (retryOf M none) qV'
                          (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
                        recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
                          (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
                    postP a outP ∧ postV a outV ∧
                    Lawful M source' (.call (.given gkind prover hearers at_ gIns payload τ) kG) ∧
                    (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source' at' τ' = attemptSrc kIdx at' τ') ∧
                    GExec M source' (.call (.given gkind prover hearers at_ gIns payload τ) kG) (.returned a) := by
                intro hOutC hCl v hvSrcK hAl hLPK' hFedK' hAbStep
                have hSrcEq : source at_ τ = some v := by
                  have h := hvSrcK; dsimp only [attemptSrc, shiftAttemptSource] at h; rwa [ite_eq_right hOutC] at h
                have hSrcJ : ∀ j, attemptSrc j at_ τ = some v := by
                  intro j; dsimp only [attemptSrc, shiftAttemptSource]; rw [ite_eq_right hOutC]; exact hSrcEq
                obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                  ih v (kP' v) qV' st buf source hStV hBufV (hPP' v) (hPV' v)
                    (hSP.2 v (allows_valid M hAl)) hSV (hShP.2 v trivial) hShV
                    (by cases gkind with | coin _ => (cases hearers with | nil => exact hRWF.2 v | cons _ _ => exact hRWF v) | request _ => exact hRWF.2 v)
                    (fun j hj => hIdxFree j hj v) (hPShape.2 v) (hUniq v).2
                    (fun j hj => (hAbStep j hj).1) (fun j hj => (hAbStep j hj).2)
                    (fun j hj => step_aborts_given M (hSrcJ j) hAl (hUniq v).1 (hAborts j hj))
                    hLPK' hFedK' (step_noHalt_given M hvSrcK hAl (hUniq v).1 hNoHaltK)
                let src'' := patchSource M src' at_ τ v
                have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                  fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                have hAlP' : ∃ recP', Alone M source prover
                    (hP.run (retryOf M (some (bound, target))) (.call (.own gkind hearers at_ gIns payload τ) kP')
                      (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
                    recP' (.returned (outP, .cons (hCPSt.symm ▸ fSt) (.cons (hLPSt.symm ▸ (buf ++ suf)) .nil))) :=
                  ⟨_, by
                    rw [handler_run_retry_own M hP bound target gkind hearers at_ gIns payload τ kP' _
                      (hPassP _ st buf hCl)]
                    exact .own hSrcEq hAlP⟩
                obtain ⟨recP', hAlP'⟩ := hAlP'
                refine ⟨a, outP, outV, fSt, suf, recP', src'', hSufV, hAlP', hAlV, hPostP, hPostV, ?_, ?_,
                  ⟨_, .given (patchSource_self M src' at_ τ v) (grun_of_agree M hAgP (hUniq v).1 hRun')⟩⟩
                · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                  exact ⟨hAl, lawful_of_agree M hAgP (hUniq v).1 hLSrc'⟩
                · intro at' τ' hNotH'
                  by_cases hEqAt : at' = at_
                  · subst at'
                    by_cases hEqT : τ' = τ
                    · subst hEqT; dsimp only [src'']; rw [patchSource_self]; exact hvSrcK.symm
                    · dsimp only [src'']; rw [patchSource_ne_ty M src' at_ τ v hEqT]; exact hAgSrc' at_ τ' hNotH'
                  · dsimp only [src'']; rw [patchSource_ne M src' at_ τ v hEqAt τ']; exact hAgSrc' at' τ' hNotH'
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrcK, hFedK'⟩ := hFedK
                obtain ⟨hAl, hLPK'⟩ := hLPK v hvSrcK
                have hOutC : at_.site ∉ insideCoins := hRWF.1
                refine hStepOwn hOutC trivial v hvSrcK hAl hLPK' hFedK' (fun j hj => ?_)
                have hSrcJ : attemptSrc j at_ τ = some v := by
                  have h := hvSrcK; dsimp only [attemptSrc, shiftAttemptSource] at h ⊢
                  rw [ite_eq_right hOutC] at h ⊢; exact h
                obtain ⟨_, hLPj'⟩ := hLPAb j hj v hSrcJ
                obtain ⟨v', hv', hFedj'⟩ := hFedAb j hj
                dsimp only [attemptSrc] at hSrcJ; rw [hSrcJ] at hv'; cases hv'
                exact ⟨hLPj', hFedj'⟩
              · obtain ⟨v, hvSrcK, hFedK'⟩ := hFedK
                obtain ⟨hAl, hLPK'⟩ := hLPK v hvSrcK
                have hOutC : at_.site ∉ insideCoins := hRWF.1
                refine hStepOwn hOutC trivial v hvSrcK hAl hLPK' hFedK' (fun j hj => ?_)
                have hSrcJ : attemptSrc j at_ τ = some v := by
                  have h := hvSrcK; dsimp only [attemptSrc, shiftAttemptSource] at h ⊢
                  rw [ite_eq_right hOutC] at h ⊢; exact h
                obtain ⟨_, hLPj'⟩ := hLPAb j hj v hSrcJ
                obtain ⟨v', hv', hFedj'⟩ := hFedAb j hj
                dsimp only [attemptSrc] at hSrcJ; rw [hSrcJ] at hv'; cases hv'
                exact ⟨hLPj', hFedj'⟩
          | _ => cases hPV0
      | @heard gkind owner hearers at_ gIns payload τ kG kP' hOwNe hPin hPP' ihUnused =>
          clear ihUnused
          cases hP0
          obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          cases gkind with
          | request svc => exact absurd hPin (hDisc.1.resolve_left hOwNe)
          | coin law =>
              rcases hDisc with ⟨hOwV, _, sig, hLaw, _, hSigIns⟩ | hNil
              · cases hOwV
                have hNonEmpty : ∃ h0 hs, hearers = h0 :: hs := by
                  cases hearers with
                  | nil => cases hPin
                  | cons h0 hs => exact ⟨h0, hs, rfl⟩
                obtain ⟨h0, hs, hHCons⟩ := hNonEmpty
                subst hHCons
                generalize hPV0 : (Process.call (GOp.given (.coin law) verifier (h0 :: hs) at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
                induction hPV with
                | @begins atV _ kV' _ ihV =>
                    obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                      ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
                    exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                      let ⟨recV, hAlV⟩ := h3 post hPost
                      ⟨.began verifier atV :: recV, by
                        rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                      h4, h5, h6, h7, h8⟩
                | @settles atV _ kV' _ ihV =>
                    obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                      ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
                    exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                      let ⟨recV, hAlV⟩ := h3 post hPost
                      ⟨.settled verifier atV :: recV, by
                        rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                      h4, h5, h6, h7, h8⟩
                | done _ => cases hPV0
                | stopsHere _ => cases hPV0
                | stopsElsewhere _ => cases hPV0
                | heard hNeS _ _ => cases hPV0; exact absurd rfl hNeS
                | unheard hNeS _ _ => cases hPV0; exact absurd rfl hNeS
                | owned hPV' =>
                    cases hPV0
                    obtain ⟨eV, hEV, hSiteV, hTyV, hClsV, hTypedV⟩ := hShV.1
                    have hGInsNil : gIns = [] := by
                      obtain ⟨s, hsLaw, hsIns, _⟩ := hTypedV
                      rw [hLaw] at hsLaw; cases hsLaw; rw [← hsIns, hSigIns]
                    subst hGInsNil; cases payload
                    obtain ⟨coin, st', chunk, hCoinV, hAl, hAtH, hSt'V, hChV, hStepP, hStepV⟩ :=
                      derived_step_heard_coin M hCPSt hCVSt hLPSt hLVSt hConDecl hLayDecl hSuiteLaw hLayLaw
                        hCC hSL hStV hBufV hEV hSiteV hTyV hPin hClsV
                    have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := fun u hu =>
                      (List.mem_append.mp hu).elim (hBufV u) (hChV u)
                    obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                      ih coin (kP' coin) _ st' (buf ++ chunk) source hSt'V hBufChV (hPP' coin) (hPV' coin)
                        (hSP.2 coin hCoinV) (hSV.2 coin hCoinV) (hShP.2 coin trivial) (hShV.2 coin trivial)
                        (hRWF coin) (fun j hj => hIdxFree j hj coin) (hPShape.2 coin) (hUniq coin).2
                        (fun j hj => hLPAb j hj coin hAl) (fun j hj => hFedAb j hj coin hAl)
                        (fun j hj => step_aborts_heard_coin M hAtH hAl (hUniq coin).1 (hAborts j hj))
                        (hLPK coin hAl) (hFedK coin hAl)
                        (step_noHalt_heard_coin M hAtH hAl (hUniq coin).1 hNoHaltK)
                    let src'' := patchSource M src' at_ τ coin
                    have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                      fun at' τ' hne => (patchSource_ne M src' at_ τ coin hne τ').symm
                    refine ⟨a, outP, outV, fSt, chunk ++ suf', recP, src'',
                      (fun u hu => (List.mem_append.mp hu).elim (hChV u) (hSufV u)), ?_, ?_,
                      hPostP, hPostV, ?_, ?_,
                      ⟨_, .given (patchSource_self M src' at_ τ coin) (grun_of_agree M hAgP (hUniq coin).1 hRun')⟩⟩
                    · exact alone_eq_proc M (handler_run_retry_clause_done M hP bound target (.hear (.coin law) verifier at_ τ) rfl kP' _ _ coin hStepP)
                        (by simpa [List.append_assoc] using hAlP)
                    · intro post hPost
                      have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := fun u hu =>
                        (List.mem_append.mp hu).elim (hSufV u) (hPost u)
                      obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                      refine ⟨recV, ?_⟩
                      have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                        simp [List.append_assoc]
                      have hBufEq2 : buf ++ chunk ++ (suf' ++ post) = (buf ++ chunk) ++ suf' ++ post := by
                        simp [List.append_assoc]
                      have hLenEq : buf.length + (chunk ++ suf').length = (buf ++ chunk).length + suf'.length := by
                        simp [List.length_append, Nat.add_assoc]
                      rw [hBufEq]
                      refine alone_eq_proc M (stack_run_clause_done M _ _ _ _ _ _ (hStepV (suf' ++ post) hSufPostV)) ?_
                      rw [hLenEq, hBufEq2, ← List.length_append]
                      exact hAlV'
                    · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                      exact ⟨hAl, lawful_of_agree M hAgP (hUniq coin).1 hLSrc'⟩
                    · intro at' τ' hNotH'
                      have hne : at' ≠ at_ := fun heq => hNotH' (heq ▸ hAtH)
                      dsimp only [src'']; rw [patchSource_ne M src' at_ τ coin hne τ']; exact hAgSrc' at' τ' hNotH'
                | _ => cases hPV0
              · subst hNil; cases hPin
      | @unheard gkind owner hearers at_ gIns payload τ kG q hOwNe hNotIn hPP' ihUnused =>
          clear ihUnused
          cases hP0
          obtain ⟨eG, hEG, hSiteG, _, hClsG⟩ := hPShape.1
          have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
          have hNotH : (∃ law, gkind = .coin law ∧ hearers = []) ∨
              (∃ svc, gkind = .request svc ∧ (owner = verifier ∨ verifier ∉ hearers)) := by
            cases gkind with
            | coin law =>
                rcases hDisc with ⟨_, hPin', _⟩ | hNil
                · exact absurd hPin' hNotIn
                · exact .inl ⟨law, rfl, hNil⟩
            | request svc => exact .inr ⟨svc, rfl, hDisc.2⟩
          have hOutC : at_.site ∉ insideCoins := by
            have hEv := attemptCoinsExclusive_ev_notin prover target d.entry.shape hExcl hEG
            rw [hClsG] at hEv
            rcases hNotH with ⟨_, rfl, rfl⟩ | ⟨_, rfl, _⟩
            · exact hSiteG ▸ hEv hOwNe
            · exact hSiteG ▸ hEv
          generalize hPV0 : (Process.call (GOp.given gkind owner hearers at_ gIns payload τ) kG : Protocol M A) = pv0 at hPV
          induction hPV with
          | @begins atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 0 trivial) (hShV.2 0 trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.began verifier atV :: recV, by
                  rw [stack_run_begin M hV atV kV' _ (hPassV _ st _ trivial)]; exact .begin hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | @settles atV _ kV' _ ihV =>
              obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
                ihV (hSV.2 () trivial) (hShV.2 () trivial) hPV0
              exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, fun post hPost =>
                let ⟨recV, hAlV⟩ := h3 post hPost
                ⟨.settled verifier atV :: recV, by
                  rw [stack_run_settle M hV atV kV' _ (hPassV _ st _ trivial)]; exact .settle hAlV⟩,
                h4, h5, h6, h7, h8⟩
          | done _ => cases hPV0
          | stopsHere _ => cases hPV0
          | stopsElsewhere _ => cases hPV0
          | @owned _ _ _ _ _ _ _ kV' hPV' =>
              cases hPV0
              have hStepV : (hCl : ROp.IsClosed M (.own gkind hearers at_ gIns payload τ)) →
                  ∀ v, (hvSrcK : attemptSrc kIdx at_ τ = some v) →
                  (hAl : Allows M gkind gIns payload τ v) →
                  (hLPK' : LawfulPrivate M (attemptSrc kIdx) (kG v)) →
                  (hFedK' : Fed M (attemptSrc kIdx) (kG v)) →
                  (∀ j, j < kIdx → LawfulPrivate M (attemptSrc j) (kG v) ∧ Fed M (attemptSrc j) (kG v)) →
                  ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
                    (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
                    (∀ u ∈ suffix, M.Valid unitTy u) ∧
                    Alone M source prover
                      (hP.run (retryOf M (some (bound, target))) q
                        (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
                      recP (.returned (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ suffix)) .nil))) ∧
                    (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
                      ∃ recV, Alone M source verifier
                        (hV.run (retryOf M none) (.call (.own gkind hearers at_ gIns payload τ) kV')
                          (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
                        recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
                          (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
                    postP a outP ∧ postV a outV ∧
                    Lawful M source' (.call (.given gkind verifier hearers at_ gIns payload τ) kG) ∧
                    (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source' at' τ' = attemptSrc kIdx at' τ') ∧
                    GExec M source' (.call (.given gkind verifier hearers at_ gIns payload τ) kG) (.returned a) := by
                intro hCl v hvSrcK hAl hLPK' hFedK' hAbStep
                have hSrcEq : source at_ τ = some v := by
                  have h := hvSrcK; dsimp only [attemptSrc, shiftAttemptSource] at h; rwa [ite_eq_right hOutC] at h
                have hSrcJ : ∀ j, attemptSrc j at_ τ = some v := by
                  intro j; dsimp only [attemptSrc, shiftAttemptSource]; rw [ite_eq_right hOutC]; exact hSrcEq
                obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                  ih v q (kV' v) st buf source hStV hBufV (hPP' v) (hPV' v)
                    hSP (hSV.2 v (allows_valid M hAl)) hShP (hShV.2 v trivial) hRWF hIdxFree
                    (hPShape.2 v) (hUniq v).2 (fun j hj => (hAbStep j hj).1) (fun j hj => (hAbStep j hj).2)
                    (fun j hj => step_aborts_given M (hSrcJ j) hAl (hUniq v).1 (hAborts j hj))
                    hLPK' hFedK' (step_noHalt_given M hvSrcK hAl (hUniq v).1 hNoHaltK)
                let src'' := patchSource M src' at_ τ v
                have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                  fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                refine ⟨a, outP, outV, fSt, suf, recP, src'', hSufV, hAlP, ?_, hPostP, hPostV, ?_, ?_,
                  ⟨_, .given (patchSource_self M src' at_ τ v) (grun_of_agree M hAgP (hUniq v).1 hRun')⟩⟩
                · intro post hPost
                  obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                  exact ⟨_, by rw [stack_run_own M hV _ _ _ _ _ _ kV' _ (hPassV _ st _ hCl)]; exact .own hSrcEq hAlV'⟩
                · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                  exact ⟨hAl, lawful_of_agree M hAgP (hUniq v).1 hLSrc'⟩
                · intro at' τ' hNotH'
                  by_cases hEqAt : at' = at_
                  · subst at'
                    by_cases hEqT : τ' = τ
                    · subst hEqT; dsimp only [src'']; rw [patchSource_self]; exact hvSrcK.symm
                    · dsimp only [src'']; rw [patchSource_ne_ty M src' at_ τ v hEqT]; exact hAgSrc' at_ τ' hNotH'
                  · dsimp only [src'']; rw [patchSource_ne M src' at_ τ v hEqAt τ']; exact hAgSrc' at' τ' hNotH'
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrcK, hFedK'⟩ := hFedK
                obtain ⟨hAl, hLPK'⟩ := hLPK v hvSrcK
                refine hStepV trivial v hvSrcK hAl hLPK' hFedK' (fun j hj => ?_)
                have hSrcJ : attemptSrc j at_ τ = some v := by
                  have h := hvSrcK; dsimp only [attemptSrc, shiftAttemptSource] at h ⊢
                  rw [ite_eq_right hOutC] at h ⊢; exact h
                obtain ⟨_, hLPj'⟩ := hLPAb j hj v hSrcJ
                obtain ⟨v', hv', hFedj'⟩ := hFedAb j hj
                dsimp only [attemptSrc] at hSrcJ; rw [hSrcJ] at hv'; cases hv'
                exact ⟨hLPj', hFedj'⟩
              · obtain ⟨v, hvSrcK, hFedK'⟩ := hFedK
                obtain ⟨hAl, hLPK'⟩ := hLPK v hvSrcK
                refine hStepV trivial v hvSrcK hAl hLPK' hFedK' (fun j hj => ?_)
                have hSrcJ : attemptSrc j at_ τ = some v := by
                  have h := hvSrcK; dsimp only [attemptSrc, shiftAttemptSource] at h ⊢
                  rw [ite_eq_right hOutC] at h ⊢; exact h
                obtain ⟨_, hLPj'⟩ := hLPAb j hj v hSrcJ
                obtain ⟨v', hv', hFedj'⟩ := hFedAb j hj
                dsimp only [attemptSrc] at hSrcJ; rw [hSrcJ] at hv'; cases hv'
                exact ⟨hLPj', hFedj'⟩
          | heard _ hVin _ =>
              cases hPV0
              rcases hNotH with ⟨_, _, rfl⟩ | ⟨_, _, hVO⟩
              · cases hVin
              · exact absurd hVin (hVO.resolve_left (by assumption))
          | @unheard _ _ _ _ _ _ _ _ qV' _ _ hPV' =>
              cases hPV0
              have hStepU : ∀ v, (hvSrcK : attemptSrc kIdx at_ τ = some v) →
                  (hAl : Allows M gkind gIns payload τ v) →
                  (hLPK' : LawfulPrivate M (attemptSrc kIdx) (kG v)) →
                  (hFedK' : Fed M (attemptSrc kIdx) (kG v)) →
                  (∀ j, j < kIdx → LawfulPrivate M (attemptSrc j) (kG v) ∧ Fed M (attemptSrc j) (kG v)) →
                  ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
                    (suffix : List (M.Val unitTy)) (recP : List (Happened M)) (source' : Source M),
                    (∀ u ∈ suffix, M.Valid unitTy u) ∧
                    Alone M source prover
                      (hP.run (retryOf M (some (bound, target))) q
                        (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
                      recP (.returned (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ suffix)) .nil))) ∧
                    (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
                      ∃ recV, Alone M source verifier
                        (hV.run (retryOf M none) qV'
                          (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
                        recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
                          (.cons (hLVSt.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
                    postP a outP ∧ postV a outV ∧
                    Lawful M source' (.call (.given gkind owner hearers at_ gIns payload τ) kG) ∧
                    (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source' at' τ' = attemptSrc kIdx at' τ') ∧
                    GExec M source' (.call (.given gkind owner hearers at_ gIns payload τ) kG) (.returned a) := by
                intro v hvSrcK hAl hLPK' hFedK' hAbStep
                have hSrcJ : ∀ j, attemptSrc j at_ τ = some v := by
                  intro j; have h := hvSrcK; dsimp only [attemptSrc, shiftAttemptSource] at h ⊢
                  rw [ite_eq_right hOutC] at h ⊢; exact h
                obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                  ih v q qV' st buf source hStV hBufV (hPP' v) (hPV' v) hSP hSV hShP hShV hRWF hIdxFree
                    (hPShape.2 v) (hUniq v).2 (fun j hj => (hAbStep j hj).1) (fun j hj => (hAbStep j hj).2)
                    (fun j hj => step_aborts_given M (hSrcJ j) hAl (hUniq v).1 (hAborts j hj))
                    hLPK' hFedK' (step_noHalt_given M hvSrcK hAl (hUniq v).1 hNoHaltK)
                let src'' := patchSource M src' at_ τ v
                have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                  fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                refine ⟨a, outP, outV, fSt, suf, recP, src'', hSufV, hAlP, hAlV, hPostP, hPostV, ?_, ?_,
                  ⟨_, .given (patchSource_self M src' at_ τ v) (grun_of_agree M hAgP (hUniq v).1 hRun')⟩⟩
                · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                  exact ⟨hAl, lawful_of_agree M hAgP (hUniq v).1 hLSrc'⟩
                · intro at' τ' hNotH'
                  by_cases hEqAt : at' = at_
                  · subst at'
                    by_cases hEqT : τ' = τ
                    · subst hEqT; dsimp only [src'']; rw [patchSource_self]; exact hvSrcK.symm
                    · dsimp only [src'']; rw [patchSource_ne_ty M src' at_ τ v hEqT]; exact hAgSrc' at_ τ' hNotH'
                  · dsimp only [src'']; rw [patchSource_ne M src' at_ τ v hEqAt τ']; exact hAgSrc' at' τ' hNotH'
              rcases hNotH with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
              · obtain ⟨v, hvSrcK, hFedK'⟩ := hFedK
                obtain ⟨hAl, hLPK'⟩ := hLPK v hvSrcK
                refine hStepU v hvSrcK hAl hLPK' hFedK' (fun j hj => ?_)
                have hSrcJ : attemptSrc j at_ τ = some v := by
                  have h := hvSrcK; dsimp only [attemptSrc, shiftAttemptSource] at h ⊢
                  rw [ite_eq_right hOutC] at h ⊢; exact h
                obtain ⟨_, hLPj'⟩ := hLPAb j hj v hSrcJ
                obtain ⟨v', hv', hFedj'⟩ := hFedAb j hj
                dsimp only [attemptSrc] at hSrcJ; rw [hSrcJ] at hv'; cases hv'
                exact ⟨hLPj', hFedj'⟩
              · obtain ⟨v, hvSrcK, hFedK'⟩ := hFedK
                obtain ⟨hAl, hLPK'⟩ := hLPK v hvSrcK
                refine hStepU v hvSrcK hAl hLPK' hFedK' (fun j hj => ?_)
                have hSrcJ : attemptSrc j at_ τ = some v := by
                  have h := hvSrcK; dsimp only [attemptSrc, shiftAttemptSource] at h ⊢
                  rw [ite_eq_right hOutC] at h ⊢; exact h
                obtain ⟨_, hLPj'⟩ := hLPAb j hj v hSrcJ
                obtain ⟨v', hv', hFedj'⟩ := hFedAb j hj
                dsimp only [attemptSrc] at hSrcJ; rw [hSrcJ] at hv'; cases hv'
                exact ⟨hLPj', hFedj'⟩

          | _ => cases hPV0
/-! ### 4f. Top-level theorems: `deploy_complete_retry` and `deploy_complete_retry_nonaborting` -/

private theorem cast_ins_eq_cast_hdr_retry {hs : Headers V} {r : Role}
    {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂) (ls : List (Layer V hs r hdr₂.ins)) :
    cast (congrArg (fun x => List (Layer V hs r x)) (congrArg ProtocolHeader.ins h.symm)) ls =
      h ▸ ls := by
  subst h; rfl

private theorem alone_cast_stack2_retry {a : Admitted V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (hE : hdr₁ = hdr₂) (c l : Layer V a.program.headers r hdr₂.ins)
    {stC stL : V.Ty} (hStC : c.state = stC) (hStL : l.state = stL)
    (ret : Option (Nat × Site))
    {B : Type} {source : Source M} {p : Program M B}
    {rec : List (Happened M)} {out : B} {c0 c1 : M.Val stC} {l0 l1 : M.Val stL}
    (hAl : Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [hE ▸ c, hE ▸ l]).run
        (retryOf M ret) p (.cons ((layer_cast_state hE c).trans hStC ▸ c0)
          (.cons ((layer_cast_state hE l).trans hStL ▸ l0) .nil)))
      rec (.returned (out, .cons ((layer_cast_state hE c).trans hStC ▸ c1)
        (.cons ((layer_cast_state hE l).trans hStL ▸ l1) .nil)))) :
    Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) (hE ▸ [c, l])).run
        (retryOf M ret) p (cast (by subst hE; subst hStC; subst hStL; rfl) (HList.cons c0 (HList.cons l0 HList.nil))))
      rec (.returned (out, cast (by subst hE; subst hStC; subst hStL; rfl) (HList.cons c1 (HList.cons l1 HList.nil)))) := by
  subst hE; subst hStC; subst hStL; exact hAl

private theorem alone_deployed_run_congr_retry {a : Admitted V} {d : Deployed V} (hA : d.admitted = a)
    {ret : Option (Nat × Site)} (hRet : d.retry = ret)
    {r : Role} {s : List (Layer V a.program.headers r d.entry.ins)}
    (hSt : hA ▸ d.stack r = s)
    {source : Source M} {ins : HList (RV M r) d.entry.ins}
    {t₁ : HList M.Val (Stack.Takes (d.stack r))} {t₂ : HList M.Val (Stack.Takes s)}
    (hT : HEq t₁ t₂)
    {rec : List (Happened M)} {out : HList (RV M r) d.entry.outs}
    {g₁ : HList M.Val (Stack.Gives (d.stack r))} {g₂ : HList M.Val (Stack.Gives s)}
    (hG : HEq g₁ g₂)
    (hRun : Alone M source r (runStack a M (hA ▸ d.callee) ret r s ins t₂) rec (.returned (out, g₂))) :
    Alone M source r (d.run M r ins t₁) rec (.returned (out, g₁)) := by
  cases d; dsimp only at hA; subst hA
  dsimp only [Deployed.run, runStack, Deployed.callee, Deployed.entry] at hSt hRun ⊢
  subst hSt; rw [hRet]; cases eq_of_heq hT; cases eq_of_heq hG; exact hRun

/-- **Abort-and-retry completeness** for non-interactive `.derived` streaming deployments whose
prover retries a declared attempt site (`declaration.retry = some (bound, retrySite)`):
if attempts `0 .. k - 1` (`k < bound`) abort at the prover and attempt `k` succeeds without halting,
then the prover rolls back transcript state and proof buffer cleanly on every abort via
`restoreAgain` and succeeds on attempt `k`, producing a proof accepted by the verifier whose
execution matches a lawful protocol run under the attempt-`k` source. -/
theorem deploy_complete_retry (enc : VocabEncoder V) {named : NamedProgram V} {assoc : Association}
    {a : Admitted V} (hAdmit : admit named assoc = .ok a)
    (declaration : Declaration) (d : Deployed V)
    (hDep : deploy enc a declaration = .ok d)
    {suite : ModuleRef} {sessionTag : Option (List Nat)}
    (hDerived : declaration.construction = .derived suite sessionTag)
    {bound : Nat} {retrySite : Site}
    (hRetry : declaration.retry = some (bound, retrySite))
    (hNoSamp : declaration.samples = none)
    (hNoRec : ∀ lay, declaration.layout = some lay → lay.recover = [])
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M)
    {prover verifier : Role} (hRoles : d.roles = some (prover, verifier))
    (first : Stack.Takes (d.stack prover) = [])
    (matched : Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier))
    (ins : HList (LVal M) d.entry.ins) (hIns : ins.All (fun a v => M.Valid a.ty v))
    (source : Source M) (k : Nat) (hKLt : k < bound)
    (hFnsNoAb : Defs.fnsNoAbort d.admitted.program.defs = true)
    (hOnce : d.entry.shape.retryAtMostOnce retrySite [] = true)
    (hOwned : d.entry.shape.retryOwnedBy prover retrySite [] = true)
    (hExcl : d.entry.shape.attemptCoinsExclusive prover retrySite = true)
    (hVNoAtt : d.entry.shape.hasAttemptFor verifier retrySite [] = false)
    (hIdxFree : ∀ j, j ≤ k →
      Program.AttemptIndexFree M retrySite j
        (roleMeaning M d.admitted.program d.callee prover [] (hideAll M prover ins)))
    (hLPAb : ∀ j, j < k →
      LawfulPrivate M (shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
        (.attempt retrySite.key j) source)
        (protocolMeaning M d.admitted.program d.callee [] ins))
    (hFedAb : ∀ j, j < k →
      Fed M (shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
        (.attempt retrySite.key j) source)
        (protocolMeaning M d.admitted.program d.callee [] ins))
    (hAborts : ∀ j, j < k →
      ∀ source₁, Lawful M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) →
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
          source₁ at' τ' = shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
            (.attempt retrySite.key j) source at' τ') →
        ∃ evs who why,
          GRun M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) evs (.stopped who why) ∧
          prover ∈ who ∧ why.isAbort = true)
    (hLPK : LawfulPrivate M (shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
        (.attempt retrySite.key k) source)
      (protocolMeaning M d.admitted.program d.callee [] ins))
    (hFedK : Fed M (shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
        (.attempt retrySite.key k) source)
      (protocolMeaning M d.admitted.program d.callee [] ins))
    (hNoHaltK : ∀ source₁, Lawful M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) →
      (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
        source₁ at' τ' = shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
          (.attempt retrySite.key k) source at' τ') →
      ∀ e, GExec M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) e →
      ∃ out, e = .returned out) :
    ∃ outP gives recordP outV givesV recordV,
      Alone M source prover
        (d.run M prover (hideAll M prover ins) (cast (congrArg (HList M.Val) first.symm) .nil))
        recordP (.returned (outP, gives)) ∧
      Alone M source verifier
        (d.run M verifier (hideAll M verifier ins) (cast (congrArg (HList M.Val) matched) gives))
        recordV (.returned (outV, givesV)) ∧
      ∃ source' out,
        Lawful M source' (protocolMeaning M d.admitted.program d.callee [] ins) ∧
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
          source' at' τ' = shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
            (.attempt retrySite.key k) source at' τ') ∧
        GExec M source' (protocolMeaning M d.admitted.program d.callee [] ins) (.returned out) ∧
        outP = hideAll M prover out.1 ∧ outV = hideAll M verifier out.1 := by
  have hProjP := projection M d.admitted.program d.callee prover [] ins
  have hProjV := projection M d.admitted.program d.callee verifier [] ins
  have hInsP : (hideAll M prover ins).All (RV.Valid M prover) := hideAll_valid M prover ins hIns
  have hInsV : (hideAll M verifier ins).All (RV.Valid M verifier) := hideAll_valid M verifier ins hIns
  have hKeep := deploy_keeps enc a declaration d hDep
  have hSafeP : (roleMeaning M d.admitted.program d.callee prover [] (hideAll M prover ins)).SafeWith
      M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) := by
    have hs := roleMeaning_safeWith_valid M (hKeep.1 ▸ hAdmit) d.callee prover [] (hideAll M prover ins) hInsP
    exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h) hs
  have hSafeV : (roleMeaning M d.admitted.program d.callee verifier [] (hideAll M verifier ins)).SafeWith
      M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) := by
    have hs := roleMeaning_safeWith_valid M (hKeep.1 ▸ hAdmit) d.callee verifier [] (hideAll M verifier ins) hInsV
    exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h) hs
  have hShapeP := roleMeaning_matchesShape M d.admitted.program d.callee prover [] (hideAll M prover ins)
  have hShapeV := roleMeaning_matchesShape M d.admitted.program d.callee verifier [] (hideAll M verifier ins)
  have hPShape := protocolMeaning_matchesShape M d.admitted.program d.callee [] ins
  have hUniq := protocolMeaning_uniqueOccs M d.admitted.program d.callee [] ins
  have hVNotMark := roleMeaning_notMarkAt_of_hasAttemptFor_false M d.admitted.program d.callee
    verifier (hideAll M verifier ins) retrySite hVNoAtt
  cases deploy_ok_elim enc a declaration d hDep with
  | interactive w _ => rw [w.hCon] at hDerived; cases hDerived
  | authored w _ => rw [w.hCon] at hDerived; cases hDerived
  | derived w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      have hRecNil : w.layout.recover = [] := hNoRec w.layout w.hLayOpt
      cases buildLayoutLayers_ok_elim w.hLay with
      | compact wL _ => have hne := wL.hNonEmpty; simp [hRecNil] at hne
      | streaming wL hLPW hLVW =>
          have hEntryF : ((a.program.findProtocol declaration.entry).get
              (by rw [w.hFound]; rfl)).1 = w.foundPair.1 := by simp [w.hFound]
          have hAbOut : w.toDeployed.entry.shape.abortsOutsideTarget retrySite [] false = [] := by
            have hSc := w.hScope
            unfold checkNonInteractiveScope at hSc
            rw [hRetry] at hSc
            simp only [Bool.and_eq_true, List.isEmpty_iff] at hSc
            simpa [DeployDerived.toDeployed, Deployed.entry, hEntryF] using hSc.2
          have hRWF := roleMeaning_retryWellFormed M a.program w.toDeployed.callee w.prover
            (hideAll M w.prover ins) retrySite hFnsNoAb hOnce hOwned hAbOut hExcl
          let conPL : Layer V a.program.headers w.prover w.foundPair.1.ins :=
            { line := .construction, state := w.stateTy, takes := [],
              gives := [], clauses := w.cPClauses, again := restoreAgain w.stateTy,
              start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP,
              finish := emptyFinish w.stateTy }
          let conVL : Layer V a.program.headers w.verifier w.foundPair.1.ins :=
            { line := .construction, state := w.stateTy, takes := [],
              gives := [], clauses := w.cVClauses, again := restoreAgain w.stateTy,
              start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtV,
              finish := emptyFinish w.stateTy }
          let layPL : Layer V a.program.headers w.prover w.foundPair.1.ins := wL.layP
          let layVL : Layer V a.program.headers w.verifier w.foundPair.1.ins := wL.layV
          have hStartEq : ∀ (ins' : HList (LVal M) w.foundPair.1.ins),
              ins'.All (fun a v => M.Valid a.ty v) →
              ∃ st0,
                conPL.start.denote (localSem M a.program.headers.fns
                  (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))) =
                  .done (.cons st0 .nil) ∧
                conVL.start.denote (localSem M a.program.headers.fns
                  (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.verifier (hideAll M w.verifier ins'))) =
                  .done (.cons st0 .nil) ∧
                M.Valid w.stateTy st0 := by
            intro ins' hIns'
            obtain ⟨st0, hDoneP, hSt0V⟩ := constructionStart_done M a
              w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP
              (heldValues M w.prover (hideAll M w.prover ins'))
              (heldValues_valid M w.prover _ (hideAll_valid M w.prover ins' hIns'))
            have hAgree := constructionStart_agree M a w.suite w.prover w.verifier
              w.foundPair.1.ins declaration.key w.sessBytes w.hSessBytes w.startRef w.absorbRef
              w.stmtP w.stmtV w.hSP w.hSV ins'
            exact ⟨st0, hDoneP, hAgree.symm.trans hDoneP, hSt0V⟩
          have hInsF := ins_cast_valid M hEntryF ins hIns
          obtain ⟨st0, hSt0P, hSt0V, hSt0Valid⟩ :=
            hStartEq (cast (congrArg (fun hdr => HList (LVal M) hdr.ins) hEntryF) ins) hInsF
          let conP' : Layer V a.program.headers w.prover _ := hEntryF ▸ conPL
          let conV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ conVL
          let layP' : Layer V a.program.headers w.prover _ := hEntryF ▸ layPL
          let layV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ layVL
          have hCPSt : conP'.state = w.stateTy := layer_cast_state hEntryF conPL
          have hCVSt : conV'.state = w.stateTy := layer_cast_state hEntryF conVL
          have hLPSt : layP'.state = .seq wL.unitTy none := layer_cast_state hEntryF layPL
          have hLVSt : layV'.state = streamStateTy wL.unitTy := layer_cast_state hEntryF layVL
          have hCPA : conP'.again = restoreAgain conP'.state := by
            have hG : ∀ {hdr₁ hdr₂ : ProtocolHeader V} (hE : hdr₁ = hdr₂)
                (l : Layer V a.program.headers w.prover hdr₂.ins),
                l.again = restoreAgain l.state → (hE ▸ l).again = restoreAgain (hE ▸ l).state := by
              intro _ _ hE _ h; subst hE; exact h
            exact hG hEntryF conPL rfl
          have hLPA : layP'.again = restoreAgain layP'.state := by
            have hG : ∀ {hdr₁ hdr₂ : ProtocolHeader V} (hE : hdr₁ = hdr₂)
                (l : Layer V a.program.headers w.prover hdr₂.ins),
                l.again = restoreAgain l.state → (hE ▸ l).again = restoreAgain (hE ▸ l).state := by
              intro _ _ hE _ h; subst hE; exact h
            exact hG hEntryF layPL rfl
          have hCC' : buildConstructionClauses.go enc a w.suite w.stateTy w.suiteUnitTy
              w.absorbRef w.prover w.verifier declaration.key
              (w.toDeployed.entry.shape.events [] id) 0
              (w.toDeployed.entry.shape.eventsWithAbsorb w.prover w.verifier [] id false) =
              .ok (hCPSt ▸ conP'.clauses, hCVSt ▸ conV'.clauses) := by
            rw [layer_cast_clauses hEntryF conPL, layer_cast_clauses hEntryF conVL]
            simpa [DeployDerived.toDeployed, DeployDerived.prover, DeployDerived.verifier,
              buildConstructionClauses, Deployed.entry, hEntryF] using w.hCC
          have hSL' : buildStreamingLayoutClauses.go a w.layout wL.unitTy
              wL.hfree w.prover w.verifier declaration.key
              (w.toDeployed.entry.shape.events [] id) 0
              (w.toDeployed.entry.shape.events [] id) =
              .ok (hLPSt ▸ layP'.clauses, hLVSt ▸ layV'.clauses) := by
            rw [layer_cast_clauses hEntryF layPL, layer_cast_clauses hEntryF layVL]
            simpa [DeployDerived.toDeployed, DeployDerived.prover, DeployDerived.verifier,
              DeployDerived.layout, buildStreamingLayoutClauses, Deployed.entry, hEntryF] using wL.hStr
          obtain ⟨out, outP, outV, finalSt, suffix, recP, source', hSufV, hAlP, hAlV,
            hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
            simulate_retry_coupled_before M w.hNe (d := w.toDeployed)
              conP' conV' layP' layV' hCPSt hCVSt hLPSt hLVSt hCPA hLPA
              w.hCon w.hLayOpt hSuiteLaw hLayLaw hCC' hSL' bound retrySite k hKLt hExcl
              (protocolMeaning M a.program _ [] ins)
              (roleMeaning M a.program _ w.prover [] (hideAll M w.prover ins))
              (roleMeaning M a.program _ w.verifier [] (hideAll M w.verifier ins))
              st0 [] source hSt0Valid (fun _ h => nomatch h)
              hProjP hProjV hSafeP hSafeV hShapeP hShapeV hRWF hIdxFree
              hPShape hUniq hLPAb hFedAb hAborts hLPK hFedK hNoHaltK
          obtain ⟨recV, hAlV0⟩ := hAlV [] (fun _ h => nomatch h)
          simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hAlP hAlV0
          -- Transport verifier from `retryOf M none` to `retryOf M (some (bound, retrySite))` via obliviousness!
          have hAlVRetry : Alone M source w.verifier
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conV', layV']).run
                (retryOf M (some (bound, retrySite)))
                (roleMeaning M a.program w.toDeployed.callee w.verifier [] (hideAll M w.verifier ins))
                (.cons (hCVSt.symm ▸ st0) (.cons (hLVSt.symm ▸ (suffix, ((0 : Nat), ()))) .nil)))
              recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt)
                (.cons (hLVSt.symm ▸ (suffix, (suffix.length, ()))) .nil))) :=
            alone_eq_proc M (handler_run_retry_eq_none M _ bound retrySite _ hVNotMark) hAlV0
          have hFinish : ∀ (hdr : ProtocolHeader V) (hE : hdr = w.foundPair.1)
              (callee : Member a.program.headers.protocols hdr)
              (ins' : HList (LVal M) hdr.ins)
              (hStartP' : conPL.start.denote (localSem M a.program.headers.fns
                (Defs.fnTable M a.program.defs)) []
                (Env.positional (heldValues M w.prover (hideAll M w.prover (cast (congrArg (fun h => HList (LVal M) h.ins) hE) ins')))) =
                .done (.cons st0 .nil))
              (hStartV' : conVL.start.denote (localSem M a.program.headers.fns
                (Defs.fnTable M a.program.defs)) []
                (Env.positional (heldValues M w.verifier (hideAll M w.verifier (cast (congrArg (fun h => HList (LVal M) h.ins) hE) ins')))) =
                .done (.cons st0 .nil))
              (first' : Stack.Takes (hE ▸ [conPL, layPL]) = [])
              (matched' : Stack.Gives (hE ▸ [conPL, layPL]) = Stack.Takes (hE ▸ [conVL, layVL]))
              (outP' : HList (RV M w.prover) hdr.outs)
              (outV' : HList (RV M w.verifier) hdr.outs)
              (recP' recV' : List (Happened M)),
              Alone M source w.prover
                ((Stack.handler M (Defs.fnTable M a.program.defs)
                  (Defs.rTable M a.program.defs) (hE ▸ [conPL, layPL])).run
                  (retryOf M (some (bound, retrySite)))
                  (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                  (cast (by subst hE; rfl)
                    (HList.cons st0 (HList.cons ([] : List (M.Val wL.unitTy)) HList.nil))))
                recP' (.returned (outP', cast (by subst hE; rfl)
                  (HList.cons finalSt (HList.cons suffix HList.nil)))) →
              Alone M source w.verifier
                ((Stack.handler M (Defs.fnTable M a.program.defs)
                  (Defs.rTable M a.program.defs) (hE ▸ [conVL, layVL])).run
                  (retryOf M (some (bound, retrySite)))
                  (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                  (cast (by subst hE; rfl)
                    (HList.cons st0 (HList.cons (suffix, ((0 : Nat), ())) HList.nil))))
                recV' (.returned (outV', cast (by subst hE; rfl)
                  (HList.cons finalSt (HList.cons (suffix, (suffix.length, ())) HList.nil)))) →
              ∃ gives givesV,
                Alone M source w.prover
                  (runStack a M callee (some (bound, retrySite)) w.prover (hE ▸ [conPL, layPL])
                    (hideAll M w.prover ins') (cast (congrArg (HList M.Val) first'.symm) .nil))
                  recP' (.returned (outP', gives)) ∧
                Alone M source w.verifier
                  (runStack a M callee (some (bound, retrySite)) w.verifier (hE ▸ [conVL, layVL])
                    (hideAll M w.verifier ins') (cast (congrArg (HList M.Val) matched') gives))
                  recV' (.returned (outV', givesV)) := by
            intro hdr hE callee ins' hSP' hSV' first' matched' outP' outV' recP' recV' hAP hAV
            subst hE
            dsimp only at hSP' hSV'
            simp only [cast_eq] at hSP' hSV'
            change Alone M source w.prover
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conPL, layPL]).run
                (retryOf M (some (bound, retrySite)))
                (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                (.cons st0 (.cons ([] : List (M.Val wL.unitTy)) .nil)))
              recP' (.returned (outP', .cons finalSt (.cons suffix .nil))) at hAP
            change Alone M source w.verifier
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conVL, layVL]).run
                (retryOf M (some (bound, retrySite)))
                (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                (.cons st0 (.cons (suffix, ((0 : Nat), ())) .nil)))
              recV' (.returned (outV', .cons finalSt (.cons (suffix, (suffix.length, ())) .nil))) at hAV
            refine ⟨.cons suffix .nil, .nil, ?_, ?_⟩
            · unfold runStack
              change Alone M source w.prover
                ((Stack.start M (Defs.fnTable M a.program.defs) [conPL, layPL]
                  (hideAll M w.prover ins') .nil).bind _) _ _
              have hStP : Stack.start M (Defs.fnTable M a.program.defs)
                  [conPL, layPL] (hideAll M w.prover ins') .nil =
                  .done (.cons st0 (.cons ([] : List (M.Val wL.unitTy)) .nil)) := by
                change ((liftLocal id (conPL.start.denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))))).bind fun f₁ =>
                    ((liftLocal id ((layoutPStart wL.unitTy).denote
                      (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                      (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))))).bind fun f₂ =>
                        (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map fun others =>
                          HList.cons f₁.single others) = _
                rw [hSP', liftLocal_done]
                dsimp only [Process.bind, HList.single]
                rw [layoutPStart_denote]; rfl
              rw [hStP]; dsimp only [Process.bind]
              have hAP' := alone_mapHalt M (g := Prod.fst) hAP
              rw [← List.append_nil recP']
              refine alone_bind M hAP' ?_
              have hFinP : Stack.finish M (Defs.fnTable M a.program.defs)
                  [conPL, layPL] (.cons finalSt (.cons suffix .nil)) =
                  .done (.cons suffix .nil) := by
                rw [stack_finish_two]; dsimp only [conPL, layPL, BuildLayoutStreaming.layP]
                rw [emptyFinish_denote]
                dsimp only [liftLocal_done, Process.bind]
                rw [identityFinish_denote]; rfl
              rw [hFinP]; exact .done
            · unfold runStack
              change Alone M source w.verifier
                ((Stack.start M (Defs.fnTable M a.program.defs) [conVL, layVL]
                  (hideAll M w.verifier ins') (.cons suffix .nil)).bind _) _ _
              have hStV : Stack.start M (Defs.fnTable M a.program.defs)
                  [conVL, layVL] (hideAll M w.verifier ins') (.cons suffix .nil) =
                  .done (.cons st0 (.cons (suffix, ((0 : Nat), ())) .nil)) := by
                change ((liftLocal id (conVL.start.denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.verifier (hideAll M w.verifier ins'))))).bind fun f₁ =>
                    ((liftLocal id ((layoutVStart wL.unitTy).denote
                      (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                      (Env.positional (.cons suffix (heldValues M w.verifier (hideAll M w.verifier ins')))))).bind fun f₂ =>
                        (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map fun others =>
                          HList.cons f₁.single others) = _
                rw [hSV', liftLocal_done]
                dsimp only [Process.bind, HList.single]
                rw [layoutVStart_denote]; rfl
              rw [hStV]; dsimp only [Process.bind]
              have hAV' := alone_mapHalt M (g := Prod.fst) hAV
              rw [← List.append_nil recV']
              refine alone_bind M hAV' ?_
              have hFinV : Stack.finish M (Defs.fnTable M a.program.defs)
                  [conVL, layVL] (.cons finalSt (.cons (suffix, (suffix.length, ())) .nil)) =
                  .done .nil := by
                rw [stack_finish_two]; dsimp only [conVL, layVL, BuildLayoutStreaming.layV]
                rw [emptyFinish_denote]
                dsimp only [liftLocal_done, Process.bind]
                rw [layoutVFinish_denote]
                simp only [Nat.beq_refl, Bool.cond_true]; rfl
              rw [hFinV]; exact .done
          have hNoSampLayer : w.prep.sampLayer = none := by
            have h := w.prep.hSamp
            unfold buildSamplesLayer at h
            rw [hNoSamp] at h
            exact (Except.ok.inj h).symm
          have hStackPEq : w.toDeployed.stack w.prover = hEntryF ▸ [conPL, layPL] := by
            dsimp only [DeployDerived.toDeployed]
            rw [dite_eq_left rfl, hNoSampLayer, hLPW]
            dsimp only
            exact (eqRec_hdr_eq_ins hEntryF _).symm
          have hStackVEq : w.toDeployed.stack w.verifier = hEntryF ▸ [conVL, layVL] := by
            dsimp only [DeployDerived.toDeployed]
            rw [dite_eq_right (Ne.symm w.hNe), dite_eq_left rfl, hLVW]
            exact (eqRec_hdr_eq_ins hEntryF _).symm
          have hFirst' : Stack.Takes (hEntryF ▸ [conPL, layPL]) = [] := by
            rw [← hStackPEq]; exact first
          have hMatched' : Stack.Gives (hEntryF ▸ [conPL, layPL]) = Stack.Takes (hEntryF ▸ [conVL, layVL]) := by
            rw [← hStackPEq, ← hStackVEq]; exact matched
          obtain ⟨gives, givesV, hRunP, hRunV⟩ :=
            hFinish _ hEntryF _ ins hSt0P hSt0V hFirst' hMatched'
              outP outV recP recV
              (alone_cast_stack2_retry M hEntryF conPL layPL rfl rfl (some (bound, retrySite)) hAlP)
              (alone_cast_stack2_retry M hEntryF conVL layVL rfl rfl (some (bound, retrySite)) hAlVRetry)
          refine ⟨outP, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackPEq.symm) gives,
            recP, outV, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackVEq.symm) givesV, recV,
            ?_, ?_, source', out, hLSrc', hAgSrc', hGEx', hPostP, hPostV⟩
          · exact alone_deployed_run_congr_retry M (d := w.toDeployed) rfl hRetry hStackPEq
              ((cast_heq _ _).trans (cast_heq _ _).symm) (cast_heq _ _) hRunP
          · exact alone_deployed_run_congr_retry M (d := w.toDeployed) rfl hRetry hStackVEq
              ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
              (cast_heq _ _) hRunV

/-- Zero-abort corollary of `deploy_complete_retry` (`k = 0`): requires neither abort hypotheses
nor `AttemptIndexFree`, since attempt `0` succeeds on the very first try. -/
theorem deploy_complete_retry_nonaborting (enc : VocabEncoder V) {named : NamedProgram V}
    {assoc : Association} {a : Admitted V} (hAdmit : admit named assoc = .ok a)
    (declaration : Declaration) (d : Deployed V)
    (hDep : deploy enc a declaration = .ok d)
    {suite : ModuleRef} {sessionTag : Option (List Nat)}
    (hDerived : declaration.construction = .derived suite sessionTag)
    {bound : Nat} {retrySite : Site}
    (hRetry : declaration.retry = some (bound, retrySite))
    (hNoSamp : declaration.samples = none)
    (hNoRec : ∀ lay, declaration.layout = some lay → lay.recover = [])
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M)
    {prover verifier : Role} (hRoles : d.roles = some (prover, verifier))
    (first : Stack.Takes (d.stack prover) = [])
    (matched : Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier))
    (ins : HList (LVal M) d.entry.ins) (hIns : ins.All (fun a v => M.Valid a.ty v))
    (source : Source M)
    (hFnsNoAb : Defs.fnsNoAbort d.admitted.program.defs = true)
    (hOnce : d.entry.shape.retryAtMostOnce retrySite [] = true)
    (hOwned : d.entry.shape.retryOwnedBy prover retrySite [] = true)
    (hExcl : d.entry.shape.attemptCoinsExclusive prover retrySite = true)
    (hVNoAtt : d.entry.shape.hasAttemptFor verifier retrySite [] = false)
    (hLP : LawfulPrivate M (shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
        (.attempt retrySite.key 0) source)
      (protocolMeaning M d.admitted.program d.callee [] ins))
    (hFed : Fed M (shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
        (.attempt retrySite.key 0) source)
      (protocolMeaning M d.admitted.program d.callee [] ins))
    (hNoHalt : ∀ source₁, Lawful M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) →
      (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
        source₁ at' τ' = shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
          (.attempt retrySite.key 0) source at' τ') →
      ∀ e, GExec M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) e →
      ∃ out, e = .returned out) :
    ∃ outP gives recordP outV givesV recordV,
      Alone M source prover
        (d.run M prover (hideAll M prover ins) (cast (congrArg (HList M.Val) first.symm) .nil))
        recordP (.returned (outP, gives)) ∧
      Alone M source verifier
        (d.run M verifier (hideAll M verifier ins) (cast (congrArg (HList M.Val) matched) gives))
        recordV (.returned (outV, givesV)) ∧
      ∃ source' out,
        Lawful M source' (protocolMeaning M d.admitted.program d.callee [] ins) ∧
        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
          source' at' τ' = shiftAttemptSource M (d.entry.shape.attemptPrivateCoins prover retrySite [] false)
            (.attempt retrySite.key 0) source at' τ') ∧
        GExec M source' (protocolMeaning M d.admitted.program d.callee [] ins) (.returned out) ∧
        outP = hideAll M prover out.1 ∧ outV = hideAll M verifier out.1 := by
  have hBoundPos : 0 < bound := by
    cases deploy_ok_elim enc a declaration d hDep with
    | interactive w _ => rw [w.hCon] at hDerived; cases hDerived
    | authored w _ => rw [w.hCon] at hDerived; cases hDerived
    | derived w _ =>
        have hSc := w.hScope
        unfold checkNonInteractiveScope at hSc
        rw [hRetry] at hSc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hSc
        exact hSc.1.1.1
  exact deploy_complete_retry M enc hAdmit declaration d hDep hDerived hRetry hNoSamp hNoRec
    hSuiteLaw hLayLaw hRoles first matched ins hIns source 0 hBoundPos
    hFnsNoAb hOnce hOwned hExcl hVNoAtt
    (fun j hj => by
      have hZ : j = 0 := Nat.eq_zero_of_le_zero hj
      subst hZ; exact Program.attemptIndexFree_zero M retrySite _)
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    hLP hFed hNoHalt

end RetrySimulation

end Zkc.Core
