module

public import Zkc.Core.Admission.Theorems
public import Zkc.Core.World.Stack
public import Zkc.Core.Projection.Theorem

@[expose] public section

/-!
Generic role-process and handler safety lemmas: `ValidReply`, `ROp.ValidPayload`,
`Process.SafeWith`, `Handler.SafeWith` composition, and `rolesSafe_validReply`.
-/

namespace Zkc.Core

/-! ## `ValidReply`, `ROp.ValidPayload`, `Process.SafeWith`, and `Handler.SafeWith` -/

section
variable {V : Vocabulary} (M : Model V)

/-- A reply to a role effect is valid in model `M` (requiring only `M.Valid`, without coin-law
support). -/
def ValidReply : (op : ROp M) → (RSig M).Reply op → Prop
  | .give .., _ => True
  | .get _ _ _ τ, v => M.Valid τ v
  | .own _ _ _ _ _ τ, v => M.Valid τ v
  | .hear _ _ _ τ, v => M.Valid τ v
  | .begin _, _ => True
  | .settle _, _ => True

theorem permitted_implies_validReply (op : ROp M) (reply : (RSig M).Reply op)
    (h : Permitted M op reply) : ValidReply M op reply := by
  cases op with
  | give => trivial
  | get => exact h
  | own kind =>
      cases kind with
      | coin => exact h.1
      | request => exact h
  | hear => exact h
  | «begin» => trivial
  | settle => trivial

/-- Outgoing values carried by a role effect are valid in model `M`. -/
def ROp.ValidPayload : ROp M → Prop
  | .give _ _ _ τ x => M.Valid τ x
  | .own _ _ _ _ payload _ => payload.All M.Valid
  | _ => True

/-- Every effect emitted by a role process satisfies `opOk`, on every `permitted` reply returns
values satisfy `onDone`, and stops satisfy `onHalt`. -/
def Process.SafeWith {H A : Type} (permitted : ∀ op, (RSig M).Reply op → Prop)
    (opOk : ROp M → Prop) (onDone : A → Prop) (onHalt : H → Prop) :
    Process (RSig M) H A → Prop
  | .done a => onDone a
  | .halt why => onHalt why
  | .call op k =>
      opOk op ∧ ∀ reply, permitted op reply →
        Process.SafeWith permitted opOk onDone onHalt (k reply)

theorem Process.safeWith_every {H A : Type} {permitted : ∀ op, (RSig M).Reply op → Prop}
    {opOk : ROp M → Prop} {onDone : A → Prop} {onHalt : H → Prop} :
    ∀ {p : Process (RSig M) H A},
      p.SafeWith M permitted opOk onDone onHalt → p.Every permitted onDone onHalt
  | .done _, h => h
  | .halt _, h => h
  | .call _ _, ⟨_, hk⟩ => fun reply hr => Process.safeWith_every (hk reply hr)

theorem Process.safeWith_mono {H A : Type}
    {perm₁ perm₂ : ∀ op, (RSig M).Reply op → Prop}
    {opOk₁ opOk₂ : ROp M → Prop} {P₁ P₂ : A → Prop} {R₁ R₂ : H → Prop}
    (hperm : ∀ op r, perm₂ op r → perm₁ op r)
    (hop : ∀ op, opOk₁ op → opOk₂ op)
    (hdone : ∀ a, P₁ a → P₂ a) (hhalt : ∀ h, R₁ h → R₂ h) :
    ∀ {p : Process (RSig M) H A},
      p.SafeWith M perm₁ opOk₁ P₁ R₁ → p.SafeWith M perm₂ opOk₂ P₂ R₂
  | .done a, h => hdone a h
  | .halt why, h => hhalt why h
  | .call op _, ⟨ho, hk⟩ =>
      ⟨hop op ho, fun reply hr =>
        Process.safeWith_mono hperm hop hdone hhalt (hk reply (hperm op reply hr))⟩

theorem Process.safeWith_and {H A : Type} {permitted : ∀ op, (RSig M).Reply op → Prop}
    {opOk₁ opOk₂ : ROp M → Prop} {P₁ P₂ : A → Prop} {R₁ R₂ : H → Prop} :
    ∀ {p : Process (RSig M) H A},
      p.SafeWith M permitted opOk₁ P₁ R₁ → p.SafeWith M permitted opOk₂ P₂ R₂ →
      p.SafeWith M permitted (fun op => opOk₁ op ∧ opOk₂ op) (fun a => P₁ a ∧ P₂ a)
        (fun h => R₁ h ∧ R₂ h)
  | .done _, h1, h2 => ⟨h1, h2⟩
  | .halt _, h1, h2 => ⟨h1, h2⟩
  | .call _ _, ⟨ho1, hk1⟩, ⟨ho2, hk2⟩ =>
      ⟨⟨ho1, ho2⟩, fun reply hr => Process.safeWith_and (hk1 reply hr) (hk2 reply hr)⟩

theorem Process.safeWith_of_every {H A : Type} {permitted : ∀ op, (RSig M).Reply op → Prop}
    {P : A → Prop} {R : H → Prop} :
    ∀ {p : Process (RSig M) H A},
      p.Every permitted P R → p.SafeWith M permitted (fun _ => True) P R
  | .done _, h => h
  | .halt _, h => h
  | .call _ _, hk => ⟨trivial, fun reply hr => Process.safeWith_of_every (hk reply hr)⟩

theorem Process.safeWith_bind {H A B : Type} {permitted : ∀ op, (RSig M).Reply op → Prop}
    {opOk : ROp M → Prop} {onDone : B → Prop} {onHalt : H → Prop}
    (p : Process (RSig M) H A) (f : A → Process (RSig M) H B) :
    (p.bind f).SafeWith M permitted opOk onDone onHalt ↔
      p.SafeWith M permitted opOk (fun a => (f a).SafeWith M permitted opOk onDone onHalt) onHalt := by
  induction p with
  | done a => exact Iff.rfl
  | halt why => exact Iff.rfl
  | call op k ih =>
      simp only [Process.bind, Process.SafeWith]
      exact and_congr_right fun _ => forall_congr' fun reply => imp_congr_right fun _ => ih reply

theorem Process.safeWith_map {H A B : Type} {permitted : ∀ op, (RSig M).Reply op → Prop}
    {opOk : ROp M → Prop} {onDone : B → Prop} {onHalt : H → Prop}
    (f : A → B) (p : Process (RSig M) H A) :
    (p.map f).SafeWith M permitted opOk onDone onHalt ↔
      p.SafeWith M permitted opOk (fun a => onDone (f a)) onHalt := by
  rw [Process.map_eq_bind, Process.safeWith_bind]
  exact Iff.rfl

theorem Process.safeWith_mapHalt {H H' A : Type} {permitted : ∀ op, (RSig M).Reply op → Prop}
    {opOk : ROp M → Prop} {onDone : A → Prop} {onHalt : H' → Prop}
    (f : H → H') : ∀ (p : Process (RSig M) H A),
    (p.mapHalt f).SafeWith M permitted opOk onDone onHalt ↔
      p.SafeWith M permitted opOk onDone (fun h => onHalt (f h))
  | .done _ => Iff.rfl
  | .halt _ => Iff.rfl
  | .call _ k => by
      simp only [Process.mapHalt, Process.SafeWith]
      exact and_congr_right fun _ => forall_congr' fun reply =>
        imp_congr_right fun _ => Process.safeWith_mapHalt f (k reply)

theorem Process.safeWith_recover {H H' A : Type} {permitted : ∀ op, (RSig M).Reply op → Prop}
    {opOk : ROp M → Prop} {onDone : A → Prop} {onHalt : H' → Prop}
    (p : Process (RSig M) H A) (f : H → Process (RSig M) H' A) :
    (p.recover f).SafeWith M permitted opOk onDone onHalt ↔
      p.SafeWith M permitted opOk onDone (fun h => (f h).SafeWith M permitted opOk onDone onHalt) := by
  induction p with
  | done _ => exact Iff.rfl
  | halt _ => exact Iff.rfl
  | call _ k ih =>
      simp only [Process.recover, Process.SafeWith]
      exact and_congr_right fun _ => forall_congr' fun reply => imp_congr_right fun _ => ih reply

theorem Process.safeWith_liftLocal {H A : Type} {permitted : ∀ op, (RSig M).Reply op → Prop}
    {opOk : ROp M → Prop} {onDone : A → Prop} {onHalt : H → Prop}
    (f : Stop → H) : ∀ (p : Local A),
    p.Every (fun _ _ => True) onDone (fun why => onHalt (f why)) →
    (liftLocal (S := RSig M) f p).SafeWith M permitted opOk onDone onHalt
  | .done _, h => h
  | .halt _, h => h
  | .call op _, _ => nomatch op

theorem Process.safeWith_markOwn {H A : Type} {permitted : ∀ op, (RSig M).Reply op → Prop}
    {opOk : ROp M → Prop} {onDone : A → Prop} {onHalt : H → Prop} (frame : Frame)
    (hperm : ∀ law at_ ins payload τ reply,
      permitted (.own (.coin law) [] ⟨frame :: at_.path, at_.key⟩ ins payload τ) reply →
      permitted (.own (.coin law) [] at_ ins payload τ) reply)
    (hop : ∀ law at_ ins payload τ,
      opOk (.own (.coin law) [] at_ ins payload τ) →
      opOk (.own (.coin law) [] ⟨frame :: at_.path, at_.key⟩ ins payload τ)) :
    ∀ {p : Process (RSig M) H A},
      p.SafeWith M permitted opOk onDone onHalt →
      (Process.markOwn M frame p).SafeWith M permitted opOk onDone onHalt
  | .done _, h => h
  | .halt _, h => h
  | .call (.own (.coin law) [] at_ ins payload τ) _, ⟨ho, hk⟩ =>
      ⟨hop law at_ ins payload τ ho, fun reply hr =>
        Process.safeWith_markOwn frame hperm hop (hk reply (hperm law at_ ins payload τ reply hr))⟩
  | .call (.own (.coin _) (_ :: _) _ _ _ _) _, ⟨ho, hk⟩ =>
      ⟨ho, fun reply hr => Process.safeWith_markOwn frame hperm hop (hk reply hr)⟩
  | .call (.own (.request _) _ _ _ _ _) _, ⟨ho, hk⟩ =>
      ⟨ho, fun reply hr => Process.safeWith_markOwn frame hperm hop (hk reply hr)⟩
  | .call (.give ..) _, ⟨ho, hk⟩ =>
      ⟨ho, fun reply hr => Process.safeWith_markOwn frame hperm hop (hk reply hr)⟩
  | .call (.get ..) _, ⟨ho, hk⟩ =>
      ⟨ho, fun reply hr => Process.safeWith_markOwn frame hperm hop (hk reply hr)⟩
  | .call (.hear ..) _, ⟨ho, hk⟩ =>
      ⟨ho, fun reply hr => Process.safeWith_markOwn frame hperm hop (hk reply hr)⟩
  | .call (.begin ..) _, ⟨ho, hk⟩ =>
      ⟨ho, fun reply hr => Process.safeWith_markOwn frame hperm hop (hk reply hr)⟩
  | .call (.settle ..) _, ⟨ho, hk⟩ =>
      ⟨ho, fun reply hr => Process.safeWith_markOwn frame hperm hop (hk reply hr)⟩

/-- A `ClosedEffects` predicate is equivalent to `SafeWith` with unrestricted replies and the
closed-effect op predicate. -/
def ROp.IsClosed : ROp M → Prop
  | .own (.coin _) [] _ _ _ _ => True
  | .own (.request _) _ _ _ _ _ => True
  | .begin _ => True
  | .settle _ => True
  | _ => False

theorem Process.closedEffects_of_safeWith {H A : Type} {P : A → Prop} {R : H → Prop} :
    ∀ {p : Process (RSig M) H A},
      p.SafeWith M (fun _ _ => True) (ROp.IsClosed M) P R → Process.ClosedEffects p
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call op k, ⟨ho, hk⟩ => by
      refine ⟨?_, fun reply => Process.closedEffects_of_safeWith (hk reply trivial)⟩
      cases op with
      | own kind hearers =>
          cases kind with
          | coin _ => cases hearers <;> exact ho
          | request _ => exact ho
      | «begin» | settle => exact ho
      | give | get | hear => exact ho

/-! ## Handler safety composition (`Handler.SafeWith`) -/

/-- A handler preserves state invariant `Inv`, transforms incoming `opOk₁` effects into outgoing
`opOk₂` effects, never halts `.undefined`, and returns permitted replies. -/
structure Handler.SafeWith {σ : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (permitted : ∀ op, (RSig M).Reply op → Prop)
    (Inv : σ → Prop) (opOk₁ opOk₂ : ROp M → Prop) : Prop where
  clauseOk : ∀ op s, opOk₁ op → Inv s →
    (h.clause op s).SafeWith M permitted opOk₂
      (fun out => permitted op out.1 ∧ Inv out.2)
      (fun stop => stop.1 ≠ .undefined ∧ Inv stop.2)
  againOk : ∀ i entry stop, Inv entry → Inv stop →
    match h.again i entry stop with
    | .ok next => Inv next
    | .error why => why ≠ .undefined

theorem Handler.answer_safeWith {τ X E : Type} {h : Handler (RSig M) (RSig M) Stop τ}
    {permitted : ∀ op, (RSig M).Reply op → Prop}
    {InvT : τ → Prop} {InvE : E → Prop} {opOk₁ opOk₂ : ROp M → Prop} {onDone : X → Prop}
    (hsafe : h.SafeWith M permitted InvT opOk₁ opOk₂) :
    ∀ {p : Process (RSig M) (Stop × E) X} {upper : E} {t : τ},
      p.SafeWith M permitted opOk₁ onDone (fun stop => stop.1 ≠ .undefined ∧ InvE stop.2) →
      InvE upper → InvT t →
      (h.answer p upper t).SafeWith M permitted opOk₂
        (fun out => onDone out.1 ∧ InvT out.2)
        (fun stop => stop.1 ≠ .undefined ∧ InvE stop.2.1 ∧ InvT stop.2.2)
  | .done _, _, _, hp, _, ht => ⟨hp, ht⟩
  | .halt _, _, _, hp, _, ht => ⟨hp.1, hp.2, ht⟩
  | .call op k, upper, t, ⟨ho, hk⟩, hu, ht => by
      simp only [Handler.answer]
      rw [Process.safeWith_bind, Process.safeWith_mapHalt]
      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun out hout => Handler.answer_safeWith hsafe (hk out.1 hout.1) hu hout.2)
        (fun stop hstop => ⟨hstop.1, hu, hstop.2⟩)
        (hsafe.clauseOk op t ho ht)

theorem Handler.SafeWith.over {σ τ : Type}
    {inner : Handler (RSig M) (RSig M) Stop σ}
    {outer : Handler (RSig M) (RSig M) Stop τ}
    {permitted : ∀ op, (RSig M).Reply op → Prop}
    {InvS : σ → Prop} {InvT : τ → Prop} {opOk₁ opOk₂ opOk₃ : ROp M → Prop}
    (hIn : inner.SafeWith M permitted InvS opOk₁ opOk₂)
    (hOut : outer.SafeWith M permitted InvT opOk₂ opOk₃) :
    (inner.over outer).SafeWith M permitted (fun st => InvS st.1 ∧ InvT st.2) opOk₁ opOk₃ where
  clauseOk op st ho hst := by
    simp only [Handler.over]
    rw [Process.safeWith_bind, Process.safeWith_mapHalt]
    exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
      (fun out hout => ⟨hout.1.1, hout.1.2, hout.2⟩)
      (fun stop hstop => ⟨hstop.1, hstop.2.1, hstop.2.2⟩)
      (Handler.answer_safeWith M hOut (hIn.clauseOk op st.1 ho hst.1) hst.1 hst.2)
  againOk i entry stop hentry hstop := by
    simp only [Handler.over]
    have h1 := hIn.againOk i entry.1 stop.1 hentry.1 hstop.1
    have h2 := hOut.againOk i entry.2 stop.2 hentry.2 hstop.2
    cases hInA : inner.again i entry.1 stop.1 with
    | error why =>
        rw [hInA] at h1; exact h1
    | ok mine =>
        rw [hInA] at h1
        cases hOutA : outer.again i entry.2 stop.2 with
        | error why =>
            rw [hOutA] at h2; exact h2
        | ok below =>
            rw [hOutA] at h2
            exact ⟨h1, h2⟩

theorem attempts_safeWith {σ A : Type} {permitted : ∀ op, (RSig M).Reply op → Prop}
    {opOk : ROp M → Prop} {Inv : σ → Prop} {onDone : A → Prop}
    (retriable : Stop → Bool) (exhausted : Stop) (hexh : exhausted ≠ .undefined)
    (again : Nat → σ → σ → Except Stop σ)
    (hagain : ∀ i e s, Inv e → Inv s → match again i e s with
      | .ok next => Inv next | .error why => why ≠ .undefined)
    (body : Nat → σ → Process (RSig M) ((Bool × Stop) × σ) (A × σ))
    (hbody : ∀ i s, Inv s → (body i s).SafeWith M permitted opOk
      (fun out => onDone out.1 ∧ Inv out.2) (fun stop => stop.1.2 ≠ .undefined ∧ Inv stop.2))
    (entry : σ) (hentry : Inv entry) :
    ∀ (n i : Nat) (s : σ), Inv s →
      (attempts retriable exhausted again body entry n i s).SafeWith M permitted opOk
        (fun out => onDone out.1 ∧ Inv out.2) (fun stop => stop.1 ≠ .undefined ∧ Inv stop.2)
  | 0, _, _, hs => ⟨hexh, hs⟩
  | n + 1, i, s, hs => by
      simp only [attempts]
      rw [Process.safeWith_recover]
      refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun _ h => h) (fun stop hstop => ?_) (hbody i s hs)
      by_cases hret : (stop.1.1 && retriable stop.1.2) = true
      · simp only [hret, ↓reduceIte]
        cases n with
        | zero => exact ⟨hexh, hstop.2⟩
        | succ m =>
            have ha := hagain (i + 1) entry stop.2 hentry hstop.2
            cases hnext : again (i + 1) entry stop.2 with
            | error why =>
                rw [hnext] at ha
                exact ⟨ha, hstop.2⟩
            | ok next =>
                rw [hnext] at ha
                exact attempts_safeWith retriable exhausted hexh again hagain body hbody
                  entry hentry (m + 1) (i + 1) next ha
      · simp only [hret, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hstop.1, hstop.2⟩

theorem Handler.SafeWith.run_and_inside {σ A : Type}
    {h : Handler (RSig M) (RSig M) Stop σ}
    {permitted : ∀ op, (RSig M).Reply op → Prop}
    {Inv : σ → Prop} {opOk₁ opOk₂ : ROp M → Prop} {onDone : A → Prop}
    (hsafe : h.SafeWith M permitted Inv opOk₁ opOk₂)
    (retry : Option (Nat × Site))
    (hpermMark : ∀ frame law at_ ins payload τ reply,
      permitted (.own (.coin law) [] ⟨frame :: at_.path, at_.key⟩ ins payload τ) reply →
      permitted (.own (.coin law) [] at_ ins payload τ) reply)
    (hopMark : ∀ frame law at_ ins payload τ,
      opOk₂ (.own (.coin law) [] at_ ins payload τ) →
      opOk₂ (.own (.coin law) [] ⟨frame :: at_.path, at_.key⟩ ins payload τ))
    (hpermBegin : ∀ at_ i, permitted (.begin at_) i)
    (hpermSettle : ∀ at_, permitted (.settle at_) ()) :
    ∀ (p : Process (RSig M) Stop A),
      p.SafeWith M permitted opOk₁ onDone (· ≠ .undefined) →
      (∀ s, Inv s → (h.run (retryOf M retry) p s).SafeWith M permitted opOk₂
        (fun out => onDone out.1 ∧ Inv out.2) (fun stop => stop.1 ≠ .undefined ∧ Inv stop.2)) ∧
      (∀ i s, Inv s → (h.inside (retryOf M retry) i p s).SafeWith M permitted opOk₂
        (fun out => onDone out.1 ∧ Inv out.2) (fun stop => stop.1.2 ≠ .undefined ∧ Inv stop.2))
  | .done a, hp => ⟨fun s hs => ⟨hp, hs⟩, fun _ s hs => ⟨hp, hs⟩⟩
  | .halt why, hp => ⟨fun s hs => ⟨hp, hs⟩, fun _ s hs => ⟨hp, hs⟩⟩
  | .call op k, ⟨ho, hk⟩ => by
      have ih : ∀ reply, permitted op reply →
          (∀ s, Inv s → (h.run (retryOf M retry) (k reply) s).SafeWith M permitted opOk₂
            (fun out => onDone out.1 ∧ Inv out.2) (fun stop => stop.1 ≠ .undefined ∧ Inv stop.2)) ∧
          (∀ i s, Inv s → (h.inside (retryOf M retry) i (k reply) s).SafeWith M permitted opOk₂
            (fun out => onDone out.1 ∧ Inv out.2) (fun stop => stop.1.2 ≠ .undefined ∧ Inv stop.2)) :=
        fun reply hr => Handler.SafeWith.run_and_inside hsafe retry hpermMark hopMark
          hpermBegin hpermSettle (k reply) (hk reply hr)
      constructor
      · intro s hs
        simp only [Handler.run]
        cases hbeg : (retryOf M retry).begins op with
        | none =>
            rw [Process.safeWith_bind]
            exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
              (fun out hout => (ih out.1 hout.1).1 out.2 hout.2)
              (fun _ h => h) (hsafe.clauseOk op s ho hs)
        | some pair =>
            obtain ⟨exhausted, number⟩ := pair
            have hexh : exhausted ≠ .undefined := by
              cases retry with
              | none => simp [retryOf] at hbeg
              | some rpair =>
                  cases op with
                  | «begin» at_ =>
                      simp only [retryOf] at hbeg
                      split at hbeg
                      · cases hbeg; intro h; cases h
                      · cases hbeg
                  | give | get | own | hear | settle => simp [retryOf] at hbeg
            have hnumPerm : ∀ i, permitted op (number i) := by
              intro i
              cases retry with
              | none => simp [retryOf] at hbeg
              | some rpair =>
                  cases op with
                  | «begin» at_ =>
                      simp only [retryOf] at hbeg
                      split at hbeg
                      · cases hbeg; exact hpermBegin at_ i
                      · cases hbeg
                  | give | get | own | hear | settle => simp [retryOf] at hbeg
            exact attempts_safeWith M _ exhausted hexh h.again hsafe.againOk
              (fun i s' => h.inside (retryOf M retry) i (k (number i)) s')
              (fun i s' hs' => (ih (number i) (hnumPerm i)).2 i s' hs') s hs _ 0 s hs
      · intro i s hs
        simp only [Handler.inside]
        cases hend : (retryOf M retry).ends op with
        | some reply =>
            have hrepPerm : permitted op reply := by
              cases retry with
              | none => simp [retryOf] at hend
              | some rpair =>
                  cases op with
                  | settle at_ =>
                      simp only [retryOf] at hend
                      split at hend
                      · cases hend; exact hpermSettle at_
                      · cases hend
                  | give | get | own | hear | «begin» => simp [retryOf] at hend
            rw [Process.safeWith_mapHalt]
            exact (ih reply hrepPerm).1 s hs
        | none =>
            rw [Process.safeWith_bind, Process.safeWith_mapHalt]
            have hcl : ((retryOf M retry).mark i (h.clause op s)).SafeWith M permitted opOk₂
                (fun out => permitted op out.1 ∧ Inv out.2)
                (fun stop => stop.1 ≠ .undefined ∧ Inv stop.2) := by
              cases retry with
              | none => exact hsafe.clauseOk op s ho hs
              | some rpair =>
                  exact Process.safeWith_markOwn M (.attempt rpair.2.key i)
                    (hpermMark _) (hopMark _) (hsafe.clauseOk op s ho hs)
            exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
              (fun out hout => (ih out.1 hout.1).2 i out.2 hout.2)
              (fun _ h => h) hcl

theorem Handler.SafeWith.run {σ A : Type}
    {h : Handler (RSig M) (RSig M) Stop σ}
    {permitted : ∀ op, (RSig M).Reply op → Prop}
    {Inv : σ → Prop} {opOk₁ opOk₂ : ROp M → Prop} {onDone : A → Prop}
    (hsafe : h.SafeWith M permitted Inv opOk₁ opOk₂)
    (retry : Option (Nat × Site))
    (hpermMark : ∀ frame law at_ ins payload τ reply,
      permitted (.own (.coin law) [] ⟨frame :: at_.path, at_.key⟩ ins payload τ) reply →
      permitted (.own (.coin law) [] at_ ins payload τ) reply)
    (hopMark : ∀ frame law at_ ins payload τ,
      opOk₂ (.own (.coin law) [] at_ ins payload τ) →
      opOk₂ (.own (.coin law) [] ⟨frame :: at_.path, at_.key⟩ ins payload τ))
    (hpermBegin : ∀ at_ i, permitted (.begin at_) i)
    (hpermSettle : ∀ at_, permitted (.settle at_) ())
    {p : Process (RSig M) Stop A} (hp : p.SafeWith M permitted opOk₁ onDone (· ≠ .undefined))
    {s : σ} (hs : Inv s) :
    (h.run (retryOf M retry) p s).SafeWith M permitted opOk₂
      (fun out => onDone out.1 ∧ Inv out.2) (fun stop => stop.1 ≠ .undefined ∧ Inv stop.2) :=
  (Handler.SafeWith.run_and_inside M hsafe retry hpermMark hopMark hpermBegin hpermSettle p hp).1 s hs

/-! ## `rolesSafe_validReply`: admitted role safety under `ValidReply M` -/

section ValidReplySafety
open BodyAnalysis BodyAnalysis.RoleContracts BodyAnalysis.HeaderContracts

private def RCalleesValid {headers : List (ProtocolHeader V)} (roles : RTable M headers) : Prop :=
  ∀ hdr (callee : Member headers hdr) (j : Role) (path : List Frame) (args : HList (RV M j) hdr.ins),
    args.All (RV.Valid M j) →
    (roles hdr callee j path args).Every (ValidReply M) (fun outs => outs.All (RV.Valid M j))
      (· ≠ .undefined)

private theorem every_mapR_validReply {B : Type} (ρ : Role → Role) {P : B → Prop} {R : Stop → Prop} :
    ∀ (p : Program M B),
      (mapR M ρ p).Every (ValidReply M) P R ↔ p.Every (ValidReply M) P R
  | .done _ => Iff.rfl
  | .halt _ => Iff.rfl
  | .call (.give ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR_validReply ρ (k u)
  | .call (.get ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR_validReply ρ (k u)
  | .call (.own ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR_validReply ρ (k u)
  | .call (.hear ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR_validReply ρ (k u)
  | .call (.begin ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR_validReply ρ (k u)
  | .call (.settle ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR_validReply ρ (k u)

private theorem application_safe_valid {hs : Headers V} (r : Role)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (rcallees : RCalleesValid M roles) {hdr : ProtocolHeader V}
    (callee : Member hs.protocols hdr) (peers : List Role) (distinct : peers.Nodup)
    (covers : peers.length = hdr.roles) (operands : List (LTy V))
    (fits : Fits operands (hdr.ins.map (LTy.map (RoleMap.ofList peers distinct).to)))
    (key : Key) (path : List Frame) (args : HList (RV M r) operands)
    (valid : args.All (RV.Valid M r)) :
    ((roleSem M r fns roles).op key (.apply callee peers distinct covers operands fits) path args).Every
      (ValidReply M) (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) := by
  let roleMap := RoleMap.ofList peers distinct
  change Process.Every (S := RSig M) (ValidReply M) _ _ ((mapR M roleMap.to
    (roles _ callee (roleMap.back r) (path ++ [.application key])
      (enterAll M roleMap r (fitAllRV M fits args)))).map (leaveAll M roleMap r))
  rw [Process.map_eq_bind, Process.every_bind, every_mapR_validReply]
  exact Process.every_mono _ _ (fun ys v => leaveAll_valid M roleMap r ys v) (fun _ h => h)
    (rcallees _ callee _ _ _ (enterAll_valid M roleMap r _ (fitAllRV_valid M fits args valid)))

private def validSetting {hs : Headers V} (catalog : FunctionContracts hs.fns) (r : Role)
    (definition : Key) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) :
    Setting (roleDialect V hs r) (RoleRaw V) where
  cfg := config catalog r definition []
  sem := roleSem M r fns roles
  notes := []
  permitted := ValidReply M
  R := roleReading M r
  Run := RoleReturns M r fns roles
  Valid := RoleValueValid M r
  undefined := (· = .undefined)
  domain := roleDomainLawful M r fns roles catalog.distinct
  F := []

private theorem rcallees_of_valid {headers : List (ProtocolHeader V)} {roles : RTable M headers}
    (h : RCalleesValid M roles) : RCallees M roles := by
  intro hdr callee j path args valid
  exact Process.safeWith_every M
    (Process.safeWith_mono M (permitted_implies_validReply M) (fun _ h => h) (fun _ h => h)
      (fun _ h => h) (Process.safeWith_of_every M (h hdr callee j path args valid)))

private theorem observedOperand_valid {hs : Headers V} (catalog : FunctionContracts hs.fns)
    (r : Role) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    {ins res} (op : RoleOp V hs r ins res) {i} (observed : (rules catalog r).observedOperand op = some i)
    {key path} {args : HList (RV M r) ins} {ys : HList (RV M r) res}
    (ran : (roleOp M r fns roles key op path args).CanReturn (ValidReply M) ys)
    {x y} (src : ((roleSem M r fns roles).dyns args)[i]? = some x)
    (dst : ((roleSem M r fns roles).dyns ys)[0]? = some y) :
    (roleReading M r).Agrees x y := by
  suffices eq : heldValue M r x = heldValue M r y by
    exact ⟨by simp [roleReading, eq], by simp [roleReading, eq], eq⟩
  cases op with
  | keep holders same =>
      by_cases here : r ∈ holders
      · have atZero : 0 = i := Option.some.inj (by simpa only [rules, here, ↓reduceIte] using observed)
        subst i
        obtain ⟨v, rfl⟩ := HList.one args
        cases ran
        cases src
        cases dst
        simp [heldValue, here, same.mpr here, reveal_carry]
      · simp [rules, here] at observed
  | give kind getters here =>
      cases observed
      obtain ⟨v, rfl⟩ := HList.one args
      cases ran with
      | call _ _ _ next =>
          cases next
          cases src
          cases dst
          have resultHere := Holders.mem_ofList.mpr (List.mem_append_right getters here)
          simp [heldValue, here, resultHere, reveal_hide]
  | _ => cases observed

private theorem effect_valid {hs : Headers V} (catalog : FunctionContracts hs.fns) (r : Role)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (callees : Callees M fns) (rcallees : RCalleesValid M roles)
    {ins outs} (op : RoleOp V hs r ins outs) (ordered : roleShared op = false)
    (key : Key) (path : List Frame) (args : HList (RV M r) ins)
    (valid : ∀ v ∈ (roleSem M r fns roles).dyns args, RoleValueValid M r v)
    (required : (rules catalog r).Required (roleSem M r fns roles) (roleReading M r)
      (RoleReturns M r fns roles) (RoleValueValid M r) op args) :
    let sem := roleSem M r fns roles
    (sem.op key op path args).Every (ValidReply M)
      (fun ys => (∀ v ∈ sem.dyns ys, RoleValueValid M r v) ∧
        (rules catalog r).Ensured sem (roleReading M r) (RoleReturns M r fns roles)
          (RoleValueValid M r) op args ys)
      (· ≠ .undefined) := by
  dsimp only
  cases op with
  | absent | keep => cases ordered
  | compute R op ins types mine here =>
      subst types
      have c := compute_corr M r fns roles here args
      have eff := (catalog.lawful M fns callees (fun _ _ => True)).effect op ordered key path _
        ((corr_valid c).mp valid) (localRequired mine c required)
      change Process.Every _ _ _ (localOp M fns op (HList.ofLocated M (revealAll M here args))) at eff
      change Process.Every _ _ _ ((liftLocal id (localOp M fns op
        (HList.ofLocated M (revealAll M here args)))).map _)
      cases ran : localOp M fns op (HList.ofLocated M (revealAll M here args)) with
      | done returned =>
          rw [ran] at eff
          obtain ⟨ok, ens⟩ := eff
          have c' : Corr M r ((roleSem M r fns roles).dyns (hideAll M r (HList.located M R returned)))
              ((localSem M hs.fns fns).dyns returned) := by
            rw [located_outputs]
            exact corr_liftAt mine _
          exact ⟨(corr_valid c').mpr ok, roleEnsured mine (corr_append c c') ens⟩
      | halt stop => rw [ran] at eff; exact eff
      | call impossible => cases impossible
  | give kind getters here =>
      obtain ⟨v, rfl⟩ := HList.one args
      intro _ _
      refine ⟨?_, fun _ h => nomatch h⟩
      intro d m
      obtain rfl := List.mem_singleton.mp m
      exact (valid_hide M r (Holders.mem_ofList.mpr (List.mem_append_right _ here)) _).mpr
        (valid _ (List.mem_singleton.mpr rfl) here)
  | get τ H kind giver getters mine =>
      intro x vr
      refine ⟨?_, fun _ h => nomatch h⟩
      intro d m
      obtain rfl := List.mem_singleton.mp m
      exact (valid_hide M r (Holders.mem_ofList.mpr (List.mem_append_left _ mine)) _).mpr vr
  | own kind hearers operands τ typed here =>
      intro x vr
      refine ⟨?_, fun _ h => nomatch h⟩
      intro d m
      obtain rfl := List.mem_singleton.mp m
      exact (valid_hide M r (Holders.mem_ofList.mpr (List.mem_cons_self ..)) _).mpr vr
  | hear kind owner hearers τ mine =>
      intro x vr
      refine ⟨?_, fun _ h => nomatch h⟩
      intro d m
      obtain rfl := List.mem_singleton.mp m
      exact (valid_hide M r (Holders.mem_ofList.mpr (List.mem_cons_of_mem _ mine)) _).mpr vr
  | apply callee peers distinct covers operands fits =>
      exact Process.every_mono _ _ (fun ys v => ⟨((roleSem M r fns roles).dyns_valid_iff ys).mpr v,
        fun _ h => nomatch h⟩) (fun _ h => h)
        (application_safe_valid M r fns roles rcallees callee peers distinct covers _ fits key path args
          (((roleSem M r fns roles).dyns_valid_iff args).mp valid))

private theorem role_begin_valid {hs : Headers V} (r : Role)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (w : Holders) (key : Key) (path : List Frame) :
    ((roleSem M r fns roles).begin w key path).Every (ValidReply M)
      (fun n => RoleValueValid M r ⟨LTy.index w, n⟩) (fun stop => ¬ stop = Stop.undefined) := by
  show Process.Every _ _ _ (if r ∈ w then _ else _)
  split
  · next h =>
      intro n _
      exact (valid_hide M r (a := LTy.index w) h n).mpr trivial
  · next h => exact valid_out M r (a := LTy.index w) h _

private theorem role_settle_valid {hs : Headers V} (r : Role)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (w : Holders) (key : Key) (path : List Frame) :
    ((roleSem M r fns roles).settle w key path).Every (ValidReply M)
      (fun _ => True) (fun stop => ¬ stop = Stop.undefined) := by
  show Process.Every _ _ _ (if r ∈ w then _ else _)
  split
  · intro _ _; trivial
  · trivial

private theorem validSettingLawful {hs : Headers V} (catalog : FunctionContracts hs.fns) (r : Role)
    (definition : Key) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (callees : Callees M fns) (rcallees : RCalleesValid M roles) :
    (validSetting M catalog r definition fns roles).Lawful := by
  have base := RoleContracts.lawful catalog r M fns roles callees (rcallees_of_valid M rcallees)
  refine ⟨?_, (fun _ h => nomatch h), RoleContracts.requiresDefined catalog r definition [] M fns roles [] []⟩
  exact {
    observedOperand := fun {_ _} op {_} obs {_ _ _ _} ran {_ _} src dst =>
      observedOperand_valid M catalog r fns roles op obs ran src dst
    computes := base.computes
    functional := base.functional
    commutative := base.commutative
    toAssertionLaws := base.toAssertionLaws
    effect := fun op ord key path args val req =>
      effect_valid M catalog r fns roles callees rcallees op ord key path args val req
    condition := base.condition
    count := base.count
    pick := base.pick
    index := base.index
    indexAt := base.indexAt
    indexFromCount := base.indexFromCount
    indexNext := base.indexNext
    collect := base.collect
    begin := role_begin_valid M r fns roles
    settle := role_settle_valid M r fns roles
    stop := base.stop
  }

private theorem validReaderLawful {hs : Headers V} (catalog : FunctionContracts hs.fns) (r : Role)
    (definition : Key) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (callees : Callees M fns) :
    (validSetting M catalog r definition fns roles).cfg.assertions.Lawful
      (validSetting M catalog r definition fns roles) :=
  roleAssertionTypes_lawful _ (assertionLaws catalog r M fns roles callees)
    (fun {_ _} op {_} printed => roleValueForm_written op printed)
    (fun passes _ typed => roleAssertionBool M fns roles passes typed)

private theorem checkedProjection_validReply {hs : Headers V} (catalog : FunctionContracts hs.fns)
    (r : Role) (header : ProtocolHeader V) {inputs : Names header.ins}
    (source : Prot V hs header inputs) (ok : ProtocolConditions header source)
    {bounds} (accepted : checkRole catalog r header (project r source) = .ok bounds)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (callees : Callees M fns) (rcallees : RCalleesValid M roles)
    (path : List Frame) (values : HList (RV M r) header.ins) (valid : values.All (RV.Valid M r)) :
    ((project r source).denote (roleSem M r fns roles) path (Env.empty.extend inputs values)).Every
      (ValidReply M) (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) := by
  let σ := validSetting M catalog r header.key fns roles
  have ⟨_, run⟩ := checkFacts_safe σ
    (validSettingLawful M catalog r header.key fns roles callees rcallees)
    (validReaderLawful M catalog r header.key fns roles callees)
    ⟨[], []⟩ inputs (project r source) bounds accepted (projectedAddresses_nodup r source ok.distinct)
    (fun _ _ h => nomatch h) path values (((roleSem M r fns roles).dyns_valid_iff values).mpr valid)
    (by simp [Contract.requires]) (noGivenFacts σ rfl _ _ _)
  exact Process.every_mono _ _ (fun ys kept => ((roleSem M r fns roles).dyns_valid_iff ys).mp kept.1)
    (fun _ h => h) run

theorem env_all_rv_valid {r : Role} {Γ : Ctx (LTy V)} {env : Env (RV M r) Γ}
    (hv : ∀ a (x : Var Γ a), RV.Valid M r a (env.get x)) :
    ∀ {items : List (LTy V)} (xs : HList (Var Γ) items), (env.all xs).All (RV.Valid M r)
  | [], .nil => trivial
  | _ :: _, .cons x rest => ⟨hv _ x, env_all_rv_valid hv rest⟩

private theorem outside_validReply {hs : Headers V} {parts : List Role} {r : Role}
    (outside : r ∉ parts) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (rcallees : RCalleesValid M roles) :
    ∀ {Γ outs} (t : Term (protocolDialect V hs) Γ outs), Within parts t →
      ∀ path (env : Env (RV M r) Γ), (∀ τ (x : Var Γ τ), RV.Valid M r τ (env.get x)) →
      ((project r t).denote (roleSem M r fns roles) path env).Every (ValidReply M)
        (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined)
  | _, _, .ret xs, _, _, _, valid => env_all_rv_valid M valid xs
  | _, _, .op key o args results rest, w, path, env, valid => by
      have hTail := fun (ys : HList (RV M r) _) (v : ys.All (RV.Valid M r)) =>
        outside_validReply outside fns roles rcallees rest w.2 path _
          (Env.extend_preserves valid results ys v)
      cases o with
      | compute R op operands types held =>
          have no : r ∉ R := fun h => outside (w.1 r h)
          simp only [project, ProtocolOp.project, dite_eq_right no, Term.denote_op, Process.every_bind]
          exact hTail _ (nothings_valid M r _)
      | flow kind giver getters holds unique =>
          have ng : r ≠ giver := fun e => outside (e ▸ w.1.1)
          have ns : r ∉ getters := fun h => outside (w.1.2 r h)
          simp only [project, ProtocolOp.project, dite_eq_right ng, dite_eq_right ns, Term.denote_op,
            Process.every_bind]
          obtain ⟨x, rfl⟩ := HList.one args
          exact hTail _ ⟨(valid_carry M (by simp [Holders.mem_ofList, ns]) (env.get x)).mpr (valid _ x),
            trivial⟩
      | given kind owner hearers operands τ typed held unique =>
          have ng : r ≠ owner := fun e => outside (e ▸ w.1.1)
          have ns : r ∉ hearers := fun h => outside (w.1.2 r h)
          simp only [project, ProtocolOp.project, dite_eq_right ng, dite_eq_right ns, Term.denote_op,
            Process.every_bind]
          exact hTail _ (nothings_valid M r _)
      | narrow R among =>
          by_cases hIn : r ∈ R
          · simp only [project, ProtocolOp.project, dite_eq_left hIn, Term.denote_op, Process.every_bind]
            obtain ⟨x, rfl⟩ := HList.one args
            exact hTail _ ⟨(valid_carry M ⟨fun _ => hIn, fun _ => among r hIn⟩ (env.get x)).mpr
              (valid _ x), trivial⟩
          · simp only [project, ProtocolOp.project, dite_eq_right hIn, Term.denote_op, Process.every_bind]
            exact hTail _ (nothings_valid M r _)
      | apply callee peers distinct covers operands fits =>
          simp only [project, ProtocolOp.project, Term.denote_op, Process.every_bind]
          exact Process.every_mono _ _ hTail (fun _ h => h)
            (application_safe_valid M r fns roles rcallees callee peers distinct covers _ fits key
              path (env.all args) (env_all_rv_valid M valid args))
  | _, _, .guard _ ps _ _ _ rest, w, path, env, valid => by
      have no : r ∉ ps := fun h => outside (w.1 r h)
      simp only [project, dite_eq_right no]
      exact outside_validReply outside fns roles rcallees rest w.2 path env valid
  | _, _, .choose _ ps _ _ _ _ _ results rest, w, path, env, valid => by
      have no : r ∉ ps := fun h => outside (w.1 r h)
      simp only [project, dite_eq_right no, Term.denote_op, Process.every_bind]
      exact outside_validReply outside fns roles rcallees rest w.2.2.2 path _
        (Env.extend_preserves valid results _ (nothings_valid M r _))
  | _, _, .cases _ ps _ _ _ _ results rest, w, path, env, valid => by
      have no : r ∉ ps := fun h => outside (w.1 r h)
      simp only [project, dite_eq_right no, Term.denote_op, Process.every_bind]
      exact outside_validReply outside fns roles rcallees rest w.2.2 path _
        (Env.extend_preserves valid results _ (nothings_valid M r _))
  | _, _, .loop _ ps _ _ _ _ _ results rest, w, path, env, valid => by
      have no : r ∉ ps := fun h => outside (w.1 r h)
      simp only [project, dite_eq_right no, Term.denote_op, Process.every_bind]
      exact outside_validReply outside fns roles rcallees rest w.2.2 path _
        (Env.extend_preserves valid results _ (nothings_valid M r _))
  | _, _, .block _ _ body results rest, w, path, env, valid => by
      simp only [project, Term.denote_block, Process.every_bind]
      exact Process.every_mono _ _
        (fun ys v => outside_validReply outside fns roles rcallees rest w.2 path _
          (Env.extend_preserves valid results ys v))
        (fun _ h => h)
        (outside_validReply outside fns roles rcallees body w.1 _ env valid)
  | _, _, .attempt _ w0 _ inputs body results rest, w, path, env, valid => by
      have no : r ∉ w0 := fun h => outside (w.1 r h)
      simp only [project, Term.denote_attempt, roleSem, ite_eq_right no, Process.bind]
      rw [Process.every_bind]
      exact Process.every_mono _ _
        (fun ys v => outside_validReply outside fns roles rcallees rest w.2.2 path _
          (Env.extend_preserves valid results ys v))
        (fun _ h => h)
        (outside_validReply outside fns roles rcallees body w.2.1 path _
          (Env.extend_preserves valid inputs _ ⟨valid_out M r no _, trivial⟩))

private theorem checkedTables_validReply : ∀ {hs : Headers V} (defs : Defs V hs),
    (hs.fns.map (·.key)).Nodup → CheckedBodies defs →
    Callees M (Defs.fnTable M defs) ∧ RCalleesValid M (Defs.rTable M defs)
  | _, .nil, distinct, _ =>
      ⟨⟨distinct, (fun _ f => nomatch f), (fun _ f => nomatch f), (fun _ f => nomatch f)⟩,
       (fun _ p => nomatch p)⟩
  | _, .fn hdr inputs body ok rest _, distinct, checked => by
      obtain ⟨safe, earlier⟩ := checked
      have ⟨fns, roles⟩ := checkedTables_validReply rest (List.nodup_cons.mp distinct).2 earlier
      refine ⟨⟨distinct, ?_, ?_, Defs.fnTable_stops_undefined M _⟩, roles⟩
      · intro callee found
        cases found with
        | head => exact HeaderSummary.holds_tables (safe M _ fns)
        | tail found => exact HeaderSummary.holds_tables (fns.satisfies _ found)
      · intro callee found args outs valid ran
        cases found with
        | tail found => exact fns.keeps _ found args outs valid ran
        | head =>
            change body.denote (localSem M _ (Defs.fnTable M rest)) [] (Env.empty.extend inputs args) = .done outs at ran
            have kept := Term.denote_valid (Defs.fnTable M rest) fns.keeps body [] (Env.empty.extend inputs args)
              (Env.extend_valid (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed) inputs args valid)
            rw [ran] at kept
            exact kept
  | _, .protocol hdr inputs body ok rest, distinct, checked => by
      obtain ⟨⟨catalog, passes⟩, earlier⟩ := checked
      have ⟨fns, roles⟩ := checkedTables_validReply rest distinct earlier
      refine ⟨fns, ?_⟩
      intro callee found r path args valid
      cases found with
      | head =>
          by_cases declared : r ∈ List.range hdr.roles
          · obtain ⟨bounds, pass⟩ := passes r declared
            exact checkedProjection_validReply M catalog r hdr body ok pass
              (Defs.fnTable M rest) (Defs.rTable M rest) fns roles path args valid
          · exact outside_validReply M declared (Defs.fnTable M rest) (Defs.rTable M rest) roles
              body ok.within path _
              (Env.extend_preserves (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed)
                inputs args valid)
      | tail found => exact roles _ found r path args valid

unseal fnMeaning roleMeaning protocolMeaning in
/-- Every admitted role program never stops `.undefined` and returns valid values against ANY
valid reply (`ValidReply M`, not requiring coin-law support). -/
theorem rolesSafe_validReply {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (accepted : admit named assoc = .ok a) {hdr : ProtocolHeader V}
    (callee : Member a.program.headers.protocols hdr) (r : Role) (path : List Frame)
    (args : HList (RV M r) hdr.ins) (valid : args.All (RV.Valid M r)) :
    (roleMeaning M a.program callee r path args).Every (ValidReply M)
      (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) := by
  have checked := admitFrom_accepted .empty [] named.definitions a.program a.annotation.bounds rfl
    (admit_ok accepted).1
  have roles := (checkedTables_validReply M a.program.defs
    (List.nodup_append.mp a.program.distinct).1 (acceptedBodies _ checked)).2
  exact roles hdr callee r path args valid

end ValidReplySafety

end

end Zkc.Core
