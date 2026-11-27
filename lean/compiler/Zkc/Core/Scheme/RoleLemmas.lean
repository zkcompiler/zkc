module

public import Zkc.Core.Admission.Theorems
public import Zkc.Core.World.Stack
public import Zkc.Core.Projection.Theorem

@[expose] public section

/-!
Generic role-process and handler safety/shape/uniqueness lemmas:
1. `ValidReply` and `ROp.ValidPayload` + `Process.SafeWith` / `Handler.SafeWith` composition
   under `Handler.over` and `Handler.run` (including `retryOf` attempts).
2. `rolesSafe_validReply`: every admitted role program never stops `.undefined` and preserves
   `RV.Valid` against ANY valid reply (`ValidReply M`, not requiring coin-law support).
3. `roleMeaning_validPayload`: every outgoing `.give` value and `.own` payload emitted by a role
   program on valid inputs is valid in `M`.
4. `roleMeaning_matchesShape`: every effect emitted by `roleMeaning` (on arbitrary replies)
   corresponds to a `ShapeEvent` of `hdr.shape.events`.
5. `protocolMeaning_uniqueOccs`: along every execution path of a typed protocol, no occurrence
   is queried twice.
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

private theorem env_all_rv_valid {r : Role} {Γ : Ctx (LTy V)} {env : Env (RV M r) Γ}
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

/-! ## `roleMeaning_validPayload`: outgoing effect payloads are valid -/

section ValidPayload

private theorem safeWith_mapR_validPayload {B : Type} (ρ : Role → Role)
    {P : B → Prop} {R : Stop → Prop} :
    ∀ (p : Program M B),
      p.SafeWith M (ValidReply M) (ROp.ValidPayload M) P R →
      (mapR M ρ p).SafeWith M (ValidReply M) (ROp.ValidPayload M) P R
  | .done _, h => h
  | .halt _, h => h
  | .call (.give ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩
  | .call (.get ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩
  | .call (.own ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩
  | .call (.hear ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩
  | .call (.begin ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩
  | .call (.settle ..) k, ⟨ho, hk⟩ => ⟨ho, fun reply hr => safeWith_mapR_validPayload ρ (k reply) (hk reply hr)⟩

private theorem ofLocated_revealAll_valid {r : Role} :
    ∀ {items : List (LTy V)} (here : ∀ a ∈ items, r ∈ a.holders) (vs : HList (RV M r) items),
      vs.All (RV.Valid M r) → (HList.ofLocated M (revealAll M here vs)).All M.Valid
  | [], _, .nil, _ => trivial
  | a :: _, here, .cons _ vs, hv =>
      ⟨hv.1 (here a List.mem_cons_self),
       ofLocated_revealAll_valid (fun b hb => here b (List.mem_cons_of_mem _ hb)) vs hv.2⟩

private theorem computeArgs_revealAll_valid {r : Role} {operands : List (LTy V)}
    {ins : List V.Ty} (types : operands.map (·.ty) = ins) (here : ∀ a ∈ operands, r ∈ a.holders)
    (vs : HList (RV M r) operands) (hv : vs.All (RV.Valid M r)) :
    (computeArgs M types (revealAll M here vs)).All M.Valid := by
  subst types
  exact ofLocated_revealAll_valid M here vs hv

private theorem hideAll_located_valid {r : Role} (R : Holders) :
    ∀ {outs : List V.Ty} (vs : HList M.Val outs),
      vs.All M.Valid → (hideAll M r (HList.located M R vs)).All (RV.Valid M r)
  | [], .nil, _ => trivial
  | τ :: _, .cons v vs, hv => by
      refine ⟨?_, hideAll_located_valid R vs hv.2⟩
      intro hIn
      exact (BodyAnalysis.RoleContracts.valid_hide M r (a := ⟨τ, R⟩) hIn v).mpr hv.1 hIn

private theorem roleOp_validPayload {hs : Headers V} (r : Role)
    (fns : FnTable M hs.fns) (keeps : FnTable.KeepsValidity fns)
    (roles : RTable M hs.protocols)
    (rcallees : ∀ hdr (callee : Member hs.protocols hdr) (j : Role) (path : List Frame)
      (args : HList (RV M j) hdr.ins), args.All (RV.Valid M j) →
      (roles hdr callee j path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
        (fun ys => ys.All (RV.Valid M j)) (fun _ => True))
    {ins res : List (LTy V)} (key : Key) (o : RoleOp V hs r ins res) (path : List Frame)
    (args : HList (RV M r) ins) (hv : args.All (RV.Valid M r)) :
    (roleOp M r fns roles key o path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
      (fun ys => ys.All (RV.Valid M r)) (fun _ => True) := by
  cases o with
  | compute R op operands types mine here =>
      show ((liftLocal id (localOp M fns op (computeArgs M types (revealAll M here args)))).map
        (fun outs => hideAll M r (HList.located M R outs))).SafeWith M _ _ _ _
      rw [Process.safeWith_map]
      cases hrun : localOp M fns op (computeArgs M types (revealAll M here args)) with
      | done outs =>
          have houts := localOp_valid fns keeps op _ outs
            (computeArgs_revealAll_valid M types here args hv) hrun
          exact hideAll_located_valid M R outs houts
      | halt _ => trivial
      | call op' _ => cases op'
  | absent items out => exact BodyAnalysis.RoleContracts.nothings_valid M r out
  | give kind getters here =>
      obtain ⟨v, rfl⟩ := HList.one args
      exact ⟨hv.1 here, fun _ _ => ⟨fun hIn =>
        (BodyAnalysis.RoleContracts.valid_hide M r hIn _).mpr (hv.1 here) hIn, trivial⟩⟩
  | get τ H kind giver getters mine =>
      exact ⟨trivial, fun x hx => ⟨fun hIn =>
        (BodyAnalysis.RoleContracts.valid_hide M r hIn _).mpr hx hIn, trivial⟩⟩
  | keep H same =>
      obtain ⟨v, rfl⟩ := HList.one args
      exact ⟨(BodyAnalysis.RoleContracts.valid_carry M same v).mpr hv.1, trivial⟩
  | own kind hearers operands τ typed here =>
      exact ⟨ofLocated_revealAll_valid M here args hv, fun x hx => ⟨fun hIn =>
        (BodyAnalysis.RoleContracts.valid_hide M r hIn _).mpr hx hIn, trivial⟩⟩
  | hear kind owner hearers τ mine =>
      exact ⟨trivial, fun x hx => ⟨fun hIn =>
        (BodyAnalysis.RoleContracts.valid_hide M r hIn _).mpr hx hIn, trivial⟩⟩
  | apply callee peers distinct covers operands fits =>
      let ρ := RoleMap.ofList peers distinct
      show ((mapR M ρ.to (roles _ callee (ρ.back r) (path ++ [.application key])
        (enterAll M ρ r (fitAllRV M fits args)))).map (leaveAll M ρ r)).SafeWith M _ _ _ _
      rw [Process.safeWith_map]
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun ys hy => BodyAnalysis.RoleContracts.leaveAll_valid M ρ r ys hy) (fun _ _ => trivial)
        (safeWith_mapR_validPayload M ρ.to _
          (rcallees _ callee _ _ _
            (BodyAnalysis.RoleContracts.enterAll_valid M ρ r _
              (BodyAnalysis.RoleContracts.fitAllRV_valid M fits args hv))))

private theorem env_extend_rv_valid {r : Role} {Γ : Ctx (LTy V)} {env : Env (RV M r) Γ}
    (hv : ∀ a (x : Var Γ a), RV.Valid M r a (env.get x)) :
    ∀ {items : List (LTy V)} (bound : Names items) (vals : HList (RV M r) items),
      vals.All (RV.Valid M r) → ∀ a (x : Var (Γ.extend bound) a),
      RV.Valid M r a ((env.extend bound vals).get x)
  | [], .nil, .nil, _, _, x => hv _ x
  | σ :: _, .cons n rest, .cons v vs, hvs, a, x =>
      env_extend_rv_valid (fun b y => by
        by_cases hEq : y.name = n
        · have hTy : σ = b := by
            have ht := y.typed; rw [Ctx.find?_insert, ite_eq_left hEq] at ht
            exact Option.some.inj ht
          subst hTy
          show RV.Valid M r σ ((env.insert n v) y.name σ y.typed)
          rw [eq_of_heq (Env.insert_at_bound env n v hEq y.typed)]
          exact hvs.1
        · show RV.Valid M r b ((env.insert n v) y.name b y.typed)
          rw [Env.insert_at_other env n v hEq y.typed]
          exact hv b ⟨y.name, by
            have ht := y.typed; rw [Ctx.find?_insert, ite_eq_right hEq] at ht; exact ht⟩)
        rest vs hvs.2 a x

private theorem pushAll_rv_valid {r : Role} :
    ∀ {each : List (LTy V)} {acc : HList (fun a => List (RV M r a)) each}
      {step : HList (RV M r) each} {k : Nat},
      HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = k) acc →
      step.All (RV.Valid M r) →
      HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = k + 1)
        (HList.push acc step)
  | [], .nil, .nil, _, _, _ => trivial
  | _ :: _, .cons xs rest, .cons v vs, _, hacc, hstep => by
      refine ⟨⟨fun w hw => ?_, by simp [hacc.1.2]⟩, pushAll_rv_valid hacc.2 hstep.2⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hstep.1
      · exact hacc.1.1 w hw

private theorem collected_rv_valid {hs : Headers V} (r : Role)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (size : Option Nat) (count : Nat) (hsize : ∀ n, size = some n → count = n) :
    ∀ {each : List (LTy V)} (acc : HList (fun a => List (RV M r a)) each),
      HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = count) acc →
      ((roleSem M r fns roles).collected size acc).All (RV.Valid M r)
  | [], .nil, _ => trivial
  | a :: _, .cons xs rest, hacc =>
      ⟨BodyAnalysis.RoleContracts.role_collect M r fns roles size a xs.reverse
          (fun n hn => by rw [List.length_reverse]; exact hacc.1.2.trans (hsize n hn))
          (fun v hv => hacc.1.1 v (List.mem_reverse.mp hv)),
       collected_rv_valid r fns roles size count hsize rest hacc.2⟩

private theorem hlist_all_append {α : Type} {F : α → Type} {P : ∀ a, F a → Prop} :
    ∀ {as bs : List α} {xs : HList F as} {ys : HList F bs},
      xs.All P → ys.All P → (xs.append ys).All P
  | [], _, .nil, _, _, hy => hy
  | _ :: _, _, .cons _ _, _, hx, hy => ⟨hx.1, hlist_all_append hx.2 hy⟩

private theorem hlist_split_all {α : Type} {F : α → Type} {P : ∀ a, F a → Prop} :
    ∀ (as : List α) {bs : List α} (xs : HList F (as ++ bs)),
      xs.All P → (HList.split as xs).1.All P ∧ (HList.split as xs).2.All P
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: as, _, .cons _ rest, h =>
      let ih := hlist_split_all as rest h.2
      ⟨⟨h.1, ih.1⟩, ih.2⟩

private theorem iterate_safeWith {σ : Type} {Inv : σ → Prop}
    {step : Nat → σ → Process (RSig M) Stop σ}
    (hstep : ∀ i s, Inv s → (step i s).SafeWith M (ValidReply M) (ROp.ValidPayload M) Inv (fun _ => True)) :
    ∀ (n i : Nat) (s : σ), Inv s →
      (Process.iterate n step i s).SafeWith M (ValidReply M) (ROp.ValidPayload M) Inv (fun _ => True)
  | 0, _, _, hs => hs
  | n + 1, i, s, hs => by
      simp only [Process.iterate]
      rw [Process.safeWith_bind]
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun s' hs' => iterate_safeWith hstep n (i + 1) s' hs') (fun _ _ => trivial)
        (hstep i s hs)

mutual
  private theorem term_role_validPayload {hs : Headers V} (r : Role)
      (fns : FnTable M hs.fns) (keeps : FnTable.KeepsValidity fns)
      (roles : RTable M hs.protocols)
      (rcallees : ∀ hdr (callee : Member hs.protocols hdr) (j : Role) (path : List Frame)
        (args : HList (RV M j) hdr.ins), args.All (RV.Valid M j) →
        (roles hdr callee j path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
          (fun ys => ys.All (RV.Valid M j)) (fun _ => True)) :
      ∀ {Γ outs} (t : Term (roleDialect V hs r) Γ outs) (path : List Frame) (env : Env (RV M r) Γ),
        (∀ a (x : Var Γ a), RV.Valid M r a (env.get x)) →
        (t.denote (roleSem M r fns roles) path env).SafeWith M (ValidReply M) (ROp.ValidPayload M)
          (fun ys => ys.All (RV.Valid M r)) (fun _ => True)
    | _, _, .ret exit, _, env, hv => env_all_rv_valid M hv exit
    | _, _, .op key o operands results rest, path, env, hv => by
        rw [Term.denote_op, Process.safeWith_bind]
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun ys hys => term_role_validPayload r fns keeps roles rcallees rest path _
            (env_extend_rv_valid M hv results ys hys))
          (fun _ _ => trivial)
          (roleOp_validPayload M r fns keeps roles rcallees key o path (env.all operands)
            (env_all_rv_valid M hv operands))
    | _, _, .guard key w c ok why rest, path, env, hv => by
        rw [Term.denote_guard]
        cases (roleSem M r fns roles).holds ok (env.get c)
        · trivial
        · exact term_role_validPayload r fns keeps roles rcallees rest path env hv
    | _, _, .choose key w c ok gives onTrue onFalse results rest, path, env, hv => by
        rw [Term.denote_choose, Process.safeWith_bind]
        have hArm : (bif (roleSem M r fns roles).holds ok (env.get c)
            then onTrue.denote (roleSem M r fns roles) path env
            else onFalse.denote (roleSem M r fns roles) path env).SafeWith M
            (ValidReply M) (ROp.ValidPayload M) (fun ys => ys.All (RV.Valid M r)) (fun _ => True) := by
          cases (roleSem M r fns roles).holds ok (env.get c)
          · exact term_role_validPayload r fns keeps roles rcallees onFalse path env hv
          · exact term_role_validPayload r fns keeps roles rcallees onTrue path env hv
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun ys hys => term_role_validPayload r fns keeps roles rcallees rest path _
            (env_extend_rv_valid M hv results ys hys))
          (fun _ _ => trivial) hArm
    | _, _, .cases key w x ok gives arms results rest, path, env, hv => by
        rw [Term.denote_cases, Process.safeWith_bind]
        have hPick := BodyAnalysis.RoleContracts.role_pick M r fns roles ok (env.get x) (hv _ x)
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun ys hys => term_role_validPayload r fns keeps roles rcallees rest path _
            (env_extend_rv_valid M hv results ys hys))
          (fun _ _ => trivial)
          (arms_role_validPayload r fns keeps roles rcallees arms path env hv _ hPick)
    | _, _, .loop (carried := carried) (each := each) key w times gives initial inputs body results rest,
        path, env, hv => by
        rw [Term.denote_loop, Process.safeWith_bind]
        let count := (roleSem M r fns roles).times times env
        have hEmpty : ∀ (es : List (LTy V)),
            HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = 0)
              (HList.empties (V := RV M r) es) := by
          intro es
          induction es with
          | nil => trivial
          | cons _ _ ih => exact ⟨⟨(fun _ h => nomatch h), rfl⟩, ih⟩
        have hIter : ∀ (n i : Nat) (s : (roleSem M r fns roles).LoopState carried each),
            s.1.All (RV.Valid M r) ∧
              HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = i) s.2 →
            (Process.iterate n ((roleSem M r fns roles).loopStep w inputs
              (fun at_ inside => body.denote (roleSem M r fns roles) at_ inside) key path env) i s).SafeWith
              M (ValidReply M) (ROp.ValidPayload M)
              (fun st => st.1.All (RV.Valid M r) ∧
                HList.All (fun a xs => (∀ v ∈ xs, RV.Valid M r a v) ∧ xs.length = i + n) st.2)
              (fun _ => True) := by
          intro n
          induction n with
          | zero => intro i s hs; exact hs
          | succ m ih =>
              intro i s hs
              simp only [Process.iterate, Semantics.loopStep]
              rw [Process.safeWith_bind, Process.safeWith_bind]
              have hIdx : RV.Valid M r (LTy.index w) ((roleSem M r fns roles).index w i) := by
                intro hIn
                exact (BodyAnalysis.RoleContracts.valid_hide M r (a := LTy.index w) hIn i).mpr trivial hIn
              have hBody := term_role_validPayload r fns keeps roles rcallees body
                (path ++ [.iteration key i]) _
                (env_extend_rv_valid M hv inputs (.cons ((roleSem M r fns roles).index w i) s.1)
                  ⟨hIdx, hs.1⟩)
              exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
                (fun ys hys => by
                  have hsp := hlist_split_all carried ys hys
                  have hst' := ih (i + 1) ((HList.split carried ys).1, s.2.push (HList.split carried ys).2)
                    ⟨hsp.1, pushAll_rv_valid M hs.2 hsp.2⟩
                  simpa [Process.SafeWith, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hst')
                (fun _ _ => trivial) hBody
        have hRun := hIter count 0 (env.all initial, HList.empties each)
          ⟨env_all_rv_valid M hv initial, hEmpty each⟩
        refine Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun st hst => term_role_validPayload r fns keeps roles rcallees rest path _
            (env_extend_rv_valid M hv results _
              (hlist_all_append hst.1
                (collected_rv_valid M r fns roles times.size count
                  (by
                    intro n hn
                    cases times with
                    | fixed m => cases hn; rfl
                    | value _ _ => cases hn)
                  st.2 (by simpa using hst.2)))))
          (fun _ _ => trivial) hRun
    | _, _, .block key number body results rest, path, env, hv => by
        rw [Term.denote_block, Process.safeWith_bind]
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun ys hys => term_role_validPayload r fns keeps roles rcallees rest path _
            (env_extend_rv_valid M hv results ys hys))
          (fun _ _ => trivial)
          (term_role_validPayload r fns keeps roles rcallees body (path ++ [.iteration key number]) env hv)
    | _, _, .attempt key w owns inputs body results rest, path, env, hv => by
        rw [Term.denote_attempt, Process.safeWith_bind]
        have hBeg : ((roleSem M r fns roles).begin w key path).SafeWith M (ValidReply M)
            (ROp.ValidPayload M) (fun n => RV.Valid M r (LTy.index w) n) (fun _ => True) := by
          show Process.SafeWith M _ _ _ _ (if r ∈ w then _ else _)
          split
          · next hIn =>
              refine ⟨trivial, fun n _ => ?_⟩
              exact (BodyAnalysis.RoleContracts.valid_hide M r (a := LTy.index w) hIn n).mpr trivial
          · next hOut => exact BodyAnalysis.RoleContracts.valid_out M r (a := LTy.index w) hOut _
        have hSet : ((roleSem M r fns roles).settle w key path).SafeWith M (ValidReply M)
            (ROp.ValidPayload M) (fun _ => True) (fun _ => True) := by
          show Process.SafeWith M _ _ _ _ (if r ∈ w then _ else _)
          split
          · exact ⟨trivial, fun _ _ => trivial⟩
          · trivial
        exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
          (fun n hn => by
            rw [Process.safeWith_bind]
            exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
              (fun ys hys => by
                rw [Process.safeWith_bind]
                exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
                  (fun _ _ => term_role_validPayload r fns keeps roles rcallees rest path _
                    (env_extend_rv_valid M hv results ys hys))
                  (fun _ _ => trivial) hSet)
              (fun _ _ => trivial)
              (term_role_validPayload r fns keeps roles rcallees body path _
                (env_extend_rv_valid M hv inputs (.cons n .nil) ⟨hn, trivial⟩)))
          (fun _ _ => trivial) hBeg
  private theorem arms_role_validPayload {hs : Headers V} (r : Role)
      (fns : FnTable M hs.fns) (keeps : FnTable.KeepsValidity fns)
      (roles : RTable M hs.protocols)
      (rcallees : ∀ hdr (callee : Member hs.protocols hdr) (j : Role) (path : List Frame)
        (args : HList (RV M j) hdr.ins), args.All (RV.Valid M j) →
        (roles hdr callee j path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
          (fun ys => ys.All (RV.Valid M j)) (fun _ => True)) :
      ∀ {Γ mid payloads} (arms : Arms (roleDialect V hs r) Γ mid payloads)
        (path : List Frame) (env : Env (RV M r) Γ),
        (∀ a (x : Var Γ a), RV.Valid M r a (env.get x)) →
        (p : Pick (RV M r) payloads) → p.All (RV.Valid M r) →
        (arms.denote (roleSem M r fns roles) path env p).SafeWith M (ValidReply M)
          (ROp.ValidPayload M) (fun ys => ys.All (RV.Valid M r)) (fun _ => True)
    | _, _, _, .nil, _, _, _, p, _ => nomatch p
    | _, _, _, .cons inputs arm _, path, env, hv, .here v, hp =>
        term_role_validPayload r fns keeps roles rcallees arm path (env.extend inputs (.cons v .nil))
          (env_extend_rv_valid M hv inputs (.cons v .nil) ⟨hp, trivial⟩)
    | _, _, _, .cons _ _ rest, path, env, hv, .there p, hp =>
        arms_role_validPayload r fns keeps roles rcallees rest path env hv p hp
end

private theorem defs_rTable_validPayload :
    ∀ {hs : Headers V} (defs : Defs V hs),
      FnTable.KeepsValidity (Defs.fnTable M defs) →
      ∀ hdr (callee : Member hs.protocols hdr) (r : Role) (path : List Frame)
        (args : HList (RV M r) hdr.ins), args.All (RV.Valid M r) →
        (Defs.rTable M defs hdr callee r path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
          (fun ys => ys.All (RV.Valid M r)) (fun _ => True)
  | _, .nil, _, _, p, _, _, _, _ => nomatch p
  | _, .fn _ _ _ _ rest _, keeps, hdr, callee, r, path, args, hv =>
      defs_rTable_validPayload rest (fun h f => keeps h (.tail f)) hdr callee r path args hv
  | _, .protocol hdr inputs body _ rest, keeps, _, callee, r, path, args, hv => by
      cases callee with
      | head =>
          exact term_role_validPayload M r (Defs.fnTable M rest) keeps (Defs.rTable M rest)
            (defs_rTable_validPayload rest keeps) (project r body) path _
            (env_extend_rv_valid M (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed)
              inputs args hv)
      | tail callee => exact defs_rTable_validPayload rest keeps _ callee r path args hv

unseal fnMeaning roleMeaning protocolMeaning in
/-- Every outgoing `.give` and `.own` payload emitted by an admitted role program on valid inputs
and valid replies is valid in `M`. -/
theorem roleMeaning_validPayload (a : Admitted V) {hdr : ProtocolHeader V}
    (callee : Member a.program.headers.protocols hdr) (r : Role) (path : List Frame)
    (args : HList (RV M r) hdr.ins) (valid : args.All (RV.Valid M r)) :
    (roleMeaning M a.program callee r path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
      (fun ys => ys.All (RV.Valid M r)) (fun _ => True) :=
  defs_rTable_validPayload M a.program.defs (a.assured M).2.1 hdr callee r path args valid

/-- Combined role safety and payload validity under `ValidReply M`. -/
theorem roleMeaning_safeWith_valid {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (accepted : admit named assoc = .ok a) {hdr : ProtocolHeader V}
    (callee : Member a.program.headers.protocols hdr) (r : Role) (path : List Frame)
    (args : HList (RV M r) hdr.ins) (valid : args.All (RV.Valid M r)) :
    (roleMeaning M a.program callee r path args).SafeWith M (ValidReply M) (ROp.ValidPayload M)
      (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) :=
  Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h.2) (fun _ h => h.1) (fun _ h => h.1)
    (Process.safeWith_and M
      (Process.safeWith_of_every M (rolesSafe_validReply M accepted callee r path args valid))
      (roleMeaning_validPayload M a callee r path args valid))

/-! ## `roleMeaning_matchesShape`: every emitted effect matches `hdr.shape.events` -/

end ValidPayload

section ShapeMatch

/-- A single role effect matches a `ShapeEvent` at role `r`. -/
def ROp.MatchesShapeEvent (r : Role) (e : ShapeEvent V) : ROp M → Prop
  | .give kind getters at_ τ _ => e.site = at_.site ∧ e.τ = τ ∧ e.cls = .flow kind r getters
  | .get kind giver at_ τ =>
      giver ≠ r ∧ e.site = at_.site ∧ e.τ = τ ∧ ∃ getters, r ∈ getters ∧ e.cls = .flow kind giver getters
  | .own kind hearers at_ ins _ τ =>
      e.site = at_.site ∧ e.τ = τ ∧ e.cls = .given kind r hearers ∧ kind.Typed ins τ
  | .hear kind owner at_ τ =>
      owner ≠ r ∧ e.site = at_.site ∧ e.τ = τ ∧ ∃ hearers, r ∈ hearers ∧ e.cls = .given kind owner hearers
  | .begin _ => True
  | .settle _ => True

/-- Every non-attempt effect matches some event in `events` for role `r`. -/
def ROp.MatchesShape (r : Role) (events : List (ShapeEvent V)) : ROp M → Prop
  | .begin _ => True
  | .settle _ => True
  | op => ∃ e ∈ events, ROp.MatchesShapeEvent M r e op

private theorem list_getD_of_lt {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem frame_applications_append :
    ∀ (p q : List Frame), Frame.applications (p ++ q) = Frame.applications p ++ Frame.applications q
  | [], _ => rfl
  | .application k :: rest, q => congrArg (k :: ·) (frame_applications_append rest q)
  | .iteration _ _ :: rest, q => frame_applications_append rest q
  | .attempt _ _ :: rest, q => frame_applications_append rest q

private theorem eventClass_rename_comp (f g : Role → Role) (c : EventClass V) :
    (c.rename g).rename f = c.rename (fun j => f (g j)) := by
  cases c with
  | flow kind giver getters => simp [EventClass.rename, List.map_map, Function.comp_def]
  | given kind owner hearers => simp [EventClass.rename, List.map_map, Function.comp_def]

private theorem eventClass_rename_id (c : EventClass V) : c.rename id = c := by
  cases c <;> simp [EventClass.rename]

mutual
  private theorem shape_events_map (through : List Key) (rename : Role → Role) :
      ∀ (s : Shape V),
        s.events through rename =
          (s.events [] id).map fun e =>
            ⟨⟨through ++ e.site.through, e.site.key⟩, e.cls.rename rename, e.τ⟩
    | .nil => rfl
    | .event key cls τ rest => by
        simp only [Shape.events, List.map_cons, List.append_nil, eventClass_rename_id,
          shape_events_map through rename rest]
    | .choice _ _ arms rest => by
        simp only [Shape.events, List.map_append, shapes_events_map through rename arms,
          shape_events_map through rename rest]
    | .loop _ _ body rest => by
        simp only [Shape.events, List.map_append, shape_events_map through rename body,
          shape_events_map through rename rest]
    | .apply key _ roles inner rest => by
        simp only [Shape.events, List.map_append, List.nil_append, id_eq,
          shape_events_map (through ++ [key]) _ inner, shape_events_map [key] _ inner,
          shape_events_map through rename rest, List.map_map]
        congr 1
        apply List.map_congr_left
        intro e _
        simp only [Function.comp_def, List.append_assoc, eventClass_rename_comp]
    | .block _ _ body rest => by
        simp only [Shape.events, List.map_append, shape_events_map through rename body,
          shape_events_map through rename rest]
    | .guard _ _ _ rest => shape_events_map through rename rest
    | .attempt _ _ body rest => by
        simp only [Shape.events, List.map_append, shape_events_map through rename body,
          shape_events_map through rename rest]
  private theorem shapes_events_map (through : List Key) (rename : Role → Role) :
      ∀ (ss : Shapes V),
        ss.events through rename =
          (ss.events [] id).map fun e =>
            ⟨⟨through ++ e.site.through, e.site.key⟩, e.cls.rename rename, e.τ⟩
    | .nil => rfl
    | .cons arm rest => by
        simp only [Shapes.events, List.map_append, shape_events_map through rename arm,
          shapes_events_map through rename rest]
end

private def EventClass.AllIn (parts : List Role) : EventClass V → Prop
  | .flow _ giver getters => giver ∈ parts ∧ ∀ g ∈ getters, g ∈ parts
  | .given _ owner hearers => owner ∈ parts ∧ ∀ h ∈ hearers, h ∈ parts

private theorem eventClass_rename_congr {parts : List Role} {f g : Role → Role}
    (h : ∀ j ∈ parts, f j = g j) : ∀ {c : EventClass V}, c.AllIn parts → c.rename f = c.rename g
  | .flow kind giver getters, ⟨hg, hgs⟩ => by
      simp only [EventClass.rename, h giver hg]
      congr 1
      exact List.map_congr_left fun x hx => h x (hgs x hx)
  | .given kind owner hearers, ⟨ho, hhs⟩ => by
      simp only [EventClass.rename, h owner ho]
      congr 1
      exact List.map_congr_left fun x hx => h x (hhs x hx)

private theorem shape_events_within {hs : Headers V}
    (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles)) :
    ∀ {parts : List Role} {Γ outs} (t : Term (protocolDialect V hs) Γ outs),
      Within parts t → ∀ e ∈ (shapeOf t).events [] id, e.cls.AllIn parts
  | _, _, _, .ret _, _, e, he => nomatch he
  | parts, _, _, .op key o _ _ rest, w, e, he => by
      have hRest := shape_events_within hProt rest w.2
      cases o with
      | compute | narrow => exact hRest e he
      | flow kind giver getters =>
          simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_cons] at he
          rcases he with rfl | he
          · exact ⟨w.1.1, by simpa [EventClass.rename] using w.1.2⟩
          · exact hRest e he
      | given kind owner hearers =>
          simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_cons] at he
          rcases he with rfl | he
          · exact ⟨w.1.1, by simpa [EventClass.rename] using w.1.2⟩
          · exact hRest e he
      | @apply hdr callee roles distinct covers _ _ =>
          simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append] at he
          rcases he with he | he
          · rw [shape_events_map] at he
            obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
            have hall0 := hProt hdr (Member.mem callee) e0 he0
            have hMap : ∀ j ∈ List.range hdr.roles, roles.getD j j ∈ parts := by
              intro j hj
              have hlt : j < roles.length := covers.symm ▸ List.mem_range.mp hj
              rw [list_getD_of_lt roles j j hlt]
              exact w.1 _ (List.getElem_mem hlt)
            cases hcls : e0.cls with
            | flow kind giver getters =>
                rw [hcls] at hall0
                refine ⟨hMap giver hall0.1, fun x hx => ?_⟩
                obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
                exact hMap g (hall0.2 g hg)
            | given kind owner hearers =>
                rw [hcls] at hall0
                refine ⟨hMap owner hall0.1, fun x hx => ?_⟩
                obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
                exact hMap h (hall0.2 h hh)
          · exact hRest e he
  | parts, _, _, .guard _ _ _ _ _ rest, w, e, he =>
      shape_events_within hProt rest w.2 e he
  | parts, _, _, .choose _ _ _ _ _ onTrue onFalse _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, Shapes.events, List.append_nil, List.mem_append] at he
      rcases he with (he | he) | he
      · exact shape_events_within hProt onTrue w.2.1 e he
      · exact shape_events_within hProt onFalse w.2.2.1 e he
      · exact shape_events_within hProt rest w.2.2.2 e he
  | parts, _, _, .cases _ _ _ _ _ arms _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact arms_shape_events_within hProt arms w.2.1 e he
      · exact shape_events_within hProt rest w.2.2 e he
  | parts, _, _, .loop _ _ _ _ _ _ body _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact shape_events_within hProt body w.2.1 e he
      · exact shape_events_within hProt rest w.2.2 e he
  | parts, _, _, .block _ _ body _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact shape_events_within hProt body w.1 e he
      · exact shape_events_within hProt rest w.2 e he
  | parts, _, _, .attempt _ _ _ _ body _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact shape_events_within hProt body w.2.1 e he
      · exact shape_events_within hProt rest w.2.2 e he
where
  arms_shape_events_within {hs : Headers V}
      (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles)) :
      ∀ {parts : List Role} {Γ mid payloads} (arms : Arms (protocolDialect V hs) Γ mid payloads),
        WithinArms parts arms → ∀ e ∈ (shapesOf arms).events [] id, e.cls.AllIn parts
    | _, _, _, _, .nil, _, e, he => nomatch he
    | parts, _, _, _, .cons _ arm rest, w, e, he => by
        simp only [shapesOf, Shapes.events, List.mem_append] at he
        rcases he with he | he
        · exact shape_events_within hProt arm w.1 e he
        · exact arms_shape_events_within hProt rest w.2 e he

private theorem safeWith_mapR_shape {B : Type} (ρ : RoleMap) (r : Role)
    (events : List (ShapeEvent V)) (events' : List (ShapeEvent V))
    (hMap : ∀ e ∈ events, ⟨e.site, e.cls.rename ρ.to, e.τ⟩ ∈ events') :
    ∀ (p : Program M B),
      p.SafeWith M (fun _ _ => True) (ROp.MatchesShape M (ρ.back r) events) (fun _ => True) (fun _ => True) →
      (mapR M ρ.to p).SafeWith M (fun _ _ => True) (ROp.MatchesShape M r events') (fun _ => True) (fun _ => True)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.give kind getters at_ τ x) k, ⟨ho, hk⟩ =>
      let ⟨e, he, hSite, hTy, hCls⟩ := ho
      ⟨⟨⟨e.site, e.cls.rename ρ.to, e.τ⟩, hMap e he, hSite, hTy, by
          simp only [hCls, EventClass.rename, ρ.right r]⟩,
        fun u _ => safeWith_mapR_shape ρ r events events' hMap (k u) (hk u trivial)⟩
  | .call (.get kind giver at_ τ) k, ⟨ho, hk⟩ =>
      let ⟨e, he, hNe, hSite, hTy, getters, hrIn, hCls⟩ := ho
      ⟨⟨⟨e.site, e.cls.rename ρ.to, e.τ⟩, hMap e he,
          fun heq => hNe (by have := congrArg ρ.back heq; rwa [ρ.left giver] at this),
          hSite, hTy, getters.map ρ.to,
          List.mem_map.mpr ⟨ρ.back r, hrIn, ρ.right r⟩, by simp only [hCls, EventClass.rename]⟩,
        fun y _ => safeWith_mapR_shape ρ r events events' hMap (k y) (hk y trivial)⟩
  | .call (.own kind hearers at_ ins payload τ) k, ⟨ho, hk⟩ =>
      let ⟨e, he, hSite, hTy, hCls, hTyped⟩ := ho
      ⟨⟨⟨e.site, e.cls.rename ρ.to, e.τ⟩, hMap e he, hSite, hTy, by
          simp only [hCls, EventClass.rename, ρ.right r], hTyped⟩,
        fun y _ => safeWith_mapR_shape ρ r events events' hMap (k y) (hk y trivial)⟩
  | .call (.hear kind owner at_ τ) k, ⟨ho, hk⟩ =>
      let ⟨e, he, hNe, hSite, hTy, hearers, hrIn, hCls⟩ := ho
      ⟨⟨⟨e.site, e.cls.rename ρ.to, e.τ⟩, hMap e he,
          fun heq => hNe (by have := congrArg ρ.back heq; rwa [ρ.left owner] at this),
          hSite, hTy, hearers.map ρ.to,
          List.mem_map.mpr ⟨ρ.back r, hrIn, ρ.right r⟩, by simp only [hCls, EventClass.rename]⟩,
        fun y _ => safeWith_mapR_shape ρ r events events' hMap (k y) (hk y trivial)⟩
  | .call (.begin _) k, ⟨_, hk⟩ =>
      ⟨trivial, fun n _ => safeWith_mapR_shape ρ r events events' hMap (k n) (hk n trivial)⟩
  | .call (.settle _) k, ⟨_, hk⟩ =>
      ⟨trivial, fun u _ => safeWith_mapR_shape ρ r events events' hMap (k u) (hk u trivial)⟩

private theorem matchesShape_mono (r : Role) {ev₁ ev₂ : List (ShapeEvent V)}
    (hSub : ∀ e ∈ ev₁, e ∈ ev₂) {op : ROp M}
    (h : ROp.MatchesShape M r ev₁ op) : ROp.MatchesShape M r ev₂ op := by
  cases op with
  | «begin» | settle => trivial
  | give | get | own | hear =>
      obtain ⟨e, he, hm⟩ := h
      exact ⟨e, hSub e he, hm⟩

private theorem iterate_safeWith_true {σ : Type} {opOk : ROp M → Prop}
    {step : Nat → σ → Process (RSig M) Stop σ}
    (hstep : ∀ i s, (step i s).SafeWith M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)) :
    ∀ (n i : Nat) (s : σ),
      (Process.iterate n step i s).SafeWith M (fun _ _ => True) opOk (fun _ => True) (fun _ => True)
  | 0, _, _ => trivial
  | n + 1, i, s => by
      simp only [Process.iterate]
      rw [Process.safeWith_bind]
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun s' _ => iterate_safeWith_true hstep n (i + 1) s') (fun _ _ => trivial)
        (hstep i s)

private theorem liftLocal_safeWith_true {A : Type} {opOk : ROp M → Prop} (p : Local A) :
    (liftLocal (S := RSig M) id p).SafeWith M (fun _ _ => True) opOk (fun _ => True) (fun _ => True) := by
  cases p with
  | done _ => trivial
  | halt _ => trivial
  | call op _ => cases op

private theorem project_matchesShape {hs : Headers V} (r : Role)
    (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles))
    (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (j : Role) (path : List Frame)
      (args : HList (RV M j) hdr.ins),
      (roles hdr callee j path args).SafeWith M (fun _ _ => True)
        (ROp.MatchesShape M j (hdr.shape.events (Frame.applications path) id))
        (fun _ => True) (fun _ => True)) :
    ∀ {Γ outs} (t : Term (protocolDialect V hs) Γ outs) (path : List Frame) (env : Env (RV M r) Γ),
      ((project r t).denote (roleSem M r fns roles) path env).SafeWith M (fun _ _ => True)
        (ROp.MatchesShape M r ((shapeOf t).events (Frame.applications path) id))
        (fun _ => True) (fun _ => True)
  | _, _, .ret _, _, _ => trivial
  | _, _, .op key o args results rest, path, env => by
      have hRest := fun (ys : HList (RV M r) _) =>
        project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys)
      cases o with
      | compute R op operands types held =>
          by_cases hIn : r ∈ R
          · simp only [project, ProtocolOp.project, dite_eq_left hIn, Term.denote_op, Process.safeWith_bind]
            show Process.SafeWith M _ _ _ _ ((liftLocal id _).map _)
            rw [Process.safeWith_map]
            exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
              (fun ys _ => hRest _) (fun _ _ => trivial) (liftLocal_safeWith_true M _)
          · simp only [project, ProtocolOp.project, dite_eq_right hIn, Term.denote_op, Process.safeWith_bind]
            exact hRest _
      | narrow R among =>
          by_cases hIn : r ∈ R
          · simp only [project, ProtocolOp.project, dite_eq_left hIn, Term.denote_op, Process.safeWith_bind]
            obtain ⟨x, rfl⟩ := HList.one args
            exact hRest _
          · simp only [project, ProtocolOp.project, dite_eq_right hIn, Term.denote_op, Process.safeWith_bind]
            exact hRest _
      | flow kind giver getters holds unique =>
          by_cases hg : r = giver
          · subst hg
            simp only [project, ProtocolOp.project, dite_true, Term.denote_op, Process.safeWith_bind]
            obtain ⟨x, rfl⟩ := HList.one args
            refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.flow kind r getters).rename id, _⟩,
              List.mem_cons_self, rfl, rfl, eventClass_rename_id (.flow kind r getters)⟩, fun _ _ => ?_⟩
            exact Process.safeWith_mono M (fun _ _ h => h)
              (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
              (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
          · by_cases hm : r ∈ getters
            · simp only [project, ProtocolOp.project, dite_eq_right hg, dite_eq_left hm,
                Term.denote_op, Process.safeWith_bind]
              refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.flow kind giver getters).rename id, _⟩,
                List.mem_cons_self, Ne.symm hg, rfl, rfl, getters, hm, eventClass_rename_id (.flow kind giver getters)⟩, fun _ _ => ?_⟩
              exact Process.safeWith_mono M (fun _ _ h => h)
                (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
                (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
            · simp only [project, ProtocolOp.project, dite_eq_right hg, dite_eq_right hm,
                Term.denote_op, Process.safeWith_bind]
              obtain ⟨x, rfl⟩ := HList.one args
              exact Process.safeWith_mono M (fun _ _ h => h)
                (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
                (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
      | given kind owner hearers operands τ typed held unique =>
          by_cases ho : r = owner
          · subst ho
            simp only [project, ProtocolOp.project, dite_true, Term.denote_op, Process.safeWith_bind]
            refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.given kind r hearers).rename id, τ⟩,
              List.mem_cons_self, rfl, rfl, eventClass_rename_id (.given kind r hearers), typed⟩, fun _ _ => ?_⟩
            exact Process.safeWith_mono M (fun _ _ h => h)
              (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
              (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
          · by_cases hh : r ∈ hearers
            · simp only [project, ProtocolOp.project, dite_eq_right ho, dite_eq_left hh,
                Term.denote_op, Process.safeWith_bind]
              refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.given kind owner hearers).rename id, τ⟩,
                List.mem_cons_self, Ne.symm ho, rfl, rfl, hearers, hh, eventClass_rename_id (.given kind owner hearers)⟩, fun _ _ => ?_⟩
              exact Process.safeWith_mono M (fun _ _ h => h)
                (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
                (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
            · simp only [project, ProtocolOp.project, dite_eq_right ho, dite_eq_right hh,
                Term.denote_op, Process.safeWith_bind]
              exact Process.safeWith_mono M (fun _ _ h => h)
                (fun _ h => matchesShape_mono M r (fun e he => List.mem_cons_of_mem _ he) h)
                (fun _ _ => trivial) (fun _ _ => trivial) (hRest _)
      | @apply hdr callee peers distinct covers operands fits =>
          simp only [project, ProtocolOp.project, Term.denote_op, Process.safeWith_bind]
          let ρ := RoleMap.ofList peers distinct
          have hApp : Frame.applications (path ++ [.application key]) = Frame.applications path ++ [key] := by
            rw [frame_applications_append]; rfl
          have hCall := hCallee hdr callee (ρ.back r) (path ++ [.application key])
            (enterAll M ρ r (fitAllRV M fits (env.all args)))
          rw [hApp] at hCall
          have hMap : ∀ e ∈ hdr.shape.events (Frame.applications path ++ [key]) id,
              ⟨e.site, e.cls.rename ρ.to, e.τ⟩ ∈
                ((shapeOf (.op key (.apply callee peers distinct covers _ fits) args results rest)).events
                  (Frame.applications path) id) := by
            intro e he
            simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append]
            left
            rw [shape_events_map] at he ⊢
            obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
            refine List.mem_map.mpr ⟨e0, he0, ?_⟩
            have hall := hProt hdr (Member.mem callee) e0 he0
            have hCong := eventClass_rename_congr (parts := List.range hdr.roles)
              (f := fun j => peers.getD j j) (g := ρ.to) (fun j hj => by
                have hlt : j < peers.length := covers.symm ▸ List.mem_range.mp hj
                rw [list_getD_of_lt peers j j hlt, RoleMap.ofList_to peers distinct j hlt]) hall
            simp only [eventClass_rename_id]
            exact congrArg (fun c => ShapeEvent.mk _ c e0.τ) hCong
          have hMapped := safeWith_mapR_shape M ρ r _ _ hMap _ hCall
          show Process.SafeWith M _ _ _ _ (Process.map (leaveAll M ρ r) _)
          rw [Process.safeWith_map]
          exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
            (fun ys _ => Process.safeWith_mono M (fun _ _ h => h)
              (fun _ h => matchesShape_mono M r (fun e he => by
                simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append]
                exact .inr he) h)
              (fun _ _ => trivial) (fun _ _ => trivial) (hRest _))
            (fun _ _ => trivial) hMapped
  | _, _, .guard key ps c ok why rest, path, env => by
      by_cases hIn : r ∈ ps
      · simp only [project, dite_eq_left hIn, Term.denote_guard]
        cases asBool M ok.1 (reveal M (ok.2.1 r hIn) (env.get c))
        · trivial
        · exact project_matchesShape r fns roles hProt hCallee rest path env
      · simp only [project, dite_eq_right hIn]
        exact project_matchesShape r fns roles hProt hCallee rest path env
  | _, _, .choose key ps c ok gives onTrue onFalse results rest, path, env => by
      have hRest := fun (ys : HList (RV M r) _) =>
        Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r
            (ev₂ := (shapeOf (.choose key ps c ok gives onTrue onFalse results rest)).events
              (Frame.applications path) id)
            (fun e he => by simp only [shapeOf, Shape.events, List.mem_append]; exact .inr he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys))
      by_cases hIn : r ∈ ps
      · simp only [project, dite_eq_left hIn, Term.denote_choose, Process.safeWith_bind]
        cases asBool M ok.1 (reveal M (ok.2.1 r hIn) (env.get c))
        · exact Process.safeWith_mono M (fun _ _ h => h)
            (fun _ h => matchesShape_mono M r (fun e he => by
              simp only [shapeOf, Shape.events, Shapes.events, List.append_nil, List.mem_append]
              exact .inl (.inr he)) h)
            (fun ys _ => hRest ys) (fun _ _ => trivial)
            (project_matchesShape r fns roles hProt hCallee onFalse path env)
        · exact Process.safeWith_mono M (fun _ _ h => h)
            (fun _ h => matchesShape_mono M r (fun e he => by
              simp only [shapeOf, Shape.events, Shapes.events, List.append_nil, List.mem_append]
              exact .inl (.inl he)) h)
            (fun ys _ => hRest ys) (fun _ _ => trivial)
            (project_matchesShape r fns roles hProt hCallee onTrue path env)
      · simp only [project, dite_eq_right hIn, Term.denote_op, Process.safeWith_bind]
        exact hRest _
  | _, _, .cases key ps x ok gives arms results rest, path, env => by
      have hRest := fun (ys : HList (RV M r) _) =>
        Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r
            (ev₂ := (shapeOf (.cases key ps x ok gives arms results rest)).events
              (Frame.applications path) id)
            (fun e he => by simp only [shapeOf, Shape.events, List.mem_append]; exact .inr he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys))
      by_cases hIn : r ∈ ps
      · simp only [project, dite_eq_left hIn, Term.denote_cases, Process.safeWith_bind]
        exact Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r (fun e he => by
            simp only [shapeOf, Shape.events, List.mem_append]; exact .inl he) h)
          (fun ys _ => hRest ys) (fun _ _ => trivial)
          (projectArms_matchesShape r fns roles hProt hCallee arms path env _)
      · simp only [project, dite_eq_right hIn, Term.denote_op, Process.safeWith_bind]
        exact hRest _
  | _, _, .loop key ps times gives init inputs body results rest, path, env => by
      have hRest := fun (ys : HList (RV M r) _) =>
        Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r
            (ev₂ := (shapeOf (.loop key ps times gives init inputs body results rest)).events
              (Frame.applications path) id)
            (fun e he => by simp only [shapeOf, Shape.events, List.mem_append]; exact .inr he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys))
      by_cases hIn : r ∈ ps
      · simp only [project, dite_eq_left hIn]
        have hLoopStep : ∀ i st,
            ((roleSem M r fns roles).loopStep ps inputs
              (fun at_ inside => (project r body).denote (roleSem M r fns roles) at_ inside)
              key path env i st).SafeWith M (fun _ _ => True)
              (ROp.MatchesShape M r ((shapeOf body).events (Frame.applications path) id))
              (fun _ => True) (fun _ => True) := by
          intro i st
          simp only [Semantics.loopStep]
          rw [Process.safeWith_bind]
          have hApp : Frame.applications (path ++ [.iteration key i]) = Frame.applications path := by
            rw [frame_applications_append]; simp [Frame.applications]
          have hb := project_matchesShape r fns roles hProt hCallee body (path ++ [.iteration key i])
            (env.extend inputs (.cons ((roleSem M r fns roles).index ps i) st.1))
          rwa [hApp] at hb
        cases times with
        | fixed n =>
            simp only [projectLoop]
            erw [Term.denote_loop, Process.safeWith_bind]
            exact Process.safeWith_mono M (fun _ _ h => h)
              (fun _ h => matchesShape_mono M r (fun e he => by
                simp only [shapeOf, Shape.events, List.mem_append]; exact .inl he) h)
              (fun st _ => hRest _) (fun _ _ => trivial)
              (iterate_safeWith_true M hLoopStep _ 0 _)
        | value c ok =>
            simp only [projectLoop]
            erw [Term.denote_loop, Process.safeWith_bind]
            exact Process.safeWith_mono M (fun _ _ h => h)
              (fun _ h => matchesShape_mono M r (fun e he => by
                simp only [shapeOf, Shape.events, List.mem_append]; exact .inl he) h)
              (fun st _ => hRest _) (fun _ _ => trivial)
              (iterate_safeWith_true M hLoopStep _ 0 _)
      · simp only [project, dite_eq_right hIn, Term.denote_op, Process.safeWith_bind]
        exact hRest _
  | _, _, .block key number body results rest, path, env => by
      simp only [project, Term.denote_block, Process.safeWith_bind]
      have hApp : Frame.applications (path ++ [.iteration key number]) = Frame.applications path := by
        rw [frame_applications_append]; simp [Frame.applications]
      have hb := project_matchesShape r fns roles hProt hCallee body (path ++ [.iteration key number]) env
      rw [hApp] at hb
      exact Process.safeWith_mono M (fun _ _ h => h)
        (fun _ h => matchesShape_mono M r (fun e he => by
          simp only [shapeOf, Shape.events, List.mem_append]; exact .inl he) h)
        (fun ys _ => Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r (fun e he => by
            simp only [shapeOf, Shape.events, List.mem_append]; exact .inr he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys)))
        (fun _ _ => trivial) hb
  | _, _, .attempt key w owns inputs body results rest, path, env => by
      simp only [project, Term.denote_attempt, Process.safeWith_bind]
      have hBeg : ((roleSem M r fns roles).begin w key path).SafeWith M (fun _ _ => True)
          (ROp.MatchesShape M r ((shapeOf (.attempt key w owns inputs body results rest)).events
            (Frame.applications path) id)) (fun _ => True) (fun _ => True) := by
        show Process.SafeWith M _ _ _ _ (if r ∈ w then _ else _)
        split
        · exact ⟨trivial, fun _ _ => trivial⟩
        · trivial
      have hSet : ((roleSem M r fns roles).settle w key path).SafeWith M (fun _ _ => True)
          (ROp.MatchesShape M r ((shapeOf (.attempt key w owns inputs body results rest)).events
            (Frame.applications path) id)) (fun _ => True) (fun _ => True) := by
        show Process.SafeWith M _ _ _ _ (if r ∈ w then _ else _)
        split
        · exact ⟨trivial, fun _ _ => trivial⟩
        · trivial
      exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
        (fun n _ =>
          Process.safeWith_mono M (fun _ _ h => h)
            (fun _ h => matchesShape_mono M r (fun e he => by
              simp only [shapeOf, Shape.events, List.mem_append]; exact .inl he) h)
            (fun ys _ =>
              Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h)
                (fun _ _ => Process.safeWith_mono M (fun _ _ h => h)
                  (fun _ h => matchesShape_mono M r (fun e he => by
                    simp only [shapeOf, Shape.events, List.mem_append]; exact .inr he) h)
                  (fun _ _ => trivial) (fun _ _ => trivial)
                  (project_matchesShape r fns roles hProt hCallee rest path (env.extend results ys)))
                (fun _ _ => trivial) hSet)
            (fun _ _ => trivial)
            (project_matchesShape r fns roles hProt hCallee body path (env.extend inputs (.cons n .nil))))
        (fun _ _ => trivial) hBeg
where
  projectArms_matchesShape {hs : Headers V} (r : Role)
      (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
      (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles))
      (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (j : Role) (path : List Frame)
        (args : HList (RV M j) hdr.ins),
        (roles hdr callee j path args).SafeWith M (fun _ _ => True)
          (ROp.MatchesShape M j (hdr.shape.events (Frame.applications path) id))
          (fun _ => True) (fun _ => True)) :
      ∀ {Γ mid payloads} (arms : Arms (protocolDialect V hs) Γ mid payloads)
        (path : List Frame) (env : Env (RV M r) Γ) (p : Pick (RV M r) payloads),
        ((projectArms r arms).denote (roleSem M r fns roles) path env p).SafeWith M (fun _ _ => True)
          (ROp.MatchesShape M r ((shapesOf arms).events (Frame.applications path) id))
          (fun _ => True) (fun _ => True)
    | _, _, _, .nil, _, _, p => nomatch p
    | _, _, _, .cons inputs arm _, path, env, .here v =>
        Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r (fun e he => by
            simp only [shapesOf, Shapes.events, List.mem_append]; exact .inl he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (project_matchesShape r fns roles hProt hCallee arm path (env.extend inputs (.cons v .nil)))
    | _, _, _, .cons _ _ rest, path, env, .there p =>
        Process.safeWith_mono M (fun _ _ h => h)
          (fun _ h => matchesShape_mono M r (fun e he => by
            simp only [shapesOf, Shapes.events, List.mem_append]; exact .inr he) h)
          (fun _ _ => trivial) (fun _ _ => trivial)
          (projectArms_matchesShape r fns roles hProt hCallee rest path env p)

private theorem defs_rTable_matchesShape :
    ∀ {hs : Headers V} (defs : Defs V hs),
      (∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles)) ∧
      (∀ hdr (callee : Member hs.protocols hdr) (r : Role) (path : List Frame)
        (args : HList (RV M r) hdr.ins),
        (Defs.rTable M defs hdr callee r path args).SafeWith M (fun _ _ => True)
          (ROp.MatchesShape M r (hdr.shape.events (Frame.applications path) id))
          (fun _ => True) (fun _ => True))
  | _, .nil => ⟨(fun _ h => nomatch h), (fun _ p => nomatch p)⟩
  | _, .fn _ _ _ _ rest _ => defs_rTable_matchesShape rest
  | _, .protocol hdr inputs body ok rest => by
      have ⟨hProt, hCallee⟩ := defs_rTable_matchesShape rest
      have hHeadProt : ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles) := by
        rw [ok.shaped]
        exact shape_events_within hProt body ok.within
      refine ⟨fun h hm => ?_, fun _ callee r path args => ?_⟩
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact hHeadProt
        · exact hProt h hm
      · cases callee with
        | head =>
            rw [ok.shaped]
            exact project_matchesShape M r (Defs.fnTable M rest) (Defs.rTable M rest)
              hProt hCallee body path (Env.empty.extend inputs args)
        | tail callee => exact hCallee _ callee r path args

unseal roleMeaning in
/-- Every non-attempt effect emitted by a role program (even against arbitrary replies!) matches
an event of `hdr.shape.events (Frame.applications path) id`. -/
theorem roleMeaning_matchesShape (p : Typed V) {hdr : ProtocolHeader V}
    (callee : Member p.headers.protocols hdr) (r : Role) (path : List Frame)
    (args : HList (RV M r) hdr.ins) :
    (roleMeaning M p callee r path args).SafeWith M (fun _ _ => True)
      (ROp.MatchesShape M r (hdr.shape.events (Frame.applications path) id))
      (fun _ => True) (fun _ => True) :=
  (defs_rTable_matchesShape M p.defs).2 hdr callee r path args

/-- A single protocol-level effect matches a `ShapeEvent`. -/
def GOp.MatchesShape (events : List (ShapeEvent V)) : GOp M → Prop
  | .flow kind giver getters at_ τ _ =>
      ∃ e ∈ events, e.site = at_.site ∧ e.τ = τ ∧ e.cls = .flow kind giver getters
  | .given kind owner hearers at_ _ _ τ =>
      ∃ e ∈ events, e.site = at_.site ∧ e.τ = τ ∧ e.cls = .given kind owner hearers

/-- Every effect emitted along a protocol process matches an event in `events`. -/
def Protocol.MatchesShape {A : Type} (events : List (ShapeEvent V)) : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call op k => GOp.MatchesShape M events op ∧ ∀ v, Protocol.MatchesShape events (k v)

private theorem protocol_matchesShape_mono {A : Type} {ev₁ ev₂ : List (ShapeEvent V)}
    (hSub : ∀ e ∈ ev₁, e ∈ ev₂) : ∀ {p : Protocol M A},
    Protocol.MatchesShape M ev₁ p → Protocol.MatchesShape M ev₂ p
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.flow ..) _, ⟨⟨e, he, hm⟩, hk⟩ =>
      ⟨⟨e, hSub e he, hm⟩, fun v => protocol_matchesShape_mono hSub (hk v)⟩
  | .call (.given ..) _, ⟨⟨e, he, hm⟩, hk⟩ =>
      ⟨⟨e, hSub e he, hm⟩, fun v => protocol_matchesShape_mono hSub (hk v)⟩

private theorem protocol_matchesShape_bind {A B : Type} {events : List (ShapeEvent V)} :
    ∀ (p : Protocol M A) (f : A → Protocol M B),
      Protocol.MatchesShape M events p → (∀ a, Protocol.MatchesShape M events (f a)) →
      Protocol.MatchesShape M events (p.bind f)
  | .done a, _, _, hf => hf a
  | .halt _, _, _, _ => trivial
  | .call _ k, f, ⟨ho, hk⟩, hf => ⟨ho, fun v => protocol_matchesShape_bind (k v) f (hk v) hf⟩

private theorem protocol_matchesShape_map {A B : Type} {events : List (ShapeEvent V)} (g : A → B) :
    ∀ (p : Protocol M A), Protocol.MatchesShape M events p → Protocol.MatchesShape M events (p.map g)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call _ k, ⟨ho, hk⟩ => ⟨ho, fun v => protocol_matchesShape_map g (k v) (hk v)⟩

private theorem protocol_matchesShape_liftLocal {A : Type} {events : List (ShapeEvent V)}
    (who : List Role) : ∀ (p : Local A), Protocol.MatchesShape M events (liftLocal (fun w => (who, w)) p)
  | .done _ => trivial
  | .halt _ => trivial
  | .call op _ => nomatch op

private theorem protocol_matchesShape_mapG {A : Type} (ρ : Role → Role)
    {ev₁ ev₂ : List (ShapeEvent V)}
    (hMap : ∀ e ∈ ev₁, ⟨e.site, e.cls.rename ρ, e.τ⟩ ∈ ev₂) :
    ∀ (p : Protocol M A), Protocol.MatchesShape M ev₁ p → Protocol.MatchesShape M ev₂ (mapG M ρ p)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.flow ..) k, ⟨⟨e, he, hSite, hTy, hCls⟩, hk⟩ =>
      ⟨⟨⟨e.site, e.cls.rename ρ, e.τ⟩, hMap e he, hSite, hTy, by simp [hCls, EventClass.rename]⟩,
        fun v => protocol_matchesShape_mapG ρ hMap (k v) (hk v)⟩
  | .call (.given ..) k, ⟨⟨e, he, hSite, hTy, hCls⟩, hk⟩ =>
      ⟨⟨⟨e.site, e.cls.rename ρ, e.τ⟩, hMap e he, hSite, hTy, by simp [hCls, EventClass.rename]⟩,
        fun v => protocol_matchesShape_mapG ρ hMap (k v) (hk v)⟩

private theorem protocol_matchesShape_iterate {σ : Type} {events : List (ShapeEvent V)}
    {step : Nat → σ → Protocol M σ}
    (hstep : ∀ i s, Protocol.MatchesShape M events (step i s)) :
    ∀ (n i : Nat) (s : σ), Protocol.MatchesShape M events (Process.iterate n step i s)
  | 0, _, _ => trivial
  | n + 1, i, s =>
      protocol_matchesShape_bind M (step i s) _ (hstep i s) fun s' =>
        protocol_matchesShape_iterate hstep n (i + 1) s'

private theorem term_observe_matchesShape {hs : Headers V}
    (fns : FnTable M hs.fns) (gTable : GTable M hs.protocols)
    (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles))
    (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (path : List Frame)
      (args : HList (LVal M) hdr.ins),
      Protocol.MatchesShape M (hdr.shape.events (Frame.applications path) id)
        (gTable hdr callee path args)) :
    ∀ {Γ outs} (t : Term (protocolDialect V hs) Γ outs) (path : List Frame) (env : Env (LVal M) Γ),
      Protocol.MatchesShape M ((shapeOf t).events (Frame.applications path) id)
        (Term.observe M fns gTable t path env)
  | _, _, .ret _, _, _ => trivial
  | _, _, .op key o args results rest, path, env => by
      have hRest := fun ys => term_observe_matchesShape fns gTable hProt hCallee rest path
        (env.extend results ys)
      cases o with
      | compute R op operands types held =>
          simp only [Term.observe, observeOp, protocolOp]
          exact protocol_matchesShape_bind M _ _
            (protocol_matchesShape_map M _ _ (protocol_matchesShape_liftLocal M R _)) (fun _ => hRest _)
      | narrow R among =>
          obtain ⟨x, rfl⟩ := HList.one args
          simp only [Term.observe, observeOp, protocolOp]
          exact hRest _
      | flow kind giver getters holds unique =>
          obtain ⟨x, rfl⟩ := HList.one args
          simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
          refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.flow kind giver getters).rename id, _⟩,
            List.mem_cons_self, rfl, rfl, eventClass_rename_id (.flow kind giver getters)⟩, fun _ => ?_⟩
          exact protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => List.mem_cons_of_mem _ he) (hRest _))
      | given kind owner hearers operands τ typed held unique =>
          cases kind with
          | coin law =>
              cases hearers with
              | nil =>
                  simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
                  refine ⟨⟨⟨⟨Frame.applications path, key⟩, (EventClass.given (.coin law) owner []).rename id, τ⟩,
                    List.mem_cons_self, rfl, rfl, eventClass_rename_id (.given (.coin law) owner [])⟩, fun _ => ?_⟩
                  exact protocol_matchesShape_mono M (fun e he => List.mem_cons_of_mem _ he) (hRest _)
              | cons h0 hs0 =>
                  simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
                  refine ⟨⟨⟨⟨Frame.applications path, key⟩,
                      (EventClass.given (.coin law) owner (h0 :: hs0)).rename id, τ⟩,
                    List.mem_cons_self, rfl, rfl, eventClass_rename_id (.given (.coin law) owner (h0 :: hs0))⟩, fun _ => ?_⟩
                  exact protocol_matchesShape_map M _ _
                    (protocol_matchesShape_mono M (fun e he => List.mem_cons_of_mem _ he) (hRest _))
          | request service =>
              simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
              refine ⟨⟨⟨⟨Frame.applications path, key⟩,
                  (EventClass.given (.request service) owner hearers).rename id, τ⟩,
                List.mem_cons_self, rfl, rfl, eventClass_rename_id (.given (.request service) owner hearers)⟩, fun _ => ?_⟩
              exact protocol_matchesShape_map M _ _
                (protocol_matchesShape_mono M (fun e he => List.mem_cons_of_mem _ he) (hRest _))
      | @apply hdr callee peers distinct covers operands fits =>
          simp only [Term.observe, observeOp]
          let ρ := RoleMap.ofList peers distinct
          have hApp : Frame.applications (path ++ [.application key]) = Frame.applications path ++ [key] := by
            rw [frame_applications_append]; rfl
          have hCall := hCallee hdr callee (path ++ [.application key])
            (unmapAll M ρ.to (fitAll M fits (env.all args)))
          rw [hApp] at hCall
          have hMap : ∀ e ∈ hdr.shape.events (Frame.applications path ++ [key]) id,
              ⟨e.site, e.cls.rename ρ.to, e.τ⟩ ∈
                ((shapeOf (.op key (.apply callee peers distinct covers _ fits) args results rest)).events
                  (Frame.applications path) id) := by
            intro e he
            simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append]
            left
            rw [shape_events_map] at he ⊢
            obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
            refine List.mem_map.mpr ⟨e0, he0, ?_⟩
            have hall := hProt hdr (Member.mem callee) e0 he0
            have hCong := eventClass_rename_congr (parts := List.range hdr.roles)
              (f := fun j => peers.getD j j) (g := ρ.to) (fun j hj => by
                have hlt : j < peers.length := covers.symm ▸ List.mem_range.mp hj
                rw [list_getD_of_lt peers j j hlt, RoleMap.ofList_to peers distinct j hlt]) hall
            simp only [eventClass_rename_id]
            exact congrArg (fun c => ShapeEvent.mk _ c e0.τ) hCong
          exact protocol_matchesShape_bind M _ _
            (protocol_matchesShape_mapG M ρ.to hMap _ hCall)
            (fun ys => protocol_matchesShape_map M _ _
              (protocol_matchesShape_mono M (fun e he => by
                simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append]; exact .inr he) (hRest _)))
  | _, _, .guard key ps c ok why rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      cases asBool M ok.1 (env.get c)
      · trivial
      · exact term_observe_matchesShape fns gTable hProt hCallee rest path env
  | _, _, .choose key ps c ok gives onTrue onFalse results rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      cases asBool M ok.1 (env.get c)
      · exact protocol_matchesShape_bind M _ _
          (protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => by
              simp only [Shapes.events, List.mem_append]; exact .inl (.inr (.inl he)))
              (term_observe_matchesShape fns gTable hProt hCallee onFalse path env)))
          (fun out => protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
              (term_observe_matchesShape fns gTable hProt hCallee rest path (env.extend results out.1))))
      · exact protocol_matchesShape_bind M _ _
          (protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => by
              simp only [Shapes.events, List.mem_append]; exact .inl (.inl he))
              (term_observe_matchesShape fns gTable hProt hCallee onTrue path env)))
          (fun out => protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
              (term_observe_matchesShape fns gTable hProt hCallee rest path (env.extend results out.1))))
  | _, _, .cases key ps s ok gives arms results rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      exact protocol_matchesShape_bind M _ _
        (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inl he))
          (observeArms_matchesShape fns gTable hProt hCallee arms path env
            ((protocolSem M fns gTable).pick ok (env.get s))))
        (fun out => protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
            (term_observe_matchesShape fns gTable hProt hCallee rest path (env.extend results out.1))))
  | _, _, .loop key ps times ok carried inputs body results rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      refine protocol_matchesShape_bind M _ _
        (protocol_matchesShape_iterate M (fun i st =>
          protocol_matchesShape_map M _ _
            (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inl he))
              (by
                have hBody := term_observe_matchesShape fns gTable hProt hCallee body
                  (path ++ [.iteration key i]) (env.extend inputs (.cons i st.1.1))
                have hApp : Frame.applications (path ++ [.iteration key i]) = Frame.applications path := by
                  rw [frame_applications_append]; simp [Frame.applications]
                rwa [hApp] at hBody))) _ 0 _)
        (fun out => protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
            (term_observe_matchesShape fns gTable hProt hCallee rest path _)))
  | _, _, .block key number body results rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      have hApp : Frame.applications (path ++ [.iteration key number]) = Frame.applications path := by
        rw [frame_applications_append]; simp [Frame.applications]
      have hBody := term_observe_matchesShape fns gTable hProt hCallee body
        (path ++ [.iteration key number]) env
      rw [hApp] at hBody
      exact protocol_matchesShape_bind M _ _
        (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inl he)) hBody)
        (fun out => protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
            (term_observe_matchesShape fns gTable hProt hCallee rest path (env.extend results out.1))))
  | _, _, .attempt key ps ok inputs body results rest, path, env => by
      simp only [Term.observe, shapeOf, Shape.events]
      exact protocol_matchesShape_bind M _ _
        (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inl he))
          (term_observe_matchesShape fns gTable hProt hCallee body path (env.extend inputs (.cons 0 .nil))))
        (fun out => protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => List.mem_append.mpr (.inr he))
            (term_observe_matchesShape fns gTable hProt hCallee rest path (env.extend results out.1))))
where
  observeArms_matchesShape {hs : Headers V}
      (fns : FnTable M hs.fns) (gTable : GTable M hs.protocols)
      (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, e.cls.AllIn (List.range hdr.roles))
      (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (path : List Frame)
        (args : HList (LVal M) hdr.ins),
        Protocol.MatchesShape M (hdr.shape.events (Frame.applications path) id)
          (gTable hdr callee path args)) :
      ∀ {Γ mid payloads} (arms : Arms (protocolDialect V hs) Γ mid payloads)
        (path : List Frame) (env : Env (LVal M) Γ) (p : Pick (LVal M) payloads),
        Protocol.MatchesShape M ((shapesOf arms).events (Frame.applications path) id)
          (Arms.observe M fns gTable arms path env p)
    | _, _, _, .nil, _, _, p => nomatch p
    | _, _, _, .cons inputs arm _, path, env, .here v =>
        protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => by
            simp only [shapesOf, Shapes.events, List.mem_append]; exact .inl he)
            (term_observe_matchesShape fns gTable hProt hCallee arm path (env.extend inputs (.cons v .nil))))
    | _, _, _, .cons _ _ rest, path, env, .there p =>
        protocol_matchesShape_map M _ _
          (protocol_matchesShape_mono M (fun e he => by
            simp only [shapesOf, Shapes.events, List.mem_append]; exact .inr he)
            (observeArms_matchesShape fns gTable hProt hCallee rest path env p))

private theorem defs_gTable_matchesShape :
    ∀ {hs : Headers V} (defs : Defs V hs) (hdr : ProtocolHeader V)
      (callee : Member hs.protocols hdr) (path : List Frame) (args : HList (LVal M) hdr.ins),
      Protocol.MatchesShape M (hdr.shape.events (Frame.applications path) id)
        (Defs.gTable M defs hdr callee path args)
  | _, .nil, _, p, _, _ => nomatch p
  | _, .fn _ _ _ _ rest _, hdr, callee, path, args => defs_gTable_matchesShape rest hdr callee path args
  | _, .protocol hdr inputs body ok rest, _, callee, path, args => by
      cases callee with
      | head =>
          have hObs := term_observe_matchesShape M (Defs.fnTable M rest) (Defs.gTable M rest)
            (defs_rTable_matchesShape M rest).1 (defs_gTable_matchesShape rest) body path
            (Env.empty.extend inputs args)
          rw [ok.shaped]
          exact protocol_matchesShape_map M _ _ hObs
      | tail callee => exact defs_gTable_matchesShape rest _ callee path args

unseal protocolMeaning in
/-- Every effect emitted along a protocol process matches an event of
`hdr.shape.events (Frame.applications path) id`. -/
theorem protocolMeaning_matchesShape (p : Typed V) {hdr : ProtocolHeader V}
    (callee : Member p.headers.protocols hdr) (path : List Frame)
    (args : HList (LVal M) hdr.ins) :
    Protocol.MatchesShape M (hdr.shape.events (Frame.applications path) id)
      (protocolMeaning M p callee path args) :=
  defs_gTable_matchesShape M p.defs hdr callee path args

end ShapeMatch

/-! ## `protocolMeaning_uniqueOccs`: no occurrence is emitted twice along any run -/

section UniqueOccs

/-- Occurrence of a protocol-level event. -/
def GOp.occurrence : GOp M → Occurrence
  | .flow _ _ _ at_ _ _ => at_
  | .given _ _ _ at_ _ _ _ => at_

/-- Every event occurrence along a protocol process satisfies `P`. -/
def Protocol.OccsIn {A : Type} (P : Occurrence → Prop) : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call op k => P (GOp.occurrence M op) ∧ ∀ v, Protocol.OccsIn P (k v)

/-- Along every execution path of a protocol process, no occurrence is emitted twice. -/
def Protocol.UniqueOccs {A : Type} : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call op k =>
      ∀ v, Protocol.OccsIn M (· ≠ GOp.occurrence M op) (k v) ∧ Protocol.UniqueOccs (k v)

theorem Protocol.occsIn_mono {A : Type} {P Q : Occurrence → Prop}
    (h : ∀ at_, P at_ → Q at_) : ∀ {p : Protocol M A},
    Protocol.OccsIn M P p → Protocol.OccsIn M Q p
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call _ _, ⟨ho, hk⟩ => ⟨h _ ho, fun v => Protocol.occsIn_mono h (hk v)⟩

theorem Protocol.occsIn_bind {A B : Type} {P : Occurrence → Prop} :
    ∀ (p : Protocol M A) (f : A → Protocol M B),
      Protocol.OccsIn M P p → (∀ a, Protocol.OccsIn M P (f a)) →
      Protocol.OccsIn M P (p.bind f)
  | .done a, _, _, hf => hf a
  | .halt _, _, _, _ => trivial
  | .call _ k, f, ⟨ho, hk⟩, hf => ⟨ho, fun v => Protocol.occsIn_bind (k v) f (hk v) hf⟩

theorem Protocol.occsIn_map {A B : Type} {P : Occurrence → Prop} (g : A → B) :
    ∀ (p : Protocol M A), Protocol.OccsIn M P p → Protocol.OccsIn M P (p.map g)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call _ k, ⟨ho, hk⟩ => ⟨ho, fun v => Protocol.occsIn_map g (k v) (hk v)⟩

theorem Protocol.occsIn_mapG {A : Type} {P : Occurrence → Prop} (ρ : Role → Role) :
    ∀ (p : Protocol M A), Protocol.OccsIn M P p → Protocol.OccsIn M P (mapG M ρ p)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.flow ..) k, ⟨ho, hk⟩ => ⟨ho, fun v => Protocol.occsIn_mapG ρ (k v) (hk v)⟩
  | .call (.given ..) k, ⟨ho, hk⟩ => ⟨ho, fun v => Protocol.occsIn_mapG ρ (k v) (hk v)⟩

theorem Protocol.uniqueOccs_bind {A B : Type} {P Q : Occurrence → Prop}
    (hDisj : ∀ at_, P at_ → Q at_ → False) :
    ∀ (p : Protocol M A) (f : A → Protocol M B),
      Protocol.OccsIn M P p → Protocol.UniqueOccs M p →
      (∀ a, Protocol.OccsIn M Q (f a) ∧ Protocol.UniqueOccs M (f a)) →
      Protocol.UniqueOccs M (p.bind f)
  | .done a, _, _, _, hf => (hf a).2
  | .halt _, _, _, _, _ => trivial
  | .call op k, f, ⟨hp, hkp⟩, hku, hf => fun v =>
      ⟨Protocol.occsIn_bind M (k v) f (hku v).1
          (fun a => Protocol.occsIn_mono M (fun at_ hq (heq : at_ = GOp.occurrence M op) =>
            hDisj _ (heq.symm ▸ hp) hq) (hf a).1),
       Protocol.uniqueOccs_bind hDisj (k v) f (hkp v) (hku v).2 hf⟩

theorem Protocol.uniqueOccs_map {A B : Type} (g : A → B) :
    ∀ (p : Protocol M A), Protocol.UniqueOccs M p → Protocol.UniqueOccs M (p.map g)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call _ k, h => fun v =>
      ⟨Protocol.occsIn_map M g (k v) (h v).1, Protocol.uniqueOccs_map g (k v) (h v).2⟩

theorem Protocol.uniqueOccs_mapG {A : Type} (ρ : Role → Role) :
    ∀ (p : Protocol M A), Protocol.UniqueOccs M p → Protocol.UniqueOccs M (mapG M ρ p)
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.flow ..) k, h => fun v =>
      ⟨Protocol.occsIn_mapG M ρ (k v) (h v).1, Protocol.uniqueOccs_mapG ρ (k v) (h v).2⟩
  | .call (.given ..) k, h => fun v =>
      ⟨Protocol.occsIn_mapG M ρ (k v) (h v).1, Protocol.uniqueOccs_mapG ρ (k v) (h v).2⟩

private def blockFrames (blocks : List (Key × Nat)) : List Frame :=
  blocks.map fun p => Frame.iteration p.1 p.2

/-- An occurrence `occ` originates from an instruction address `(bs, k)` in `addrs` under base
path `base`: either directly at `⟨base ++ blockFrames bs, k⟩` or inside a loop/application at
`(bs, k)`. -/
private def OccUnder (base : List Frame) (addrs : List (List (Key × Nat) × Key))
    (occ : Occurrence) : Prop :=
  ∃ bs k, (bs, k) ∈ addrs ∧
    (occ = ⟨base ++ blockFrames bs, k⟩ ∨
     ∃ tail, occ.path = base ++ blockFrames bs ++ .application k :: tail ∨
       ∃ i, occ.path = base ++ blockFrames bs ++ .iteration k i :: tail)

private theorem blockFrames_append (bs₁ bs₂ : List (Key × Nat)) :
    blockFrames (bs₁ ++ bs₂) = blockFrames bs₁ ++ blockFrames bs₂ :=
  List.map_append

private theorem occUnder_mono {base : List Frame} {a₁ a₂ : List (List (Key × Nat) × Key)}
    (h : ∀ x ∈ a₁, x ∈ a₂) {occ : Occurrence} (ho : OccUnder base a₁ occ) : OccUnder base a₂ occ := by
  obtain ⟨bs, k, hmem, hform⟩ := ho
  exact ⟨bs, k, h _ hmem, hform⟩

private theorem list_eq_append_head_ne {α : Type} :
    ∀ {p : List α} {a b : α} {t₁ t₂ : List α}, p ++ a :: t₁ = p ++ b :: t₂ → a = b
  | [], _, _, _, _, h => (List.cons.inj h).1
  | _ :: _, _, _, _, _, h => list_eq_append_head_ne (List.cons.inj h).2

private theorem occUnder_disjoint {base : List Frame}
    {a₁ a₂ : List (List (Key × Nat) × Key)} {bKeys : List Key}
    (hDisj : ∀ x ∈ a₁, x ∉ a₂)
    (hBlk : ∀ bk ∈ bKeys, ∀ x ∈ a₁ ++ a₂, x.2 ≠ bk)
    (hInB : ∀ x ∈ a₁ ++ a₂, ∀ p ∈ x.1, p.1 ∈ bKeys) :
    ∀ occ, OccUnder base a₁ occ → OccUnder base a₂ occ → False := by
  intro occ ⟨bs₁, k₁, h1, hf1⟩ ⟨bs₂, k₂, h2, hf2⟩
  have hnePair : (bs₁, k₁) ≠ (bs₂, k₂) := fun heq => hDisj _ h1 (heq ▸ h2)
  have hPrefCmp : ∀ (l₁ l₂ : List (Key × Nat)),
      (∀ p ∈ l₁, p.1 ∈ bKeys) → (∀ p ∈ l₂, p.1 ∈ bKeys) →
      (l₁ = l₂) ∨
      (∃ pre a b r₁ r₂, l₁ = pre ++ a :: r₁ ∧ l₂ = pre ++ b :: r₂ ∧ a ≠ b) ∨
      (∃ a r, l₂ = l₁ ++ a :: r ∧ a.1 ∈ bKeys) ∨
      (∃ a r, l₁ = l₂ ++ a :: r ∧ a.1 ∈ bKeys) := by
    intro l₁
    induction l₁ with
    | nil =>
        intro l₂ _ hb2
        cases l₂ with
        | nil => exact .inl rfl
        | cons a r => exact .inr (.inr (.inl ⟨a, r, rfl, hb2 a List.mem_cons_self⟩))
    | cons x xs ih =>
        intro l₂ hb1 hb2
        cases l₂ with
        | nil => exact .inr (.inr (.inr ⟨x, xs, rfl, hb1 x List.mem_cons_self⟩))
        | cons y ys =>
            by_cases hxy : x = y
            · subst hxy
              rcases ih ys (fun p hp => hb1 p (List.mem_cons_of_mem _ hp))
                  (fun p hp => hb2 p (List.mem_cons_of_mem _ hp)) with
                rfl | ⟨pre, a, b, r₁, r₂, h1', h2', hab⟩ | ⟨a, r, h', ha⟩ | ⟨a, r, h', ha⟩
              · exact .inl rfl
              · exact .inr (.inl ⟨x :: pre, a, b, r₁, r₂, by simp [h1'], by simp [h2'], hab⟩)
              · exact .inr (.inr (.inl ⟨a, r, by simp [h'], ha⟩))
              · exact .inr (.inr (.inr ⟨a, r, by simp [h'], ha⟩))
            · exact .inr (.inl ⟨[], x, y, xs, ys, rfl, rfl, hxy⟩)
  have hPathOf : ∀ {bs : List (Key × Nat)} {k : Key},
      (occ = ⟨base ++ blockFrames bs, k⟩ ∨
        ∃ tail, occ.path = base ++ blockFrames bs ++ .application k :: tail ∨
          ∃ i, occ.path = base ++ blockFrames bs ++ .iteration k i :: tail) →
      (occ.path = base ++ blockFrames bs ∧ occ.key = k) ∨
      (∃ f tail, occ.path = base ++ blockFrames bs ++ f :: tail ∧
        (f = .application k ∨ ∃ i, f = .iteration k i)) := by
    rintro bs k (rfl | ⟨tail, hp | ⟨i, hp⟩⟩)
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨.application k, tail, hp, .inl rfl⟩
    · exact .inr ⟨.iteration k i, tail, hp, .inr ⟨i, rfl⟩⟩
  have hp1 := hPathOf hf1
  have hp2 := hPathOf hf2
  rcases hPrefCmp bs₁ bs₂ (hInB _ (List.mem_append_left _ h1)) (hInB _ (List.mem_append_right _ h2)) with
    rfl | ⟨pre, a, b, r₁, r₂, hbs1, hbs2, hab⟩ | ⟨a, r, hbs2, ha⟩ | ⟨a, r, hbs1, ha⟩
  · have hkne : k₁ ≠ k₂ := fun hk => hnePair (by rw [hk])
    rcases hp1 with ⟨p1, e1⟩ | ⟨f1, t1, p1, hfk1⟩ <;> rcases hp2 with ⟨p2, e2⟩ | ⟨f2, t2, p2, hfk2⟩
    · exact hkne (e1.symm.trans e2)
    · have hlen := congrArg List.length (p1.symm.trans p2)
      simp only [List.length_append, List.length_cons] at hlen; omega
    · have hlen := congrArg List.length (p1.symm.trans p2)
      simp only [List.length_append, List.length_cons] at hlen; omega
    · have hfeq := list_eq_append_head_ne (p1.symm.trans p2)
      rcases hfk1 with rfl | ⟨_, rfl⟩ <;> rcases hfk2 with rfl | ⟨_, rfl⟩ <;> cases hfeq
      · exact hkne rfl
      · exact hkne rfl
  · have hEq : ∀ (bs : List (Key × Nat)) (suf : List Frame),
        occ.path = base ++ blockFrames bs ++ suf →
        ∀ pre' x r', bs = pre' ++ x :: r' →
        ∃ suf', occ.path = (base ++ blockFrames pre') ++ Frame.iteration x.1 x.2 :: suf' := by
      intro bs suf hp pre' x r' hbs
      subst hbs
      rw [blockFrames_append] at hp
      refine ⟨blockFrames r' ++ suf, ?_⟩
      simpa [blockFrames, List.append_assoc] using hp
    have hA : ∃ s₁, occ.path = (base ++ blockFrames pre) ++ Frame.iteration a.1 a.2 :: s₁ := by
      rcases hp1 with ⟨p1, _⟩ | ⟨f1, t1, p1, _⟩
      · exact hEq bs₁ [] (by simpa using p1) pre a r₁ hbs1
      · exact hEq bs₁ (f1 :: t1) p1 pre a r₁ hbs1
    have hB : ∃ s₂, occ.path = (base ++ blockFrames pre) ++ Frame.iteration b.1 b.2 :: s₂ := by
      rcases hp2 with ⟨p2, _⟩ | ⟨f2, t2, p2, _⟩
      · exact hEq bs₂ [] (by simpa using p2) pre b r₂ hbs2
      · exact hEq bs₂ (f2 :: t2) p2 pre b r₂ hbs2
    obtain ⟨s₁, hs1⟩ := hA
    obtain ⟨s₂, hs2⟩ := hB
    have hfeq := list_eq_append_head_ne (hs1.symm.trans hs2)
    injection hfeq with h1 h2
    exact hab (Prod.ext h1 h2)
  · have hB : ∃ s₂, occ.path = (base ++ blockFrames bs₁) ++ Frame.iteration a.1 a.2 :: s₂ := by
      rcases hp2 with ⟨p2, _⟩ | ⟨f2, t2, p2, _⟩
      · rw [hbs2, blockFrames_append] at p2
        exact ⟨blockFrames r, by simpa [blockFrames, List.append_assoc] using p2⟩
      · rw [hbs2, blockFrames_append] at p2
        exact ⟨blockFrames r ++ f2 :: t2, by simpa [blockFrames, List.append_assoc] using p2⟩
    obtain ⟨s₂, hs2⟩ := hB
    rcases hp1 with ⟨p1, _⟩ | ⟨f1, t1, p1, hfk1⟩
    · have hlen := congrArg List.length (p1.symm.trans hs2)
      simp only [List.length_append, List.length_cons] at hlen; omega
    · have hfeq := list_eq_append_head_ne (p1.symm.trans hs2)
      rcases hfk1 with rfl | ⟨_, rfl⟩
      · cases hfeq
      · injection hfeq with hkeq _
        exact hBlk a.1 ha (bs₁, k₁) (List.mem_append_left _ h1) hkeq
  · have hA : ∃ s₁, occ.path = (base ++ blockFrames bs₂) ++ Frame.iteration a.1 a.2 :: s₁ := by
      rcases hp1 with ⟨p1, _⟩ | ⟨f1, t1, p1, _⟩
      · rw [hbs1, blockFrames_append] at p1
        exact ⟨blockFrames r, by simpa [blockFrames, List.append_assoc] using p1⟩
      · rw [hbs1, blockFrames_append] at p1
        exact ⟨blockFrames r ++ f1 :: t1, by simpa [blockFrames, List.append_assoc] using p1⟩
    obtain ⟨s₁, hs1⟩ := hA
    rcases hp2 with ⟨p2, _⟩ | ⟨f2, t2, p2, hfk2⟩
    · have hlen := congrArg List.length (p2.symm.trans hs1)
      simp only [List.length_append, List.length_cons] at hlen; omega
    · have hfeq := list_eq_append_head_ne (p2.symm.trans hs1)
      rcases hfk2 with rfl | ⟨_, rfl⟩
      · cases hfeq
      · injection hfeq with hkeq _
        exact hBlk a.1 ha (bs₂, k₂) (List.mem_append_right _ h2) hkeq

mutual
  private theorem addresses_blocks_in {D : Dialect} :
      ∀ {Γ outs} (t : Term D Γ outs) (blocks : List (Key × Nat)) (bKeys : List Key),
        (∀ p ∈ blocks, p.1 ∈ bKeys) → (∀ k ∈ t.blockKeys, k ∈ bKeys) →
        ∀ x ∈ t.addresses blocks, ∀ p ∈ x.1, p.1 ∈ bKeys
    | _, _, .ret _, _, _, _, _, _, hx => nomatch hx
    | _, _, .step key i _ rest, blocks, bKeys, hb, hbk, x, hx => by
        simp only [Term.addresses, List.mem_append] at hx
        simp only [Term.blockKeys, List.mem_append] at hbk
        rcases hx with hx | hx
        · exact instr_addresses_blocks_in i key blocks bKeys hb (fun k hk => hbk k (.inl hk)) x hx
        · exact addresses_blocks_in rest blocks bKeys hb (fun k hk => hbk k (.inr hk)) x hx

  private theorem instr_addresses_blocks_in {D : Dialect} :
      ∀ {Γ mid} (i : Instr D Γ mid) (key : Key) (blocks : List (Key × Nat)) (bKeys : List Key),
        (∀ p ∈ blocks, p.1 ∈ bKeys) → (∀ k ∈ i.blockKeys key, k ∈ bKeys) →
        ∀ x ∈ i.addresses blocks key, ∀ p ∈ x.1, p.1 ∈ bKeys
    | _, _, .op .., _, _, _, hb, _, _, hx => by
        simp only [Instr.addresses, List.mem_singleton] at hx; subst hx; exact hb
    | _, _, .guard .., _, _, _, hb, _, _, hx => by
        simp only [Instr.addresses, List.mem_singleton] at hx; subst hx; exact hb
    | _, _, .choose _ _ _ _ onTrue onFalse, _, blocks, bKeys, hb, hbk, x, hx => by
        simp only [Instr.addresses, List.mem_cons, List.mem_append] at hx
        simp only [Instr.blockKeys, List.mem_append] at hbk
        rcases hx with rfl | hx | hx
        · exact hb
        · exact addresses_blocks_in onTrue blocks bKeys hb (fun k hk => hbk k (.inl hk)) x hx
        · exact addresses_blocks_in onFalse blocks bKeys hb (fun k hk => hbk k (.inr hk)) x hx
    | _, _, .cases _ _ _ _ arms, _, blocks, bKeys, hb, hbk, x, hx => by
        simp only [Instr.addresses, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hb
        · exact arms_addresses_blocks_in arms blocks bKeys hb hbk x hx
    | _, _, .loop _ _ _ _ _ body, _, blocks, bKeys, hb, hbk, x, hx => by
        simp only [Instr.addresses, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hb
        · exact addresses_blocks_in body blocks bKeys hb hbk x hx
    | _, _, .block num body, key, blocks, bKeys, hb, hbk, x, hx =>
        addresses_blocks_in body (blocks ++ [(key, num)]) bKeys
          (fun p hp => by
            rcases List.mem_append.mp hp with hp | hp
            · exact hb p hp
            · rw [List.mem_singleton.mp hp]; exact hbk key List.mem_cons_self)
          (fun k hk => hbk k (List.mem_cons_of_mem _ hk)) x hx
    | _, _, .attempt _ _ _ body, _, blocks, bKeys, hb, hbk, x, hx => by
        simp only [Instr.addresses, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hb
        · exact addresses_blocks_in body blocks bKeys hb hbk x hx

  private theorem arms_addresses_blocks_in {D : Dialect} :
      ∀ {Γ mid payloads} (arms : Arms D Γ mid payloads) (blocks : List (Key × Nat)) (bKeys : List Key),
        (∀ p ∈ blocks, p.1 ∈ bKeys) → (∀ k ∈ arms.blockKeys, k ∈ bKeys) →
        ∀ x ∈ arms.addresses blocks, ∀ p ∈ x.1, p.1 ∈ bKeys
    | _, _, _, .nil, _, _, _, _, _, hx => nomatch hx
    | _, _, _, .cons _ arm rest, blocks, bKeys, hb, hbk, x, hx => by
        simp only [Arms.addresses, List.mem_append] at hx
        simp only [Arms.blockKeys, List.mem_append] at hbk
        rcases hx with hx | hx
        · exact addresses_blocks_in arm blocks bKeys hb (fun k hk => hbk k (.inl hk)) x hx
        · exact arms_addresses_blocks_in rest blocks bKeys hb (fun k hk => hbk k (.inr hk)) x hx
end

mutual
  private theorem addresses_shift {D : Dialect} :
      ∀ {Γ outs} (t : Term D Γ outs) (pre bs : List (Key × Nat)),
        t.addresses (pre ++ bs) = (t.addresses bs).map (fun p => (pre ++ p.1, p.2))
    | _, _, .ret _, _, _ => rfl
    | _, _, .step key i _ rest, pre, bs => by
        simp only [Term.addresses, List.map_append, instr_addresses_shift i key pre bs,
          addresses_shift rest pre bs]

  private theorem instr_addresses_shift {D : Dialect} :
      ∀ {Γ mid} (i : Instr D Γ mid) (key : Key) (pre bs : List (Key × Nat)),
        i.addresses (pre ++ bs) key = (i.addresses bs key).map (fun p => (pre ++ p.1, p.2))
    | _, _, .op .., _, _, _ => rfl
    | _, _, .guard .., _, _, _ => rfl
    | _, _, .choose _ _ _ _ onTrue onFalse, _, pre, bs => by
        simp only [Instr.addresses, List.map_cons, List.map_append,
          addresses_shift onTrue pre bs, addresses_shift onFalse pre bs]
    | _, _, .cases _ _ _ _ arms, _, pre, bs => by
        simp only [Instr.addresses, List.map_cons, arms_addresses_shift arms pre bs]
    | _, _, .loop _ _ _ _ _ body, _, pre, bs => by
        simp only [Instr.addresses, List.map_cons, addresses_shift body pre bs]
    | _, _, .block num body, key, pre, bs => by
        simp only [Instr.addresses, List.append_assoc, addresses_shift body pre (bs ++ [(key, num)])]
    | _, _, .attempt _ _ _ body, _, pre, bs => by
        simp only [Instr.addresses, List.map_cons, addresses_shift body pre bs]

  private theorem arms_addresses_shift {D : Dialect} :
      ∀ {Γ mid payloads} (arms : Arms D Γ mid payloads) (pre bs : List (Key × Nat)),
        arms.addresses (pre ++ bs) = (arms.addresses bs).map (fun p => (pre ++ p.1, p.2))
    | _, _, _, .nil, _, _ => rfl
    | _, _, _, .cons _ arm rest, pre, bs => by
        simp only [Arms.addresses, List.map_append, addresses_shift arm pre bs,
          arms_addresses_shift rest pre bs]
end

private theorem nodup_of_map_shift {pre : List (Key × Nat)} {l : List (List (Key × Nat) × Key)}
    (h : (l.map fun p => (pre ++ p.1, p.2)).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      simp only [List.map_cons, List.nodup_cons] at h
      refine List.nodup_cons.mpr ⟨?_, ih h.2⟩
      intro hmem
      exact h.1 (List.mem_map.mpr ⟨x, hmem, rfl⟩)

private theorem occUnder_hasPrefix {base : List Frame} {addrs : List (List (Key × Nat) × Key)}
    {occ : Occurrence} (h : OccUnder base addrs occ) : ∃ tail, occ.path = base ++ tail := by
  obtain ⟨bs, k, _, rfl | ⟨tail, hp | ⟨i, hp⟩⟩⟩ := h
  · exact ⟨blockFrames bs, rfl⟩
  · exact ⟨blockFrames bs ++ .application k :: tail, by simpa [List.append_assoc] using hp⟩
  · exact ⟨blockFrames bs ++ .iteration k i :: tail, by simpa [List.append_assoc] using hp⟩

private theorem liftLocal_occsIn_unique {A : Type} {P : Occurrence → Prop}
    (f : Stop → List Role × Stop) (p : Local A) :
    Protocol.OccsIn M P (liftLocal (S := GSig M) f p) ∧
      Protocol.UniqueOccs M (liftLocal (S := GSig M) f p) := by
  cases p with
  | done _ => exact ⟨trivial, trivial⟩
  | halt _ => exact ⟨trivial, trivial⟩
  | call op _ => cases op

private theorem term_observe_unique {hs : Headers V}
    (fns : FnTable M hs.fns) (gTable : GTable M hs.protocols)
    (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (path : List Frame)
      (args : HList (LVal M) hdr.ins),
      Protocol.OccsIn M (fun occ => ∃ tail, occ.path = path ++ tail) (gTable hdr callee path args) ∧
        Protocol.UniqueOccs M (gTable hdr callee path args)) :
    ∀ {Γ outs} (t : Term (protocolDialect V hs) Γ outs) (base : List Frame)
      (blocks : List (Key × Nat)) (bKeys : List Key) (env : Env (LVal M) Γ),
      (t.addresses blocks).Nodup →
      (∀ bk ∈ bKeys, ∀ x ∈ t.addresses blocks, x.2 ≠ bk) →
      (∀ p ∈ blocks, p.1 ∈ bKeys) →
      (∀ k ∈ t.blockKeys, k ∈ bKeys) →
      Protocol.OccsIn M (OccUnder base (t.addresses blocks))
          (Term.observe M fns gTable t (base ++ blockFrames blocks) env) ∧
        Protocol.UniqueOccs M (Term.observe M fns gTable t (base ++ blockFrames blocks) env)
  | _, _, .ret _, _, _, _, _, _, _, _, _ => ⟨trivial, trivial⟩
  | _, _, .op key o args results rest, base, blocks, bKeys, env, hnd, hblk, hb, hbk => by
      simp only [Term.addresses, Instr.addresses, List.singleton_append, List.nodup_cons] at hnd
      have hRest := fun (ys : HList (LVal M) _) =>
        term_observe_unique fns gTable hCallee rest base blocks bKeys (env.extend results ys)
          hnd.2 (fun bk hbk' x hx => hblk bk hbk' x (List.mem_cons_of_mem _ hx)) hb
          (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hDisj : ∀ occ, OccUnder base [(blocks, key)] occ →
          OccUnder base (rest.addresses blocks) occ → False :=
        occUnder_disjoint (bKeys := bKeys)
          (fun x hx => by rw [List.mem_singleton.mp hx]; exact hnd.1)
          (fun bk hbk' x hx => hblk bk hbk' x (by simpa [Term.addresses, Instr.addresses] using hx))
          (fun x hx => addresses_blocks_in (.op key o args results rest) blocks bKeys hb hbk x
            (by simpa [Term.addresses, Instr.addresses] using hx))
      have hMonoHead : ∀ {occ}, OccUnder base [(blocks, key)] occ →
          OccUnder base ((Term.op key o args results rest).addresses blocks) occ :=
        occUnder_mono (fun x hx => by
          rw [List.mem_singleton.mp hx]; exact List.mem_cons_self)
      have hMonoRest : ∀ {occ}, OccUnder base (rest.addresses blocks) occ →
          OccUnder base ((Term.op key o args results rest).addresses blocks) occ :=
        occUnder_mono (fun x hx => List.mem_cons_of_mem _ hx)
      cases o with
      | compute R op operands types held =>
          simp only [Term.observe, observeOp, protocolOp]
          have hLoc := liftLocal_occsIn_unique M (P := OccUnder base [(blocks, key)])
            (fun why => (R, why)) (localOp M fns op (computeArgs M types (env.all args)))
          refine ⟨Protocol.occsIn_bind M _ _
              (Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => hMonoHead) hLoc.1))
              (fun ys => Protocol.occsIn_mono M (fun _ => hMonoRest) (hRest ys).1),
            Protocol.uniqueOccs_bind M hDisj _ _
              (Protocol.occsIn_map M _ _ hLoc.1) (Protocol.uniqueOccs_map M _ _ hLoc.2) hRest⟩
      | narrow R among =>
          obtain ⟨x, rfl⟩ := HList.one args
          simp only [Term.observe, observeOp, protocolOp]
          exact ⟨Protocol.occsIn_mono M (fun _ => hMonoRest) (hRest _).1, (hRest _).2⟩
      | flow kind giver getters holds unique =>
          simp only [Term.observe, observeOp]
          obtain ⟨x, rfl⟩ := HList.one args
          have hHere : OccUnder base [(blocks, key)] ⟨base ++ blockFrames blocks, key⟩ :=
            ⟨blocks, key, List.mem_singleton_self _, .inl rfl⟩
          refine ⟨⟨hMonoHead hHere, fun _ => Protocol.occsIn_map M _ _
              (Protocol.occsIn_mono M (fun _ => hMonoRest) (hRest _).1)⟩,
            fun _ => ⟨Protocol.occsIn_map M _ _
              (Protocol.occsIn_mono M (fun occ ho (heq : occ = ⟨base ++ blockFrames blocks, key⟩) =>
                hDisj _ (heq.symm ▸ hHere) ho) (hRest _).1),
              Protocol.uniqueOccs_map M _ _ (hRest _).2⟩⟩
      | given kind owner hearers operands τ typed held unique =>
          have hHere : OccUnder base [(blocks, key)] ⟨base ++ blockFrames blocks, key⟩ :=
            ⟨blocks, key, List.mem_singleton_self _, .inl rfl⟩
          cases kind with
          | coin law =>
              cases hearers with
              | nil =>
                  simp only [Term.observe, observeOp]
                  refine ⟨⟨hMonoHead hHere, fun v => Protocol.occsIn_mono M (fun _ => hMonoRest) (hRest _).1⟩,
                    fun v => ⟨Protocol.occsIn_mono M (fun occ ho (heq : occ = ⟨base ++ blockFrames blocks, key⟩) =>
                      hDisj _ (heq.symm ▸ hHere) ho) (hRest _).1,
                      (hRest _).2⟩⟩
              | cons h0 hs0 =>
                  simp only [Term.observe, observeOp]
                  refine ⟨⟨hMonoHead hHere, fun v => Protocol.occsIn_map M _ _
                      (Protocol.occsIn_mono M (fun _ => hMonoRest) (hRest _).1)⟩,
                    fun v => ⟨Protocol.occsIn_map M _ _
                      (Protocol.occsIn_mono M (fun occ ho (heq : occ = ⟨base ++ blockFrames blocks, key⟩) =>
                        hDisj _ (heq.symm ▸ hHere) ho) (hRest _).1),
                      Protocol.uniqueOccs_map M _ _ (hRest _).2⟩⟩
          | request service =>
              simp only [Term.observe, observeOp]
              refine ⟨⟨hMonoHead hHere, fun v => Protocol.occsIn_map M _ _
                  (Protocol.occsIn_mono M (fun _ => hMonoRest) (hRest _).1)⟩,
                fun v => ⟨Protocol.occsIn_map M _ _
                  (Protocol.occsIn_mono M (fun occ ho (heq : occ = ⟨base ++ blockFrames blocks, key⟩) =>
                    hDisj _ (heq.symm ▸ hHere) ho) (hRest _).1),
                  Protocol.uniqueOccs_map M _ _ (hRest _).2⟩⟩
      | apply callee peers distinct covers operands fits =>
          simp only [Term.observe, observeOp]
          have hCall := hCallee _ callee (base ++ blockFrames blocks ++ [.application key])
            (unmapAll M (RoleMap.ofList peers distinct).to (fitAll M fits (env.all args)))
          have hCallOcc : Protocol.OccsIn M (OccUnder base [(blocks, key)])
              (mapG M (RoleMap.ofList peers distinct).to
                (gTable _ callee (base ++ blockFrames blocks ++ [.application key]) _)) :=
            Protocol.occsIn_mapG M _ _
              (Protocol.occsIn_mono M (fun occ ⟨tail, hp⟩ =>
                ⟨blocks, key, List.mem_singleton_self _, .inr ⟨tail, .inl (by simpa [List.append_assoc] using hp)⟩⟩)
                hCall.1)
          have hCallUniq := Protocol.uniqueOccs_mapG M (RoleMap.ofList peers distinct).to _ hCall.2
          refine ⟨Protocol.occsIn_bind M _ _
              (Protocol.occsIn_mono M (fun _ => hMonoHead) hCallOcc)
              (fun inner => Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => hMonoRest) (hRest _).1)),
            Protocol.uniqueOccs_bind M hDisj _ _ hCallOcc hCallUniq
              (fun inner => ⟨Protocol.occsIn_map M _ _ (hRest _).1,
                Protocol.uniqueOccs_map M _ _ (hRest _).2⟩)⟩
  | _, _, .guard key ps c ok why rest, base, blocks, bKeys, env, hnd, hblk, hb, hbk => by
      simp only [Term.addresses, Instr.addresses, List.singleton_append, List.nodup_cons] at hnd
      simp only [Term.observe]
      cases asBool M ok.1 (env.get c)
      · exact ⟨trivial, trivial⟩
      · have hRest := term_observe_unique fns gTable hCallee rest base blocks bKeys env
          hnd.2 (fun bk hbk' x hx => hblk bk hbk' x (List.mem_cons_of_mem _ hx)) hb
          (fun k hk => hbk k (by simp only [Term.blockKeys, Instr.blockKeys, List.nil_append]; exact hk))
        exact ⟨Protocol.occsIn_mono M (fun _ => occUnder_mono (fun _ h => List.mem_cons_of_mem _ h)) hRest.1,
          hRest.2⟩
  | _, _, .choose key ps c ok gives onTrue onFalse results rest, base, blocks, bKeys, env,
      hnd, hblk, hb, hbk => by
      simp only [Term.addresses, Instr.addresses, List.cons_append, List.nodup_cons,
        List.nodup_append] at hnd
      have hRest := fun (ys : HList (LVal M) _) =>
        term_observe_unique fns gTable hCallee rest base blocks bKeys (env.extend results ys)
          hnd.2.2.1
          (fun bk hbk' x hx => hblk bk hbk' x (by simp [Term.addresses, Instr.addresses, hx])) hb
          (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hTrue := term_observe_unique fns gTable hCallee onTrue base blocks bKeys env
        hnd.2.1.1
        (fun bk hbk' x hx => hblk bk hbk' x (by simp [Term.addresses, Instr.addresses, hx])) hb
        (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hFalse := term_observe_unique fns gTable hCallee onFalse base blocks bKeys env
        hnd.2.1.2.1
        (fun bk hbk' x hx => hblk bk hbk' x (by simp [Term.addresses, Instr.addresses, hx])) hb
        (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hDisjT : ∀ occ, OccUnder base (onTrue.addresses blocks) occ →
          OccUnder base (rest.addresses blocks) occ → False :=
        occUnder_disjoint (bKeys := bKeys)
          (fun x hx hxr => hnd.2.2.2 x (List.mem_append_left _ hx) x hxr rfl)
          (fun bk hbk' x hx => hblk bk hbk' x (by
            rcases List.mem_append.mp hx with hx | hx <;>
              simp [Term.addresses, Instr.addresses, hx]))
          (fun x hx => addresses_blocks_in (.choose key ps c ok gives onTrue onFalse results rest)
            blocks bKeys hb hbk x (by
              rcases List.mem_append.mp hx with hx | hx <;>
                simp [Term.addresses, Instr.addresses, hx]))
      have hDisjF : ∀ occ, OccUnder base (onFalse.addresses blocks) occ →
          OccUnder base (rest.addresses blocks) occ → False :=
        occUnder_disjoint (bKeys := bKeys)
          (fun x hx hxr => hnd.2.2.2 x (List.mem_append_right _ hx) x hxr rfl)
          (fun bk hbk' x hx => hblk bk hbk' x (by
            rcases List.mem_append.mp hx with hx | hx <;>
              simp [Term.addresses, Instr.addresses, hx]))
          (fun x hx => addresses_blocks_in (.choose key ps c ok gives onTrue onFalse results rest)
            blocks bKeys hb hbk x (by
              rcases List.mem_append.mp hx with hx | hx <;>
                simp [Term.addresses, Instr.addresses, hx]))
      simp only [Term.observe]
      cases asBool M ok.1 (env.get c)
      · refine ⟨Protocol.occsIn_bind M _ _
            (Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
              simp [Term.addresses, Instr.addresses, hx])) hFalse.1))
            (fun arm => Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
              simp [Term.addresses, Instr.addresses, hx])) (hRest arm.1).1)),
          Protocol.uniqueOccs_bind M hDisjF _ _
            (Protocol.occsIn_map M _ _ hFalse.1) (Protocol.uniqueOccs_map M _ _ hFalse.2)
            (fun arm => ⟨Protocol.occsIn_map M _ _ (hRest arm.1).1,
              Protocol.uniqueOccs_map M _ _ (hRest arm.1).2⟩)⟩
      · refine ⟨Protocol.occsIn_bind M _ _
            (Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
              simp [Term.addresses, Instr.addresses, hx])) hTrue.1))
            (fun arm => Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
              simp [Term.addresses, Instr.addresses, hx])) (hRest arm.1).1)),
          Protocol.uniqueOccs_bind M hDisjT _ _
            (Protocol.occsIn_map M _ _ hTrue.1) (Protocol.uniqueOccs_map M _ _ hTrue.2)
            (fun arm => ⟨Protocol.occsIn_map M _ _ (hRest arm.1).1,
              Protocol.uniqueOccs_map M _ _ (hRest arm.1).2⟩)⟩
  | _, _, .cases key ps x ok gives arms results rest, base, blocks, bKeys, env,
      hnd, hblk, hb, hbk => by
      simp only [Term.addresses, Instr.addresses, List.cons_append, List.nodup_cons,
        List.nodup_append] at hnd
      have hRest := fun (ys : HList (LVal M) _) =>
        term_observe_unique fns gTable hCallee rest base blocks bKeys (env.extend results ys)
          hnd.2.2.1
          (fun bk hbk' x hx => hblk bk hbk' x (by simp [Term.addresses, Instr.addresses, hx])) hb
          (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hArms := arms_observe_unique fns gTable hCallee arms base blocks bKeys env
        ((protocolSem M fns gTable).pick ok (env.get x))
        hnd.2.1
        (fun bk hbk' x hx => hblk bk hbk' x (by simp [Term.addresses, Instr.addresses, hx])) hb
        (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hDisj : ∀ occ, OccUnder base (arms.addresses blocks) occ →
          OccUnder base (rest.addresses blocks) occ → False :=
        occUnder_disjoint (bKeys := bKeys)
          (fun x hx hxr => hnd.2.2.2 x hx x hxr rfl)
          (fun bk hbk' x hx => hblk bk hbk' x (by
            rcases List.mem_append.mp hx with hx | hx <;>
              simp [Term.addresses, Instr.addresses, hx]))
          (fun a ha => addresses_blocks_in (.cases key ps x ok gives arms results rest)
            blocks bKeys hb hbk a (by
              rcases List.mem_append.mp ha with ha | ha <;>
                simp [Term.addresses, Instr.addresses, ha]))
      simp only [Term.observe]
      refine ⟨Protocol.occsIn_bind M _ _
          (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
            simp [Term.addresses, Instr.addresses, hx])) hArms.1)
          (fun chosen => Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
            simp [Term.addresses, Instr.addresses, hx])) (hRest chosen.1).1)),
        Protocol.uniqueOccs_bind M hDisj _ _ hArms.1 hArms.2
          (fun chosen => ⟨Protocol.occsIn_map M _ _ (hRest chosen.1).1,
            Protocol.uniqueOccs_map M _ _ (hRest chosen.1).2⟩)⟩
  | _, _, .loop (carried := carried) (each := each) key ps times gives initial inputs body results rest,
      base, blocks, bKeys, env, hnd, hblk, hb, hbk => by
      simp only [Term.addresses, Instr.addresses, List.cons_append, List.nodup_cons,
        List.nodup_append] at hnd
      have hRest := fun (ys : HList (LVal M) _) =>
        term_observe_unique fns gTable hCallee rest base blocks bKeys (env.extend results ys)
          hnd.2.2.1
          (fun bk hbk' x hx => hblk bk hbk' x (by simp [Term.addresses, Instr.addresses, hx])) hb
          (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hBodyAt : ∀ i (st : (protocolSem M fns gTable).LoopState carried each ×
          ((shapeOf body).fields.map .many).Val M),
          Protocol.OccsIn M (fun occ => ∃ tail, occ.path = base ++ blockFrames blocks ++ .iteration key i :: tail)
            ((Term.observe M fns gTable body (base ++ blockFrames blocks ++ [.iteration key i])
              (env.extend inputs (.cons ((protocolSem M fns gTable).index ps i) st.1.1))).map
                (fun out => (((HList.split carried out.1).1, st.1.2.push (HList.split carried out.1).2),
                  Fields.push M st.2 out.2))) ∧
          Protocol.UniqueOccs M
            ((Term.observe M fns gTable body (base ++ blockFrames blocks ++ [.iteration key i])
              (env.extend inputs (.cons ((protocolSem M fns gTable).index ps i) st.1.1))).map
                (fun out => (((HList.split carried out.1).1, st.1.2.push (HList.split carried out.1).2),
                  Fields.push M st.2 out.2))) := by
        intro i st
        have hShift : body.addresses blocks = (body.addresses []).map (fun p => (blocks ++ p.1, p.2)) := by
          simpa using addresses_shift body blocks []
        have hBodyNd : (body.addresses []).Nodup := nodup_of_map_shift (hShift ▸ hnd.2.1)
        have hBodyBlk : ∀ bk ∈ bKeys, ∀ x ∈ body.addresses [], x.2 ≠ bk := by
          intro bk hbk' x hx
          have hmem : (blocks ++ x.1, x.2) ∈ body.addresses blocks := by
            rw [hShift]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
          exact hblk bk hbk' (blocks ++ x.1, x.2) (by simp [Term.addresses, Instr.addresses, hmem])
        have hBody := term_observe_unique fns gTable hCallee body
          (base ++ blockFrames blocks ++ [.iteration key i]) [] bKeys
          (env.extend inputs (.cons ((protocolSem M fns gTable).index ps i) st.1.1))
          hBodyNd hBodyBlk (fun _ h => nomatch h)
          (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
        rw [show blockFrames [] = [] from rfl, List.append_nil] at hBody
        refine ⟨Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun occ ho => ?_) hBody.1),
          Protocol.uniqueOccs_map M _ _ hBody.2⟩
        obtain ⟨tail, hp⟩ := occUnder_hasPrefix ho
        exact ⟨tail, by simpa [List.append_assoc] using hp⟩
      let step := fun i (st : (protocolSem M fns gTable).LoopState carried each ×
          ((shapeOf body).fields.map .many).Val M) =>
        (Term.observe M fns gTable body (base ++ blockFrames blocks ++ [.iteration key i])
          (env.extend inputs (.cons ((protocolSem M fns gTable).index ps i) st.1.1))).map
          fun out => (((HList.split carried out.1).1, st.1.2.push (HList.split carried out.1).2),
            Fields.push M st.2 out.2)
      have hIter : ∀ (n start : Nat) (s : (protocolSem M fns gTable).LoopState carried each ×
          ((shapeOf body).fields.map .many).Val M),
          Protocol.OccsIn M
            (fun occ => ∃ j tail, start ≤ j ∧ occ.path = base ++ blockFrames blocks ++ .iteration key j :: tail)
            (Process.iterate n step start s) ∧
          Protocol.UniqueOccs M (Process.iterate n step start s) := by
        intro n
        induction n with
        | zero => intro _ _; exact ⟨trivial, trivial⟩
        | succ m ih =>
            intro start s
            simp only [Process.iterate]
            dsimp only [step]
            have hStep := hBodyAt start s
            have hDisjStep : ∀ (occ : Occurrence),
                (∃ tail, occ.path = base ++ blockFrames blocks ++ .iteration key start :: tail) →
                (∃ j tail, start + 1 ≤ j ∧ occ.path = base ++ blockFrames blocks ++ .iteration key j :: tail) →
                False := by
              rintro occ ⟨t1, hp1⟩ ⟨j, t2, hle, hp2⟩
              have hfeq := list_eq_append_head_ne (hp1.symm.trans hp2)
              cases hfeq
              omega
            refine ⟨Protocol.occsIn_bind M _ _
                (Protocol.occsIn_mono M (fun occ ⟨t, hp⟩ => ⟨start, t, Nat.le_refl _, hp⟩) hStep.1)
                (fun s' => Protocol.occsIn_mono M (fun occ ⟨j, t, hle, hp⟩ =>
                  ⟨j, t, Nat.le_trans (Nat.le_succ _) hle, hp⟩) (ih (start + 1) s').1),
              Protocol.uniqueOccs_bind M hDisjStep _ _ hStep.1 hStep.2 (fun s' => ih (start + 1) s')⟩
      have hLoopAll := hIter ((protocolSem M fns gTable).times times env) 0
        ((env.all initial, HList.empties each), Fields.empty M (shapeOf body).fields)
      have hLoopOcc : Protocol.OccsIn M (OccUnder base [(blocks, key)])
          (Process.iterate ((protocolSem M fns gTable).times times env) step 0
            ((env.all initial, HList.empties each), Fields.empty M (shapeOf body).fields)) :=
        Protocol.occsIn_mono M (fun occ ⟨j, tail, _, hp⟩ =>
          ⟨blocks, key, List.mem_singleton_self _, .inr ⟨tail, .inr ⟨j, hp⟩⟩⟩) hLoopAll.1
      have hDisj : ∀ occ, OccUnder base [(blocks, key)] occ →
          OccUnder base (rest.addresses blocks) occ → False :=
        occUnder_disjoint (bKeys := bKeys)
          (fun x hx => by
            rw [List.mem_singleton.mp hx]
            intro hmem
            exact hnd.1 (List.mem_append_right _ hmem))
          (fun bk hbk' x hx => hblk bk hbk' x (by
            rcases List.mem_append.mp hx with hx | hx
            · rw [List.mem_singleton.mp hx]; exact List.mem_cons_self
            · simp [Term.addresses, Instr.addresses, hx]))
          (fun x hx => addresses_blocks_in
            (.loop key ps times gives initial inputs body results rest) blocks bKeys hb hbk x
            (by
              rcases List.mem_append.mp hx with hx | hx
              · rw [List.mem_singleton.mp hx]; exact List.mem_cons_self
              · simp [Term.addresses, Instr.addresses, hx]))
      simp only [Term.observe]
      refine ⟨Protocol.occsIn_bind M _ _
          (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
            rw [List.mem_singleton.mp hx]; exact List.mem_cons_self)) hLoopOcc)
          (fun state => Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
            simp [Term.addresses, Instr.addresses, hx])) (hRest _).1)),
        Protocol.uniqueOccs_bind M hDisj _ _ hLoopOcc hLoopAll.2
          (fun state => ⟨Protocol.occsIn_map M _ _ (hRest _).1,
            Protocol.uniqueOccs_map M _ _ (hRest _).2⟩)⟩
  | _, _, .block key number body results rest, base, blocks, bKeys, env, hnd, hblk, hb, hbk => by
      simp only [Term.addresses, Instr.addresses, List.nodup_append] at hnd
      have hBody := term_observe_unique fns gTable hCallee body base (blocks ++ [(key, number)]) bKeys env
        hnd.1
        (fun bk hbk' x hx => hblk bk hbk' x (List.mem_append_left _ hx))
        (fun p hp => by
          rcases List.mem_append.mp hp with hp | hp
          · exact hb p hp
          · rw [List.mem_singleton.mp hp]
            exact hbk key (by simp [Term.blockKeys, Instr.blockKeys]))
        (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hRest := fun (ys : HList (LVal M) _) =>
        term_observe_unique fns gTable hCallee rest base blocks bKeys (env.extend results ys)
          hnd.2.1
          (fun bk hbk' x hx => hblk bk hbk' x (List.mem_append_right _ hx)) hb
          (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hDisj : ∀ occ, OccUnder base (body.addresses (blocks ++ [(key, number)])) occ →
          OccUnder base (rest.addresses blocks) occ → False :=
        occUnder_disjoint (bKeys := bKeys)
          (fun x hx hxr => hnd.2.2 x hx x hxr rfl)
          (fun bk hbk' x hx => hblk bk hbk' x (by
            rcases List.mem_append.mp hx with hx | hx <;>
              simp [Term.addresses, Instr.addresses, hx]))
          (fun x hx => addresses_blocks_in (.block key number body results rest) blocks bKeys hb hbk x
            (by rcases List.mem_append.mp hx with hx | hx <;> simp [Term.addresses, Instr.addresses, hx]))
      have hPath : base ++ blockFrames blocks ++ [.iteration key number] =
          base ++ blockFrames (blocks ++ [(key, number)]) := by
        rw [blockFrames_append, List.append_assoc]; rfl
      simp only [Term.observe, hPath]
      refine ⟨Protocol.occsIn_bind M _ _
          (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
            simp [Term.addresses, Instr.addresses, hx])) hBody.1)
          (fun inner => Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
            simp [Term.addresses, Instr.addresses, hx])) (hRest inner.1).1)),
        Protocol.uniqueOccs_bind M hDisj _ _ hBody.1 hBody.2
          (fun inner => ⟨Protocol.occsIn_map M _ _ (hRest inner.1).1,
            Protocol.uniqueOccs_map M _ _ (hRest inner.1).2⟩)⟩
  | _, _, .attempt key w owns inputs body results rest, base, blocks, bKeys, env,
      hnd, hblk, hb, hbk => by
      simp only [Term.addresses, Instr.addresses, List.cons_append, List.nodup_cons,
        List.nodup_append] at hnd
      have hBody := term_observe_unique fns gTable hCallee body base blocks bKeys
        (env.extend inputs (.cons (V := LVal M) (a := LTy.index w) (0 : Nat) .nil))
        hnd.2.1
        (fun bk hbk' x hx => hblk bk hbk' x (by simp [Term.addresses, Instr.addresses, hx])) hb
        (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hRest := fun (ys : HList (LVal M) _) =>
        term_observe_unique fns gTable hCallee rest base blocks bKeys (env.extend results ys)
          hnd.2.2.1
          (fun bk hbk' x hx => hblk bk hbk' x (by simp [Term.addresses, Instr.addresses, hx])) hb
          (fun k hk => hbk k (by simp [Term.blockKeys, Instr.blockKeys, hk]))
      have hDisj : ∀ occ, OccUnder base (body.addresses blocks) occ →
          OccUnder base (rest.addresses blocks) occ → False :=
        occUnder_disjoint (bKeys := bKeys)
          (fun x hx hxr => hnd.2.2.2 x hx x hxr rfl)
          (fun bk hbk' x hx => hblk bk hbk' x (by
            rcases List.mem_append.mp hx with hx | hx <;>
              simp [Term.addresses, Instr.addresses, hx]))
          (fun x hx => addresses_blocks_in (.attempt key w owns inputs body results rest)
            blocks bKeys hb hbk x (by
              rcases List.mem_append.mp hx with hx | hx <;>
                simp [Term.addresses, Instr.addresses, hx]))
      simp only [Term.observe]
      refine ⟨Protocol.occsIn_bind M _ _
          (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
            simp [Term.addresses, Instr.addresses, hx])) hBody.1)
          (fun inner => Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => by
            simp [Term.addresses, Instr.addresses, hx])) (hRest inner.1).1)),
        Protocol.uniqueOccs_bind M hDisj _ _ hBody.1 hBody.2
          (fun inner => ⟨Protocol.occsIn_map M _ _ (hRest inner.1).1,
            Protocol.uniqueOccs_map M _ _ (hRest inner.1).2⟩)⟩
where
  arms_observe_unique {hs : Headers V}
      (fns : FnTable M hs.fns) (gTable : GTable M hs.protocols)
      (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (path : List Frame)
        (args : HList (LVal M) hdr.ins),
        Protocol.OccsIn M (fun occ => ∃ tail, occ.path = path ++ tail) (gTable hdr callee path args) ∧
          Protocol.UniqueOccs M (gTable hdr callee path args)) :
      ∀ {Γ mid payloads} (arms : Arms (protocolDialect V hs) Γ mid payloads)
        (base : List Frame) (blocks : List (Key × Nat)) (bKeys : List Key)
        (env : Env (LVal M) Γ) (p : Pick (LVal M) payloads),
        (arms.addresses blocks).Nodup →
        (∀ bk ∈ bKeys, ∀ x ∈ arms.addresses blocks, x.2 ≠ bk) →
        (∀ p ∈ blocks, p.1 ∈ bKeys) →
        (∀ k ∈ arms.blockKeys, k ∈ bKeys) →
        Protocol.OccsIn M (OccUnder base (arms.addresses blocks))
            (Arms.observe M fns gTable arms (base ++ blockFrames blocks) env p) ∧
          Protocol.UniqueOccs M (Arms.observe M fns gTable arms (base ++ blockFrames blocks) env p)
    | _, _, _, .nil, _, _, _, _, p, _, _, _, _ => nomatch p
    | _, _, _, .cons inputs arm rest, base, blocks, bKeys, env, .here v, hnd, hblk, hb, hbk => by
        simp only [Arms.addresses, List.nodup_append] at hnd
        have hArm := term_observe_unique fns gTable hCallee arm base blocks bKeys
          (env.extend inputs (.cons v .nil)) hnd.1
          (fun bk hbk' x hx => hblk bk hbk' x (List.mem_append_left _ hx)) hb
          (fun k hk => hbk k (by simp [Arms.blockKeys, hk]))
        simp only [Arms.observe]
        exact ⟨Protocol.occsIn_map M _ _
            (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => List.mem_append_left _ hx)) hArm.1),
          Protocol.uniqueOccs_map M _ _ hArm.2⟩
    | _, _, _, .cons _ arm rest, base, blocks, bKeys, env, .there p, hnd, hblk, hb, hbk => by
        simp only [Arms.addresses, List.nodup_append] at hnd
        have hRest := arms_observe_unique fns gTable hCallee rest base blocks bKeys env p hnd.2.1
          (fun bk hbk' x hx => hblk bk hbk' x (List.mem_append_right _ hx)) hb
          (fun k hk => hbk k (by simp [Arms.blockKeys, hk]))
        simp only [Arms.observe]
        exact ⟨Protocol.occsIn_map M _ _
            (Protocol.occsIn_mono M (fun _ => occUnder_mono (fun x hx => List.mem_append_right _ hx)) hRest.1),
          Protocol.uniqueOccs_map M _ _ hRest.2⟩

private theorem defs_gTable_uniqueOccs :
    ∀ {hs : Headers V} (defs : Defs V hs) (hdr : ProtocolHeader V)
      (callee : Member hs.protocols hdr) (path : List Frame) (args : HList (LVal M) hdr.ins),
      Protocol.OccsIn M (fun occ => ∃ tail, occ.path = path ++ tail)
          (Defs.gTable M defs hdr callee path args) ∧
        Protocol.UniqueOccs M (Defs.gTable M defs hdr callee path args)
  | _, .nil, _, p, _, _ => nomatch p
  | _, .fn _ _ _ _ rest _, hdr, callee, path, args =>
      defs_gTable_uniqueOccs rest hdr callee path args
  | _, .protocol hdr inputs body ok rest, _, callee, path, args => by
      cases callee with
      | head =>
          have hDist := ok.distinct
          unfold Term.Distinct at hDist
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at hDist
          have hObs := term_observe_unique M (Defs.fnTable M rest) (Defs.gTable M rest)
            (defs_gTable_uniqueOccs rest) body path [] body.blockKeys
            (Env.empty.extend inputs args) hDist.1 hDist.2 (fun _ h => nomatch h) (fun _ h => h)
          simp only [blockFrames, List.map_nil, List.append_nil] at hObs
          show Protocol.OccsIn M _ ((Term.observe M (Defs.fnTable M rest) (Defs.gTable M rest) body
              path (Env.empty.extend inputs args)).map _) ∧
            Protocol.UniqueOccs M ((Term.observe M (Defs.fnTable M rest) (Defs.gTable M rest) body
              path (Env.empty.extend inputs args)).map _)
          exact ⟨Protocol.occsIn_map M _ _ (Protocol.occsIn_mono M (fun _ => occUnder_hasPrefix) hObs.1),
            Protocol.uniqueOccs_map M _ _ hObs.2⟩
      | tail callee => exact defs_gTable_uniqueOccs rest _ callee path args

unseal protocolMeaning in
/-- Along every execution path of a typed protocol, no occurrence is queried twice. -/
theorem protocolMeaning_uniqueOccs (p : Typed V) {hdr : ProtocolHeader V}
    (callee : Member p.headers.protocols hdr) (path : List Frame)
    (args : HList (LVal M) hdr.ins) :
    Protocol.UniqueOccs M (protocolMeaning M p callee path args) :=
  (defs_gTable_uniqueOccs M p.defs hdr callee path args).2

end UniqueOccs

end

end Zkc.Core
