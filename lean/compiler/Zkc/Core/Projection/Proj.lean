module

public import Zkc.Core.Meaning.Role

@[expose] public section

/-!
`Proj`, the relation of a role's process to a protocol's, and its lemmas.

Sequencing (`Proj.bind`, `Proj.map`), weakening (`Proj.mono`), iteration (`Proj.iterate`), a
role map (`Proj.mapRoles`), and a role that takes no part: in a computation by others
(`Proj.liftOut`), in a callee in which it plays no role (`Proj.unmapped`), in a loop whose
iterations it takes no part in (`Proj.iterate_quiet`).
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

/-- The process of a role is a projection of the process of the protocol: it performs the
role's part of each event; where it gets a value it is related at the value that was given;
where the world gives a value both are related at every reply; a role that stops performs
the stop, and a role that does not is not constrained by the stop of others. The marks of an
attempt are the role's alone: a role that begins one continues as the protocol does at the
number `0`, and one that settles one continues. -/
inductive Proj (r : Role) {A B : Type} (post : A → B → Prop) :
    Protocol M A → Program M B → Prop where
  | done {a b} : post a b → Proj r post (.done a) (.done b)
  | stopsHere {who why} : r ∈ who → Proj r post (.halt (who, why)) (.halt why)
  | stopsElsewhere {who why q} : r ∉ who → Proj r post (.halt (who, why)) q
  | gave {kind getters at_ τ x} {k : Unit → Protocol M A} {k' : Unit → Program M B} :
      r ∉ getters → Proj r post (k ()) (k' ()) →
      Proj r post (.call (.flow kind r getters at_ τ x) k) (.call (.give kind getters at_ τ x) k')
  | got {kind giver getters at_ τ x} {k : Unit → Protocol M A} {k' : M.Val τ → Program M B} :
      giver ≠ r → r ∈ getters → Proj r post (k ()) (k' x) →
      Proj r post (.call (.flow kind giver getters at_ τ x) k) (.call (.get kind giver at_ τ) k')
  | passed {kind giver getters at_ τ x} {k : Unit → Protocol M A} {q} :
      giver ≠ r → r ∉ getters → Proj r post (k ()) q →
      Proj r post (.call (.flow kind giver getters at_ τ x) k) q
  | owned {kind hearers at_ ins payload τ} {k : M.Val τ → Protocol M A}
      {k' : M.Val τ → Program M B} :
      (∀ v, Proj r post (k v) (k' v)) →
      Proj r post (.call (.given kind r hearers at_ ins payload τ) k)
        (.call (.own kind hearers at_ ins payload τ) k')
  | heard {kind owner hearers at_ ins payload τ} {k : M.Val τ → Protocol M A}
      {k' : M.Val τ → Program M B} :
      owner ≠ r → r ∈ hearers → (∀ v, Proj r post (k v) (k' v)) →
      Proj r post (.call (.given kind owner hearers at_ ins payload τ) k)
        (.call (.hear kind owner at_ τ) k')
  | unheard {kind owner hearers at_ ins payload τ} {k : M.Val τ → Protocol M A} {q} :
      owner ≠ r → r ∉ hearers → (∀ v, Proj r post (k v) q) →
      Proj r post (.call (.given kind owner hearers at_ ins payload τ) k) q
  | begins {at_} {p : Protocol M A} {k' : Nat → Program M B} :
      Proj r post p (k' 0) → Proj r post p (.call (.begin at_) k')
  | settles {at_} {p : Protocol M A} {k' : Unit → Program M B} :
      Proj r post p (k' ()) → Proj r post p (.call (.settle at_) k')

theorem Proj.bind {r : Role} {A B A' B' : Type} {post : A → B → Prop} {post' : A' → B' → Prop}
    {p : Protocol M A} {q : Program M B} {f : A → Protocol M A'} {g : B → Program M B'}
    (h : Proj M r post p q) (hk : ∀ a b, post a b → Proj M r post' (f a) (g b)) :
    Proj M r post' (p.bind f) (q.bind g) := by
  induction h with
  | done hp => exact hk _ _ hp
  | stopsHere mem => exact .stopsHere mem
  | stopsElsewhere out => exact .stopsElsewhere out
  | gave hr _ ih => exact .gave hr ih
  | got hg hm _ ih => exact .got hg hm ih
  | passed hg hm _ ih => exact .passed hg hm ih
  | owned _ ih => exact .owned ih
  | heard ho hm _ ih => exact .heard ho hm ih
  | unheard ho hm _ ih => exact .unheard ho hm ih
  | begins _ ih => exact .begins ih
  | settles _ ih => exact .settles ih

theorem Proj.mono {r : Role} {A B : Type} {post post' : A → B → Prop} {p : Protocol M A}
    {q : Program M B} (h : Proj M r post p q) (hw : ∀ a b, post a b → post' a b) :
    Proj M r post' p q := by
  induction h with
  | done hp => exact .done (hw _ _ hp)
  | stopsHere mem => exact .stopsHere mem
  | stopsElsewhere out => exact .stopsElsewhere out
  | gave hr _ ih => exact .gave hr ih
  | got hg hm _ ih => exact .got hg hm ih
  | passed hg hm _ ih => exact .passed hg hm ih
  | owned _ ih => exact .owned ih
  | heard ho hm _ ih => exact .heard ho hm ih
  | unheard ho hm _ ih => exact .unheard ho hm ih
  | begins _ ih => exact .begins ih
  | settles _ ih => exact .settles ih

theorem Proj.map {r : Role} {A B A' B' : Type} {post : A → B → Prop} {post' : A' → B' → Prop}
    {p : Protocol M A} {q : Program M B} {f : A → A'} {g : B → B'} (h : Proj M r post p q)
    (hw : ∀ a b, post a b → post' (f a) (g b)) : Proj M r post' (p.map f) (q.map g) := by
  rw [Process.map_eq_bind, Process.map_eq_bind]
  exact Proj.bind M h fun a b hab => .done (hw a b hab)

/-- A map of the protocol's results alone. -/
theorem Proj.map_left {r : Role} {A B A' : Type} {post : A → B → Prop} {post' : A' → B → Prop}
    {p : Protocol M A} {q : Program M B} {f : A → A'} (h : Proj M r post p q)
    (hw : ∀ a b, post a b → post' (f a) b) : Proj M r post' (p.map f) q := by
  have mapped := Proj.map M (g := fun b => b) h hw
  rwa [Process.map_id'] at mapped

/-- Where the role's process is a projection of a map of the protocol's process, it is a
projection of the protocol's process. -/
theorem Proj.of_map_left {r : Role} {A A' B : Type} {post : A' → B → Prop} {f : A → A'}
    (p : Protocol M A) {q : Program M B} (h : Proj M r post (p.map f) q) :
    Proj M r (fun a b => post (f a) b) p q := by
  generalize e : p.map f = p' at h
  induction h generalizing p with
  | done hp =>
      cases p with
      | done a => cases e; exact .done hp
      | halt _ => cases e
      | call _ _ => cases e
  | stopsHere mem =>
      cases p with
      | done _ => cases e
      | halt payload => cases e; exact .stopsHere mem
      | call _ _ => cases e
  | stopsElsewhere out =>
      cases p with
      | done _ => cases e
      | halt payload => cases e; exact .stopsElsewhere out
      | call _ _ => cases e
  | gave hr _ ih =>
      cases p with
      | done _ => cases e
      | halt _ => cases e
      | call op k => cases e; exact .gave hr (ih (k ()) rfl)
  | got hg hm _ ih =>
      cases p with
      | done _ => cases e
      | halt _ => cases e
      | call op k => cases e; exact .got hg hm (ih (k ()) rfl)
  | passed hg hm _ ih =>
      cases p with
      | done _ => cases e
      | halt _ => cases e
      | call op k => cases e; exact .passed hg hm (ih (k ()) rfl)
  | owned _ ih =>
      cases p with
      | done _ => cases e
      | halt _ => cases e
      | call op k => cases e; exact .owned fun v => ih v (k v) rfl
  | heard ho hm _ ih =>
      cases p with
      | done _ => cases e
      | halt _ => cases e
      | call op k => cases e; exact .heard ho hm fun v => ih v (k v) rfl
  | unheard ho hm _ ih =>
      cases p with
      | done _ => cases e
      | halt _ => cases e
      | call op k => cases e; exact .unheard ho hm fun v => ih v (k v) rfl
  | begins _ ih => exact .begins (ih p e)
  | settles _ ih => exact .settles (ih p e)

/-- A loop: when one iteration of the role is a projection of one iteration of the protocol
at related states, so is the loop. -/
theorem Proj.iterate {r : Role} {A B : Type} {inv : A → B → Prop}
    {stepG : Nat → A → Protocol M A} {stepR : Nat → B → Program M B}
    (hstep : ∀ i a b, inv a b → Proj M r inv (stepG i a) (stepR i b)) :
    ∀ (n i : Nat) (a : A) (b : B), inv a b →
      Proj M r inv (Process.iterate n stepG i a) (Process.iterate n stepR i b)
  | 0, _, _, _, h => .done h
  | n + 1, i, _, _, h =>
      Proj.bind M (hstep i _ _ h) fun a' b' h' => Proj.iterate hstep n (i + 1) a' b' h'

/-- A loop whose iterations a role takes no part in. -/
theorem Proj.iterate_quiet {r : Role} {A : Type} {step : Nat → A → Protocol M A}
    (h : ∀ i a, Proj M r (fun _ (_ : Unit) => True) (step i a) (.done ())) :
    ∀ (n i : Nat) (a : A),
      Proj M r (fun _ (_ : Unit) => True) (Process.iterate n step i a) (.done ())
  | 0, _, _ => .done trivial
  | n + 1, i, a =>
      Proj.bind M (q := .done ()) (g := fun _ => .done ()) (h i a) fun _ _ _ =>
        Proj.iterate_quiet h n (i + 1) _

/-- A computation by roles that hold a value: the role is one of them. -/
theorem Proj.liftIn {r : Role} {R : Holders} (hr : r ∈ R) {A A' B : Type}
    {post : A' → B → Prop} {f : A → A'} {g : A → B} (hw : ∀ a, post (f a) (g a)) :
    ∀ p : Local A, Proj M r post ((liftLocal (fun why => (R, why)) p).map f) ((liftLocal id p).map g)
  | .done a => .done (hw a)
  | .halt _ => .stopsHere hr
  | .call op _ => nomatch op

/-- A computation by roles other than `r`: the role does nothing during it. -/
theorem Proj.liftOut {r : Role} {R : Holders} (hr : r ∉ R) {A A' B : Type}
    {post : A' → B → Prop} {f : A → A'} (b : B) (hb : ∀ a, post (f a) b) :
    ∀ p : Local A, Proj M r post ((liftLocal (fun why => (R, why)) p).map f) (.done b)
  | .done a => .done (hb a)
  | .halt _ => .stopsElsewhere hr
  | .call op _ => nomatch op

theorem mem_map_of_injective {ρ : Role → Role} (inj : ∀ a b, ρ a = ρ b → a = b) {r : Role}
    {roles : List Role} : ρ r ∈ roles.map ρ ↔ r ∈ roles := by
  constructor
  · intro m
    obtain ⟨i, hi, e⟩ := List.mem_map.mp m
    exact inj _ _ e ▸ hi
  · intro m
    exact List.mem_map.mpr ⟨_, m, rfl⟩

/-- The caller's role that plays the callee's role `j` runs the callee's program of `j`,
with its peers renamed. -/
theorem Proj.mapRoles {ρ : Role → Role} (inj : ∀ a b, ρ a = ρ b → a = b) {j : Role}
    {A B : Type} {post : A → B → Prop} {p : Protocol M A} {q : Program M B}
    (h : Proj M j post p q) : Proj M (ρ j) post (mapG M ρ p) (mapR M ρ q) := by
  induction h with
  | done hp => exact .done hp
  | stopsHere mem => exact .stopsHere ((mem_map_of_injective inj).mpr mem)
  | stopsElsewhere out => exact .stopsElsewhere fun m => out ((mem_map_of_injective inj).mp m)
  | gave hr _ ih => exact .gave (fun m => hr ((mem_map_of_injective inj).mp m)) ih
  | got hg hm _ ih => exact .got (fun e => hg (inj _ _ e)) ((mem_map_of_injective inj).mpr hm) ih
  | passed hg hm _ ih =>
      exact .passed (fun e => hg (inj _ _ e)) (fun m => hm ((mem_map_of_injective inj).mp m)) ih
  | owned _ ih => exact .owned ih
  | heard ho hm _ ih =>
      exact .heard (fun e => ho (inj _ _ e)) ((mem_map_of_injective inj).mpr hm) ih
  | unheard ho hm _ ih =>
      exact .unheard (fun e => ho (inj _ _ e)) (fun m => hm ((mem_map_of_injective inj).mp m)) ih
  | begins _ ih => exact .begins ih
  | settles _ ih => exact .settles ih

/-- A role of the caller that plays no role of the callee does nothing during the
application, whatever it returns. -/
theorem Proj.unmapped {ρ : Role → Role} {r : Role} (hr : ∀ j, ρ j ≠ r) {A B : Type} (b : B) :
    ∀ (p : Protocol M A), Proj M r (fun _ _ => True) (mapG M ρ p) (.done b)
  | .done _ => .done trivial
  | .halt (who, _) =>
      .stopsElsewhere fun m => by
        obtain ⟨j, _, e⟩ := List.mem_map.mp m
        exact hr j e
  | .call (.flow _ giver getters _ _ _) k =>
      .passed (hr giver) (fun m => by obtain ⟨j, _, e⟩ := List.mem_map.mp m; exact hr j e)
        (Proj.unmapped hr b (k ()))
  | .call (.given _ owner hearers _ _ _ _) k =>
      .unheard (hr owner) (fun m => by obtain ⟨j, _, e⟩ := List.mem_map.mp m; exact hr j e)
        fun v => Proj.unmapped hr b (k v)

end

end Zkc.Core
