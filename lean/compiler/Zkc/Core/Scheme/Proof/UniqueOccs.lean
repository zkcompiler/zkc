module

public import Zkc.Core.Scheme.Proof.ShapeObserve

@[expose] public section

/-!
Occurrence uniqueness along protocol runs (`protocolMeaning_uniqueOccs`): along every execution
path of a typed protocol, no occurrence is queried twice.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

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
