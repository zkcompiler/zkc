import Std

set_option autoImplicit false

namespace Zkc.Source.MessageSchema
inductive Ix where
  | lit : Nat → Ix
  | param : Nat → Ix
  | round : Ix
  | add : Ix → Ix → Ix
  | mul : Ix → Ix → Ix
  | hidden : Nat → Ix
  deriving Repr, DecidableEq

def Ix.eval (env : List Nat) (round : Option Nat) : Ix → Option Nat
  | .lit n => some n
  | .param k => env[k]?
  | .round => round
  | .add a b => do return (← a.eval env round) + (← b.eval env round)
  | .mul a b => do return (← a.eval env round) * (← b.eval env round)
  | .hidden _ => none

structure Schema where
  fieldId : Nat
  domainId : Nat
  instanceId : Nat
  cardinal : Nat
  rounds : Ix
  width : Ix
  deriving Repr

structure Contract where
  fieldId : Nat
  domainId : Nat
  instanceId : Nat
  cardinal : Nat
  rounds : Nat
  round : Nat
  width : Nat
  deriving Repr, DecidableEq

-- No symbolic constraint solver. Evaluate only public inputs at this boundary.
def form (s : Schema) (env : List Nat) (i : Nat) : Option Contract := do
  let rounds ← s.rounds.eval env none
  let width ← s.width.eval env (some i)
  if 0 < s.cardinal ∧ i < rounds then
    some ⟨s.fieldId, s.domainId, s.instanceId, s.cardinal, rounds, i, width⟩
  else none

structure Raw where
  fieldId : Nat
  domainId : Nat
  instanceId : Nat
  round : Nat
  values : List Nat
  deriving Repr, DecidableEq

def Valid (c : Contract) (m : Raw) : Prop :=
  0 < c.cardinal ∧ c.round < c.rounds ∧
  m.fieldId = c.fieldId ∧ m.domainId = c.domainId ∧
  m.instanceId = c.instanceId ∧ m.round = c.round ∧
  m.values.length = c.width ∧ ∀ x ∈ m.values, x < c.cardinal
instance (c : Contract) (m : Raw) : Decidable (Valid c m) := by
  unfold Valid
  infer_instance
abbrev Payload (c : Contract) := {m : Raw // Valid c m}

def check (c : Contract) (m : Raw) : Option (Payload c) :=
  if h : Valid c m then some ⟨m,h⟩ else none

def encode (m : Raw) : List Nat :=
  [m.fieldId, m.domainId, m.instanceId, m.round] ++ m.values

def parse : List Nat → Option Raw
  | f :: d :: inst :: r :: xs => some ⟨f,d,inst,r,xs⟩
  | _ => none

def decode (c : Contract) (words : List Nat) : Option (Payload c) := do
  let m ← parse words
  check c m

@[simp] theorem parse_encode (m : Raw) : parse (encode m) = some m := by
  cases m
  rfl

theorem parse_exact (words : List Nat) (m : Raw) (h : parse words = some m) :
    encode m = words := by
  match words with
  | f :: d :: inst :: r :: xs => simp only [parse, Option.some.injEq] at h; subst m; rfl
  | [] => simp [parse] at h
  | [_] => simp [parse] at h
  | [_,_] => simp [parse] at h
  | [_,_,_] => simp [parse] at h

-- This is a theorem about the executable check, not only typed constructors.
theorem check_exact (c : Contract) (m : Raw) (p : Payload c)
    (h : check c m = some p) : p.val = m := by
  unfold check at h
  split at h
  next hv => cases Option.some.inj h; rfl
  next hv => simp at h

theorem check_complete (c : Contract) (m : Raw) (h : Valid c m) :
    check c m = some ⟨m,h⟩ := by simp [check, h]

theorem decode_exact (c : Contract) (words : List Nat) (p : Payload c)
    (h : decode c words = some p) : encode p.val = words ∧ Valid c p.val := by
  unfold decode at h
  cases hp : parse words with
  | none => simp [hp] at h
  | some m =>
    simp only [hp] at h
    have he := check_exact c m p h
    exact ⟨he ▸ parse_exact words m hp, p.property⟩

-- EVERY valid message is admitted, with its exact arbitrary malicious contents.
theorem decode_complete (c : Contract) (m : Raw) (h : Valid c m) :
    decode c (encode m) = some ⟨m,h⟩ := by
  simp [decode, check, h]

-- The wire adversary quantifier equals the payload quantifier; no honest premise.
theorem adversary_quantifier (c : Contract) (P : Raw → Prop) :
    (∀ p : Payload c, P p.val) ↔ (∀ m, Valid c m → P m) := by
  constructor
  · intro h m hv; exact h ⟨m,hv⟩
  · intro h p; exact h p.val p.property

structure Cursor (c : Contract) where
  next : Nat
  bounded : next ≤ c.rounds

def advance (c : Contract) (words : List Nat) : Option (Payload c × Cursor c) := do
  let p ← decode c words
  return (p, ⟨c.round + 1, Nat.succ_le_of_lt p.property.2.1⟩)

theorem advance_preserves (c : Contract) (words : List Nat)
    (out : Payload c × Cursor c) (h : advance c words = some out) :
    encode out.1.val = words ∧ out.2.next = c.round + 1 ∧ out.2.next ≤ c.rounds := by
  unfold advance at h
  cases hd : decode c words with
  | none => simp [hd] at h
  | some p =>
    simp [hd] at h
    subst out
    exact ⟨(decode_exact c words p hd).1, rfl, Nat.succ_le_of_lt p.property.2.1⟩

-- Plan refinements are separate, and forget to exactly the same payload.
abbrev Honest (c : Contract) (R : Raw → Prop) := {p : Payload c // R p.val}
def forget {c : Contract} {R : Raw → Prop} (h : Honest c R) : Payload c := h.val

theorem honest_forget_decodes {c : Contract} {R : Raw → Prop} (h : Honest c R) :
    decode c (encode (forget h).val) = some (forget h) :=
  decode_complete c h.val.val h.val.property

-- Formation reflects actual public evaluation, including the current public round.
theorem form_sound (s : Schema) (env : List Nat) (i : Nat) (c : Contract)
    (h : form s env i = some c) :
    s.rounds.eval env none = some c.rounds ∧
    s.width.eval env (some i) = some c.width ∧
    c.round = i ∧ c.fieldId = s.fieldId ∧ c.domainId = s.domainId ∧
    c.instanceId = s.instanceId ∧ c.cardinal = s.cardinal := by
  unfold form at h
  cases hr : s.rounds.eval env none with
  | none => simp [hr] at h
  | some rounds =>
    cases hw : s.width.eval env (some i) with
    | none => simp [hr, hw] at h
    | some width =>
      by_cases hv : 0 < s.cardinal ∧ i < rounds
      · simp [hr, hw, hv] at h
        cases h
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp [hr, hw, hv] at h

-- One joined result: public schema evaluation -> decoder -> bounded shape cursor.
theorem family_boundary (s : Schema) (env : List Nat) (i : Nat) (c : Contract)
    (hf : form s env i = some c) (words : List Nat)
    (out : Payload c × Cursor c) (ha : advance c words = some out) :
    encode out.1.val = words ∧
    out.1.val.values.length = c.width ∧
    s.width.eval env (some i) = some c.width ∧
    out.2.next = i + 1 ∧ out.2.next ≤ c.rounds := by
  have hf' := form_sound s env i c hf
  have ha' := advance_preserves c words out ha
  exact ⟨ha'.1, out.1.property.2.2.2.2.2.2.1, hf'.2.1,
    hf'.2.2.1 ▸ ha'.2.1, ha'.2.2⟩

end Zkc.Source.MessageSchema
