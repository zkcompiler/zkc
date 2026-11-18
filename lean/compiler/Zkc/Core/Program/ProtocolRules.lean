module

public import Zkc.Core.Program.LocalRules

@[expose] public section

/-! Reading the operations and control of a protocol against the preceding headers. -/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- What is written for an operation of a protocol. -/
def ProtocolOp.print {hs : Headers V} {ins res : List (LTy V)} :
    ProtocolOp V hs ins res → ProtocolRaw V
  | .compute R o _ _ _ => .compute R (LocalOp.print o)
  | .flow (τ := τ) kind giver getters _ _ => .event (.flow kind giver getters) τ
  | .given kind owner hearers _ τ _ _ _ => .event (.given kind owner hearers) τ
  | .narrow R _ => .narrow R
  | .apply (hdr := hdr) _ roles _ _ _ _ => .apply hdr.key roles

def decideCovers (actual expected : LTy V) : Decidable (actual.Covers expected) :=
  inferInstanceAs (Decidable (actual.ty = expected.ty ∧ ∀ r ∈ expected.holders, r ∈ actual.holders))

def decideFits : (actual expected : List (LTy V)) → Decidable (Fits actual expected)
  | [], [] => isTrue trivial
  | a :: as, b :: bs =>
      letI := decideCovers a b
      letI := decideFits as bs
      inferInstanceAs (Decidable (a.Covers b ∧ Fits as bs))
  | [], _ :: _ | _ :: _, [] => isFalse id

def decideGiven (kind : GivenKind V) (ins : List V.Ty) (out : V.Ty) :
    Decidable (kind.Typed ins out) := by
  cases kind with
  | request key => exact inferInstanceAs (Decidable (ins.length = 1))
  | coin law =>
      unfold GivenKind.Typed
      cases h : V.law law with
      | none => exact isFalse fun ⟨_, found, _⟩ => by rw [h] at found; contradiction
      | some sig =>
          if agree : sig.ins = ins ∧ sig.out = out then exact isTrue ⟨sig, h, agree⟩
          else exact isFalse fun ⟨_, same, found⟩ => by rw [h] at same; cases same; exact agree found

/-- Resolve the written operation on the actual located operands. The role list on an
application is ordered by callee role. The returned ports use the very same role map. -/
def ProtocolOp.read (hs : Headers V) : (raw : ProtocolRaw V) → (ins : List (LTy V)) →
    Except (Finding (LTy V) (ProtocolRaw V)) ((res : List (LTy V)) × ProtocolOp V hs ins res)
  | .compute roles raw, ins =>
      match LocalOp.read hs.fns raw (ins.map (·.ty)) with
      | .error fail => .error ⟨fail.rule, .operation (.compute roles raw)⟩
      | .ok ⟨_, op⟩ =>
          if held : ∀ a ∈ ins, ∀ r ∈ roles, r ∈ a.holders then
            .ok ⟨_, .compute roles op ins rfl held⟩
          else .error ⟨.operands, .given ins⟩
  | .event (.flow kind giver getters) τ, [⟨actual, holders⟩] =>
      if τ = actual then
        if ok : giver ∈ holders ∧ giver ∉ getters then .ok ⟨_, .flow kind giver getters ok.1 ok.2⟩
        else .error ⟨.operands, .operation (.event (.flow kind giver getters) τ)⟩
      else .error ⟨.operands, .types [⟨τ, holders⟩] [⟨actual, holders⟩]⟩
  | .event (.flow ..) _, ins => .error ⟨.operands, .number 1 ins.length⟩
  | .event (.given kind owner hearers) τ, ins =>
      letI := decideGiven kind (ins.map (·.ty)) τ
      if typed : kind.Typed (ins.map (·.ty)) τ then
        if ok : (∀ a ∈ ins, owner ∈ a.holders) ∧ owner ∉ hearers then
          .ok ⟨_, .given kind owner hearers ins τ typed ok.1 ok.2⟩
        else .error ⟨.operands, .operation (.event (.given kind owner hearers) τ)⟩
      else .error ⟨.operands, .operation (.event (.given kind owner hearers) τ)⟩
  | .narrow roles, [⟨_, holders⟩] =>
      if among : ∀ r ∈ roles, r ∈ holders then .ok ⟨_, .narrow roles among⟩
      else .error ⟨.operands, .operation (.narrow roles)⟩
  | .narrow _, ins => .error ⟨.operands, .number 1 ins.length⟩
  | .apply key roles, ins =>
      match Member.withKey (·.key) key hs.protocols with
      | [⟨hdr, callee⟩] =>
          if distinct : roles.Nodup then
            if covers : roles.length = hdr.roles then
              let ports := hdr.ins.map (LTy.map (RoleMap.ofList roles distinct).to)
              letI := decideFits ins ports
              if fits : Fits ins ports then .ok ⟨_, .apply callee roles distinct covers ins fits⟩
              else .error ⟨.operands, .types ports ins⟩
            else .error ⟨.operands, .number hdr.roles roles.length⟩
          else .error ⟨.operands, .operation (.apply key roles)⟩
      | found => .error ⟨.callee, .callee key found.length⟩

/-- The printed operation is recovered with its exact operands, result ports and callee. -/
theorem ProtocolOp.read_print {hs : Headers V} (distinct : hs.keys.Nodup) :
    ∀ {ins outs} (o : ProtocolOp V hs ins outs),
      ProtocolOp.read hs o.print ins = .ok ⟨outs, o⟩ := by
  have uniqueFunctions := (List.nodup_append.mp distinct).1
  have uniqueProtocols := (List.nodup_append.mp distinct).2.1
  intro ins outs o
  cases o with
  | compute roles op operands types held =>
      subst types
      simp only [ProtocolOp.print, ProtocolOp.read, LocalOp.read_print uniqueFunctions]
      rw [dite_eq_left held]
  | flow kind giver getters holds apart =>
      simp only [ProtocolOp.print, ProtocolOp.read, ↓reduceIte]
      rw [dite_eq_left (And.intro holds apart)]
  | given kind owner hearers ins τ typed held apart =>
      simp only [ProtocolOp.print, ProtocolOp.read, dite_eq_left typed]
      rw [dite_eq_left (And.intro held apart)]
  | narrow roles among =>
      simp only [ProtocolOp.print, ProtocolOp.read]
      rw [dite_eq_left among]
  | apply callee roles nd covers ins fits =>
      simp only [ProtocolOp.print, ProtocolOp.read, Member.withKey_key (·.key) callee uniqueProtocols,
        nd, covers, fits, ↓reduceDIte]

/-- Reading preserves the spelling of every accepted operation, including the type of a
flow and the key and ordered role map of an application. -/
theorem ProtocolOp.print_read {hs : Headers V} {ins outs : List (LTy V)}
    (raw : ProtocolRaw V) (o : ProtocolOp V hs ins outs)
    (found : ProtocolOp.read hs raw ins = .ok ⟨outs, o⟩) : o.print = raw := by
  cases raw with
  | compute roles raw =>
      simp only [ProtocolOp.read] at found
      split at found
      · cases found
      · rename_i res inner read
        split at found
        · cases found
          simp only [ProtocolOp.print, LocalOp.print_read raw inner read]
        · cases found
  | event cls τ =>
      cases cls with
      | flow kind giver getters =>
          cases ins with
          | nil => cases found
          | cons a rest =>
              cases rest with
              | cons => cases found
              | nil =>
                  cases a with
                  | mk actual holders =>
                      simp only [ProtocolOp.read] at found
                      split at found
                      · rename_i same
                        split at found
                        · cases found
                          cases same
                          rfl
                        · cases found
                      · cases found
      | given kind owner hearers =>
          simp only [ProtocolOp.read] at found
          split at found
          · split at found
            · cases found
              rfl
            · cases found
          · cases found
  | narrow roles =>
      cases ins with
      | nil => cases found
      | cons a rest =>
          cases rest with
          | cons => cases found
          | nil =>
              cases a
              simp only [ProtocolOp.read] at found
              split at found
              · cases found
                rfl
              · cases found
  | apply key roles =>
      simp only [ProtocolOp.read] at found
      split at found
      · rename_i hdr callee located
        have named : hdr.key = key := Member.key_of_withKey (·.key) key
          (found := ⟨hdr, callee⟩) (located ▸ List.mem_singleton_self _)
        split at found
        · split at found
          · split at found
            · cases found
              simp only [ProtocolOp.print, named]
            · cases found
          · cases found
        · cases found
      · cases found

def decideSingleton : (roles : List Role) → Decidable (∃ owner, roles = [owner])
  | [] => isFalse fun ⟨_, h⟩ => nomatch h
  | [r] => isTrue ⟨r, rfl⟩
  | _ :: _ :: _ => isFalse fun ⟨_, h⟩ => nomatch h

/-- Read located operations and controls without changing the order of participants. -/
def protocolRules (hs : Headers V) :
    Rules (protocolDialect V hs) (ProtocolRaw V) (List Role) where
  sameTy := inferInstanceAs (DecidableEq (LTy V))
  op := ProtocolOp.read hs
  who := Except.ok
  condition := fun ps t => inferInstanceAs
    (Decidable (t.ty = .bool ∧ (∀ r ∈ ps, r ∈ t.holders) ∧ ps ≠ []))
  alternatives := fun ps ⟨ty, holders⟩ =>
    match ty with
    | .variant key alts =>
        if ok : (∀ r ∈ ps, r ∈ holders) ∧ ps ≠ [] then
          some ⟨_, key, alts, rfl, rfl, ok⟩
        else none
    | _ => none
  count := fun ps t => inferInstanceAs
    (Decidable (t.ty = .nat ∧ (∀ r ∈ ps, r ∈ t.holders) ∧ ps ≠ []))
  gives := fun ps t => inferInstanceAs (Decidable (∀ r ∈ t.holders, r ∈ ps))
  attempt := decideSingleton
  printOp := ProtocolOp.print
  printWho := id

theorem protocolRules_lawful {hs : Headers V} (distinct : hs.keys.Nodup) :
    (protocolRules hs).Lawful where
  op := ProtocolOp.read_print distinct
  who _ := rfl
  alternatives ps t payloads := fun ⟨key, alts, same, eq, held, active⟩ => by
    obtain ⟨ty, holders⟩ := t
    change ty = .variant key alts at same
    subst ty
    subst payloads
    exact ⟨⟨key, alts, rfl, rfl, held, active⟩, by
      simp only [protocolRules, dite_eq_left (And.intro held active)]⟩

theorem protocolRules_canonical {hs : Headers V} : (protocolRules hs).Canonical where
  op := ProtocolOp.print_read
  who _ _ found := by cases found; rfl

end

end Zkc.Core
