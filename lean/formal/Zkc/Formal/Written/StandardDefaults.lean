module

public import Zkc.Formal.Written.FunctionMeaning

@[expose] public section
set_option autoImplicit false

namespace Zkc.Formal.Written.StandardDefaults
open Core

variable {C : Carriers Standard}

structure Sample (C : Carriers Standard) (t : Standard.Ty) where
  value : t.Val C
  valid : t.Valid C value

def truth : Sample C (.bool : Standard.Ty) := ⟨true, trivial⟩
/-- A valid default for each nominal carrier. -/
abbrev Nominals (C : Carriers Standard) := (k : Standard.TypeKey) → Sample C (.nominal k)

variable (nominal : Nominals C)
def bounded (n : Nat) (h : 0 < n) : Sample C (.fin n : Standard.Ty) := ⟨0, h⟩
def sequence {t : Standard.Ty} (s : Sample C t) (size : Option Nat) : Sample C (.seq t size) where
  value := List.replicate (size.getD 0) s.value
  valid := by
    constructor
    · intro v h
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp h
      exact s.valid
    · intro n eq
      simp [eq]

abbrev lifted (t : Zkc.Vocabulary.Ty) : Standard.Ty := t.mapNominal Sum.inl

def atomSample (a : Zkc.Vocabulary.Atom) : Sample C (lifted a.ty) := by
  cases a <;> exact nominal _

def elementSample : (item : Zkc.Vocabulary.Element) → Sample C (lifted item.ty)
  | .atom a => atomSample nominal a
  | .sized item n => sequence (elementSample item) (some n)

structure Samples (C : Carriers Standard) (ts : List Standard.Ty) where
  values : HList (Ty.Val C) ts
  valid : values.All (Ty.Valid C)

def single {t : Standard.Ty} (v : Sample C t) : Samples C [t] := ⟨.cons v.value .nil, v.valid, trivial⟩

local macro "default_output " sample:term : tactic => `(tactic| first
  | exact single truth
  | exact single ($sample _)
  | exact single (bounded _ (by decide))
  | exact single (sequence ($sample _) _)
  | exact single (sequence (bounded _ (by decide)) _))

set_option maxHeartbeats 2000000 in
/-- Every output signature admitted by the linked standard table has a valid inhabitant. -/
def rowSamples (k : Standard.RowKey) (sig : RowSignature Standard.TypeKey Standard.RowKey)
    (h : Standard.row k = some sig) : Samples C sig.outs := by
  cases k with
  | inr => cases h
  | inl key =>
    cases key with
    | field op f among =>
      cases op <;> cases f <;> cases among <;> cases h <;> default_output nominal
    | group op a =>
      cases op <;> cases a <;> try rename_i g
      all_goals first | cases h <;> default_output nominal | cases g <;> cases h <;> default_output nominal
    | seq op item size =>
      let sample := elementSample nominal item
      cases op <;> cases size <;> first
        | cases h <;> exact single sample
        | cases h <;> exact single (sequence sample _)
        | cases h <;> default_output nominal
        | cases item with
          | sized => cases h
          | atom a => cases a <;> cases h <;> default_output nominal
    | hash kind => cases kind <;> cases h <;> default_output nominal
    | pair => cases h; default_output nominal

theorem restricted {k : Standard.RowKey} {sig : RowSignature Standard.TypeKey Standard.RowKey}
    {d} (h : Standard.row k = some sig) (hk : sig.kind = .restricted d) :
    ∃ f, k = .inl (.field .nonzero f .all) ∧ d = .inl (.field .isNonzero f .all) := by
  cases k with
  | inr => cases h
  | inl key =>
    cases key with
    | field op f among => cases op <;> cases f <;> cases among <;> cases h <;> cases hk <;> exact ⟨_, rfl, rfl⟩
    | group op a => cases op <;> cases a <;> first | cases h <;> cases hk | rename_i g; cases g <;> cases h <;> cases hk
    | seq op item size =>
      cases op <;> cases size <;> first
        | cases h <;> cases hk
        | cases item with
          | sized => cases h
          | atom a => cases a <;> cases h <;> cases hk
    | hash kind => cases kind <;> cases h <;> cases hk
    | pair => cases h; cases hk

end Zkc.Formal.Written.StandardDefaults
