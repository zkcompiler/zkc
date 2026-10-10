import Zkc.Protocols.BackendProfiles.Encoding

set_option autoImplicit false

namespace Zkc.Protocols.BackendProfiles
open Lean (Json)
open Zkc.Realization.JsonArrays

-- Selected by the consumer from prior source admission, outside the payload.
-- Its interpretation and occurrence selection are explicit upstream premises.
structure Anchor where
  occurrence : String
  profile : Profile
  inputs : Nat
  body : Block String
  exports : List Nat
  deriving DecidableEq, Repr

def anchorOf (label : String) (r : Request) : Anchor :=
  ⟨label, r.profile, r.inputs, r.expected, r.expectedExports⟩

def termBound {Op : Type} : Nat → Term Op → Bool
  | 0, _ => false
  | _+1, .input i => i < 512
  | _+1, .literal _ => true
  | fuel+1, .apply _ a b => termBound fuel a && termBound fuel b
  | fuel+1, .choose c a b => termBound fuel c && termBound fuel a && termBound fuel b

def blockBound {Op : Type} (b : Block Op) : Bool :=
  b.length ≤ 256 && b.all (fun (i,t) => i < 512 && termBound 12 t)

def exportsBound (xs : List Nat) : Bool := xs.length ≤ 32 && xs.all (· < 512)

def bounded (r : Request) : Bool :=
  r.inputs ≤ 128 && blockBound r.expected && blockBound r.native &&
    exportsBound r.expectedExports && exportsBound r.nativeExports

inductive AdmissionDecision where
  | accepted
  | bounds
  | representation
  | sourceBinding
  | lowering (reason : Zkc.Protocols.BackendProfiles.Decision)
  deriving DecidableEq, Repr

-- The proposer is arbitrary: its JSON/schema decoding need not be sound.
-- The fuel bounds structural depth, not total process time or input bytes.
def validate (a : Anchor) (raw : Json) (label : String) (r : Request) : AdmissionDecision :=
  if !bounded r then .bounds
  else if !checkJson 32 raw (requestWire label r) then .representation
  else if a != anchorOf label r then .sourceBinding
  else if check r != .accepted then .lowering (check r)
  else .accepted

theorem accepted_facts (a : Anchor) (raw : Json) (label : String) (r : Request)
    (h : validate a raw label r = .accepted) :
    bounded r = true ∧ checkJson 32 raw (requestWire label r) = true ∧
      a = anchorOf label r ∧ check r = .accepted := by
  simp only [validate] at h
  split at h <;> try contradiction
  rename_i hb
  split at h <;> try contradiction
  rename_i hw
  split at h <;> try contradiction
  rename_i ha
  split at h <;> try contradiction
  rename_i hc
  simpa using And.intro hb (And.intro hw (And.intro ha hc))

theorem accepted_representation (a : Anchor) (raw : Json) (label : String) (r : Request)
    (h : validate a raw label r = .accepted) : raw = toJson (requestWire label r) :=
  checkJson_sound 32 raw _ (accepted_facts a raw label r h).2.1

theorem source_mismatch_refused (a : Anchor) (raw : Json) (label : String) (r : Request)
    (wrong : a ≠ anchorOf label r) : validate a raw label r ≠ .accepted := by
  intro h
  exact wrong (accepted_facts a raw label r h).2.2.1

theorem occurrence_mismatch_refused (a : Anchor) (raw : Json) (label : String) (r : Request)
    (wrong : a.occurrence ≠ label) : validate a raw label r ≠ .accepted := by
  apply source_mismatch_refused
  intro h
  exact wrong (congrArg Anchor.occurrence h)

theorem accepted_unique (a : Anchor) (raw : Json) (label other : String) (r s : Request)
    (hr : validate a raw label r = .accepted)
    (hs : validate a raw other s = .accepted) : label = other ∧ r = s :=
  representation_unique raw 32 32 label other r s
    (accepted_facts a raw label r hr).2.1 (accepted_facts a raw other s hs).2.1

-- No coercion from an unchecked Request exists. The indices keep the selected
-- consumer anchor and the exact JSON value attached to the proof consumer.
structure Admitted (a : Anchor) (raw : Json) where
  label : String
  request : Request
  checked : validate a raw label request = .accepted

end Zkc.Protocols.BackendProfiles
