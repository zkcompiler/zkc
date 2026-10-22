module

public import ZkcSecurity.HashChain.Model
public import ZkcSecurity.FiatShamir.Obligations

@[expose] public section

/-! The byte encoding of hash-chain inputs.

A [native hash-chain suite](../../../../../docs/spec/ir/construction.md#native-hash-chain-suites)
feeds its byte hash with inputs of three shapes, each beginning with a role tag:

```text
bind:     t_bind    ‖ enc(e)
absorb:   t_absorb  ‖ s ‖ enc(e)
request:  t_request ‖ s ‖ enc(e) ‖ k:u64be
```

with `s` a full digest and `k` a counter block. The tags are
`"zkc.hash-chain.bind/0" ‖ 0x00`, `"zkc.hash-chain.absorb/0" ‖ 0x00` and
`"zkc.hash-chain.request/0" ‖ 0x00`; none is a prefix of another
(`tags_not_prefix`). Events are framed as

```text
frame(kind, label, data) = kind:u8 ‖ |label|:u64be ‖ label ‖ |data|:u64be ‖ data
```

A frame determines its own length, so a frame followed by any bytes parses
uniquely (`frame_append_inj`) and the encoding of bounded frames is injective
and prefix-free in the sense of the serialization obligation of
[history providers](../../../../../docs/spec/ir/construction-obligations.md#history-providers)
(`frame_prefixFree`). The events of the installed suites are the binding (the
domain, the suite name and the invocation root, as three frames), messages
(kind 1) and requests (kind 2, the requested length as data); their encoding is
injective (`NativeEvent.encode_injective`).

`encodeInput` sends a classified input to its bytes. Its restriction to chain
inputs with counters below `2^64` is injective whenever states have a fixed
length and the event encoding is injective (`encodeInput_injective`): the role
tag fixes the role, the state has a fixed length, and the counter is the last
eight bytes. So the byte hash, read as a random oracle, is a random oracle on
classified inputs, which `ZkcSecurity.HashChain.Model` uses.
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain.Encoding

/-- Byte strings. -/
abbrev Bytes := List UInt8

section Integers

/-- `n` as eight big-endian bytes, modulo `2^64`. -/
def u64be (n : ℕ) : Bytes := [7, 6, 5, 4, 3, 2, 1, 0].map fun index => UInt8.ofNat (n / 256 ^ index)

@[simp] theorem u64be_length (n : ℕ) : (u64be n).length = 8 := rfl

/-- The residues modulo `256^k` agree when the first `k` base-256 digits agree. -/
theorem mod_pow_eq_of_digits {n m : ℕ} :
    ∀ count, (∀ index < count, n / 256 ^ index % 256 = m / 256 ^ index % 256) →
      n % 256 ^ count = m % 256 ^ count
  | 0, _ => by simp [Nat.mod_one]
  | count + 1, digits => by
      rw [Nat.mod_pow_succ, Nat.mod_pow_succ,
        mod_pow_eq_of_digits count fun index below => digits index (by omega),
        digits count (by omega)]

/-- Eight big-endian bytes determine a number below `2^64`. -/
theorem u64be_injective {n m : ℕ} (smallN : n < 2 ^ 64) (smallM : m < 2 ^ 64)
    (same : u64be n = u64be m) : n = m := by
  have digit : ∀ index ∈ [7, 6, 5, 4, 3, 2, 1, 0],
      n / 256 ^ index % 256 = m / 256 ^ index % 256 := by
    intro index member
    have bytes := congrArg (fun bytes : Bytes => bytes.map UInt8.toNat) same
    simp only [u64be, List.map_map, Function.comp_def, UInt8.toNat_ofNat'] at bytes
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at bytes
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have residues := mod_pow_eq_of_digits 8 fun index below => digit index (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega)
  rwa [Nat.mod_eq_of_lt (by simpa using smallN), Nat.mod_eq_of_lt (by simpa using smallM)]
    at residues

end Integers

section Frames

/-- A framed event: its kind byte, label and data. -/
structure Frame where
  kind : UInt8
  label : Bytes
  data : Bytes
  deriving DecidableEq

/-- `kind ‖ |label|:u64be ‖ label ‖ |data|:u64be ‖ data`. -/
def Frame.encode (frame : Frame) : Bytes :=
  frame.kind :: (u64be frame.label.length ++ frame.label ++ u64be frame.data.length ++ frame.data)

/-- Label and data lengths below `2^64`, as the eight-byte length fields require. -/
def Frame.Bounded (frame : Frame) : Prop :=
  frame.label.length < 2 ^ 64 ∧ frame.data.length < 2 ^ 64

/-- A frame followed by any bytes determines the frame and the bytes after it. -/
theorem frame_append_inj {first second : Frame} (firstBounded : first.Bounded)
    (secondBounded : second.Bounded) {rest other : Bytes}
    (same : first.encode ++ rest = second.encode ++ other) : first = second ∧ rest = other := by
  obtain ⟨kind, label, data⟩ := first
  obtain ⟨kind', label', data'⟩ := second
  simp only [Frame.encode, List.cons_append, List.cons.injEq, List.append_assoc] at same
  obtain ⟨kinds, afterKind⟩ := same
  obtain ⟨labelLength, afterLabelLength⟩ := List.append_inj afterKind (by simp)
  have labels : label.length = label'.length :=
    u64be_injective firstBounded.1 secondBounded.1 labelLength
  obtain ⟨sameLabel, afterLabel⟩ := List.append_inj afterLabelLength labels
  obtain ⟨dataLength, afterDataLength⟩ := List.append_inj afterLabel (by simp)
  have datas : data.length = data'.length :=
    u64be_injective firstBounded.2 secondBounded.2 dataLength
  obtain ⟨sameData, rests⟩ := List.append_inj afterDataLength datas
  subst kinds sameLabel sameData
  exact ⟨rfl, rests⟩

/-- The encoding of bounded frames is injective and prefix-free. -/
theorem frame_prefixFree :
    FiatShamir.Obligations.PrefixFreeEncoding fun frame : {frame : Frame // frame.Bounded} =>
      frame.val.encode := by
  intro first second rest same
  obtain ⟨equal, rest⟩ := frame_append_inj first.property second.property
    (same.trans (List.append_nil _).symm)
  exact ⟨Subtype.ext equal, rest⟩

end Frames

section Tags

/-- An ASCII role name followed by a zero byte. -/
def tag (name : String) : Bytes := name.toList.map (fun character => UInt8.ofNat character.toNat) ++ [0]

/-- The tag of binding inputs. -/
def bindTag : Bytes := tag "zkc.hash-chain.bind/0"
/-- The tag of absorbing inputs. -/
def absorbTag : Bytes := tag "zkc.hash-chain.absorb/0"
/-- The tag of request inputs. -/
def requestTag : Bytes := tag "zkc.hash-chain.request/0"

/-- No role tag is a prefix of another. -/
theorem tags_not_prefix :
    ¬ bindTag <+: absorbTag ∧ ¬ absorbTag <+: bindTag ∧ ¬ bindTag <+: requestTag ∧
      ¬ requestTag <+: bindTag ∧ ¬ absorbTag <+: requestTag ∧ ¬ requestTag <+: absorbTag := by
  decide

/-- Bytes that begin with two different tags would make one tag a prefix of the
other. -/
theorem tag_append_ne {first second : Bytes}
    (unrelated : ¬ first <+: second ∧ ¬ second <+: first) {rest other : Bytes} :
    first ++ rest ≠ second ++ other := by
  intro same
  rcases List.prefix_or_prefix_of_prefix (List.prefix_append first rest)
      (same ▸ List.prefix_append second other) with prefixed | prefixed
  · exact unrelated.1 prefixed
  · exact unrelated.2 prefixed

end Tags

section Inputs
variable {E S X : Type}

/-- The bytes of a classified input: the role tag, the state, the event's
encoding and, for a request, the counter block. Other inputs are their own
bytes. -/
def encodeInput (stateBytes : S → Bytes) (eventBytes : E → Bytes) : Input E S Bytes → Bytes
  | .bind event => bindTag ++ eventBytes event
  | .absorb state event => absorbTag ++ stateBytes state ++ eventBytes event
  | .request state event block => requestTag ++ stateBytes state ++ eventBytes event ++ u64be block
  | .other bytes => bytes

/-- A chain input with a counter below `2^64`. -/
def Encodable : Input E S Bytes → Prop
  | .bind _ => True
  | .absorb _ _ => True
  | .request _ _ block => block < 2 ^ 64
  | .other _ => False

/-- Chain inputs with counters below `2^64` have distinct bytes when states have
one length and events are encoded injectively. -/
theorem encodeInput_injective {stateBytes : S → Bytes} {eventBytes : E → Bytes} {width : ℕ}
    (stateLength : ∀ state, (stateBytes state).length = width)
    (stateInjective : Function.Injective stateBytes) (eventInjective : Function.Injective eventBytes)
    {first second : Input E S Bytes} (firstEncodable : Encodable first)
    (secondEncodable : Encodable second)
    (same : encodeInput stateBytes eventBytes first = encodeInput stateBytes eventBytes second) :
    first = second := by
  have ⟨bindAbsorb, absorbBind, bindRequest, requestBind, absorbRequest, requestAbsorb⟩ :=
    tags_not_prefix
  cases first with
  | other => exact firstEncodable.elim
  | bind event =>
      cases second with
      | other => exact secondEncodable.elim
      | bind event' =>
          simp only [encodeInput, List.append_cancel_left_eq] at same
          rw [eventInjective same]
      | absorb state' event' =>
          simp only [encodeInput, List.append_assoc] at same
          exact absurd same (tag_append_ne ⟨bindAbsorb, absorbBind⟩)
      | request state' event' block' =>
          simp only [encodeInput, List.append_assoc] at same
          exact absurd same (tag_append_ne ⟨bindRequest, requestBind⟩)
  | absorb state event =>
      cases second with
      | other => exact secondEncodable.elim
      | bind event' =>
          simp only [encodeInput, List.append_assoc] at same
          exact absurd same (tag_append_ne ⟨absorbBind, bindAbsorb⟩)
      | absorb state' event' =>
          simp only [encodeInput, List.append_assoc, List.append_cancel_left_eq] at same
          obtain ⟨states, events⟩ := List.append_inj same (by rw [stateLength, stateLength])
          rw [stateInjective states, eventInjective events]
      | request state' event' block' =>
          simp only [encodeInput, List.append_assoc] at same
          exact absurd same (tag_append_ne ⟨absorbRequest, requestAbsorb⟩)
  | request state event block =>
      cases second with
      | other => exact secondEncodable.elim
      | bind event' =>
          simp only [encodeInput, List.append_assoc] at same
          exact absurd same (tag_append_ne ⟨requestBind, bindRequest⟩)
      | absorb state' event' =>
          simp only [encodeInput, List.append_assoc] at same
          exact absurd same (tag_append_ne ⟨requestAbsorb, absorbRequest⟩)
      | request state' event' block' =>
          simp only [encodeInput, List.append_assoc, List.append_cancel_left_eq] at same
          obtain ⟨states, same⟩ := List.append_inj same (by rw [stateLength, stateLength])
          have lengths : (eventBytes event ++ u64be block).length =
              (eventBytes event' ++ u64be block').length := by rw [same]
          simp only [List.length_append, u64be_length, Nat.add_right_cancel_iff] at lengths
          obtain ⟨events, blocks⟩ := List.append_inj same lengths
          rw [stateInjective states, eventInjective events,
            u64be_injective firstEncodable secondEncodable blocks]

end Inputs

section NativeEvents

/-- The events of the installed native suites. -/
inductive NativeEvent where
  /-- The binding of the first state: the suite's name and the invocation root. -/
  | binding (suite root : Bytes)
  /-- An absorbed message with its label. -/
  | message (label data : Bytes)
  /-- A request occurrence: its label and the requested length. -/
  | request (label : Bytes) (length : ℕ)
  deriving DecidableEq

/-- The ASCII bytes of a label or fixed datum. -/
def ascii (text : String) : Bytes := text.toList.map fun character => UInt8.ofNat character.toNat

/-- `frame(0, "domain", "zkc.artifact/0") ‖ frame(0, "suite", suite) ‖
frame(1, "binding", root)`, `frame(1, label, data)` and
`frame(2, label, length:u64be)`. -/
def NativeEvent.encode : NativeEvent → Bytes
  | .binding suite root =>
      (Frame.mk 0 (ascii "domain") (ascii "zkc.artifact/0")).encode ++
        (Frame.mk 0 (ascii "suite") suite).encode ++ (Frame.mk 1 (ascii "binding") root).encode
  | .message label data => (Frame.mk 1 label data).encode
  | .request label length => (Frame.mk 2 label (u64be length)).encode

/-- Lengths below `2^64`. -/
def NativeEvent.Bounded : NativeEvent → Prop
  | .binding suite root => suite.length < 2 ^ 64 ∧ root.length < 2 ^ 64
  | .message label data => label.length < 2 ^ 64 ∧ data.length < 2 ^ 64
  | .request label length => label.length < 2 ^ 64 ∧ length < 2 ^ 64

/-- Bounded native events have distinct encodings. -/
theorem NativeEvent.encode_injective {first second : NativeEvent} (firstBounded : first.Bounded)
    (secondBounded : second.Bounded) (same : first.encode = second.encode) : first = second := by
  have fixed : (Frame.mk 0 (ascii "domain") (ascii "zkc.artifact/0")).Bounded := by
    constructor <;> decide
  cases first with
  | binding suite root =>
      cases second with
      | binding suite' root' =>
          simp only [NativeEvent.encode, List.append_assoc] at same
          obtain ⟨-, same⟩ := frame_append_inj fixed fixed same
          have suiteLabel : (ascii "suite").length < 2 ^ 64 := by decide
          have bindingLabel : (ascii "binding").length < 2 ^ 64 := by decide
          obtain ⟨suites, same⟩ := frame_append_inj (first := Frame.mk 0 (ascii "suite") suite)
            (second := Frame.mk 0 (ascii "suite") suite') ⟨suiteLabel, firstBounded.1⟩
            ⟨suiteLabel, secondBounded.1⟩ same
          obtain ⟨roots, -⟩ := frame_append_inj (first := Frame.mk 1 (ascii "binding") root)
            (second := Frame.mk 1 (ascii "binding") root') ⟨bindingLabel, firstBounded.2⟩
            ⟨bindingLabel, secondBounded.2⟩ (rest := []) (other := [])
            (by simpa using same)
          cases suites
          cases roots
          rfl
      | message label data =>
          simp only [NativeEvent.encode, Frame.encode, List.cons_append, List.cons.injEq] at same
          exact absurd same.1 (by decide)
      | request label length =>
          simp only [NativeEvent.encode, Frame.encode, List.cons_append, List.cons.injEq] at same
          exact absurd same.1 (by decide)
  | message label data =>
      cases second with
      | binding suite root =>
          simp only [NativeEvent.encode, Frame.encode, List.cons_append, List.cons.injEq] at same
          exact absurd same.1 (by decide)
      | message label' data' =>
          obtain ⟨frames, -⟩ := frame_append_inj (rest := []) (other := [])
            (first := Frame.mk 1 label data) (second := Frame.mk 1 label' data') firstBounded
            secondBounded (by simpa [NativeEvent.encode] using same)
          cases frames
          rfl
      | request label' length' =>
          simp only [NativeEvent.encode, Frame.encode, List.cons.injEq] at same
          exact absurd same.1 (by decide)
  | request label length =>
      cases second with
      | binding suite root =>
          simp only [NativeEvent.encode, Frame.encode, List.cons_append, List.cons.injEq] at same
          exact absurd same.1 (by decide)
      | message label' data' =>
          simp only [NativeEvent.encode, Frame.encode, List.cons.injEq] at same
          exact absurd same.1 (by decide)
      | request label' length' =>
          obtain ⟨frames, -⟩ := frame_append_inj (rest := []) (other := [])
            (first := Frame.mk 2 label (u64be length)) (second := Frame.mk 2 label' (u64be length'))
            ⟨firstBounded.1, by simp⟩ ⟨secondBounded.1, by simp⟩
            (by simpa [NativeEvent.encode] using same)
          simp only [Frame.mk.injEq, true_and] at frames
          rw [frames.1, u64be_injective firstBounded.2 secondBounded.2 frames.2]

/-- The encoding of bounded native events, as the event encoding of a hash chain,
is injective. -/
theorem NativeEvent.encode_injective_bounded :
    Function.Injective fun event : {event : NativeEvent // event.Bounded} => event.val.encode :=
  fun first second same => Subtype.ext (encode_injective first.property second.property same)

/-- Fixed-length digests as bytes are injective with one length. -/
theorem ofFn_injective {length : ℕ} :
    Function.Injective fun digest : Fin length → UInt8 => List.ofFn digest :=
  fun _ _ same => List.ofFn_injective same

end NativeEvents

end ZkcSecurity.HashChain.Encoding
