module

public import ZkcSecurity.HashChain.Bytes
public import ZkcSecurity.Commitment.HistoryKeys
public import ZkcSecurity.Commitment.HashedLeaves
public import ZkcSecurity.Stage.Joint

@[expose] public section

/-! # Row calls and chain inputs on one byte hash

A verifier with committed tables over a native hash-chain suite calls one byte hash for two
purposes: the chain's binding, absorbing and request inputs, and the Merkle tree's leaf and node
inputs. This module fixes the byte encodings of both and proves them jointly injective, so that
the shared hash, read as a random oracle, is a random oracle on classified inputs.

**Chain inputs.** The chain absorbs the concrete reading's events (`Absorbed`): the events of base
operations and committed roots. A chain input the verifier makes (`ChainInput`) is a binding, an
absorption, or a counter block below `2^64` of a request whose occurrence is the event of a base
operation; roots are absorbed but never requested. `ChainCall` is the type of such inputs, encoded
by `ZkcSecurity.HashChain.Encoding.encodeInput`.

**Row calls.** A Merkle tree with hashed leaves makes leaf calls on rows and node calls on two
child digests (`RowCall`, with its `LeafHashing` model `rowHashing`). Tagged rows (`TaggedRows`)
encode them as

```text
leaf:  leafTag ‖ header ‖ row bytes
node:  nodeTag ‖ left ‖ right
```

with the digests in the chain's state encoding. The installed Keccak-256 rows use the tags
`"zkc.oracle.keccak256.leaf/0" ‖ 0x00` and `"zkc.oracle.keccak256.node/0" ‖ 0x00` and the header
`|codec|:u64le ‖ codec ‖ width:u64le ‖ height:u64le` (`keccakRows`), as in the
[installed binary Merkle schemes](../../../../../docs/spec/domains/oracles.md#installed-binary-merkle-schemes).

**Separation from bytes.** Tagged rows carry the separation of their tags: the leaf and node tags
and the three chain tags are pairwise non-prefix (`TagsSeparated`). Row calls and chain calls then
have jointly injective encodings (`TaggedRows.separated`): a tag that is not a prefix of another
fixes the role, a leaf input then fixes its row through the row codec, a node input its two
fixed-length digests, and a chain input is fixed by `encodeInput_injective`. The Keccak tags are separated (`keccak_tagsSeparated`); a row
tag that prefixes a chain tag is not (`TestsSecurity.HashChainJointFrame`). An `Encoding` packages
the encodings with this separation, and its `namespaces` are the joint stage's
`ZkcSecurity.Stage.Joint.Namespaces`.

**Classification.** Every byte string is classified (`Encoding.classify`) as the row call or the
chain call it encodes, or else as another input. The classification is injective
(`Encoding.classify_injective`), it reads every row call and every chain call back
(`classify_callBytes`, `classify_chainBytes`), and a classified request is always a chain call, so
its occurrence is the event of a base operation (`classify_request`).
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain.Joint
open ZkcSecurity.Commitment ZkcSecurity.HashChain.Encoding

section ChainInputs
variable {E Shape S : Type}

/-- A chain input the verifier makes: a binding, an absorption, or a counter block below `2^64`
of a request whose occurrence is the event of a base operation. -/
def ChainInput : Input (Absorbed E Shape S) S Bytes → Prop
  | .bind _ => True
  | .absorb _ _ => True
  | .request _ occurrence block => (∃ event, occurrence = .event event) ∧ block < 2 ^ 64
  | .other _ => False

/-- The chain inputs the verifier makes. -/
abbrev ChainCall (E Shape S : Type) := {input : Input (Absorbed E Shape S) S Bytes // ChainInput input}

theorem ChainCall.encodable (call : ChainCall E Shape S) : Encodable call.val := by
  obtain ⟨input, chain⟩ := call
  cases input with
  | bind => trivial
  | absorb => trivial
  | request _ _ _ => exact chain.2
  | other => exact chain.elim

end ChainInputs

section RowCalls
variable {Row S : Type}

/-- The calls of a Merkle tree with hashed leaves: a leaf call hashes a row, a node call two child
digests. -/
inductive RowCall (Row S : Type) where
  | leaf (row : Row)
  | node (left right : S)
  deriving DecidableEq

/-- The row calls as a model of Merkle trees with hashed leaves. -/
def rowHashing (Row S : Type) : LeafHashing Row (RowCall Row S) S where
  leaf := .leaf
  node := .node
  leafRow
    | .leaf row => some row
    | .node _ _ => none
  children
    | .node left right => some (left, right)
    | .leaf _ => none
  leafRow_leaf _ := rfl
  children_node _ _ := rfl

/-- The bytes of a row call under leaf and node tags, a leaf header and a row codec, with digests
in the state encoding. -/
def taggedCallBytes (leafTag nodeTag header : Bytes) (rowBytes : Row → Bytes) (stateBytes : S → Bytes) :
    RowCall Row S → Bytes
  | .leaf row => leafTag ++ header ++ rowBytes row
  | .node left right => nodeTag ++ stateBytes left ++ stateBytes right

/-- Two byte strings neither of which is a prefix of the other. -/
def Unrelated (first second : Bytes) : Prop := ¬ first <+: second ∧ ¬ second <+: first

instance (first second : Bytes) : Decidable (Unrelated first second) := by
  unfold Unrelated
  infer_instance

/-- The leaf and node tags and the three chain tags are pairwise non-prefix. -/
def TagsSeparated (leafTag nodeTag : Bytes) : Prop :=
  Unrelated leafTag nodeTag ∧ Unrelated leafTag bindTag ∧ Unrelated leafTag absorbTag ∧
    Unrelated leafTag requestTag ∧ Unrelated nodeTag bindTag ∧ Unrelated nodeTag absorbTag ∧
      Unrelated nodeTag requestTag

instance (leafTag nodeTag : Bytes) : Decidable (TagsSeparated leafTag nodeTag) := by
  unfold TagsSeparated
  infer_instance

/-- Tagged byte encodings of row calls: tags for leaf and node inputs that are separated from each
other and from the chain tags, a fixed leaf header and an injective row codec. -/
structure TaggedRows (Row : Type) where
  leafTag : Bytes
  nodeTag : Bytes
  /-- The tags are separated (`TagsSeparated`), stated as its conjunction. -/
  separatedTags : Unrelated leafTag nodeTag ∧ Unrelated leafTag bindTag ∧
    Unrelated leafTag absorbTag ∧ Unrelated leafTag requestTag ∧ Unrelated nodeTag bindTag ∧
      Unrelated nodeTag absorbTag ∧ Unrelated nodeTag requestTag
  header : Bytes
  rowBytes : Row → Bytes
  rowInjective : Function.Injective rowBytes

/-- Tagged rows' tags are separated. -/
theorem TaggedRows.tagsSeparated (rows : TaggedRows Row) : TagsSeparated rows.leafTag rows.nodeTag :=
  rows.separatedTags

/-- The bytes of a row call, with digests in the state encoding. -/
def TaggedRows.callBytes (rows : TaggedRows Row) (stateBytes : S → Bytes) : RowCall Row S → Bytes :=
  taggedCallBytes rows.leafTag rows.nodeTag rows.header rows.rowBytes stateBytes

variable {E Shape : Type}

/-- Row calls and chain calls have jointly injective encodings when the tags are separated, the
state encoding is injective with one length and the event encoding is injective. -/
theorem TaggedRows.separated (rows : TaggedRows Row) {stateBytes : S → Bytes}
    {eventBytes : Absorbed E Shape S → Bytes} {stateLength : ℕ}
    (stateLengths : ∀ state, (stateBytes state).length = stateLength)
    (stateInjective : Function.Injective stateBytes) (eventInjective : Function.Injective eventBytes) :
    Function.Injective (Sum.elim (rows.callBytes stateBytes)
      fun call : ChainCall E Shape S => encodeInput stateBytes eventBytes call.val) := by
  obtain ⟨leafNode, leafBind, leafAbsorb, leafRequest, nodeBind, nodeAbsorb, nodeRequest⟩ :=
    rows.separatedTags
  have chainTag : ∀ (tag rest : Bytes) (call : ChainCall E Shape S), Unrelated tag bindTag →
      Unrelated tag absorbTag → Unrelated tag requestTag →
        tag ++ rest ≠ encodeInput stateBytes eventBytes call.val := by
    rintro tag rest ⟨input, chain⟩ bind absorb request same
    cases input with
    | bind event => exact tag_append_ne bind same
    | absorb state event =>
        simp only [encodeInput, List.append_assoc] at same
        exact tag_append_ne absorb same
    | request state event block =>
        simp only [encodeInput, List.append_assoc] at same
        exact tag_append_ne request same
    | other => exact chain.elim
  intro first second same
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          congr 1
          cases first with
          | leaf row =>
              cases second with
              | leaf row' =>
                  simp only [Sum.elim_inl, TaggedRows.callBytes, taggedCallBytes, List.append_assoc,
                    List.append_cancel_left_eq] at same
                  rw [rows.rowInjective same]
              | node left right =>
                  simp only [Sum.elim_inl, TaggedRows.callBytes, taggedCallBytes, List.append_assoc] at same
                  exact absurd same (tag_append_ne leafNode)
          | node left right =>
              cases second with
              | leaf row =>
                  simp only [Sum.elim_inl, TaggedRows.callBytes, taggedCallBytes, List.append_assoc] at same
                  exact absurd same (tag_append_ne ⟨leafNode.2, leafNode.1⟩)
              | node left' right' =>
                  simp only [Sum.elim_inl, TaggedRows.callBytes, taggedCallBytes, List.append_assoc,
                    List.append_cancel_left_eq] at same
                  obtain ⟨lefts, rights⟩ := List.append_inj same
                    (by rw [stateLengths, stateLengths])
                  rw [stateInjective lefts, stateInjective rights]
      | inr second =>
          exfalso
          cases first with
          | leaf row =>
              simp only [Sum.elim_inl, Sum.elim_inr, TaggedRows.callBytes, taggedCallBytes,
                List.append_assoc] at same
              exact chainTag _ _ second leafBind leafAbsorb leafRequest same
          | node left right =>
              simp only [Sum.elim_inl, Sum.elim_inr, TaggedRows.callBytes, taggedCallBytes,
                List.append_assoc] at same
              exact chainTag _ _ second nodeBind nodeAbsorb nodeRequest same
  | inr first =>
      cases second with
      | inl second =>
          exfalso
          cases second with
          | leaf row =>
              simp only [Sum.elim_inl, Sum.elim_inr, TaggedRows.callBytes, taggedCallBytes,
                List.append_assoc] at same
              exact chainTag _ _ first leafBind leafAbsorb leafRequest same.symm
          | node left right =>
              simp only [Sum.elim_inl, Sum.elim_inr, TaggedRows.callBytes, taggedCallBytes,
                List.append_assoc] at same
              exact chainTag _ _ first nodeBind nodeAbsorb nodeRequest same.symm
      | inr second =>
          congr 1
          exact Subtype.ext (encodeInput_injective stateLengths stateInjective eventInjective
            first.encodable second.encodable same)

end RowCalls

section Keccak

/-- `n` as eight little-endian bytes, modulo `2^64`. -/
def u64le (n : ℕ) : Bytes := (u64be n).reverse

/-- The leaf tag of the installed Keccak-256 rows. -/
def keccakLeafTag : Bytes := tag "zkc.oracle.keccak256.leaf/0"

/-- The node tag of the installed Keccak-256 rows. -/
def keccakNodeTag : Bytes := tag "zkc.oracle.keccak256.node/0"

/-- The Keccak tags and the chain tags are pairwise non-prefix. -/
theorem keccak_tagsSeparated : TagsSeparated keccakLeafTag keccakNodeTag := by
  decide

/-- The leaf header of a table: the codec's length and name, the width and the height. -/
def keccakHeader (codec : Bytes) (width height : ℕ) : Bytes :=
  u64le codec.length ++ codec ++ u64le width ++ u64le height

/-- The installed Keccak-256 rows of one table shape, with an injective row codec. -/
def keccakRows {Row : Type} (codec : Bytes) (width height : ℕ) (rowBytes : Row → Bytes)
    (rowInjective : Function.Injective rowBytes) : TaggedRows Row where
  leafTag := keccakLeafTag
  nodeTag := keccakNodeTag
  separatedTags := keccak_tagsSeparated
  header := keccakHeader codec width height
  rowBytes := rowBytes
  rowInjective := rowInjective

end Keccak

section Encodings
variable {E Shape S Query : Type}

/-- The byte encodings of the shared hash's inputs: hash calls of the commitment and chain calls
of the provider, with injective state and event encodings, states of one length, and namespace
separation. -/
structure Encoding (E Shape S Query : Type) where
  callBytes : Query → Bytes
  stateBytes : S → Bytes
  eventBytes : Absorbed E Shape S → Bytes
  stateLength : ℕ
  stateLengths : ∀ state, (stateBytes state).length = stateLength
  stateInjective : Function.Injective stateBytes
  eventInjective : Function.Injective eventBytes
  separated : Function.Injective (Sum.elim callBytes
    fun call : ChainCall E Shape S => encodeInput stateBytes eventBytes call.val)

namespace Encoding
variable (encoding : Encoding E Shape S Query)

/-- The bytes of a chain input. -/
def chainBytes (input : Input (Absorbed E Shape S) S Bytes) : Bytes :=
  encodeInput encoding.stateBytes encoding.eventBytes input

/-- The encodings as the joint stage's namespaces. -/
def namespaces : Stage.Joint.Namespaces Query (ChainCall E Shape S) Bytes where
  hash := encoding.callBytes
  chain call := encoding.chainBytes call.val
  separated := encoding.separated

/-- The bytes of a classified input: a hash call or a chain input. -/
def bytesOf : Query ⊕ Input (Absorbed E Shape S) S Bytes → Bytes
  | .inl call => encoding.callBytes call
  | .inr input => encoding.chainBytes input

open Classical in
/-- The classification of bytes: the hash call or the chain call they encode, or another input. -/
noncomputable def classify (bytes : Bytes) : Query ⊕ Input (Absorbed E Shape S) S Bytes :=
  if found : ∃ target : Query ⊕ ChainCall E Shape S,
      Sum.elim encoding.callBytes (fun call : ChainCall E Shape S => encoding.chainBytes call.val)
        target = bytes then
    match Classical.choose found with
    | .inl call => .inl call
    | .inr call => .inr call.val
  else .inr (.other bytes)

theorem bytesOf_classify (bytes : Bytes) : encoding.bytesOf (encoding.classify bytes) = bytes := by
  unfold classify
  split_ifs with found
  · have spec := Classical.choose_spec found
    revert spec
    cases Classical.choose found <;> intro spec <;> exact spec
  · rfl

/-- The classification is injective. -/
theorem classify_injective : Function.Injective encoding.classify := fun first second same => by
  rw [← encoding.bytesOf_classify first, ← encoding.bytesOf_classify second, same]

/-- A hash call's bytes are classified as that call. -/
theorem classify_callBytes (call : Query) :
    encoding.classify (encoding.callBytes call) = .inl call := by
  have found : ∃ target : Query ⊕ ChainCall E Shape S,
      Sum.elim encoding.callBytes (fun call : ChainCall E Shape S => encoding.chainBytes call.val)
        target = encoding.callBytes call := ⟨.inl call, rfl⟩
  unfold classify
  rw [dite_eq_left_of_eq_true (eq_true found)]
  have chosen := encoding.separated ((Classical.choose_spec found).trans
    (show encoding.callBytes call = Sum.elim encoding.callBytes
      (fun call : ChainCall E Shape S => encoding.chainBytes call.val) (.inl call) from rfl))
  rw [chosen]

/-- A chain call's bytes are classified as that call. -/
theorem classify_chainBytes (call : ChainCall E Shape S) :
    encoding.classify (encoding.chainBytes call.val) = .inr call.val := by
  obtain ⟨input, chain⟩ := call
  have found : ∃ target : Query ⊕ ChainCall E Shape S,
      Sum.elim encoding.callBytes (fun call : ChainCall E Shape S => encoding.chainBytes call.val)
        target = encoding.chainBytes input := ⟨.inr ⟨input, chain⟩, rfl⟩
  unfold classify
  rw [dite_eq_left_of_eq_true (eq_true found)]
  have chosen := encoding.separated ((Classical.choose_spec found).trans
    (show encoding.chainBytes input = Sum.elim encoding.callBytes
      (fun call : ChainCall E Shape S => encoding.chainBytes call.val) (.inr ⟨input, chain⟩) from rfl))
  rw [chosen]

/-- Bytes classified as a hash call are that call's bytes. -/
theorem eq_of_classify_inl {bytes : Bytes} {call : Query} (classified : encoding.classify bytes = .inl call) :
    bytes = encoding.callBytes call := by
  rw [← encoding.bytesOf_classify bytes, classified]
  rfl

/-- A classified input is a chain call or another input. -/
theorem classify_inr {bytes : Bytes} {input : Input (Absorbed E Shape S) S Bytes}
    (classified : encoding.classify bytes = .inr input) :
    ChainInput input ∨ input = .other bytes := by
  unfold classify at classified
  split_ifs at classified with found
  · revert classified
    cases Classical.choose found with
    | inl call => intro classified; cases classified
    | inr call =>
        intro classified
        cases classified
        exact Or.inl call.property
  · cases classified
    exact Or.inr rfl

/-- A classified request is a chain call: its occurrence is the event of a base operation and its
counter is below `2^64`. -/
theorem classify_request {bytes : Bytes} {state : S} {occurrence : Absorbed E Shape S} {block : ℕ}
    (classified : encoding.classify bytes = .inr (.request state occurrence block)) :
    ∃ event, occurrence = .event event := by
  rcases encoding.classify_inr classified with chain | other
  · exact chain.1
  · cases other

/-- The chain input bytes stand for: the classified chain input, or another input for hash
calls. -/
noncomputable def chainInput (bytes : Bytes) : Input (Absorbed E Shape S) S Bytes :=
  match encoding.classify bytes with
  | .inl _ => .other bytes
  | .inr input => input

theorem chainInput_of_inr {bytes : Bytes} {input : Input (Absorbed E Shape S) S Bytes}
    (classified : encoding.classify bytes = .inr input) : encoding.chainInput bytes = input := by
  simp only [chainInput, classified]

theorem chainInput_of_inl {bytes : Bytes} {call : Query} (classified : encoding.classify bytes = .inl call) :
    encoding.chainInput bytes = .other bytes := by
  simp only [chainInput, classified]

/-- The chain input of a chain call's bytes is that call. -/
theorem chainInput_chainBytes (call : ChainCall E Shape S) :
    encoding.chainInput (encoding.chainBytes call.val) = call.val :=
  encoding.chainInput_of_inr (encoding.classify_chainBytes call)

end Encoding

/-- Tagged rows with separated tags, an injective state encoding of one length and an injective
event encoding give the encodings of the shared hash's inputs. -/
def TaggedRows.encoding {Row : Type} (rows : TaggedRows Row) (stateBytes : S → Bytes)
    (eventBytes : Absorbed E Shape S → Bytes) (stateLength : ℕ)
    (stateLengths : ∀ state, (stateBytes state).length = stateLength)
    (stateInjective : Function.Injective stateBytes) (eventInjective : Function.Injective eventBytes) :
    Encoding E Shape S (RowCall Row S) where
  callBytes := rows.callBytes stateBytes
  stateBytes := stateBytes
  eventBytes := eventBytes
  stateLength := stateLength
  stateLengths := stateLengths
  stateInjective := stateInjective
  eventInjective := eventInjective
  separated := rows.separated stateLengths stateInjective eventInjective

end Encodings

end ZkcSecurity.HashChain.Joint
