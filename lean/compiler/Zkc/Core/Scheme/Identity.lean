module

public import Zkc.Core.Format.Canonical
public import Zkc.Core.Scheme.Deployed
public import Zkc.Core.Program.EraseProgram

@[expose] public section

/-!
Canonical byte encoding of declarations and reachable erased definitions, yielding a
deterministic deployment identity (`schemeIdentity`, `deployedIdentity`) that:
1. emits strictly canonical bytes (`< 256`, `deployedIdentity_bytes`);
2. reads only the declaration and the erased definitions in `Deployed.closure`, ignoring
   annotations, associations, and unreachable definitions (`deployedIdentity_reads`).
-/

namespace Zkc.Core

/-! ## Canonical encoding helpers -/

/-- Canonical byte encoders for the abstract keys of a vocabulary, used to include reachable
erased definitions in a deployed scheme's canonical identity. -/
structure VocabEncoder (V : Vocabulary) where
  typeKey : V.TypeKey → List Nat
  rowKey : V.RowKey → List Nat
  lawKey : V.LawKey → List Nat

/-- Encode a natural as shortest-form unsigned LEB128 bytes. -/
def encodeNat (n : Nat) : List Nat := formatNat.write n

/-- Encode a boolean as a single canonical byte (`0` or `1`). -/
def encodeBool (b : Bool) : List Nat := formatBool.write b

/-- Encode a key by its number. -/
def encodeKey (k : Key) : List Nat := encodeNat k.number

/-- Encode a length-prefixed list using `f` for each element. -/
def encodeList {A : Type} (f : A → List Nat) (xs : List A) : List Nat :=
  encodeNat xs.length ++ writeCanonicalMany f xs

/-- Encode an optional value with a one-byte tag (`0` for `none`, `1` for `some`). -/
def encodeOption {A : Type} (f : A → List Nat) : Option A → List Nat
  | none => [0]
  | some a => 1 :: f a

/-- Encode a UTF-8 string as length-prefixed bytes. -/
def encodeString (s : String) : List Nat :=
  let bytes := s.toUTF8.toList.map UInt8.toNat
  encodeNat bytes.length ++ bytes

/-- Encode an ASCII/UTF-8 label string directly as its raw bytes (`< 256`). -/
def encodeLabelBytes (s : String) : List Nat :=
  s.toUTF8.toList.map UInt8.toNat

/-- Encode a site (`through`, `key`) canonically. -/
def encodeSite (s : Site) : List Nat :=
  encodeList encodeKey s.through ++ encodeKey s.key

/-- Encode a `RoleKind` as a single canonical tag byte. -/
def encodeRoleKind : RoleKind → List Nat
  | .online => [0]
  | .offline => [1]
  | .service => [2]

/-- Encode a `ModuleRef`. -/
def encodeModuleRef (m : ModuleRef) : List Nat :=
  encodeList (fun p => encodeKey p.1 ++ encodeKey p.2) m.members

/-- Encode a `Construction`. -/
def encodeConstruction : Construction → List Nat
  | .interactive => [0]
  | .derived suite tag => 1 :: encodeModuleRef suite ++ encodeOption (encodeList encodeNat) tag
  | .authored => [2]

/-- Encode a `Layout`. -/
def encodeLayout (l : Layout) : List Nat :=
  encodeModuleRef l.module ++
    encodeList encodeSite l.carry ++
    encodeList (fun p => encodeSite p.1 ++ encodeKey p.2) l.recover

/-- Encode a `Grind`. -/
def encodeGrind (g : Grind) : List Nat :=
  encodeNat g.bits ++ encodeList encodeSite g.sites

/-- Encode a `Commitment`. -/
def encodeCommitment (c : Commitment) : List Nat :=
  encodeKey c.kind ++ encodeModuleRef c.scheme ++
    encodeOption encodeSite c.proverKey ++ encodeOption encodeSite c.verifierKey

/-- Encode a `Pin`. -/
def encodePin (p : Pin) : List Nat :=
  encodeSite p.site ++ encodeKey p.hash ++ encodeList encodeNat p.digest

/-- Canonical byte encoding of a scheme `Declaration`, including its application bytes. -/
def encodeDeclaration (d : Declaration) : List Nat :=
  encodeKey d.key ++
    encodeKey d.entry ++
    encodeList encodeRoleKind d.kinds ++
    encodeConstruction d.construction ++
    encodeOption encodeNat d.prover ++
    encodeOption encodeLayout d.layout ++
    encodeOption (fun r => encodeNat r.1 ++ encodeSite r.2) d.retry ++
    encodeOption encodeKey d.samples ++
    encodeList encodeKey d.context ++
    encodeList encodeGrind d.grinds ++
    encodeList encodeCommitment d.commits ++
    encodeList encodePin d.pins ++
    encodeList encodeNat d.application

/-- Encode a `Reason` as a single tag byte. -/
def encodeReason : Reason → List Nat
  | .reject => [0]
  | .abort => [1]
  | .exhausted => [2]
  | .refused => [3]

/-- Encode a `Repeat`. -/
def encodeRepeat : Repeat → List Nat
  | .fixed n => 0 :: encodeNat n
  | .count name => 1 :: encodeNat name

/-- Encode a `FlowKind` as a single tag byte. -/
def encodeFlowKind : FlowKind → List Nat
  | .message => [0]
  | .rows => [1]
  | .opening => [2]

/-- Encode an `OwnedName` as a single tag byte. -/
def encodeOwnedName : OwnedName → List Nat
  | .natAdd => [0]
  | .natSub => [1]
  | .natMul => [2]
  | .natDiv => [3]
  | .natRem => [4]
  | .natPow => [5]
  | .natEqual => [6]
  | .natLess => [7]
  | .boolAnd => [8]
  | .boolOr => [9]
  | .boolNot => [10]
  | .boolEqual => [11]
  | .seqLength => [12]
  | .seqAt => [13]
  | .seqSlice => [14]
  | .seqConcat => [15]
  | .seqFill => [16]
  | .seqSized => [17]
  | .natBelow => [18]
  | .seqUnsized => [19]
  | .finToNat => [20]
  | .finWiden => [21]
  | .make => [22]
  | .get => [23]
  | .take => [24]
  | .variant => [25]

section
variable {V : Vocabulary} (enc : VocabEncoder V)

mutual
  /-- Canonical byte encoding of a core type. -/
  def encodeTy : V.Ty → List Nat
    | .bool => [0]
    | .nat => [1]
    | .fin bound => 2 :: encodeNat bound
    | .seq item size => 3 :: encodeTy item ++ encodeOption encodeNat size
    | .tuple items => 4 :: encodeTys items
    | .record key linear fields => 5 :: encodeKey key ++ encodeBool linear ++ encodeTys fields
    | .variant key alts => 6 :: encodeKey key ++ encodeTys alts
    | .nominal key => 7 :: encodeList encodeNat (enc.typeKey key)

  /-- Canonical byte encoding of a `Tys` list. -/
  def encodeTys : Tys V.TypeKey → List Nat
    | .nil => [0]
    | .cons head rest => 1 :: encodeTy head ++ encodeTys rest
end

/-- Canonical byte encoding of a located type. -/
def encodeLTy (a : LTy V) : List Nat :=
  encodeTy enc a.ty ++ encodeList encodeNat a.holders

/-- Canonical byte encoding of a `GivenKind`. -/
def encodeGivenKind : GivenKind V → List Nat
  | .coin law => 0 :: encodeList encodeNat (enc.lawKey law)
  | .request service => 1 :: encodeKey service

/-- Canonical byte encoding of an `EventClass`. -/
def encodeEventClass : EventClass V → List Nat
  | .flow kind giver getters =>
      0 :: encodeFlowKind kind ++ encodeNat giver ++ encodeList encodeNat getters
  | .given kind owner hearers =>
      1 :: encodeGivenKind enc kind ++ encodeNat owner ++ encodeList encodeNat hearers

/-- Canonical byte encoding of a `LocalRaw` operation. -/
def encodeLocalRaw : LocalRaw V → List Nat
  | .row key => 0 :: encodeList encodeNat (enc.rowKey key)
  | .owned name tys nums =>
      1 :: encodeOwnedName name ++ encodeList (encodeTy enc) tys ++ encodeList encodeNat nums
  | .literal τ data => 2 :: encodeTy enc τ ++ encodeList encodeNat data
  | .call callee => 3 :: encodeKey callee

/-- Canonical byte encoding of a `ProtocolRaw` operation. -/
def encodeProtocolRaw : ProtocolRaw V → List Nat
  | .compute roles o => 0 :: encodeList encodeNat roles ++ encodeLocalRaw enc o
  | .event cls τ => 1 :: encodeEventClass enc cls ++ encodeTy enc τ
  | .narrow roles => 2 :: encodeList encodeNat roles
  | .apply callee roles => 3 :: encodeKey callee ++ encodeList encodeNat roles

end

section
variable {Op Who : Type} (encOp : Op → List Nat) (encWho : Who → List Nat)

mutual
  /-- Canonical byte encoding of a generic erased instruction. -/
  def encodeInstruction : Instruction Op Who → List Nat
    | .op key results o operands =>
        0 :: encodeKey key ++ encodeList encodeNat results ++ encOp o ++ encodeList encodeNat operands
    | .guard key who cond why =>
        1 :: encodeKey key ++ encWho who ++ encodeNat cond ++ encodeReason why
    | .choose key who cond results onTrue onFalse =>
        2 :: encodeKey key ++ encWho who ++ encodeNat cond ++ encodeList encodeNat results ++
          encodeRegion onTrue ++ encodeRegion onFalse
    | .cases key who subject results arms =>
        3 :: encodeKey key ++ encWho who ++ encodeNat subject ++ encodeList encodeNat results ++
          encodeRegions arms
    | .loop key who times carried results body =>
        4 :: encodeKey key ++ encWho who ++ encodeRepeat times ++ encodeList encodeNat carried ++
          encodeList encodeNat results ++ encodeRegion body
    | .block key number results body =>
        5 :: encodeKey key ++ encodeNat number ++ encodeList encodeNat results ++ encodeRegion body
    | .attempt key who results body =>
        6 :: encodeKey key ++ encWho who ++ encodeList encodeNat results ++ encodeRegion body

  /-- Canonical byte encoding of a list of erased instructions. -/
  def encodeInstructions : List (Instruction Op Who) → List Nat
    | [] => [0]
    | i :: rest => 1 :: encodeInstruction i ++ encodeInstructions rest

  /-- Canonical byte encoding of an erased region. -/
  def encodeRegion : Region Op Who → List Nat
    | .mk inputs body exit =>
        encodeList encodeNat inputs ++ encodeInstructions body ++ encodeList encodeNat exit

  /-- Canonical byte encoding of a list of erased regions. -/
  def encodeRegions : List (Region Op Who) → List Nat
    | [] => [0]
    | r :: rest => 1 :: encodeRegion r ++ encodeRegions rest
end

end

/-- Canonical byte encoding of an erased `Definition` (excluding non-semantic analysis notes). -/
def encodeDefinition {V : Vocabulary} (enc : VocabEncoder V) : Definition V → List Nat
  | .fn key ins outs canStop kernel _ body _ =>
      0 :: encodeKey key ++
        encodeList (encodeTy enc) ins ++
        encodeList (encodeTy enc) outs ++
        encodeBool canStop ++
        encodeOption encodeKey kernel ++
        encodeRegion (encodeLocalRaw enc) (fun _ => []) body
  | .protocol key roles ins outs body =>
      1 :: encodeKey key ++
        encodeNat roles ++
        encodeList (encodeLTy enc) ins ++
        encodeList (encodeLTy enc) outs ++
        encodeRegion (encodeProtocolRaw enc) (encodeList encodeNat) body

/-- Canonical identity bytes of a scheme over an admitted program: binds the declaration
(including application context) and the reachable erased definitions in `closure`. -/
def schemeIdentity {V : Vocabulary} (enc : VocabEncoder V) (a : Admitted V)
    (declaration : Declaration) : List Nat :=
  let closure := (declaration.entry :: declaration.definitions).flatMap a.program.defs.closureOf
  let defs := (erase a.program).definitions.filter fun d => decide (d.key ∈ closure)
  encodeDeclaration declaration ++ encodeList (encodeDefinition enc) defs

/-- Canonical identity bytes of a deployed scheme (`Functions.identity`). -/
def deployedIdentity {V : Vocabulary} (enc : VocabEncoder V) (d : Deployed V) : List Nat :=
  schemeIdentity enc d.admitted d.declaration

/-- `deployedIdentity` satisfies `Statements.identityReads`: it depends only on the declaration
and the reachable erased definitions in `Deployed.closure`. -/
theorem deployedIdentity_reads {V : Vocabulary} (enc : VocabEncoder V)
    (d d' : Deployed V) (hdecl : d.declaration = d'.declaration)
    (hdefs :
      (erase d.admitted.program).definitions.filter (fun defn => decide (defn.key ∈ d.closure)) =
      (erase d'.admitted.program).definitions.filter (fun defn => decide (defn.key ∈ d'.closure))) :
    deployedIdentity enc d = deployedIdentity enc d' := by
  unfold deployedIdentity schemeIdentity
  dsimp only
  have hcl :
      (erase d.admitted.program).definitions.filter
        (fun defn => decide (defn.key ∈ (d.declaration.entry :: d.declaration.definitions).flatMap
          d.admitted.program.defs.closureOf)) =
      (erase d'.admitted.program).definitions.filter
        (fun defn => decide (defn.key ∈ (d'.declaration.entry :: d'.declaration.definitions).flatMap
          d'.admitted.program.defs.closureOf)) := hdefs
  rw [hcl, hdecl]

/-! ## Byte-range invariants (`< 256`) -/

private theorem mem_append_lt {xs ys : List Nat} (hx : ∀ b, b ∈ xs → b < 256)
    (hy : ∀ b, b ∈ ys → b < 256) : ∀ b, b ∈ xs ++ ys → b < 256 := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact hx b h
  · exact hy b h

private theorem mem_cons_lt {a : Nat} {xs : List Nat} (ha : a < 256)
    (hx : ∀ b, b ∈ xs → b < 256) : ∀ b, b ∈ a :: xs → b < 256 := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | h
  · exact ha
  · exact hx b h

theorem encodeNat_bytes (n : Nat) : ∀ b, b ∈ encodeNat n → b < 256 :=
  formatNat_lawful.bytes n trivial

theorem encodeBool_bytes (x : Bool) : ∀ b, b ∈ encodeBool x → b < 256 :=
  formatBool_lawful.bytes x trivial

theorem encodeKey_bytes (k : Key) : ∀ b, b ∈ encodeKey k → b < 256 :=
  encodeNat_bytes k.number

private theorem writeMany_bytes_of {A : Type} (f : A → List Nat)
    (hf : ∀ a b, b ∈ f a → b < 256) : ∀ (xs : List A) b, b ∈ writeCanonicalMany f xs → b < 256
  | [], _, h => nomatch h
  | x :: xs, b, h =>
      mem_append_lt (hf x) (writeMany_bytes_of f hf xs) b h

theorem encodeList_bytes {A : Type} (f : A → List Nat) (hf : ∀ a b, b ∈ f a → b < 256)
    (xs : List A) : ∀ b, b ∈ encodeList f xs → b < 256 :=
  mem_append_lt (encodeNat_bytes xs.length) (writeMany_bytes_of f hf xs)

theorem encodeOption_bytes {A : Type} (f : A → List Nat) (hf : ∀ a b, b ∈ f a → b < 256) :
    ∀ (o : Option A) b, b ∈ encodeOption f o → b < 256
  | none, b, h => by simp [encodeOption] at h; omega
  | some a, b, h => mem_cons_lt (by omega) (hf a) b h

theorem encodeLabelBytes_bytes (s : String) : ∀ b, b ∈ encodeLabelBytes s → b < 256 := by
  intro b hb
  simp only [encodeLabelBytes, List.mem_map] at hb
  obtain ⟨u, _, rfl⟩ := hb
  exact u.toNat_lt

theorem encodeSite_bytes (s : Site) : ∀ b, b ∈ encodeSite s → b < 256 :=
  mem_append_lt (encodeList_bytes encodeKey encodeKey_bytes s.through) (encodeKey_bytes s.key)

theorem encodeRoleKind_bytes : ∀ rk b, b ∈ encodeRoleKind rk → b < 256
  | .online, b, h => by simp [encodeRoleKind] at h; omega
  | .offline, b, h => by simp [encodeRoleKind] at h; omega
  | .service, b, h => by simp [encodeRoleKind] at h; omega

theorem encodeModuleRef_bytes (m : ModuleRef) : ∀ b, b ∈ encodeModuleRef m → b < 256 :=
  encodeList_bytes (fun p : Key × Key => encodeKey p.1 ++ encodeKey p.2)
    (fun p => mem_append_lt (encodeKey_bytes p.1) (encodeKey_bytes p.2)) m.members

theorem encodeConstruction_bytes : ∀ c b, b ∈ encodeConstruction c → b < 256
  | .interactive, b, h => by simp [encodeConstruction] at h; omega
  | .derived suite tag, b, h => by
      simp only [encodeConstruction, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeModuleRef_bytes suite b h
      · exact encodeOption_bytes _ (encodeList_bytes encodeNat encodeNat_bytes) tag b h
  | .authored, b, h => by simp [encodeConstruction] at h; omega

theorem encodeLayout_bytes (l : Layout) : ∀ b, b ∈ encodeLayout l → b < 256 := by
  intro b h
  simp only [encodeLayout, List.mem_append, or_assoc] at h
  rcases h with h | h | h
  · exact encodeModuleRef_bytes l.module b h
  · exact encodeList_bytes encodeSite encodeSite_bytes l.carry b h
  · exact encodeList_bytes (fun p : Site × Key => encodeSite p.1 ++ encodeKey p.2)
      (fun p => mem_append_lt (encodeSite_bytes p.1) (encodeKey_bytes p.2)) l.recover b h

theorem encodeGrind_bytes (g : Grind) : ∀ b, b ∈ encodeGrind g → b < 256 :=
  mem_append_lt (encodeNat_bytes g.bits) (encodeList_bytes encodeSite encodeSite_bytes g.sites)

theorem encodeCommitment_bytes (c : Commitment) : ∀ b, b ∈ encodeCommitment c → b < 256 := by
  intro b h
  simp only [encodeCommitment, List.mem_append, or_assoc] at h
  rcases h with h | h | h | h
  · exact encodeKey_bytes c.kind b h
  · exact encodeModuleRef_bytes c.scheme b h
  · exact encodeOption_bytes encodeSite encodeSite_bytes c.proverKey b h
  · exact encodeOption_bytes encodeSite encodeSite_bytes c.verifierKey b h

theorem encodePin_bytes (p : Pin) : ∀ b, b ∈ encodePin p → b < 256 := by
  intro b h
  simp only [encodePin, List.mem_append, or_assoc] at h
  rcases h with h | h | h
  · exact encodeSite_bytes p.site b h
  · exact encodeKey_bytes p.hash b h
  · exact encodeList_bytes encodeNat encodeNat_bytes p.digest b h

theorem encodeDeclaration_bytes (d : Declaration) : ∀ b, b ∈ encodeDeclaration d → b < 256 := by
  intro b h
  simp only [encodeDeclaration, List.mem_append, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact encodeKey_bytes d.key b h
  · exact encodeKey_bytes d.entry b h
  · exact encodeList_bytes encodeRoleKind encodeRoleKind_bytes d.kinds b h
  · exact encodeConstruction_bytes d.construction b h
  · exact encodeOption_bytes encodeNat encodeNat_bytes d.prover b h
  · exact encodeOption_bytes encodeLayout encodeLayout_bytes d.layout b h
  · exact encodeOption_bytes (fun r : Nat × Site => encodeNat r.1 ++ encodeSite r.2)
      (fun r => mem_append_lt (encodeNat_bytes r.1) (encodeSite_bytes r.2)) d.retry b h
  · exact encodeOption_bytes encodeKey encodeKey_bytes d.samples b h
  · exact encodeList_bytes encodeKey encodeKey_bytes d.context b h
  · exact encodeList_bytes encodeGrind encodeGrind_bytes d.grinds b h
  · exact encodeList_bytes encodeCommitment encodeCommitment_bytes d.commits b h
  · exact encodeList_bytes encodePin encodePin_bytes d.pins b h
  · exact encodeList_bytes encodeNat encodeNat_bytes d.application b h

theorem encodeReason_bytes : ∀ r b, b ∈ encodeReason r → b < 256
  | .reject, b, h | .abort, b, h | .exhausted, b, h | .refused, b, h => by
      simp [encodeReason] at h; omega

theorem encodeRepeat_bytes : ∀ r b, b ∈ encodeRepeat r → b < 256
  | .fixed n, b, h => mem_cons_lt (by omega) (encodeNat_bytes n) b h
  | .count n, b, h => mem_cons_lt (by omega) (encodeNat_bytes n) b h

theorem encodeFlowKind_bytes : ∀ k b, b ∈ encodeFlowKind k → b < 256
  | .message, b, h | .rows, b, h | .opening, b, h => by simp [encodeFlowKind] at h; omega

theorem encodeOwnedName_bytes : ∀ n b, b ∈ encodeOwnedName n → b < 256 := by
  intro n b h
  cases n <;> simp [encodeOwnedName] at h <;> omega

section
variable {V : Vocabulary} (enc : VocabEncoder V)

mutual
  theorem encodeTy_bytes : ∀ (τ : V.Ty) b, b ∈ encodeTy enc τ → b < 256
    | .bool, b, h | .nat, b, h => by simp [encodeTy] at h; omega
    | .fin bound, b, h => mem_cons_lt (by omega) (encodeNat_bytes bound) b h
    | .seq item size, b, h => by
        simp only [encodeTy, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h
        · omega
        · exact encodeTy_bytes item b h
        · exact encodeOption_bytes encodeNat encodeNat_bytes size b h
    | .tuple items, b, h => mem_cons_lt (by omega) (encodeTys_bytes items) b h
    | .record key lin fields, b, h => by
        simp only [encodeTy, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h | h
        · omega
        · exact encodeKey_bytes key b h
        · exact encodeBool_bytes lin b h
        · exact encodeTys_bytes fields b h
    | .variant key alts, b, h => by
        simp only [encodeTy, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h
        · omega
        · exact encodeKey_bytes key b h
        · exact encodeTys_bytes alts b h
    | .nominal key, b, h =>
        mem_cons_lt (by omega) (encodeList_bytes encodeNat encodeNat_bytes (enc.typeKey key)) b h

  theorem encodeTys_bytes : ∀ (τs : Tys V.TypeKey) b, b ∈ encodeTys enc τs → b < 256
    | .nil, b, h => by simp [encodeTys] at h; omega
    | .cons head rest, b, h => by
        simp only [encodeTys, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h
        · omega
        · exact encodeTy_bytes head b h
        · exact encodeTys_bytes rest b h
end

theorem encodeLTy_bytes (a : LTy V) : ∀ b, b ∈ encodeLTy enc a → b < 256 :=
  mem_append_lt (encodeTy_bytes enc a.ty) (encodeList_bytes encodeNat encodeNat_bytes a.holders)

theorem encodeGivenKind_bytes : ∀ g b, b ∈ encodeGivenKind enc g → b < 256
  | .coin law, b, h =>
      mem_cons_lt (by omega) (encodeList_bytes encodeNat encodeNat_bytes (enc.lawKey law)) b h
  | .request svc, b, h => mem_cons_lt (by omega) (encodeKey_bytes svc) b h

theorem encodeEventClass_bytes : ∀ c b, b ∈ encodeEventClass enc c → b < 256
  | .flow kind giver getters, b, h => by
      simp only [encodeEventClass, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h
      · omega
      · exact encodeFlowKind_bytes kind b h
      · exact encodeNat_bytes giver b h
      · exact encodeList_bytes encodeNat encodeNat_bytes getters b h
  | .given kind owner hearers, b, h => by
      simp only [encodeEventClass, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h
      · omega
      · exact encodeGivenKind_bytes enc kind b h
      · exact encodeNat_bytes owner b h
      · exact encodeList_bytes encodeNat encodeNat_bytes hearers b h

theorem encodeLocalRaw_bytes : ∀ o b, b ∈ encodeLocalRaw enc o → b < 256
  | .row key, b, h =>
      mem_cons_lt (by omega) (encodeList_bytes encodeNat encodeNat_bytes (enc.rowKey key)) b h
  | .owned name tys nums, b, h => by
      simp only [encodeLocalRaw, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h
      · omega
      · exact encodeOwnedName_bytes name b h
      · exact encodeList_bytes (encodeTy enc) (encodeTy_bytes enc) tys b h
      · exact encodeList_bytes encodeNat encodeNat_bytes nums b h
  | .literal τ data, b, h => by
      simp only [encodeLocalRaw, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeTy_bytes enc τ b h
      · exact encodeList_bytes encodeNat encodeNat_bytes data b h
  | .call callee, b, h => mem_cons_lt (by omega) (encodeKey_bytes callee) b h

theorem encodeProtocolRaw_bytes : ∀ o b, b ∈ encodeProtocolRaw enc o → b < 256
  | .compute roles o, b, h => by
      simp only [encodeProtocolRaw, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeList_bytes encodeNat encodeNat_bytes roles b h
      · exact encodeLocalRaw_bytes enc o b h
  | .event cls τ, b, h => by
      simp only [encodeProtocolRaw, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeEventClass_bytes enc cls b h
      · exact encodeTy_bytes enc τ b h
  | .narrow roles, b, h =>
      mem_cons_lt (by omega) (encodeList_bytes encodeNat encodeNat_bytes roles) b h
  | .apply callee roles, b, h => by
      simp only [encodeProtocolRaw, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeKey_bytes callee b h
      · exact encodeList_bytes encodeNat encodeNat_bytes roles b h

end

section
variable {Op Who : Type}

mutual
  theorem encodeInstruction_bytes (encOp : Op → List Nat) (encWho : Who → List Nat)
      (hOp : ∀ o b, b ∈ encOp o → b < 256) (hWho : ∀ w b, b ∈ encWho w → b < 256) :
      ∀ (i : Instruction Op Who) b, b ∈ encodeInstruction encOp encWho i → b < 256
    | .op key results o operands, b, h => by
        simp only [encodeInstruction, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h | h | h
        · omega
        · exact encodeKey_bytes key b h
        · exact encodeList_bytes encodeNat encodeNat_bytes results b h
        · exact hOp o b h
        · exact encodeList_bytes encodeNat encodeNat_bytes operands b h
    | .guard key who cond why, b, h => by
        simp only [encodeInstruction, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h | h | h
        · omega
        · exact encodeKey_bytes key b h
        · exact hWho who b h
        · exact encodeNat_bytes cond b h
        · exact encodeReason_bytes why b h
    | .choose key who cond results onTrue onFalse, b, h => by
        simp only [encodeInstruction, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h | h | h | h | h
        · omega
        · exact encodeKey_bytes key b h
        · exact hWho who b h
        · exact encodeNat_bytes cond b h
        · exact encodeList_bytes encodeNat encodeNat_bytes results b h
        · exact encodeRegion_bytes encOp encWho hOp hWho onTrue b h
        · exact encodeRegion_bytes encOp encWho hOp hWho onFalse b h
    | .cases key who subject results arms, b, h => by
        simp only [encodeInstruction, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h | h | h | h
        · omega
        · exact encodeKey_bytes key b h
        · exact hWho who b h
        · exact encodeNat_bytes subject b h
        · exact encodeList_bytes encodeNat encodeNat_bytes results b h
        · exact encodeRegions_bytes encOp encWho hOp hWho arms b h
    | .loop key who times carried results body, b, h => by
        simp only [encodeInstruction, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h | h | h | h | h
        · omega
        · exact encodeKey_bytes key b h
        · exact hWho who b h
        · exact encodeRepeat_bytes times b h
        · exact encodeList_bytes encodeNat encodeNat_bytes carried b h
        · exact encodeList_bytes encodeNat encodeNat_bytes results b h
        · exact encodeRegion_bytes encOp encWho hOp hWho body b h
    | .block key number results body, b, h => by
        simp only [encodeInstruction, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h | h | h
        · omega
        · exact encodeKey_bytes key b h
        · exact encodeNat_bytes number b h
        · exact encodeList_bytes encodeNat encodeNat_bytes results b h
        · exact encodeRegion_bytes encOp encWho hOp hWho body b h
    | .attempt key who results body, b, h => by
        simp only [encodeInstruction, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h | h | h
        · omega
        · exact encodeKey_bytes key b h
        · exact hWho who b h
        · exact encodeList_bytes encodeNat encodeNat_bytes results b h
        · exact encodeRegion_bytes encOp encWho hOp hWho body b h

  theorem encodeInstructions_bytes (encOp : Op → List Nat) (encWho : Who → List Nat)
      (hOp : ∀ o b, b ∈ encOp o → b < 256) (hWho : ∀ w b, b ∈ encWho w → b < 256) :
      ∀ (is : List (Instruction Op Who)) b, b ∈ encodeInstructions encOp encWho is → b < 256
    | [], b, h => by simp [encodeInstructions] at h; omega
    | i :: rest, b, h => by
        simp only [encodeInstructions, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h
        · omega
        · exact encodeInstruction_bytes encOp encWho hOp hWho i b h
        · exact encodeInstructions_bytes encOp encWho hOp hWho rest b h

  theorem encodeRegion_bytes (encOp : Op → List Nat) (encWho : Who → List Nat)
      (hOp : ∀ o b, b ∈ encOp o → b < 256) (hWho : ∀ w b, b ∈ encWho w → b < 256) :
      ∀ (r : Region Op Who) b, b ∈ encodeRegion encOp encWho r → b < 256
    | .mk inputs body exit, b, h => by
        simp only [encodeRegion, List.mem_append, or_assoc] at h
        rcases h with h | h | h
        · exact encodeList_bytes encodeNat encodeNat_bytes inputs b h
        · exact encodeInstructions_bytes encOp encWho hOp hWho body b h
        · exact encodeList_bytes encodeNat encodeNat_bytes exit b h

  theorem encodeRegions_bytes (encOp : Op → List Nat) (encWho : Who → List Nat)
      (hOp : ∀ o b, b ∈ encOp o → b < 256) (hWho : ∀ w b, b ∈ encWho w → b < 256) :
      ∀ (rs : List (Region Op Who)) b, b ∈ encodeRegions encOp encWho rs → b < 256
    | [], b, h => by simp [encodeRegions] at h; omega
    | r :: rest, b, h => by
        simp only [encodeRegions, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h
        · omega
        · exact encodeRegion_bytes encOp encWho hOp hWho r b h
        · exact encodeRegions_bytes encOp encWho hOp hWho rest b h
end

end

theorem encodeDefinition_bytes {V : Vocabulary} (enc : VocabEncoder V) :
    ∀ (d : Definition V) b, b ∈ encodeDefinition enc d → b < 256
  | .fn key ins outs canStop kernel _ body _, b, h => by
      simp only [encodeDefinition, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h | h | h | h
      · omega
      · exact encodeKey_bytes key b h
      · exact encodeList_bytes (encodeTy enc) (encodeTy_bytes enc) ins b h
      · exact encodeList_bytes (encodeTy enc) (encodeTy_bytes enc) outs b h
      · exact encodeBool_bytes canStop b h
      · exact encodeOption_bytes encodeKey encodeKey_bytes kernel b h
      · exact encodeRegion_bytes _ _ (encodeLocalRaw_bytes enc)
          (fun _ _ h => absurd h (List.not_mem_nil)) body b h
  | .protocol key roles ins outs body, b, h => by
      simp only [encodeDefinition, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h | h | h
      · omega
      · exact encodeKey_bytes key b h
      · exact encodeNat_bytes roles b h
      · exact encodeList_bytes (encodeLTy enc) (encodeLTy_bytes enc) ins b h
      · exact encodeList_bytes (encodeLTy enc) (encodeLTy_bytes enc) outs b h
      · exact encodeRegion_bytes _ _ (encodeProtocolRaw_bytes enc)
          (encodeList_bytes encodeNat encodeNat_bytes) body b h

/-- Every element of `schemeIdentity` is a valid byte (`< 256`). -/
theorem schemeIdentity_bytes {V : Vocabulary} (enc : VocabEncoder V) (a : Admitted V)
    (declaration : Declaration) : ∀ b, b ∈ schemeIdentity enc a declaration → b < 256 :=
  mem_append_lt (encodeDeclaration_bytes declaration)
    (encodeList_bytes (encodeDefinition enc) (encodeDefinition_bytes enc) _)

/-- Every element of `deployedIdentity` is a valid byte (`< 256`). -/
theorem deployedIdentity_bytes {V : Vocabulary} (enc : VocabEncoder V) (d : Deployed V) :
    ∀ b, b ∈ deployedIdentity enc d → b < 256 :=
  schemeIdentity_bytes enc d.admitted d.declaration

end Zkc.Core
