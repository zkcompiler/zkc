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

/-- A vocabulary encoder is injective when distinct type, row, and law keys map to distinct lists. -/
def VocabEncoder.Injective {V : Vocabulary} (enc : VocabEncoder V) : Prop :=
  (∀ k₁ k₂, enc.typeKey k₁ = enc.typeKey k₂ → k₁ = k₂) ∧
  (∀ k₁ k₂, enc.rowKey k₁ = enc.rowKey k₂ → k₁ = k₂) ∧
  (∀ k₁ k₂, enc.lawKey k₁ = enc.lawKey k₂ → k₁ = k₂)

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

/-- Canonical length-prefixed ASCII domain tag `"zkc.core.proof/1"` (order-independent
canonical reachability closure with `lawMembers` and stripped proof-only annotations). -/
def proofDomainTag : List Nat :=
  [16, 122, 107, 99, 46, 99, 111, 114, 101, 46, 112, 114, 111, 111, 102, 47, 49]

/-- Canonical length-prefixed ASCII domain tag `"zkc.core.stmt/0"`. -/
def stmtDomainTag : List Nat :=
  [15, 122, 107, 99, 46, 99, 111, 114, 101, 46, 115, 116, 109, 116, 47, 48]

/-- Canonical length-prefixed ASCII domain tag `"zkc.core.msg/0"`. -/
def msgDomainTag : List Nat :=
  [14, 122, 107, 99, 46, 99, 111, 114, 101, 46, 109, 115, 103, 47, 48]

/-- Canonical length-prefixed ASCII domain tag `"zkc.core.draw/0"`. -/
def drawDomainTag : List Nat :=
  [15, 122, 107, 99, 46, 99, 111, 114, 101, 46, 100, 114, 97, 119, 47, 48]

/-- Encode a site (`through`, `key`) canonically. -/
def encodeSite (s : Site) : List Nat :=
  encodeList encodeKey s.through ++ encodeKey s.key

/-- Versioned canonical domain label for a statement input at index `i`. -/
def stmtLabel (i : Nat) : List Nat :=
  stmtDomainTag ++ encodeNat i

/-- Versioned canonical domain label for a message at site `s` (binding full `s.through` and `s.key`). -/
def msgLabel (s : Site) : List Nat :=
  msgDomainTag ++ encodeSite s

/-- Versioned canonical domain label for a verifier draw at site `s` (binding full `s.through` and `s.key`). -/
def drawLabel (s : Site) : List Nat :=
  drawDomainTag ++ encodeSite s

/-- Encode a `RoleKind` as a single canonical tag byte. -/
def encodeRoleKind : RoleKind → List Nat
  | .online => [0]
  | .offline => [1]
  | .service => [2]

/-- Encode a `ModuleRef`, committing both ordinary members and law-specific bindings. -/
def encodeModuleRef (m : ModuleRef) : List Nat :=
  encodeList (fun p => encodeKey p.1 ++ encodeKey p.2) m.members ++
    encodeList (fun p => encodeKey p.1 ++ encodeList encodeNat p.2.1 ++ encodeKey p.2.2) m.lawMembers

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

/-- Canonical byte encoding of a positional operand over `Empty`. -/
def encodeOperandEmpty : Operand Empty → List Nat
  | .arg pos => encodeNat pos
  | .apply w _ => nomatch w

/-- Canonical byte encoding of a positional requirement over `Empty`. -/
def encodeReqEmpty : Requirement Empty → List Nat
  | .le a b => 0 :: encodeOperandEmpty a ++ encodeOperandEmpty b
  | .lt a b => 1 :: encodeOperandEmpty a ++ encodeOperandEmpty b
  | .atLeast a n => 2 :: encodeOperandEmpty a ++ encodeNat n
  | .below a n => 3 :: encodeOperandEmpty a ++ encodeNat n
  | .exactly a n => 4 :: encodeOperandEmpty a ++ encodeNat n
  | .difference a b n => 5 :: encodeOperandEmpty a ++ encodeOperandEmpty b ++ encodeNat n
  | .holds a => 6 :: encodeOperandEmpty a
  | .bounded a => 7 :: encodeOperandEmpty a

section
variable {Raw : Type} (encRaw : Raw → List Nat)

mutual
  /-- Canonical byte encoding of a stored assertion expression. -/
  def encodeExpr : BodyAnalysis.Expr Raw → List Nat
    | .arg pos => 0 :: encodeNat pos
    | .apply w ops res => 1 :: encRaw w ++ encodeExprs ops ++ encodeNat res

  /-- Canonical byte encoding of stored assertion expression lists. -/
  def encodeExprs : BodyAnalysis.Exprs Raw → List Nat
    | .nil => [0]
    | .cons e rest => 1 :: encodeExpr e ++ encodeExprs rest
end

/-- Canonical byte encoding of a `ContractClause`. -/
def encodeContractClause (c : BodyAnalysis.ContractClause Raw) : List Nat :=
  encodeExpr encRaw c.assertion ++ encodeOption (encodeExpr encRaw) c.staticBound

/-- Canonical byte encoding of a `StaticRegion`. -/
def encodeStaticRegion : BodyAnalysis.StaticRegion → List Nat
  | .root => [0]
  | .body p ord k => 1 :: encodeStaticRegion p ++ encodeNat ord ++ encodeKey k
  | .otherwise p ord k => 2 :: encodeStaticRegion p ++ encodeNat ord ++ encodeKey k
  | .arm p ord => 3 :: encodeStaticRegion p ++ encodeNat ord
  | .block p ord k n => 4 :: encodeStaticRegion p ++ encodeNat ord ++ encodeKey k ++ encodeNat n

/-- Canonical byte encoding of a `StaticCursor`. -/
def encodeStaticCursor (c : BodyAnalysis.StaticCursor) : List Nat :=
  encodeStaticRegion c.enclosing ++ encodeNat c.ordinal

/-- Canonical byte encoding of an `AnnotationSite`. -/
def encodeAnnotationSite : BodyAnalysis.AnnotationSite → List Nat
  | .instruction c k => 0 :: encodeStaticCursor c ++ encodeKey k
  | .block c k n => 1 :: encodeStaticCursor c ++ encodeKey k ++ encodeNat n

/-- Canonical byte encoding of a body analysis `Annotation`. -/
def encodeAnnotation : BodyAnalysis.Annotation Raw → List Nat
  | .invariant uses as => 0 :: encodeList encodeNat uses ++ encodeList (encodeExpr encRaw) as
  | .step lem names => 1 :: encodeNat lem ++ encodeList encodeNat names
  | .fact uses a => 2 :: encodeList encodeNat uses ++ encodeExpr encRaw a

/-- Canonical byte encoding of `BodyAnalysis.Annotations`. -/
def encodeAnnotations (notes : BodyAnalysis.Annotations Raw) : List Nat :=
  encodeList (fun p => encodeAnnotationSite p.1 ++ encodeAnnotation encRaw p.2) notes

end

/-- Canonical byte encoding of a `HeaderClause`. -/
def encodeHeaderClause {V : Vocabulary} (enc : VocabEncoder V) : HeaderClause V → List Nat
  | .positional req => 0 :: encodeReqEmpty req
  | .assertion c => 1 :: encodeContractClause (encodeLocalRaw enc) c

/-- Canonical byte encoding of a `HeaderSummary`. -/
def encodeHeaderSummary {V : Vocabulary} (enc : VocabEncoder V) (s : HeaderSummary V) : List Nat :=
  encodeList (encodeHeaderClause enc) s.requires ++ encodeList (encodeHeaderClause enc) s.ensures

/-- Canonical byte encoding of an erased `Definition` (including function summaries and notes). -/
def encodeDefinition {V : Vocabulary} (enc : VocabEncoder V) : Definition V → List Nat
  | .fn key ins outs canStop kernel summary body notes =>
      0 :: encodeKey key ++
        encodeList (encodeTy enc) ins ++
        encodeList (encodeTy enc) outs ++
        encodeBool canStop ++
        encodeOption encodeKey kernel ++
        encodeHeaderSummary enc summary ++
        encodeRegion (encodeLocalRaw enc) (fun _ => []) body ++
        encodeAnnotations (encodeLocalRaw enc) notes
  | .protocol key roles ins outs body =>
      1 :: encodeKey key ++
        encodeNat roles ++
        encodeList (encodeLTy enc) ins ++
        encodeList (encodeLTy enc) outs ++
        encodeRegion (encodeProtocolRaw enc) (encodeList encodeNat) body

/-- Deduplicate a list of keys preserving first-occurrence traversal order. -/
def dedupFirst (seen : List Key) : List Key → List Key
  | [] => []
  | k :: ks =>
      if k ∈ seen then dedupFirst seen ks
      else k :: dedupFirst (k :: seen) ks

/-- Strip proof-only analysis annotations from an erased definition before hashing into the
deployment identity (preserving all executable code, headers, and summaries). -/
def stripProofNotes {V : Vocabulary} : Definition V → Definition V
  | .fn key ins outs canStop kernel summary body _ =>
      .fn key ins outs canStop kernel summary body []
  | .protocol key roles ins outs body =>
      .protocol key roles ins outs body

/-- Find an erased definition by its unique key. -/
def lookupDefByKey {V : Vocabulary} (defs : List (Definition V)) (k : Key) :
    Option (Definition V) :=
  defs.find? fun d => decide (d.key = k)

/-- Deterministic reference-order key list of all definitions reachable from `declaration.entry`
followed by `declaration.definitions`. Independent of how unrelated or independent definitions
are ordered inside `a.program`. -/
def canonicalClosureKeys {V : Vocabulary} (a : Admitted V) (declaration : Declaration) : List Key :=
  dedupFirst [] ((declaration.entry :: declaration.definitions).flatMap a.program.defs.closureOf)

/-- Canonical, definition-order-independent, proof-note-stripped list of reachable erased
definitions for `(a, declaration)`. -/
def canonicalClosureDefs {V : Vocabulary} (a : Admitted V) (declaration : Declaration) :
    List (Definition V) :=
  let erased := (erase a.program).definitions
  (canonicalClosureKeys a declaration).filterMap fun k =>
    (lookupDefByKey erased k).map stripProofNotes

/-- Versioned canonical identity bytes (`zkc.core.proof/1`) of a scheme over an admitted program:
binds the declaration (including application context and `lawMembers`) and all reachable erased
definitions in canonical reference order (`canonicalClosureDefs`), independent of package
definition ordering, proof-only annotations, associations, and unreachable definitions. -/
def schemeIdentity {V : Vocabulary} (enc : VocabEncoder V) (a : Admitted V)
    (declaration : Declaration) : List Nat :=
  proofDomainTag ++ encodeDeclaration declaration ++
    encodeList (encodeDefinition enc) (canonicalClosureDefs a declaration)

/-- Canonical identity bytes committed inside a deployed scheme (`Functions.identity`).
Reads the identity fixed at deployment time under the encoder that resolved `d.declaration`. -/
def deployedIdentity {V : Vocabulary} (d : Deployed V) : List Nat :=
  d.identity

/-- `schemeIdentity` reads only the declaration and `canonicalClosureDefs`. -/
theorem schemeIdentity_reads {V : Vocabulary} (enc : VocabEncoder V)
    (a₁ a₂ : Admitted V) (decl₁ decl₂ : Declaration)
    (hdecl : decl₁ = decl₂)
    (hdefs : canonicalClosureDefs a₁ decl₁ = canonicalClosureDefs a₂ decl₂) :
    schemeIdentity enc a₁ decl₁ = schemeIdentity enc a₂ decl₂ := by
  subst hdecl
  unfold schemeIdentity
  rw [hdefs]

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

theorem proofDomainTag_bytes : ∀ b, b ∈ proofDomainTag → b < 256 := by decide
theorem stmtDomainTag_bytes : ∀ b, b ∈ stmtDomainTag → b < 256 := by decide
theorem msgDomainTag_bytes : ∀ b, b ∈ msgDomainTag → b < 256 := by decide
theorem drawDomainTag_bytes : ∀ b, b ∈ drawDomainTag → b < 256 := by decide

theorem encodeSite_bytes (s : Site) : ∀ b, b ∈ encodeSite s → b < 256 :=
  mem_append_lt (encodeList_bytes encodeKey encodeKey_bytes s.through) (encodeKey_bytes s.key)

theorem stmtLabel_bytes (i : Nat) : ∀ b, b ∈ stmtLabel i → b < 256 :=
  mem_append_lt stmtDomainTag_bytes (encodeNat_bytes i)

theorem msgLabel_bytes (s : Site) : ∀ b, b ∈ msgLabel s → b < 256 :=
  mem_append_lt msgDomainTag_bytes (encodeSite_bytes s)

theorem drawLabel_bytes (s : Site) : ∀ b, b ∈ drawLabel s → b < 256 :=
  mem_append_lt drawDomainTag_bytes (encodeSite_bytes s)

theorem encodeRoleKind_bytes : ∀ rk b, b ∈ encodeRoleKind rk → b < 256
  | .online, b, h => by simp [encodeRoleKind] at h; omega
  | .offline, b, h => by simp [encodeRoleKind] at h; omega
  | .service, b, h => by simp [encodeRoleKind] at h; omega

theorem encodeModuleRef_bytes (m : ModuleRef) : ∀ b, b ∈ encodeModuleRef m → b < 256 :=
  mem_append_lt
    (encodeList_bytes (fun p : Key × Key => encodeKey p.1 ++ encodeKey p.2)
      (fun p => mem_append_lt (encodeKey_bytes p.1) (encodeKey_bytes p.2)) m.members)
    (encodeList_bytes (fun p : Key × List Nat × Key =>
        encodeKey p.1 ++ encodeList encodeNat p.2.1 ++ encodeKey p.2.2)
      (fun p => mem_append_lt
        (mem_append_lt (encodeKey_bytes p.1) (encodeList_bytes encodeNat encodeNat_bytes p.2.1))
        (encodeKey_bytes p.2.2)) m.lawMembers)

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

theorem encodeOperandEmpty_bytes : ∀ o b, b ∈ encodeOperandEmpty o → b < 256
  | .arg pos, b, h => encodeNat_bytes pos b h
  | .apply w _, _, _ => nomatch w

theorem encodeReqEmpty_bytes : ∀ req b, b ∈ encodeReqEmpty req → b < 256
  | .le a b, x, h => by
      simp only [encodeReqEmpty, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeOperandEmpty_bytes a x h
      · exact encodeOperandEmpty_bytes b x h
  | .lt a b, x, h => by
      simp only [encodeReqEmpty, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeOperandEmpty_bytes a x h
      · exact encodeOperandEmpty_bytes b x h
  | .atLeast a n, x, h => by
      simp only [encodeReqEmpty, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeOperandEmpty_bytes a x h
      · exact encodeNat_bytes n x h
  | .below a n, x, h => by
      simp only [encodeReqEmpty, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeOperandEmpty_bytes a x h
      · exact encodeNat_bytes n x h
  | .exactly a n, x, h => by
      simp only [encodeReqEmpty, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeOperandEmpty_bytes a x h
      · exact encodeNat_bytes n x h
  | .difference a b n, x, h => by
      simp only [encodeReqEmpty, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h
      · omega
      · exact encodeOperandEmpty_bytes a x h
      · exact encodeOperandEmpty_bytes b x h
      · exact encodeNat_bytes n x h
  | .holds a, x, h => mem_cons_lt (by omega) (encodeOperandEmpty_bytes a) x h
  | .bounded a, x, h => mem_cons_lt (by omega) (encodeOperandEmpty_bytes a) x h

section
variable {Raw : Type}

mutual
  theorem encodeExpr_bytes (encRaw : Raw → List Nat) (hRaw : ∀ r b, b ∈ encRaw r → b < 256) :
      ∀ (e : BodyAnalysis.Expr Raw) b, b ∈ encodeExpr encRaw e → b < 256
    | .arg pos, b, h => mem_cons_lt (by omega) (encodeNat_bytes pos) b h
    | .apply w ops res, b, h => by
        simp only [encodeExpr, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h | h
        · omega
        · exact hRaw w b h
        · exact encodeExprs_bytes encRaw hRaw ops b h
        · exact encodeNat_bytes res b h

  theorem encodeExprs_bytes (encRaw : Raw → List Nat) (hRaw : ∀ r b, b ∈ encRaw r → b < 256) :
      ∀ (es : BodyAnalysis.Exprs Raw) b, b ∈ encodeExprs encRaw es → b < 256
    | .nil, b, h => by simp [encodeExprs] at h; omega
    | .cons e rest, b, h => by
        simp only [encodeExprs, List.mem_cons, List.mem_append, or_assoc] at h
        rcases h with rfl | h | h
        · omega
        · exact encodeExpr_bytes encRaw hRaw e b h
        · exact encodeExprs_bytes encRaw hRaw rest b h
end

theorem encodeContractClause_bytes (encRaw : Raw → List Nat) (hRaw : ∀ r b, b ∈ encRaw r → b < 256)
    (c : BodyAnalysis.ContractClause Raw) :
    ∀ b, b ∈ encodeContractClause encRaw c → b < 256 :=
  mem_append_lt (encodeExpr_bytes encRaw hRaw c.assertion)
    (encodeOption_bytes _ (encodeExpr_bytes encRaw hRaw) c.staticBound)

theorem encodeStaticRegion_bytes : ∀ (r : BodyAnalysis.StaticRegion) b, b ∈ encodeStaticRegion r → b < 256
  | .root, b, h => by simp [encodeStaticRegion] at h; omega
  | .body p ord k, b, h => by
      simp only [encodeStaticRegion, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h
      · omega
      · exact encodeStaticRegion_bytes p b h
      · exact encodeNat_bytes ord b h
      · exact encodeKey_bytes k b h
  | .otherwise p ord k, b, h => by
      simp only [encodeStaticRegion, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h
      · omega
      · exact encodeStaticRegion_bytes p b h
      · exact encodeNat_bytes ord b h
      · exact encodeKey_bytes k b h
  | .arm p ord, b, h => by
      simp only [encodeStaticRegion, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeStaticRegion_bytes p b h
      · exact encodeNat_bytes ord b h
  | .block p ord k n, b, h => by
      simp only [encodeStaticRegion, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h | h
      · omega
      · exact encodeStaticRegion_bytes p b h
      · exact encodeNat_bytes ord b h
      · exact encodeKey_bytes k b h
      · exact encodeNat_bytes n b h

theorem encodeStaticCursor_bytes (c : BodyAnalysis.StaticCursor) :
    ∀ b, b ∈ encodeStaticCursor c → b < 256 :=
  mem_append_lt (encodeStaticRegion_bytes c.enclosing) (encodeNat_bytes c.ordinal)

theorem encodeAnnotationSite_bytes : ∀ (s : BodyAnalysis.AnnotationSite) b, b ∈ encodeAnnotationSite s → b < 256
  | .instruction c k, b, h => by
      simp only [encodeAnnotationSite, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeStaticCursor_bytes c b h
      · exact encodeKey_bytes k b h
  | .block c k n, b, h => by
      simp only [encodeAnnotationSite, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h
      · omega
      · exact encodeStaticCursor_bytes c b h
      · exact encodeKey_bytes k b h
      · exact encodeNat_bytes n b h

theorem encodeAnnotation_bytes (encRaw : Raw → List Nat) (hRaw : ∀ r b, b ∈ encRaw r → b < 256) :
    ∀ (a : BodyAnalysis.Annotation Raw) b, b ∈ encodeAnnotation encRaw a → b < 256
  | .invariant uses as, b, h => by
      simp only [encodeAnnotation, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeList_bytes encodeNat encodeNat_bytes uses b h
      · exact encodeList_bytes (encodeExpr encRaw) (encodeExpr_bytes encRaw hRaw) as b h
  | .step lem names, b, h => by
      simp only [encodeAnnotation, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeNat_bytes lem b h
      · exact encodeList_bytes encodeNat encodeNat_bytes names b h
  | .fact uses a, b, h => by
      simp only [encodeAnnotation, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h
      · omega
      · exact encodeList_bytes encodeNat encodeNat_bytes uses b h
      · exact encodeExpr_bytes encRaw hRaw a b h

theorem encodeAnnotations_bytes (encRaw : Raw → List Nat) (hRaw : ∀ r b, b ∈ encRaw r → b < 256)
    (notes : BodyAnalysis.Annotations Raw) :
    ∀ b, b ∈ encodeAnnotations encRaw notes → b < 256 :=
  encodeList_bytes (fun p : BodyAnalysis.AnnotationSite × BodyAnalysis.Annotation Raw =>
      encodeAnnotationSite p.1 ++ encodeAnnotation encRaw p.2)
    (fun p => mem_append_lt (encodeAnnotationSite_bytes p.1)
      (encodeAnnotation_bytes encRaw hRaw p.2)) notes

end

theorem encodeHeaderClause_bytes {V : Vocabulary} (enc : VocabEncoder V) :
    ∀ (c : HeaderClause V) b, b ∈ encodeHeaderClause enc c → b < 256
  | .positional req, b, h => mem_cons_lt (by omega) (encodeReqEmpty_bytes req) b h
  | .assertion c, b, h =>
      mem_cons_lt (by omega) (encodeContractClause_bytes _ (encodeLocalRaw_bytes enc) c) b h

theorem encodeHeaderSummary_bytes {V : Vocabulary} (enc : VocabEncoder V) (s : HeaderSummary V) :
    ∀ b, b ∈ encodeHeaderSummary enc s → b < 256 :=
  mem_append_lt (encodeList_bytes _ (encodeHeaderClause_bytes enc) s.requires)
    (encodeList_bytes _ (encodeHeaderClause_bytes enc) s.ensures)

theorem encodeDefinition_bytes {V : Vocabulary} (enc : VocabEncoder V) :
    ∀ (d : Definition V) b, b ∈ encodeDefinition enc d → b < 256
  | .fn key ins outs canStop kernel summary body notes, b, h => by
      simp only [encodeDefinition, List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h | h | h | h | h | h
      · omega
      · exact encodeKey_bytes key b h
      · exact encodeList_bytes (encodeTy enc) (encodeTy_bytes enc) ins b h
      · exact encodeList_bytes (encodeTy enc) (encodeTy_bytes enc) outs b h
      · exact encodeBool_bytes canStop b h
      · exact encodeOption_bytes encodeKey encodeKey_bytes kernel b h
      · exact encodeHeaderSummary_bytes enc summary b h
      · exact encodeRegion_bytes _ _ (encodeLocalRaw_bytes enc)
          (fun _ _ h => absurd h (List.not_mem_nil)) body b h
      · exact encodeAnnotations_bytes _ (encodeLocalRaw_bytes enc) notes b h
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
  mem_append_lt (mem_append_lt proofDomainTag_bytes (encodeDeclaration_bytes declaration))
    (encodeList_bytes (encodeDefinition enc) (encodeDefinition_bytes enc) _)

/-! ## Prefix-freeness and injectivity of canonical identity encoding -/

/-- A byte encoder is prefix-free (hence injective): no encoding is a prefix of another. -/
def PrefixFree {A : Type} (f : A → List Nat) : Prop :=
  ∀ a b r₁ r₂, f a ++ r₁ = f b ++ r₂ → a = b ∧ r₁ = r₂

/-- Helper: peel one prefix-free component from an append equality. -/
private theorem peel {A : Type} {f : A → List Nat} (hf : PrefixFree f) {a b : A} {r₁ r₂ : List Nat}
    (h : f a ++ r₁ = f b ++ r₂) : a = b ∧ r₁ = r₂ :=
  hf a b r₁ r₂ h

theorem encodeNat_prefixFree : PrefixFree encodeNat := by
  intro a b r₁ r₂ h
  have h1 := formatNat_lawful.reads a r₁ trivial
  have h2 := formatNat_lawful.reads b r₂ trivial
  change formatNat.write a ++ r₁ = formatNat.write b ++ r₂ at h
  rw [h] at h1
  rw [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

theorem encodeBool_prefixFree : PrefixFree encodeBool := by
  intro a b r₁ r₂ h
  have h1 := formatBool_lawful.reads a r₁ trivial
  have h2 := formatBool_lawful.reads b r₂ trivial
  change formatBool.write a ++ r₁ = formatBool.write b ++ r₂ at h
  rw [h] at h1
  rw [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

theorem encodeKey_prefixFree : PrefixFree encodeKey := by
  intro ⟨a⟩ ⟨b⟩ r₁ r₂ h
  obtain ⟨hab, hr⟩ := encodeNat_prefixFree a b r₁ r₂ h
  exact ⟨congrArg Key.mk hab, hr⟩

private theorem writeMany_prefixFree {A : Type} {f : A → List Nat} (hf : PrefixFree f) :
    ∀ (xs ys : List A) (r₁ r₂ : List Nat), xs.length = ys.length →
      writeCanonicalMany f xs ++ r₁ = writeCanonicalMany f ys ++ r₂ → xs = ys ∧ r₁ = r₂
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | [], _ :: _, _, _, hlen, _ => nomatch hlen
  | x :: xs, y :: ys, r₁, r₂, hlen, h => by
      simp only [writeCanonicalMany, List.append_assoc] at h
      obtain ⟨hxy, hrest⟩ := hf x y _ _ h
      obtain ⟨hxs, hr⟩ := writeMany_prefixFree hf xs ys r₁ r₂ (Nat.succ.inj hlen) hrest
      exact ⟨by rw [hxy, hxs], hr⟩

theorem encodeList_prefixFree {A : Type} {f : A → List Nat} (hf : PrefixFree f) :
    PrefixFree (encodeList f) := by
  intro xs ys r₁ r₂ h
  simp only [encodeList, List.append_assoc] at h
  obtain ⟨hlen, hrest⟩ := encodeNat_prefixFree xs.length ys.length _ _ h
  exact writeMany_prefixFree hf xs ys r₁ r₂ hlen hrest

theorem encodeOption_prefixFree {A : Type} {f : A → List Nat} (hf : PrefixFree f) :
    PrefixFree (encodeOption f) := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeOption, List.cons_append, List.nil_append] at h
  · exact ⟨rfl, (List.cons.inj h).2⟩
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · obtain ⟨hab, hr⟩ := hf _ _ r₁ r₂ (List.cons.inj h).2
    exact ⟨congrArg some hab, hr⟩

theorem encodeSite_prefixFree : PrefixFree encodeSite := by
  intro ⟨t₁, k₁⟩ ⟨t₂, k₂⟩ r₁ r₂ h
  simp only [encodeSite, List.append_assoc] at h
  obtain ⟨ht, h1⟩ := encodeList_prefixFree encodeKey_prefixFree t₁ t₂ _ _ h
  obtain ⟨hk, hr⟩ := encodeKey_prefixFree k₁ k₂ r₁ r₂ h1
  exact ⟨by rw [ht, hk], hr⟩

theorem encodeRoleKind_prefixFree : PrefixFree encodeRoleKind := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeRoleKind, List.cons_append, List.nil_append] at h <;>
    first | exact ⟨rfl, (List.cons.inj h).2⟩ | cases (List.cons.inj h).1

theorem encodeModuleRef_prefixFree : PrefixFree encodeModuleRef := by
  intro ⟨m₁, lm₁⟩ ⟨m₂, lm₂⟩ r₁ r₂ h
  simp only [encodeModuleRef, List.append_assoc] at h
  have hPair : PrefixFree (fun p : Key × Key => encodeKey p.1 ++ encodeKey p.2) := by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ s₁ s₂ hp
    simp only [List.append_assoc] at hp
    obtain ⟨h1, hs⟩ := encodeKey_prefixFree a₁ b₁ _ _ hp
    obtain ⟨h2, hr⟩ := encodeKey_prefixFree a₂ b₂ s₁ s₂ hs
    exact ⟨by rw [h1, h2], hr⟩
  have hLawPair : PrefixFree (fun p : Key × List Nat × Key =>
      encodeKey p.1 ++ (encodeList encodeNat p.2.1 ++ encodeKey p.2.2)) := by
    intro ⟨a₁, a₂, a₃⟩ ⟨b₁, b₂, b₃⟩ s₁ s₂ hp
    simp only [List.append_assoc] at hp
    obtain ⟨h1, hs1⟩ := encodeKey_prefixFree a₁ b₁ _ _ hp
    obtain ⟨h2, hs2⟩ := encodeList_prefixFree encodeNat_prefixFree a₂ b₂ _ _ hs1
    obtain ⟨h3, hr⟩ := encodeKey_prefixFree a₃ b₃ s₁ s₂ hs2
    exact ⟨by rw [h1, h2, h3], hr⟩
  obtain ⟨hm, h1⟩ := encodeList_prefixFree hPair m₁ m₂ _ _ h
  obtain ⟨hlm, hr⟩ := encodeList_prefixFree hLawPair lm₁ lm₂ r₁ r₂ h1
  exact ⟨by rw [hm, hlm], hr⟩

theorem encodeConstruction_prefixFree : PrefixFree encodeConstruction := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeConstruction, List.cons_append, List.nil_append, List.append_assoc] at h <;>
    try exact ⟨rfl, (List.cons.inj h).2⟩
  all_goals try cases (List.cons.inj h).1
  obtain ⟨hs, h1⟩ := encodeModuleRef_prefixFree _ _ _ _ (List.cons.inj h).2
  obtain ⟨ht, hr⟩ := encodeOption_prefixFree (encodeList_prefixFree encodeNat_prefixFree) _ _ r₁ r₂ h1
  exact ⟨by rw [hs, ht], hr⟩

theorem encodeLayout_prefixFree : PrefixFree encodeLayout := by
  intro ⟨m₁, c₁, rec₁⟩ ⟨m₂, c₂, rec₂⟩ r₁ r₂ h
  simp only [encodeLayout, List.append_assoc] at h
  obtain ⟨hm, h1⟩ := encodeModuleRef_prefixFree m₁ m₂ _ _ h
  obtain ⟨hc, h2⟩ := encodeList_prefixFree encodeSite_prefixFree c₁ c₂ _ _ h1
  have hRec : PrefixFree (fun p : Site × Key => encodeSite p.1 ++ encodeKey p.2) := by
    intro ⟨s₁, k₁⟩ ⟨s₂, k₂⟩ t₁ t₂ hp
    simp only [List.append_assoc] at hp
    obtain ⟨hs, ht⟩ := encodeSite_prefixFree s₁ s₂ _ _ hp
    obtain ⟨hk, hr⟩ := encodeKey_prefixFree k₁ k₂ t₁ t₂ ht
    exact ⟨by rw [hs, hk], hr⟩
  obtain ⟨hrc, hr⟩ := encodeList_prefixFree hRec rec₁ rec₂ r₁ r₂ h2
  exact ⟨by rw [hm, hc, hrc], hr⟩

theorem encodeGrind_prefixFree : PrefixFree encodeGrind := by
  intro ⟨b₁, s₁⟩ ⟨b₂, s₂⟩ r₁ r₂ h
  simp only [encodeGrind, List.append_assoc] at h
  obtain ⟨hb, h1⟩ := encodeNat_prefixFree b₁ b₂ _ _ h
  obtain ⟨hs, hr⟩ := encodeList_prefixFree encodeSite_prefixFree s₁ s₂ r₁ r₂ h1
  exact ⟨by rw [hb, hs], hr⟩

theorem encodeCommitment_prefixFree : PrefixFree encodeCommitment := by
  intro ⟨k₁, s₁, p₁, v₁⟩ ⟨k₂, s₂, p₂, v₂⟩ r₁ r₂ h
  simp only [encodeCommitment, List.append_assoc] at h
  obtain ⟨hk, h1⟩ := encodeKey_prefixFree k₁ k₂ _ _ h
  obtain ⟨hs, h2⟩ := encodeModuleRef_prefixFree s₁ s₂ _ _ h1
  obtain ⟨hp, h3⟩ := encodeOption_prefixFree encodeSite_prefixFree p₁ p₂ _ _ h2
  obtain ⟨hv, hr⟩ := encodeOption_prefixFree encodeSite_prefixFree v₁ v₂ r₁ r₂ h3
  exact ⟨by rw [hk, hs, hp, hv], hr⟩

theorem encodePin_prefixFree : PrefixFree encodePin := by
  intro ⟨s₁, h₁, d₁⟩ ⟨s₂, h₂, d₂⟩ r₁ r₂ h
  simp only [encodePin, List.append_assoc] at h
  obtain ⟨hs, h1⟩ := encodeSite_prefixFree s₁ s₂ _ _ h
  obtain ⟨hh, h2⟩ := encodeKey_prefixFree h₁ h₂ _ _ h1
  obtain ⟨hd, hr⟩ := encodeList_prefixFree encodeNat_prefixFree d₁ d₂ r₁ r₂ h2
  exact ⟨by rw [hs, hh, hd], hr⟩

theorem encodeDeclaration_prefixFree : PrefixFree encodeDeclaration := by
  intro ⟨k₁, e₁, kd₁, c₁, p₁, l₁, rt₁, sm₁, cx₁, g₁, cm₁, pn₁, ap₁⟩
        ⟨k₂, e₂, kd₂, c₂, p₂, l₂, rt₂, sm₂, cx₂, g₂, cm₂, pn₂, ap₂⟩ r₁ r₂ h
  simp only [encodeDeclaration, List.append_assoc] at h
  obtain ⟨hk, h1⟩ := encodeKey_prefixFree k₁ k₂ _ _ h
  obtain ⟨he, h2⟩ := encodeKey_prefixFree e₁ e₂ _ _ h1
  obtain ⟨hkd, h3⟩ := encodeList_prefixFree encodeRoleKind_prefixFree kd₁ kd₂ _ _ h2
  obtain ⟨hc, h4⟩ := encodeConstruction_prefixFree c₁ c₂ _ _ h3
  obtain ⟨hp, h5⟩ := encodeOption_prefixFree encodeNat_prefixFree p₁ p₂ _ _ h4
  obtain ⟨hl, h6⟩ := encodeOption_prefixFree encodeLayout_prefixFree l₁ l₂ _ _ h5
  have hRt : PrefixFree (fun r : Nat × Site => encodeNat r.1 ++ encodeSite r.2) := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ t₁ t₂ hrt
    simp only [List.append_assoc] at hrt
    obtain ⟨ha, ht⟩ := encodeNat_prefixFree a₁ a₂ _ _ hrt
    obtain ⟨hb, hr⟩ := encodeSite_prefixFree b₁ b₂ t₁ t₂ ht
    exact ⟨by rw [ha, hb], hr⟩
  obtain ⟨hrt, h7⟩ := encodeOption_prefixFree hRt rt₁ rt₂ _ _ h6
  obtain ⟨hsm, h8⟩ := encodeOption_prefixFree encodeKey_prefixFree sm₁ sm₂ _ _ h7
  obtain ⟨hcx, h9⟩ := encodeList_prefixFree encodeKey_prefixFree cx₁ cx₂ _ _ h8
  obtain ⟨hg, h10⟩ := encodeList_prefixFree encodeGrind_prefixFree g₁ g₂ _ _ h9
  obtain ⟨hcm, h11⟩ := encodeList_prefixFree encodeCommitment_prefixFree cm₁ cm₂ _ _ h10
  obtain ⟨hpn, h12⟩ := encodeList_prefixFree encodePin_prefixFree pn₁ pn₂ _ _ h11
  obtain ⟨hap, hr⟩ := encodeList_prefixFree encodeNat_prefixFree ap₁ ap₂ r₁ r₂ h12
  exact ⟨by rw [hk, he, hkd, hc, hp, hl, hrt, hsm, hcx, hg, hcm, hpn, hap], hr⟩

/-- Distinct `Declaration` values always have distinct canonical byte encodings. -/
theorem encodeDeclaration_injective (d₁ d₂ : Declaration)
    (h : encodeDeclaration d₁ = encodeDeclaration d₂) : d₁ = d₂ :=
  (encodeDeclaration_prefixFree d₁ d₂ [] [] (by simpa using h)).1

theorem encodeReason_prefixFree : PrefixFree encodeReason := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeReason, List.cons_append, List.nil_append] at h <;>
    first | exact ⟨rfl, (List.cons.inj h).2⟩ | cases (List.cons.inj h).1

theorem encodeRepeat_prefixFree : PrefixFree encodeRepeat := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeRepeat, List.cons_append] at h
  · obtain ⟨hn, hr⟩ := encodeNat_prefixFree _ _ r₁ r₂ (List.cons.inj h).2; exact ⟨congrArg Repeat.fixed hn, hr⟩
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · obtain ⟨hn, hr⟩ := encodeNat_prefixFree _ _ r₁ r₂ (List.cons.inj h).2; exact ⟨congrArg Repeat.count hn, hr⟩

theorem encodeFlowKind_prefixFree : PrefixFree encodeFlowKind := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeFlowKind, List.cons_append, List.nil_append] at h <;>
    first | exact ⟨rfl, (List.cons.inj h).2⟩ | cases (List.cons.inj h).1

theorem encodeOwnedName_prefixFree : PrefixFree encodeOwnedName := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeOwnedName, List.cons_append, List.nil_append] at h <;>
    first | exact ⟨rfl, (List.cons.inj h).2⟩ | cases (List.cons.inj h).1

section Injectivity
variable {V : Vocabulary} (enc : VocabEncoder V)

mutual
  theorem encodeTy_prefixFree (hEnc : enc.Injective) : ∀ (a b : V.Ty) (r₁ r₂ : List Nat),
      encodeTy enc a ++ r₁ = encodeTy enc b ++ r₂ → a = b ∧ r₁ = r₂
    | .bool, .bool, _, _, h => by
        simp only [encodeTy, List.cons_append, List.nil_append] at h
        exact ⟨rfl, (List.cons.inj h).2⟩
    | .nat, .nat, _, _, h => by
        simp only [encodeTy, List.cons_append, List.nil_append] at h
        exact ⟨rfl, (List.cons.inj h).2⟩
    | .fin n₁, .fin n₂, r₁, r₂, h => by
        simp only [encodeTy, List.cons_append] at h
        obtain ⟨hn, hr⟩ := encodeNat_prefixFree n₁ n₂ r₁ r₂ (List.cons.inj h).2
        exact ⟨congrArg Ty.fin hn, hr⟩
    | .seq i₁ s₁, .seq i₂ s₂, r₁, r₂, h => by
        simp only [encodeTy, List.cons_append, List.append_assoc] at h
        obtain ⟨hi, h2⟩ := encodeTy_prefixFree hEnc i₁ i₂ _ _ (List.cons.inj h).2
        obtain ⟨hs, hr⟩ := encodeOption_prefixFree encodeNat_prefixFree s₁ s₂ r₁ r₂ h2
        exact ⟨by rw [hi, hs], hr⟩
    | .tuple ts₁, .tuple ts₂, r₁, r₂, h => by
        simp only [encodeTy, List.cons_append] at h
        obtain ⟨hts, hr⟩ := encodeTys_prefixFree hEnc ts₁ ts₂ r₁ r₂ (List.cons.inj h).2
        exact ⟨congrArg Ty.tuple hts, hr⟩
    | .record k₁ l₁ f₁, .record k₂ l₂ f₂, r₁, r₂, h => by
        simp only [encodeTy, List.cons_append, List.append_assoc] at h
        obtain ⟨hk, h2⟩ := encodeKey_prefixFree k₁ k₂ _ _ (List.cons.inj h).2
        obtain ⟨hl, h3⟩ := encodeBool_prefixFree l₁ l₂ _ _ h2
        obtain ⟨hf, hr⟩ := encodeTys_prefixFree hEnc f₁ f₂ r₁ r₂ h3
        exact ⟨by rw [hk, hl, hf], hr⟩
    | .variant k₁ a₁, .variant k₂ a₂, r₁, r₂, h => by
        simp only [encodeTy, List.cons_append, List.append_assoc] at h
        obtain ⟨hk, h2⟩ := encodeKey_prefixFree k₁ k₂ _ _ (List.cons.inj h).2
        obtain ⟨ha, hr⟩ := encodeTys_prefixFree hEnc a₁ a₂ r₁ r₂ h2
        exact ⟨by rw [hk, ha], hr⟩
    | .nominal k₁, .nominal k₂, r₁, r₂, h => by
        simp only [encodeTy, List.cons_append] at h
        obtain ⟨hk, hr⟩ := encodeList_prefixFree encodeNat_prefixFree (enc.typeKey k₁) (enc.typeKey k₂)
          r₁ r₂ (List.cons.inj h).2
        exact ⟨congrArg Ty.nominal (hEnc.1 k₁ k₂ hk), hr⟩
    | .bool, .nat, _, _, h | .bool, .fin _, _, _, h | .bool, .seq _ _, _, _, h
    | .bool, .tuple _, _, _, h | .bool, .record _ _ _, _, _, h | .bool, .variant _ _, _, _, h
    | .bool, .nominal _, _, _, h
    | .nat, .bool, _, _, h | .nat, .fin _, _, _, h | .nat, .seq _ _, _, _, h
    | .nat, .tuple _, _, _, h | .nat, .record _ _ _, _, _, h | .nat, .variant _ _, _, _, h
    | .nat, .nominal _, _, _, h
    | .fin _, .bool, _, _, h | .fin _, .nat, _, _, h | .fin _, .seq _ _, _, _, h
    | .fin _, .tuple _, _, _, h | .fin _, .record _ _ _, _, _, h | .fin _, .variant _ _, _, _, h
    | .fin _, .nominal _, _, _, h
    | .seq _ _, .bool, _, _, h | .seq _ _, .nat, _, _, h | .seq _ _, .fin _, _, _, h
    | .seq _ _, .tuple _, _, _, h | .seq _ _, .record _ _ _, _, _, h | .seq _ _, .variant _ _, _, _, h
    | .seq _ _, .nominal _, _, _, h
    | .tuple _, .bool, _, _, h | .tuple _, .nat, _, _, h | .tuple _, .fin _, _, _, h
    | .tuple _, .seq _ _, _, _, h | .tuple _, .record _ _ _, _, _, h | .tuple _, .variant _ _, _, _, h
    | .tuple _, .nominal _, _, _, h
    | .record _ _ _, .bool, _, _, h | .record _ _ _, .nat, _, _, h | .record _ _ _, .fin _, _, _, h
    | .record _ _ _, .seq _ _, _, _, h | .record _ _ _, .tuple _, _, _, h | .record _ _ _, .variant _ _, _, _, h
    | .record _ _ _, .nominal _, _, _, h
    | .variant _ _, .bool, _, _, h | .variant _ _, .nat, _, _, h | .variant _ _ , .fin _, _, _, h
    | .variant _ _, .seq _ _, _, _, h | .variant _ _, .tuple _, _, _, h | .variant _ _, .record _ _ _, _, _, h
    | .variant _ _, .nominal _, _, _, h
    | .nominal _, .bool, _, _, h | .nominal _, .nat, _, _, h | .nominal _, .fin _, _, _, h
    | .nominal _, .seq _ _, _, _, h | .nominal _, .tuple _, _, _, h | .nominal _, .record _ _ _, _, _, h
    | .nominal _, .variant _ _, _, _, h => by
        simp only [encodeTy, List.cons_append] at h
        cases (List.cons.inj h).1

  theorem encodeTys_prefixFree (hEnc : enc.Injective) : ∀ (a b : Tys V.TypeKey) (r₁ r₂ : List Nat),
      encodeTys enc a ++ r₁ = encodeTys enc b ++ r₂ → a = b ∧ r₁ = r₂
    | .nil, .nil, _, _, h => by
        simp only [encodeTys, List.cons_append, List.nil_append] at h
        exact ⟨rfl, (List.cons.inj h).2⟩
    | .nil, .cons _ _, _, _, h => by
        simp only [encodeTys, List.cons_append] at h; cases (List.cons.inj h).1
    | .cons _ _, .nil, _, _, h => by
        simp only [encodeTys, List.cons_append] at h; cases (List.cons.inj h).1
    | .cons h₁ t₁, .cons h₂ t₂, r₁, r₂, h => by
        simp only [encodeTys, List.cons_append, List.append_assoc] at h
        obtain ⟨hh, h2⟩ := encodeTy_prefixFree hEnc h₁ h₂ _ _ (List.cons.inj h).2
        obtain ⟨ht, hr⟩ := encodeTys_prefixFree hEnc t₁ t₂ r₁ r₂ h2
        exact ⟨by rw [hh, ht], hr⟩
end

theorem encodeLTy_prefixFree (hEnc : enc.Injective) : PrefixFree (encodeLTy enc) := by
  intro ⟨t₁, hs₁⟩ ⟨t₂, hs₂⟩ r₁ r₂ h
  simp only [encodeLTy, List.append_assoc] at h
  obtain ⟨ht, h1⟩ := encodeTy_prefixFree enc hEnc t₁ t₂ _ _ h
  obtain ⟨hh, hr⟩ := encodeList_prefixFree encodeNat_prefixFree hs₁ hs₂ r₁ r₂ h1
  exact ⟨by rw [ht, hh], hr⟩

theorem encodeGivenKind_prefixFree (hEnc : enc.Injective) : PrefixFree (encodeGivenKind enc) := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeGivenKind, List.cons_append] at h
  · obtain ⟨hl, hr⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ r₁ r₂ (List.cons.inj h).2
    exact ⟨congrArg GivenKind.coin (hEnc.2.2 _ _ hl), hr⟩
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · obtain ⟨hk, hr⟩ := encodeKey_prefixFree _ _ r₁ r₂ (List.cons.inj h).2
    exact ⟨congrArg GivenKind.request hk, hr⟩

theorem encodeEventClass_prefixFree (hEnc : enc.Injective) : PrefixFree (encodeEventClass enc) := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeEventClass, List.cons_append, List.append_assoc] at h
  · obtain ⟨hk, h1⟩ := encodeFlowKind_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨hg, h2⟩ := encodeNat_prefixFree _ _ _ _ h1
    obtain ⟨hgs, hr⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ r₁ r₂ h2
    exact ⟨by rw [hk, hg, hgs], hr⟩
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · obtain ⟨hk, h1⟩ := encodeGivenKind_prefixFree enc hEnc _ _ _ _ (List.cons.inj h).2
    obtain ⟨ho, h2⟩ := encodeNat_prefixFree _ _ _ _ h1
    obtain ⟨hhs, hr⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ r₁ r₂ h2
    exact ⟨by rw [hk, ho, hhs], hr⟩

theorem encodeLocalRaw_prefixFree (hEnc : enc.Injective) : PrefixFree (encodeLocalRaw enc) := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeLocalRaw, List.cons_append, List.append_assoc] at h <;>
    try cases (List.cons.inj h).1
  · obtain ⟨hk, hr⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ r₁ r₂ (List.cons.inj h).2
    exact ⟨congrArg LocalRaw.row (hEnc.2.1 _ _ hk), hr⟩
  · obtain ⟨hn, h1⟩ := encodeOwnedName_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨ht, h2⟩ := encodeList_prefixFree (encodeTy_prefixFree enc hEnc) _ _ _ _ h1
    obtain ⟨hnu, hr⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ r₁ r₂ h2
    exact ⟨by rw [hn, ht, hnu], hr⟩
  · obtain ⟨ht, h1⟩ := encodeTy_prefixFree enc hEnc _ _ _ _ (List.cons.inj h).2
    obtain ⟨hd, hr⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ r₁ r₂ h1
    exact ⟨by rw [ht, hd], hr⟩
  · obtain ⟨hc, hr⟩ := encodeKey_prefixFree _ _ r₁ r₂ (List.cons.inj h).2
    exact ⟨congrArg LocalRaw.call hc, hr⟩

theorem encodeProtocolRaw_prefixFree (hEnc : enc.Injective) : PrefixFree (encodeProtocolRaw enc) := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeProtocolRaw, List.cons_append, List.append_assoc] at h <;>
    try cases (List.cons.inj h).1
  · obtain ⟨hr1, h1⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨ho, hr⟩ := encodeLocalRaw_prefixFree enc hEnc _ _ r₁ r₂ h1
    exact ⟨by rw [hr1, ho], hr⟩
  · obtain ⟨hc, h1⟩ := encodeEventClass_prefixFree enc hEnc _ _ _ _ (List.cons.inj h).2
    obtain ⟨ht, hr⟩ := encodeTy_prefixFree enc hEnc _ _ r₁ r₂ h1
    exact ⟨by rw [hc, ht], hr⟩
  · obtain ⟨hr1, hr⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ r₁ r₂ (List.cons.inj h).2
    exact ⟨congrArg ProtocolRaw.narrow hr1, hr⟩
  · obtain ⟨hc, h1⟩ := encodeKey_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨hr1, hr⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ r₁ r₂ h1
    exact ⟨by rw [hc, hr1], hr⟩

end Injectivity

section RegionInjectivity
variable {Op Who : Type} (encOp : Op → List Nat) (encWho : Who → List Nat)

mutual
  theorem encodeInstruction_prefixFree (hOp : PrefixFree encOp) (hWho : PrefixFree encWho) :
      ∀ (a b : Instruction Op Who) (r₁ r₂ : List Nat),
      encodeInstruction encOp encWho a ++ r₁ = encodeInstruction encOp encWho b ++ r₂ →
      a = b ∧ r₁ = r₂
    | .op k₁ rs₁ o₁ ops₁, .op k₂ rs₂ o₂ ops₂, r₁, r₂, h => by
        simp only [encodeInstruction, List.cons_append, List.append_assoc] at h
        obtain ⟨hk, h1⟩ := encodeKey_prefixFree k₁ k₂ _ _ (List.cons.inj h).2
        obtain ⟨hrs, h2⟩ := encodeList_prefixFree encodeNat_prefixFree rs₁ rs₂ _ _ h1
        obtain ⟨ho, h3⟩ := hOp o₁ o₂ _ _ h2
        obtain ⟨hops, hr⟩ := encodeList_prefixFree encodeNat_prefixFree ops₁ ops₂ r₁ r₂ h3
        exact ⟨by rw [hk, hrs, ho, hops], hr⟩
    | .guard k₁ w₁ c₁ why₁, .guard k₂ w₂ c₂ why₂, r₁, r₂, h => by
        simp only [encodeInstruction, List.cons_append, List.append_assoc] at h
        obtain ⟨hk, h1⟩ := encodeKey_prefixFree k₁ k₂ _ _ (List.cons.inj h).2
        obtain ⟨hw, h2⟩ := hWho w₁ w₂ _ _ h1
        obtain ⟨hc, h3⟩ := encodeNat_prefixFree c₁ c₂ _ _ h2
        obtain ⟨hwhy, hr⟩ := encodeReason_prefixFree why₁ why₂ r₁ r₂ h3
        exact ⟨by rw [hk, hw, hc, hwhy], hr⟩
    | .choose k₁ w₁ c₁ rs₁ t₁ f₁, .choose k₂ w₂ c₂ rs₂ t₂ f₂, r₁, r₂, h => by
        simp only [encodeInstruction, List.cons_append, List.append_assoc] at h
        obtain ⟨hk, h1⟩ := encodeKey_prefixFree k₁ k₂ _ _ (List.cons.inj h).2
        obtain ⟨hw, h2⟩ := hWho w₁ w₂ _ _ h1
        obtain ⟨hc, h3⟩ := encodeNat_prefixFree c₁ c₂ _ _ h2
        obtain ⟨hrs, h4⟩ := encodeList_prefixFree encodeNat_prefixFree rs₁ rs₂ _ _ h3
        obtain ⟨ht, h5⟩ := encodeRegion_prefixFree hOp hWho t₁ t₂ _ _ h4
        obtain ⟨hf, hr⟩ := encodeRegion_prefixFree hOp hWho f₁ f₂ r₁ r₂ h5
        exact ⟨by rw [hk, hw, hc, hrs, ht, hf], hr⟩
    | .cases k₁ w₁ s₁ rs₁ a₁, .cases k₂ w₂ s₂ rs₂ a₂, r₁, r₂, h => by
        simp only [encodeInstruction, List.cons_append, List.append_assoc] at h
        obtain ⟨hk, h1⟩ := encodeKey_prefixFree k₁ k₂ _ _ (List.cons.inj h).2
        obtain ⟨hw, h2⟩ := hWho w₁ w₂ _ _ h1
        obtain ⟨hs, h3⟩ := encodeNat_prefixFree s₁ s₂ _ _ h2
        obtain ⟨hrs, h4⟩ := encodeList_prefixFree encodeNat_prefixFree rs₁ rs₂ _ _ h3
        obtain ⟨ha, hr⟩ := encodeRegions_prefixFree hOp hWho a₁ a₂ r₁ r₂ h4
        exact ⟨by rw [hk, hw, hs, hrs, ha], hr⟩
    | .loop k₁ w₁ t₁ c₁ rs₁ b₁, .loop k₂ w₂ t₂ c₂ rs₂ b₂, r₁, r₂, h => by
        simp only [encodeInstruction, List.cons_append, List.append_assoc] at h
        obtain ⟨hk, h1⟩ := encodeKey_prefixFree k₁ k₂ _ _ (List.cons.inj h).2
        obtain ⟨hw, h2⟩ := hWho w₁ w₂ _ _ h1
        obtain ⟨ht, h3⟩ := encodeRepeat_prefixFree t₁ t₂ _ _ h2
        obtain ⟨hc, h4⟩ := encodeList_prefixFree encodeNat_prefixFree c₁ c₂ _ _ h3
        obtain ⟨hrs, h5⟩ := encodeList_prefixFree encodeNat_prefixFree rs₁ rs₂ _ _ h4
        obtain ⟨hb, hr⟩ := encodeRegion_prefixFree hOp hWho b₁ b₂ r₁ r₂ h5
        exact ⟨by rw [hk, hw, ht, hc, hrs, hb], hr⟩
    | .block k₁ n₁ rs₁ b₁, .block k₂ n₂ rs₂ b₂, r₁, r₂, h => by
        simp only [encodeInstruction, List.cons_append, List.append_assoc] at h
        obtain ⟨hk, h1⟩ := encodeKey_prefixFree k₁ k₂ _ _ (List.cons.inj h).2
        obtain ⟨hn, h2⟩ := encodeNat_prefixFree n₁ n₂ _ _ h1
        obtain ⟨hrs, h3⟩ := encodeList_prefixFree encodeNat_prefixFree rs₁ rs₂ _ _ h2
        obtain ⟨hb, hr⟩ := encodeRegion_prefixFree hOp hWho b₁ b₂ r₁ r₂ h3
        exact ⟨by rw [hk, hn, hrs, hb], hr⟩
    | .attempt k₁ w₁ rs₁ b₁, .attempt k₂ w₂ rs₂ b₂, r₁, r₂, h => by
        simp only [encodeInstruction, List.cons_append, List.append_assoc] at h
        obtain ⟨hk, h1⟩ := encodeKey_prefixFree k₁ k₂ _ _ (List.cons.inj h).2
        obtain ⟨hw, h2⟩ := hWho w₁ w₂ _ _ h1
        obtain ⟨hrs, h3⟩ := encodeList_prefixFree encodeNat_prefixFree rs₁ rs₂ _ _ h2
        obtain ⟨hb, hr⟩ := encodeRegion_prefixFree hOp hWho b₁ b₂ r₁ r₂ h3
        exact ⟨by rw [hk, hw, hrs, hb], hr⟩
    | .op .., .guard .., _, _, h | .op .., .choose .., _, _, h | .op .., .cases .., _, _, h
    | .op .., .loop .., _, _, h | .op .., .block .., _, _, h | .op .., .attempt .., _, _, h
    | .guard .., .op .., _, _, h | .guard .., .choose .., _, _, h | .guard .., .cases .., _, _, h
    | .guard .., .loop .., _, _, h | .guard .., .block .., _, _, h | .guard .., .attempt .., _, _, h
    | .choose .., .op .., _, _, h | .choose .., .guard .., _, _, h | .choose .., .cases .., _, _, h
    | .choose .., .loop .., _, _, h | .choose .., .block .., _, _, h | .choose .., .attempt .., _, _, h
    | .cases .., .op .., _, _, h | .cases .., .guard .., _, _, h | .cases .., .choose .., _, _, h
    | .cases .., .loop .., _, _, h | .cases .., .block .., _, _, h | .cases .., .attempt .., _, _, h
    | .loop .., .op .., _, _, h | .loop .., .guard .., _, _, h | .loop .., .choose .., _, _, h
    | .loop .., .cases .., _, _, h | .loop .., .block .., _, _, h | .loop .., .attempt .., _, _, h
    | .block .., .op .., _, _, h | .block .., .guard .., _, _, h | .block .., .choose .., _, _, h
    | .block .., .cases .., _, _, h | .block .., .loop .., _, _, h | .block .., .attempt .., _, _, h
    | .attempt .., .op .., _, _, h | .attempt .., .guard .., _, _, h | .attempt .., .choose .., _, _, h
    | .attempt .., .cases .., _, _, h | .attempt .., .loop .., _, _, h | .attempt .., .block .., _, _, h => by
        simp only [encodeInstruction, List.cons_append] at h
        cases (List.cons.inj h).1

  theorem encodeInstructions_prefixFree (hOp : PrefixFree encOp) (hWho : PrefixFree encWho) :
      ∀ (a b : List (Instruction Op Who)) (r₁ r₂ : List Nat),
      encodeInstructions encOp encWho a ++ r₁ = encodeInstructions encOp encWho b ++ r₂ →
      a = b ∧ r₁ = r₂
    | [], [], _, _, h => by
        simp only [encodeInstructions, List.cons_append, List.nil_append] at h
        exact ⟨rfl, (List.cons.inj h).2⟩
    | [], _ :: _, _, _, h => by
        simp only [encodeInstructions, List.cons_append] at h; cases (List.cons.inj h).1
    | _ :: _, [], _, _, h => by
        simp only [encodeInstructions, List.cons_append] at h; cases (List.cons.inj h).1
    | i₁ :: rest₁, i₂ :: rest₂, r₁, r₂, h => by
        simp only [encodeInstructions, List.cons_append, List.append_assoc] at h
        obtain ⟨hi, h1⟩ := encodeInstruction_prefixFree hOp hWho i₁ i₂ _ _ (List.cons.inj h).2
        obtain ⟨hrest, hr⟩ := encodeInstructions_prefixFree hOp hWho rest₁ rest₂ r₁ r₂ h1
        exact ⟨by rw [hi, hrest], hr⟩

  theorem encodeRegion_prefixFree (hOp : PrefixFree encOp) (hWho : PrefixFree encWho) :
      ∀ (a b : Region Op Who) (r₁ r₂ : List Nat),
      encodeRegion encOp encWho a ++ r₁ = encodeRegion encOp encWho b ++ r₂ →
      a = b ∧ r₁ = r₂
    | .mk i₁ b₁ e₁, .mk i₂ b₂ e₂, r₁, r₂, h => by
        simp only [encodeRegion, List.append_assoc] at h
        obtain ⟨hi, h1⟩ := encodeList_prefixFree encodeNat_prefixFree i₁ i₂ _ _ h
        obtain ⟨hb, h2⟩ := encodeInstructions_prefixFree hOp hWho b₁ b₂ _ _ h1
        obtain ⟨he, hr⟩ := encodeList_prefixFree encodeNat_prefixFree e₁ e₂ r₁ r₂ h2
        exact ⟨by rw [hi, hb, he], hr⟩

  theorem encodeRegions_prefixFree (hOp : PrefixFree encOp) (hWho : PrefixFree encWho) :
      ∀ (a b : List (Region Op Who)) (r₁ r₂ : List Nat),
      encodeRegions encOp encWho a ++ r₁ = encodeRegions encOp encWho b ++ r₂ →
      a = b ∧ r₁ = r₂
    | [], [], _, _, h => by
        simp only [encodeRegions, List.cons_append, List.nil_append] at h
        exact ⟨rfl, (List.cons.inj h).2⟩
    | [], _ :: _, _, _, h => by
        simp only [encodeRegions, List.cons_append] at h; cases (List.cons.inj h).1
    | _ :: _, [], _, _, h => by
        simp only [encodeRegions, List.cons_append] at h; cases (List.cons.inj h).1
    | x₁ :: rest₁, x₂ :: rest₂, r₁, r₂, h => by
        simp only [encodeRegions, List.cons_append, List.append_assoc] at h
        obtain ⟨hx, h1⟩ := encodeRegion_prefixFree hOp hWho x₁ x₂ _ _ (List.cons.inj h).2
        obtain ⟨hrest, hr⟩ := encodeRegions_prefixFree hOp hWho rest₁ rest₂ r₁ r₂ h1
        exact ⟨by rw [hx, hrest], hr⟩
end

end RegionInjectivity

/-- Statement domain labels are injective. -/
theorem stmtLabel_injective {i₁ i₂ : Nat} (h : stmtLabel i₁ = stmtLabel i₂) : i₁ = i₂ := by
  unfold stmtLabel at h
  have h1 := List.append_cancel_left h
  exact (encodeNat_prefixFree i₁ i₂ [] [] (by simpa using h1)).1

/-- Message site domain labels are injective on full `Site` (`through` and `key`). -/
theorem msgLabel_injective {s₁ s₂ : Site} (h : msgLabel s₁ = msgLabel s₂) : s₁ = s₂ := by
  unfold msgLabel at h
  have h1 := List.append_cancel_left h
  exact (encodeSite_prefixFree s₁ s₂ [] [] (by simpa using h1)).1

/-- Draw site domain labels are injective on full `Site` (`through` and `key`). -/
theorem drawLabel_injective {s₁ s₂ : Site} (h : drawLabel s₁ = drawLabel s₂) : s₁ = s₂ := by
  unfold drawLabel at h
  have h1 := List.append_cancel_left h
  exact (encodeSite_prefixFree s₁ s₂ [] [] (by simpa using h1)).1

/-- Message and draw domain labels are disjoint for all sites. -/
theorem msgLabel_ne_drawLabel (s₁ s₂ : Site) : msgLabel s₁ ≠ drawLabel s₂ := by
  intro h
  simp only [msgLabel, drawLabel, msgDomainTag, drawDomainTag, List.cons_append] at h
  cases h

/-- Statement and message domain labels are disjoint. -/
theorem stmtLabel_ne_msgLabel (i : Nat) (s : Site) : stmtLabel i ≠ msgLabel s := by
  intro h
  simp only [stmtLabel, msgLabel, stmtDomainTag, msgDomainTag, List.cons_append] at h
  cases h

/-- Statement and draw domain labels are disjoint. -/
theorem stmtLabel_ne_drawLabel (i : Nat) (s : Site) : stmtLabel i ≠ drawLabel s := by
  intro h
  simp only [stmtLabel, drawLabel, stmtDomainTag, drawDomainTag, List.cons_append] at h
  cases h

theorem encodeOperandEmpty_prefixFree : PrefixFree encodeOperandEmpty := by
  intro a b r₁ r₂ h
  cases a with
  | arg p₁ =>
      cases b with
      | arg p₂ =>
          obtain ⟨hp, hr⟩ := encodeNat_prefixFree p₁ p₂ r₁ r₂ h
          exact ⟨congrArg Operand.arg hp, hr⟩
      | apply w _ => nomatch w
  | apply w _ => nomatch w

theorem encodeReqEmpty_prefixFree : PrefixFree encodeReqEmpty := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeReqEmpty, List.cons_append, List.append_assoc] at h
  · obtain ⟨h1, hr1⟩ := encodeOperandEmpty_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨h2, hr2⟩ := encodeOperandEmpty_prefixFree _ _ r₁ r₂ hr1
    exact ⟨by rw [h1, h2], hr2⟩
  all_goals try cases (List.cons.inj h).1
  · obtain ⟨h1, hr1⟩ := encodeOperandEmpty_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨h2, hr2⟩ := encodeOperandEmpty_prefixFree _ _ r₁ r₂ hr1
    exact ⟨by rw [h1, h2], hr2⟩
  · obtain ⟨h1, hr1⟩ := encodeOperandEmpty_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨h2, hr2⟩ := encodeNat_prefixFree _ _ r₁ r₂ hr1
    exact ⟨by rw [h1, h2], hr2⟩
  · obtain ⟨h1, hr1⟩ := encodeOperandEmpty_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨h2, hr2⟩ := encodeNat_prefixFree _ _ r₁ r₂ hr1
    exact ⟨by rw [h1, h2], hr2⟩
  · obtain ⟨h1, hr1⟩ := encodeOperandEmpty_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨h2, hr2⟩ := encodeNat_prefixFree _ _ r₁ r₂ hr1
    exact ⟨by rw [h1, h2], hr2⟩
  · obtain ⟨h1, hr1⟩ := encodeOperandEmpty_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨h2, hr2⟩ := encodeOperandEmpty_prefixFree _ _ _ _ hr1
    obtain ⟨h3, hr3⟩ := encodeNat_prefixFree _ _ r₁ r₂ hr2
    exact ⟨by rw [h1, h2, h3], hr3⟩
  · obtain ⟨h1, hr1⟩ := encodeOperandEmpty_prefixFree _ _ r₁ r₂ (List.cons.inj h).2
    exact ⟨by rw [h1], hr1⟩
  · obtain ⟨h1, hr1⟩ := encodeOperandEmpty_prefixFree _ _ r₁ r₂ (List.cons.inj h).2
    exact ⟨by rw [h1], hr1⟩

section SummaryInjectivity
variable {Raw : Type}

mutual
  theorem encodeExpr_prefixFree {encRaw : Raw → List Nat} (hRaw : PrefixFree encRaw) :
      ∀ (a b : BodyAnalysis.Expr Raw) (r₁ r₂ : List Nat),
      encodeExpr encRaw a ++ r₁ = encodeExpr encRaw b ++ r₂ → a = b ∧ r₁ = r₂
    | .arg p₁, .arg p₂, r₁, r₂, h => by
        simp only [encodeExpr, List.cons_append] at h
        obtain ⟨hp, hr⟩ := encodeNat_prefixFree p₁ p₂ r₁ r₂ (List.cons.inj h).2
        exact ⟨by rw [hp], hr⟩
    | .arg _, .apply .., _, _, h => by simp only [encodeExpr, List.cons_append] at h; cases (List.cons.inj h).1
    | .apply .., .arg _, _, _, h => by simp only [encodeExpr, List.cons_append] at h; cases (List.cons.inj h).1
    | .apply w₁ o₁ res₁, .apply w₂ o₂ res₂, r₁, r₂, h => by
        simp only [encodeExpr, List.cons_append, List.append_assoc] at h
        obtain ⟨hw, h1⟩ := hRaw w₁ w₂ _ _ (List.cons.inj h).2
        obtain ⟨ho, h2⟩ := encodeExprs_prefixFree hRaw o₁ o₂ _ _ h1
        obtain ⟨hres, hr⟩ := encodeNat_prefixFree res₁ res₂ r₁ r₂ h2
        exact ⟨by rw [hw, ho, hres], hr⟩

  theorem encodeExprs_prefixFree {encRaw : Raw → List Nat} (hRaw : PrefixFree encRaw) :
      ∀ (a b : BodyAnalysis.Exprs Raw) (r₁ r₂ : List Nat),
      encodeExprs encRaw a ++ r₁ = encodeExprs encRaw b ++ r₂ → a = b ∧ r₁ = r₂
    | .nil, .nil, _, _, h => by
        simp only [encodeExprs, List.cons_append, List.nil_append] at h
        exact ⟨rfl, (List.cons.inj h).2⟩
    | .nil, .cons .., _, _, h => by simp only [encodeExprs, List.cons_append] at h; cases (List.cons.inj h).1
    | .cons .., .nil, _, _, h => by simp only [encodeExprs, List.cons_append] at h; cases (List.cons.inj h).1
    | .cons e₁ rest₁, .cons e₂ rest₂, r₁, r₂, h => by
        simp only [encodeExprs, List.cons_append, List.append_assoc] at h
        obtain ⟨he, h1⟩ := encodeExpr_prefixFree hRaw e₁ e₂ _ _ (List.cons.inj h).2
        obtain ⟨hrest, hr⟩ := encodeExprs_prefixFree hRaw rest₁ rest₂ r₁ r₂ h1
        exact ⟨by rw [he, hrest], hr⟩
end

theorem encodeContractClause_prefixFree {encRaw : Raw → List Nat} (hRaw : PrefixFree encRaw) :
    PrefixFree (encodeContractClause encRaw) := by
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ r₁ r₂ h
  simp only [encodeContractClause, List.append_assoc] at h
  obtain ⟨ha, h1⟩ := encodeExpr_prefixFree hRaw a₁ a₂ _ _ h
  obtain ⟨hb, hr⟩ := encodeOption_prefixFree (encodeExpr_prefixFree hRaw) b₁ b₂ r₁ r₂ h1
  exact ⟨by rw [ha, hb], hr⟩

theorem encodeStaticRegion_prefixFree : PrefixFree encodeStaticRegion := by
  intro a b r₁ r₂ h
  induction a generalizing b r₁ r₂ with
  | root =>
      cases b <;> simp only [encodeStaticRegion, List.cons_append, List.nil_append] at h
      · exact ⟨rfl, (List.cons.inj h).2⟩
      all_goals cases (List.cons.inj h).1
  | body p₁ o₁ k₁ ih =>
      cases b <;> simp only [encodeStaticRegion, List.cons_append, List.append_assoc] at h
      · cases (List.cons.inj h).1
      · obtain ⟨hp, h1⟩ := ih _ _ _ (List.cons.inj h).2
        obtain ⟨ho, h2⟩ := encodeNat_prefixFree _ _ _ _ h1
        obtain ⟨hk, hr⟩ := encodeKey_prefixFree _ _ r₁ r₂ h2
        exact ⟨by rw [hp, ho, hk], hr⟩
      all_goals cases (List.cons.inj h).1
  | otherwise p₁ o₁ k₁ ih =>
      cases b <;> simp only [encodeStaticRegion, List.cons_append, List.append_assoc] at h
      · cases (List.cons.inj h).1
      · cases (List.cons.inj h).1
      · obtain ⟨hp, h1⟩ := ih _ _ _ (List.cons.inj h).2
        obtain ⟨ho, h2⟩ := encodeNat_prefixFree _ _ _ _ h1
        obtain ⟨hk, hr⟩ := encodeKey_prefixFree _ _ r₁ r₂ h2
        exact ⟨by rw [hp, ho, hk], hr⟩
      all_goals cases (List.cons.inj h).1
  | arm p₁ o₁ ih =>
      cases b <;> simp only [encodeStaticRegion, List.cons_append, List.append_assoc] at h
      · cases (List.cons.inj h).1
      · cases (List.cons.inj h).1
      · cases (List.cons.inj h).1
      · obtain ⟨hp, h1⟩ := ih _ _ _ (List.cons.inj h).2
        obtain ⟨ho, hr⟩ := encodeNat_prefixFree _ _ r₁ r₂ h1
        exact ⟨by rw [hp, ho], hr⟩
      · cases (List.cons.inj h).1
  | block p₁ o₁ k₁ n₁ ih =>
      cases b <;> simp only [encodeStaticRegion, List.cons_append, List.append_assoc] at h
      · cases (List.cons.inj h).1
      · cases (List.cons.inj h).1
      · cases (List.cons.inj h).1
      · cases (List.cons.inj h).1
      · obtain ⟨hp, h1⟩ := ih _ _ _ (List.cons.inj h).2
        obtain ⟨ho, h2⟩ := encodeNat_prefixFree _ _ _ _ h1
        obtain ⟨hk, h3⟩ := encodeKey_prefixFree _ _ _ _ h2
        obtain ⟨hn, hr⟩ := encodeNat_prefixFree _ _ r₁ r₂ h3
        exact ⟨by rw [hp, ho, hk, hn], hr⟩

theorem encodeStaticCursor_prefixFree : PrefixFree encodeStaticCursor := by
  intro ⟨e₁, o₁⟩ ⟨e₂, o₂⟩ r₁ r₂ h
  simp only [encodeStaticCursor, List.append_assoc] at h
  obtain ⟨he, h1⟩ := encodeStaticRegion_prefixFree e₁ e₂ _ _ h
  obtain ⟨ho, hr⟩ := encodeNat_prefixFree o₁ o₂ r₁ r₂ h1
  exact ⟨by rw [he, ho], hr⟩

theorem encodeAnnotationSite_prefixFree : PrefixFree encodeAnnotationSite := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeAnnotationSite, List.cons_append, List.append_assoc] at h
  · obtain ⟨hc, h1⟩ := encodeStaticCursor_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨hk, hr⟩ := encodeKey_prefixFree _ _ r₁ r₂ h1
    exact ⟨by rw [hc, hk], hr⟩
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · obtain ⟨hc, h1⟩ := encodeStaticCursor_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨hk, h2⟩ := encodeKey_prefixFree _ _ _ _ h1
    obtain ⟨hn, hr⟩ := encodeNat_prefixFree _ _ r₁ r₂ h2
    exact ⟨by rw [hc, hk, hn], hr⟩

theorem encodeAnnotation_prefixFree {encRaw : Raw → List Nat} (hRaw : PrefixFree encRaw) :
    PrefixFree (encodeAnnotation encRaw) := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeAnnotation, List.cons_append, List.append_assoc] at h
  · obtain ⟨hu, h1⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨ha, hr⟩ := encodeList_prefixFree (encodeExpr_prefixFree hRaw) _ _ r₁ r₂ h1
    exact ⟨by rw [hu, ha], hr⟩
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · obtain ⟨hl, h1⟩ := encodeNat_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨hn, hr⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ r₁ r₂ h1
    exact ⟨by rw [hl, hn], hr⟩
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · obtain ⟨hu, h1⟩ := encodeList_prefixFree encodeNat_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨ha, hr⟩ := encodeExpr_prefixFree hRaw _ _ r₁ r₂ h1
    exact ⟨by rw [hu, ha], hr⟩

theorem encodeAnnotations_prefixFree {encRaw : Raw → List Nat} (hRaw : PrefixFree encRaw) :
    PrefixFree (encodeAnnotations encRaw) := by
  apply encodeList_prefixFree
  intro ⟨s₁, a₁⟩ ⟨s₂, a₂⟩ r₁ r₂ h
  simp only [List.append_assoc] at h
  obtain ⟨hs, h1⟩ := encodeAnnotationSite_prefixFree s₁ s₂ _ _ h
  obtain ⟨ha, hr⟩ := encodeAnnotation_prefixFree hRaw a₁ a₂ r₁ r₂ h1
  exact ⟨by rw [hs, ha], hr⟩

end SummaryInjectivity

theorem encodeHeaderClause_prefixFree {V : Vocabulary} (enc : VocabEncoder V) (hEnc : enc.Injective) :
    PrefixFree (encodeHeaderClause enc) := by
  intro a b r₁ r₂ h
  cases a <;> cases b <;> simp only [encodeHeaderClause, List.cons_append] at h
  · obtain ⟨hrq, hr⟩ := encodeReqEmpty_prefixFree _ _ r₁ r₂ (List.cons.inj h).2
    exact ⟨by rw [hrq], hr⟩
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · obtain ⟨hc, hr⟩ := encodeContractClause_prefixFree (encodeLocalRaw_prefixFree enc hEnc)
      _ _ r₁ r₂ (List.cons.inj h).2
    exact ⟨by rw [hc], hr⟩

theorem encodeHeaderSummary_prefixFree {V : Vocabulary} (enc : VocabEncoder V) (hEnc : enc.Injective) :
    PrefixFree (encodeHeaderSummary enc) := by
  intro ⟨req₁, ens₁⟩ ⟨req₂, ens₂⟩ r₁ r₂ h
  simp only [encodeHeaderSummary, List.append_assoc] at h
  obtain ⟨hreq, h1⟩ := encodeList_prefixFree (encodeHeaderClause_prefixFree enc hEnc) req₁ req₂ _ _ h
  obtain ⟨hens, hr⟩ := encodeList_prefixFree (encodeHeaderClause_prefixFree enc hEnc) ens₁ ens₂ r₁ r₂ h1
  exact ⟨by rw [hreq, hens], hr⟩

theorem encodeDefinition_prefixFree {V : Vocabulary} (enc : VocabEncoder V) (hEnc : enc.Injective) :
    PrefixFree (encodeDefinition enc) := by
  intro d₁ d₂ r₁ r₂ h
  cases d₁ <;> cases d₂ <;> simp only [encodeDefinition, List.cons_append, List.append_assoc] at h
  · obtain ⟨hk, h1⟩ := encodeKey_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨hi, h2⟩ := encodeList_prefixFree (encodeTy_prefixFree enc hEnc) _ _ _ _ h1
    obtain ⟨ho, h3⟩ := encodeList_prefixFree (encodeTy_prefixFree enc hEnc) _ _ _ _ h2
    obtain ⟨hs, h4⟩ := encodeBool_prefixFree _ _ _ _ h3
    obtain ⟨hker, h5⟩ := encodeOption_prefixFree encodeKey_prefixFree _ _ _ _ h4
    obtain ⟨hsum, h6⟩ := encodeHeaderSummary_prefixFree enc hEnc _ _ _ _ h5
    have hUnit : PrefixFree (fun _ : Unit => ([] : List Nat)) := fun u₁ u₂ s₁ s₂ hs' => by
      cases u₁; cases u₂; exact ⟨rfl, hs'⟩
    obtain ⟨hb, h7⟩ := encodeRegion_prefixFree (encodeLocalRaw enc) (fun _ => [])
      (encodeLocalRaw_prefixFree enc hEnc) hUnit _ _ _ _ h6
    obtain ⟨hn, hr⟩ := encodeAnnotations_prefixFree (encodeLocalRaw_prefixFree enc hEnc) _ _ r₁ r₂ h7
    exact ⟨by rw [hk, hi, ho, hs, hker, hsum, hb, hn], hr⟩
  · cases (List.cons.inj h).1
  · cases (List.cons.inj h).1
  · obtain ⟨hk, h1⟩ := encodeKey_prefixFree _ _ _ _ (List.cons.inj h).2
    obtain ⟨hrol, h2⟩ := encodeNat_prefixFree _ _ _ _ h1
    obtain ⟨hi, h3⟩ := encodeList_prefixFree (encodeLTy_prefixFree enc hEnc) _ _ _ _ h2
    obtain ⟨ho, h4⟩ := encodeList_prefixFree (encodeLTy_prefixFree enc hEnc) _ _ _ _ h3
    obtain ⟨hb, hr⟩ := encodeRegion_prefixFree (encodeProtocolRaw enc) (encodeList encodeNat)
      (encodeProtocolRaw_prefixFree enc hEnc) (encodeList_prefixFree encodeNat_prefixFree) _ _ r₁ r₂ h4
    exact ⟨by rw [hk, hrol, hi, ho, hb], hr⟩

/-- Exact converse of `schemeIdentity_reads` under an injective `VocabEncoder`: equal canonical
identities imply literal equality of the declarations and of `canonicalClosureDefs` (the reachable
erased definitions in canonical reference order with proof-only annotations stripped). -/
theorem schemeIdentity_injective {V : Vocabulary} (enc : VocabEncoder V) (hEnc : enc.Injective)
    (a₁ a₂ : Admitted V) (decl₁ decl₂ : Declaration)
    (hEq : schemeIdentity enc a₁ decl₁ = schemeIdentity enc a₂ decl₂) :
    decl₁ = decl₂ ∧
    canonicalClosureDefs a₁ decl₁ = canonicalClosureDefs a₂ decl₂ := by
  unfold schemeIdentity at hEq
  simp only [List.append_assoc] at hEq
  have h1 := List.append_cancel_left hEq
  obtain ⟨hDecl, hRest⟩ := encodeDeclaration_prefixFree decl₁ decl₂ _ _ h1
  obtain ⟨hDefs, _⟩ := encodeList_prefixFree (encodeDefinition_prefixFree enc hEnc)
    (canonicalClosureDefs a₁ decl₁)
    (canonicalClosureDefs a₂ decl₂)
    [] [] (by rw [List.append_nil, List.append_nil]; exact hRest)
  exact ⟨hDecl, hDefs⟩

end Zkc.Core
