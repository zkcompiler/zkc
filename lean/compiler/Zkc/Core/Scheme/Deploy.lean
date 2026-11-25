module

public import Zkc.Core.Format.Canonical
public import Zkc.Core.Scheme.Deployed
public import Zkc.Core.Projection.Theorem
public import Zkc.Core.World.Runs
public import Zkc.Core.Program.EraseProgram

@[expose] public section

/-!
Non-interactive scheme deployment over an admitted core program.

This module provides:
1. Canonical byte encodings of declarations, occurrences, and reachable erased definitions,
   yielding a deterministic scheme identity (`deployedIdentity`, `schemeIdentity`) that reads
   only the declaration and its reachable erased definitions (`deployedIdentity_reads`).
2. An abstract deterministic Fiat-Shamir transcript model (`TranscriptModel`) whose lawfulness
   states that squeezed challenges lie in the support of the coin's law.
3. Static validation of a scheme declaration against an admitted program (`planDeployment`),
   producing a proof-carrying `DeploymentPlan`.
4. A two-layer `Core.Handler` stack composed with `Handler.over` over unmodified `roleMeaning`:
   - inner layer: Fiat-Shamir transcript absorption and challenge squeezing;
   - outer layer: canonical proof serialization (prover) and strict canonical deserialization
     with trailing-byte rejection (verifier).
5. Formal coverage (`deploy_coverage`) and completeness (`deploy_complete`) theorems proved
   directly from `Zkc.Core.projection` and `Zkc.Core.canonicalFormat_lawful`, using only
   `propext` and `Quot.sound`.
-/

namespace Zkc.Core

/-! ## Canonical encoding helpers for identity and transcript domain separation -/

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

/-- Encode a path frame for domain separation and occurrence binding. -/
def encodeFrame : Frame → List Nat
  | .application k => 0 :: encodeKey k
  | .iteration loop n => 1 :: encodeKey loop ++ encodeNat n
  | .attempt k n => 2 :: encodeKey k ++ encodeNat n

/-- Encode an occurrence (`path`, `key`) canonically. -/
def encodeOccurrence (at_ : Occurrence) : List Nat :=
  encodeList encodeFrame at_.path ++ encodeKey at_.key

/-- Encode a site (`through`, `key`) canonically. -/
def encodeSite (s : Site) : List Nat :=
  encodeList encodeKey s.through ++ encodeKey s.key

/-- Encode a `RoleKind` as a single canonical tag byte. -/
def encodeRoleKind : RoleKind → List Nat
  | .online => [0]
  | .offline => [1]
  | .service => [2]

/-- Encode a `CatalogueSuite` as a single canonical tag byte. -/
def encodeCatalogueSuite : CatalogueSuite → List Nat
  | .merlin3Bls12381 => [0]
  | .cfrgShake128 => [1]
  | .poseidon2KoalaBear => [2]

/-- Encode a `ModuleRef`. -/
def encodeModuleRef (m : ModuleRef) : List Nat :=
  encodeList (fun p => encodeKey p.1 ++ encodeKey p.2) m.members

/-- Encode a `Construction`. -/
def encodeConstruction : Construction → List Nat
  | .interactive => [0]
  | .derived suite => 1 :: encodeModuleRef suite
  | .catalogue suite tag => 2 :: encodeCatalogueSuite suite ++ encodeOption encodeString tag

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

/-- Canonical byte encoding of a scheme `Declaration`. -/
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
    encodeList encodePin d.pins

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

/-- The erased definitions reached by a declaration and its entry protocol. -/
def reachableDefinitions {V : Vocabulary} (a : Admitted V) (decl : Declaration) :
    List (Definition V) :=
  let closure := (decl.entry :: decl.definitions).flatMap a.program.defs.closureOf
  (erase a.program).definitions.filter (fun definition => decide (definition.key ∈ closure))

/-- The canonical byte identity of a scheme from its declaration and reachable erased
definitions. -/
def schemeIdentity {V : Vocabulary} (enc : VocabEncoder V)
    (decl : Declaration) (reachable : List (Definition V)) : List Nat :=
  encodeDeclaration decl ++ encodeList (encodeDefinition enc) reachable

/-- The canonical byte identity of a `Deployed` scheme. -/
def deployedIdentity {V : Vocabulary} (enc : VocabEncoder V) (d : Deployed V) : List Nat :=
  schemeIdentity enc d.declaration
    ((erase d.admitted.program).definitions.filter (fun definition => decide (definition.key ∈ d.closure)))

/-- `deployedIdentity` reads only the declaration and the erased definitions in the
deployment's closure, satisfying `Statements.identityReads`. -/
theorem deployedIdentity_reads {V : Vocabulary} (enc : VocabEncoder V) (d d' : Deployed V)
    (hdecl : d.declaration = d'.declaration)
    (hdefs :
      (erase d.admitted.program).definitions.filter (fun definition => decide (definition.key ∈ d.closure)) =
      (erase d'.admitted.program).definitions.filter (fun definition => decide (definition.key ∈ d'.closure))) :
    deployedIdentity enc d = deployedIdentity enc d' := by
  simp only [deployedIdentity, hdecl, hdefs]

/-! ## Transcript domain-separation labels and abstract transcript model -/

/-- Domain-separation tag for absorbing the canonical public statement at transcript start. -/
def statementLabel : List Nat := [1]

/-- Domain-separation label for absorbing a prover message at occurrence `at_`. -/
def messageLabel (at_ : Occurrence) : List Nat := 2 :: encodeOccurrence at_

/-- Domain-separation label for squeezing a public coin challenge at occurrence `at_`. -/
def coinLabel (at_ : Occurrence) : List Nat := 3 :: encodeOccurrence at_

/-- Abstract deterministic stateful Fiat-Shamir transcript over a model `M`.
Concrete deployment suites (Merlin, CFRG SHAKE-128, Poseidon2) instantiate this structure
in downstream tools; random-oracle security proofs instantiate it with an ideal oracle. -/
structure TranscriptModel (V : Vocabulary) (M : Model V) where
  State : Type
  /-- Initialize transcript state from the deployed scheme identity bytes. -/
  init : List Nat → State
  /-- Absorb a domain-separated label and canonical payload bytes. -/
  absorb : State → List Nat → List Nat → State
  /-- Deterministically derive a challenge of type `τ` for a nullary coin law `law`,
  returning `none` only for unsupported types or laws. -/
  squeeze : State → V.LawKey → (τ : V.Ty) → List Nat → Option (M.Val τ × State)

/-- A transcript model is lawful when for every nullary coin law of the vocabulary,
`squeeze` succeeds and produces a challenge allowed by that law in `M`. -/
def TranscriptModel.Lawful {V : Vocabulary} {M : Model V} (tm : TranscriptModel V M) : Prop :=
  ∀ (st : tm.State) (law : V.LawKey) (s : LawSignature V.TypeKey)
    (_ : V.law law = some s) (_ : s.ins = []) (τ : V.Ty) (_ : s.out = τ) (label : List Nat),
    ∃ c st', tm.squeeze st law τ label = some (c, st') ∧
      Allows M (.coin law) [] .nil τ c

/-! ## Static validation and `DeploymentPlan` -/

/-- Refusal reasons when validating a non-interactive scheme declaration for deployment. -/
inductive DeployRefusal where
  | entryNotFound (entry : Key)
  | roleKindsLength (expected found : Nat)
  | interactiveNotSupported
  | invalidParties
  | nonDistinctParties (role : Role)
  | retryBoundZero
  | retryNotAnAttempt (site : Site)
  | abortOutsideAttempt (sites : List Site)
  | unsupportedFlow (site : Site) (giver : Role) (getters : List Role)
  | unsupportedHeardCoin (site : Site) (owner : Role) (hearers : List Role)
  | nonNullaryHeardCoin (site : Site)
  | unsupportedRequest (site : Site) (service : Key)
deriving DecidableEq, Repr

/-- Whether a shape event is supported by two-party non-interactive Fiat-Shamir deployment
between `prover` and `verifier`. -/
def EventCovered (V : Vocabulary) (prover verifier : Role) (e : ShapeEvent V) : Prop :=
  match e.cls with
  | .flow _ giver getters =>
      (giver = prover ∧ verifier ∈ getters ∧ prover ∉ getters) ∨
      (giver ≠ prover ∧ prover ∉ getters ∧ giver ≠ verifier ∧ verifier ∉ getters)
  | .given (.coin law) owner hearers =>
      hearers = [] ∨
      ((((owner = verifier ∧ prover ∈ hearers) ∨ (owner = prover ∧ verifier ∈ hearers)) ∨
        (owner ≠ prover ∧ prover ∉ hearers ∧ owner ≠ verifier ∧ verifier ∉ hearers)) ∧
        ∃ s, V.law law = some s ∧ s.ins = [] ∧ s.out = e.τ)
  | .given (.request _) owner hearers =>
      owner ≠ prover ∧ prover ∉ hearers ∧ owner ≠ verifier ∧ verifier ∉ hearers

/-- Decide and validate that a single `ShapeEvent` is covered by the deployment plan. -/
def checkEventCovered {V : Vocabulary} (prover verifier : Role) (e : ShapeEvent V) :
    Except DeployRefusal (PLift (EventCovered V prover verifier e)) :=
  match hcls : e.cls with
  | .flow _ giver getters =>
      if h1 : giver = prover ∧ verifier ∈ getters ∧ prover ∉ getters then
        .ok ⟨by simp [EventCovered, hcls, h1]⟩
      else if h2 : giver ≠ prover ∧ prover ∉ getters ∧ giver ≠ verifier ∧ verifier ∉ getters then
        .ok ⟨by simp [EventCovered, hcls, h2]⟩
      else
        .error (.unsupportedFlow e.site giver getters)
  | .given (.coin law) owner hearers =>
      if hpriv : hearers = [] then
        .ok ⟨by simp [EventCovered, hcls, hpriv]⟩
      else if hparties :
          ((owner = verifier ∧ prover ∈ hearers) ∨ (owner = prover ∧ verifier ∈ hearers)) ∨
          (owner ≠ prover ∧ prover ∉ hearers ∧ owner ≠ verifier ∧ verifier ∉ hearers) then
        match hlaw : V.law law with
        | some s =>
            if hsig : s.ins = [] ∧ s.out = e.τ then
              .ok ⟨by
                simp only [EventCovered, hcls]
                exact .inr ⟨hparties, s, hlaw, hsig.1, hsig.2⟩⟩
            else
              .error (.nonNullaryHeardCoin e.site)
        | none => .error (.nonNullaryHeardCoin e.site)
      else
        .error (.unsupportedHeardCoin e.site owner hearers)
  | .given (.request service) owner hearers =>
      if hsilent : owner ≠ prover ∧ prover ∉ hearers ∧ owner ≠ verifier ∧ verifier ∉ hearers then
        .ok ⟨by simp [EventCovered, hcls, hsilent]⟩
      else
        .error (.unsupportedRequest e.site service)

/-- Validate that every event in `events` is covered by the deployment plan. -/
def checkAllEventsCovered {V : Vocabulary} (prover verifier : Role) :
    (events : List (ShapeEvent V)) →
    Except DeployRefusal (PLift (∀ e, e ∈ events → EventCovered V prover verifier e))
  | [] => .ok ⟨fun _ h => nomatch h⟩
  | e :: rest => do
      let ⟨he⟩ ← checkEventCovered prover verifier e
      let ⟨hrest⟩ ← checkAllEventsCovered prover verifier rest
      pure ⟨fun e' hm => by
        rcases List.mem_cons.mp hm with rfl | hm
        · exact he
        · exact hrest e' hm⟩

/-- A validated, deterministic non-interactive deployment plan for an admitted core program. -/
structure DeploymentPlan (V : Vocabulary) where
  admitted : Admitted V
  declaration : Declaration
  found : (admitted.program.findProtocol declaration.entry).isSome
  prover : Role
  verifier : Role
  rolesEq :
    proverAndVerifier ((admitted.program.findProtocol declaration.entry).get found).1 declaration =
      some (prover, verifier)
  distinctParties : prover ≠ verifier
  nonInteractive : declaration.interactive = false
  scopedRetry :
    (∀ bound site, declaration.retry = some (bound, site) →
      0 < bound ∧
        site ∈ ((admitted.program.findProtocol declaration.entry).get found).1.shape.attemptSites []) ∧
    ((admitted.program.findProtocol declaration.entry).get found).1.shape.abortsOutside [] false = []
  eventsCovered :
    ∀ e, e ∈ ((admitted.program.findProtocol declaration.entry).get found).1.shape.events [] id →
      EventCovered V prover verifier e
  identity : List Nat

section
variable {V : Vocabulary}

/-- The entry protocol header resolved by a deployment plan. -/
def DeploymentPlan.entry (plan : DeploymentPlan V) : ProtocolHeader V :=
  ((plan.admitted.program.findProtocol plan.declaration.entry).get plan.found).1

/-- The member proof for the entry protocol of a deployment plan. -/
def DeploymentPlan.callee (plan : DeploymentPlan V) :
    Member plan.admitted.program.headers.protocols plan.entry :=
  ((plan.admitted.program.findProtocol plan.declaration.entry).get plan.found).2

/-- The entry header of a deployment plan has the key named by the declaration. -/
theorem DeploymentPlan.entry_key (plan : DeploymentPlan V) :
    plan.entry.key = plan.declaration.entry :=
  Typed.findProtocol_key (Option.some_get plan.found).symm

/-- The public statement types (inputs held by both prover and verifier). -/
def DeploymentPlan.statementTypes (plan : DeploymentPlan V) : List V.Ty :=
  statementOf plan.entry plan.prover plan.verifier

/-- The private witness types (inputs held by prover alone). -/
def DeploymentPlan.witnessTypes (plan : DeploymentPlan V) : List V.Ty :=
  witnessOf plan.entry plan.prover plan.verifier

/-- Validate a declaration's retry scope against an entry protocol header. -/
def checkRetryScope (hdr : ProtocolHeader V) (retry : Option (Nat × Site)) :
    Except DeployRefusal (PLift (∀ bound site, retry = some (bound, site) →
      0 < bound ∧ site ∈ hdr.shape.attemptSites [])) :=
  match retry with
  | none => .ok ⟨fun _ _ h => by cases h⟩
  | some (bound, site) =>
      if hb : 0 < bound then
        if hsite : site ∈ hdr.shape.attemptSites [] then
          .ok ⟨fun _ _ h => by
            injection h with hp
            injection hp with hbEq hsEq
            subst hbEq; subst hsEq
            exact ⟨hb, hsite⟩⟩
        else .error (.retryNotAnAttempt site)
      else .error .retryBoundZero

/-- Validate a scheme declaration against an admitted program and produce a deterministic
`DeploymentPlan`. -/
def planDeployment (enc : VocabEncoder V) (a : Admitted V) (decl : Declaration) :
    Except DeployRefusal (DeploymentPlan V) :=
  match hfind : a.program.findProtocol decl.entry with
  | none => .error (.entryNotFound decl.entry)
  | some foundEntry =>
      if _ : decl.kinds.length ≠ foundEntry.1.roles then
        .error (.roleKindsLength foundEntry.1.roles decl.kinds.length)
      else if hinter : decl.interactive = true then
        .error .interactiveNotSupported
      else
        match hroles : proverAndVerifier foundEntry.1 decl with
        | none => .error .invalidParties
        | some (prover, verifier) =>
            if hdistinct : prover = verifier then
              .error (.nonDistinctParties prover)
            else
              match habortsNil : foundEntry.1.shape.abortsOutside [] false with
              | x :: xs => .error (.abortOutsideAttempt (x :: xs))
              | [] =>
                  match checkRetryScope foundEntry.1 decl.retry with
                  | .error e => .error e
                  | .ok ⟨hretry⟩ =>
                      match checkAllEventsCovered prover verifier (foundEntry.1.shape.events [] id) with
                      | .error e => .error e
                      | .ok ⟨hcov⟩ =>
                          have hfound : (a.program.findProtocol decl.entry).isSome = true := by
                            simp [hfind]
                          have hget : (a.program.findProtocol decl.entry).get hfound = foundEntry := by
                            simp [hfind]
                          have hnonInter : decl.interactive = false := by
                            cases h : decl.interactive
                            · rfl
                            · exact absurd h hinter
                          .ok
                            { admitted := a
                              declaration := decl
                              found := hfound
                              prover := prover
                              verifier := verifier
                              rolesEq := by rw [hget]; exact hroles
                              distinctParties := hdistinct
                              nonInteractive := hnonInter
                              scopedRetry := ⟨by rw [hget]; exact hretry, by rw [hget]; exact habortsNil⟩
                              eventsCovered := by rw [hget]; exact hcov
                              identity := schemeIdentity enc decl (reachableDefinitions a decl) }

end

/-! ## Statement extraction and agreement between prover and verifier -/

section
variable {V : Vocabulary} (M : Model V)

/-- Extract the public statement values (inputs held by both `prover` and `verifier`, in order)
from a role's view of the protocol inputs. -/
def statementValues (prover verifier r : Role) (hr : r = prover ∨ r = verifier) :
    {items : List (LTy V)} → HList (RV M r) items →
      HList M.Val (items.filterMap fun a =>
        if prover ∈ a.holders ∧ verifier ∈ a.holders then some a.ty else none)
  | [], .nil => .nil
  | a :: _, .cons v rest =>
      if h : prover ∈ a.holders ∧ verifier ∈ a.holders then
        have hmem : r ∈ a.holders := by
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2
        cast (by simp [List.filterMap, h])
          (HList.cons (reveal M hmem v) (statementValues prover verifier r hr rest))
      else
        cast (by simp [List.filterMap, h])
          (statementValues prover verifier r hr rest)

/-- Extract the public statement values directly from the full protocol inputs. -/
def statementValuesFull (prover verifier : Role) :
    {items : List (LTy V)} → HList (LVal M) items →
      HList M.Val (items.filterMap fun a =>
        if prover ∈ a.holders ∧ verifier ∈ a.holders then some a.ty else none)
  | [], .nil => .nil
  | a :: _, .cons v rest =>
      if h : prover ∈ a.holders ∧ verifier ∈ a.holders then
        cast (by simp [List.filterMap, h])
          (HList.cons (V := M.Val) v (statementValuesFull prover verifier rest))
      else
        cast (by simp [List.filterMap, h])
          (statementValuesFull prover verifier rest)

/-- A role holding its projection of `ins` extracts the exact same statement values as the
full input list. -/
theorem statementValues_hideAll (prover verifier r : Role) (hr : r = prover ∨ r = verifier) :
    ∀ {items : List (LTy V)} (ins : HList (LVal M) items),
      statementValues M prover verifier r hr (hideAll M r ins) =
        statementValuesFull M prover verifier ins
  | [], .nil => rfl
  | a :: _, .cons v rest => by
      change (if h : prover ∈ a.holders ∧ verifier ∈ a.holders then
        cast (by simp [List.filterMap, h])
          (HList.cons (reveal M (by rcases hr with rfl | rfl; exact h.1; exact h.2) (hide M r a v))
            (statementValues M prover verifier r hr (hideAll M r rest)))
      else
        cast (by simp [List.filterMap, h])
          (statementValues M prover verifier r hr (hideAll M r rest))) =
      (if h : prover ∈ a.holders ∧ verifier ∈ a.holders then
        cast (by simp [List.filterMap, h])
          (HList.cons (V := M.Val) v (statementValuesFull M prover verifier rest))
      else
        cast (by simp [List.filterMap, h])
          (statementValuesFull M prover verifier rest))
      split
      · next h =>
          have hmem : r ∈ a.holders := by rcases hr with rfl | rfl; exact h.1; exact h.2
          rw [reveal_hide M hmem v, statementValues_hideAll prover verifier r hr rest]
      · rw [statementValues_hideAll prover verifier r hr rest]

/-- Prover and verifier extract identical statement values from their projections of `ins`. -/
theorem statementValues_prover_eq_verifier (prover verifier : Role)
    {items : List (LTy V)} (ins : HList (LVal M) items) :
    statementValues M prover verifier prover (.inl rfl) (hideAll M prover ins) =
      statementValues M prover verifier verifier (.inr rfl) (hideAll M verifier ins) := by
  rw [statementValues_hideAll, statementValues_hideAll]

/-- Initial transcript state: initialize with the deployed scheme identity, then absorb the
canonical encoding of the public statement values. -/
def startTranscript (codecs : ValidCodecs M) (tm : TranscriptModel V M)
    (identity : List Nat) {stmtTys : List V.Ty} (stmtVals : HList M.Val stmtTys) : tm.State :=
  tm.absorb (tm.init identity) statementLabel (writeHList M codecs stmtVals)

/-! ## Two-layer `Core.Handler` stack (Fiat-Shamir + Canonical Proof Buffer) -/

/-- Inner prover handler (Fiat-Shamir): absorbs every prover-to-verifier flow into the
transcript before passing it down to the proof serializer, and squeezes every coin shared
between prover and verifier from the transcript. Private prover coins pass through unchanged. -/
def fsProverHandler (codecs : ValidCodecs M) (tm : TranscriptModel V M)
    (verifier : Role) : Handler (RSig M) (RSig M) Stop tm.State where
  clause op st :=
    match op with
    | .give kind getters at_ τ x =>
        if verifier ∈ getters then
          let st' := tm.absorb st (messageLabel at_) ((canonicalFormat M codecs τ).write x)
          .call (.give kind getters at_ τ x) fun _ => .done ((), st')
        else
          .call (.give kind getters at_ τ x) fun _ => .done ((), st)
    | .hear (.coin law) owner at_ τ =>
        if owner = verifier then
          match tm.squeeze st law τ (coinLabel at_) with
          | some (c, st') => .done (c, st')
          | none => .halt (.declared .reject at_, st)
        else
          .call (.hear (.coin law) owner at_ τ) fun v => .done (v, st)
    | .own (.coin law) hearers at_ ins payload τ =>
        if verifier ∈ hearers then
          match tm.squeeze st law τ (coinLabel at_) with
          | some (c, st') => .done (c, st')
          | none => .halt (.declared .reject at_, st)
        else
          .call (.own (.coin law) hearers at_ ins payload τ) fun v => .done (v, st)
    | other => .call other fun reply => .done (reply, st)
  again _ entry _ := .ok entry

/-- Outer prover handler (Canonical Proof Writer): intercepts every prover-to-verifier flow
and appends its canonical wire bytes to the proof buffer. -/
def proofWriterHandler (codecs : ValidCodecs M) (verifier : Role) :
    Handler (RSig M) (RSig M) Stop (List Nat) where
  clause op buf :=
    match op with
    | .give kind getters at_ τ x =>
        if verifier ∈ getters then
          .done ((), buf ++ (canonicalFormat M codecs τ).write x)
        else
          .call (.give kind getters at_ τ x) fun _ => .done ((), buf)
    | other => .call other fun reply => .done (reply, buf)
  again _ entry _ := .ok entry

/-- Composed two-layer prover handler: Fiat-Shamir inner over Canonical Proof Writer outer. -/
def proverHandler (codecs : ValidCodecs M) (tm : TranscriptModel V M) (verifier : Role) :
    Handler (RSig M) (RSig M) Stop (tm.State × List Nat) :=
  (fsProverHandler M codecs tm verifier).over (proofWriterHandler M codecs verifier)

/-- Inner verifier handler (Fiat-Shamir): forwards prover-to-verifier receives to the proof
reader below, absorbs the decoded canonical bytes into the transcript, and squeezes every
coin shared between prover and verifier from the transcript. -/
def fsVerifierHandler (codecs : ValidCodecs M) (tm : TranscriptModel V M)
    (prover : Role) : Handler (RSig M) (RSig M) Stop tm.State where
  clause op st :=
    match op with
    | .get kind giver at_ τ =>
        if giver = prover then
          .call (.get kind giver at_ τ) fun x =>
            let st' := tm.absorb st (messageLabel at_) ((canonicalFormat M codecs τ).write x)
            .done (x, st')
        else
          .call (.get kind giver at_ τ) fun x => .done (x, st)
    | .own (.coin law) hearers at_ ins payload τ =>
        if prover ∈ hearers then
          match tm.squeeze st law τ (coinLabel at_) with
          | some (c, st') => .done (c, st')
          | none => .halt (.declared .reject at_, st)
        else
          .call (.own (.coin law) hearers at_ ins payload τ) fun v => .done (v, st)
    | .hear (.coin law) owner at_ τ =>
        if owner = prover then
          match tm.squeeze st law τ (coinLabel at_) with
          | some (c, st') => .done (c, st')
          | none => .halt (.declared .reject at_, st)
        else
          .call (.hear (.coin law) owner at_ τ) fun v => .done (v, st)
    | other => .call other fun reply => .done (reply, st)
  again _ entry _ := .ok entry

/-- Outer verifier handler (Canonical Proof Reader): decodes each prover message from the
proof byte buffer using `canonicalFormat`, rejecting immediately on truncated or non-canonical
bytes. -/
def proofReaderHandler (codecs : ValidCodecs M) (prover : Role) :
    Handler (RSig M) (RSig M) Stop (List Nat) where
  clause op buf :=
    match op with
    | .get kind giver at_ τ =>
        if giver = prover then
          match (canonicalFormat M codecs τ).read buf with
          | some (x, rest) => .done (x, rest)
          | none => .halt (.declared .reject at_, buf)
        else
          .call (.get kind giver at_ τ) fun x => .done (x, buf)
    | other => .call other fun reply => .done (reply, buf)
  again _ entry _ := .ok entry

/-- Composed two-layer verifier handler: Fiat-Shamir inner over Canonical Proof Reader outer. -/
def verifierHandler (codecs : ValidCodecs M) (tm : TranscriptModel V M) (prover : Role) :
    Handler (RSig M) (RSig M) Stop (tm.State × List Nat) :=
  (fsVerifierHandler M codecs tm prover).over (proofReaderHandler M codecs prover)

/-- The deployed prover process for a validated `DeploymentPlan`, running the two-layer
handler stack over unmodified `roleMeaning` and returning `(outputs, proofBytes)`. -/
def DeploymentPlan.proverProcess (plan : DeploymentPlan V) (codecs : ValidCodecs M)
    (tm : TranscriptModel V M) (ins : HList (RV M plan.prover) plan.entry.ins) :
    Process (RSig M) Stop (HList (RV M plan.prover) plan.entry.outs × List Nat) :=
  let st₀ := startTranscript M codecs tm plan.identity
    (statementValues M plan.prover plan.verifier plan.prover (.inl rfl) ins)
  let raw := roleMeaning M plan.admitted.program plan.callee plan.prover [] ins
  (((proverHandler M codecs tm plan.verifier).run (retryOf M plan.declaration.retry)
      raw (st₀, [])).mapHalt Prod.fst).map fun out => (out.1, out.2.2)

/-- The deployed verifier process for a validated `DeploymentPlan`, running the two-layer
handler stack over unmodified `roleMeaning` and rejecting any trailing unconsumed proof
bytes before returning the verifier outputs. -/
def DeploymentPlan.verifierProcess (plan : DeploymentPlan V) (codecs : ValidCodecs M)
    (tm : TranscriptModel V M) (ins : HList (RV M plan.verifier) plan.entry.ins)
    (proof : List Nat) :
    Process (RSig M) Stop (HList (RV M plan.verifier) plan.entry.outs) :=
  let st₀ := startTranscript M codecs tm plan.identity
    (statementValues M plan.prover plan.verifier plan.verifier (.inr rfl) ins)
  let raw := roleMeaning M plan.admitted.program plan.callee plan.verifier [] ins
  (((verifierHandler M codecs tm plan.prover).run (retryOf M plan.declaration.retry)
      raw (st₀, proof)).mapHalt Prod.fst).bind fun out =>
    if out.2.2.isEmpty then .done out.1
    else .halt (.declared .reject ⟨[], plan.declaration.entry⟩)

end

/-! ## Basic plan properties and handler coverage -/

/-- `planDeployment` preserves the admitted program, the declaration, and the entry key. -/
theorem planDeployment_keeps {V : Vocabulary} (enc : VocabEncoder V)
    (a : Admitted V) (decl : Declaration) (plan : DeploymentPlan V)
    (h : planDeployment enc a decl = .ok plan) :
    plan.admitted = a ∧ plan.declaration = decl ∧ plan.entry.key = decl.entry := by
  unfold planDeployment at h
  repeat (split at h <;> try cases h)
  exact ⟨rfl, rfl, DeploymentPlan.entry_key _⟩

/-- Every online flow and every heard coin in a validated `DeploymentPlan` is handled by the
two-layer Fiat-Shamir and canonical proof-buffer handlers: no online flow or heard coin
between prover and verifier escapes to the network below. -/
theorem deploy_coverage {V : Vocabulary} (plan : DeploymentPlan V) (M : Model V)
    (codecs : ValidCodecs M) (tm : TranscriptModel V M) :
    ∀ e, e ∈ plan.entry.shape.events [] id →
      match e.cls with
      | .flow kind giver getters =>
          (giver = plan.prover ∧ plan.verifier ∈ getters →
            ∀ (at_ : Occurrence) (x : M.Val e.τ) (st : tm.State) (buf : List Nat),
              (proverHandler M codecs tm plan.verifier).clause (.give kind getters at_ e.τ x) (st, buf) =
                .done ((), (tm.absorb st (messageLabel at_) ((canonicalFormat M codecs e.τ).write x),
                  buf ++ (canonicalFormat M codecs e.τ).write x))) ∧
          (giver = plan.prover ∧ plan.verifier ∈ getters →
            ∀ (at_ : Occurrence) (st : tm.State) (buf : List Nat),
              (verifierHandler M codecs tm plan.prover).clause (.get kind giver at_ e.τ) (st, buf) =
                match (canonicalFormat M codecs e.τ).read buf with
                | some (x, rest) =>
                    .done (x, (tm.absorb st (messageLabel at_) ((canonicalFormat M codecs e.τ).write x), rest))
                | none => .halt (.declared .reject at_, (st, buf))) ∧
          ¬ (giver = plan.verifier ∧ plan.prover ∈ getters)
      | .given (.coin law) owner hearers =>
          (owner = plan.verifier ∧ plan.prover ∈ hearers →
            ∀ (at_ : Occurrence) (st : tm.State) (buf : List Nat) (c : M.Val e.τ) (st' : tm.State),
              tm.squeeze st law e.τ (coinLabel at_) = some (c, st') →
              (proverHandler M codecs tm plan.verifier).clause (.hear (.coin law) owner at_ e.τ) (st, buf) =
                .done (c, (st', buf))) ∧
          (owner = plan.verifier ∧ plan.prover ∈ hearers →
            ∀ (at_ : Occurrence) (ins : List V.Ty) (payload : HList M.Val ins)
              (st : tm.State) (buf : List Nat) (c : M.Val e.τ) (st' : tm.State),
              tm.squeeze st law e.τ (coinLabel at_) = some (c, st') →
              (verifierHandler M codecs tm plan.prover).clause (.own (.coin law) hearers at_ ins payload e.τ) (st, buf) =
                .done (c, (st', buf)))
      | .given (.request _) owner hearers =>
          owner ≠ plan.prover ∧ plan.prover ∉ hearers ∧ owner ≠ plan.verifier ∧ plan.verifier ∉ hearers := by
  intro e he
  have hcov := plan.eventsCovered e he
  cases hcls : e.cls with
  | flow kind giver getters =>
      simp only [EventCovered, hcls] at hcov
      refine ⟨?_, ?_, ?_⟩
      · intro ⟨_, hmem⟩ at_ x st buf
        simp only [proverHandler, Handler.over, fsProverHandler, proofWriterHandler, hmem,
          ↓reduceIte, Handler.answer, Process.mapHalt, Process.bind]
      · intro ⟨hg, _⟩ at_ st buf
        subst hg
        simp only [verifierHandler, Handler.over, fsVerifierHandler, proofReaderHandler,
          ↓reduceIte, Handler.answer]
        cases hread : (canonicalFormat M codecs e.τ).read buf with
        | none => rfl
        | some p =>
            obtain ⟨x, rest⟩ := p
            rfl
      · intro ⟨hg, hm⟩
        rcases hcov with ⟨hgp, _, hnp⟩ | ⟨_, _, hnv, _⟩
        · exact plan.distinctParties (hgp.symm.trans hg)
        · exact hnv hg
  | given gkind owner hearers =>
      cases gkind with
      | coin law =>
          refine ⟨?_, ?_⟩
          · intro ⟨ho, _⟩ at_ st buf c st' hsq
            subst ho
            simp only [proverHandler, Handler.over, fsProverHandler, proofWriterHandler,
              ↓reduceIte, hsq, Handler.answer, Process.mapHalt, Process.bind]
          · intro ⟨_, hm⟩ at_ ins payload st buf c st' hsq
            simp only [verifierHandler, Handler.over, fsVerifierHandler, proofReaderHandler,
              hm, ↓reduceIte, hsq, Handler.answer, Process.mapHalt, Process.bind]
      | request service =>
          simp only [EventCovered, hcls] at hcov
          exact hcov

/-! ## Completeness theorem (`deploy_complete`) -/

section Completeness
variable {V : Vocabulary} (M : Model V)

/-- Protocol-level compatibility with two-party non-interactive Fiat-Shamir deployment:
every flow is prover-to-verifier carrying a valid value (or silent to both online parties),
every heard coin is a nullary coin law shared between verifier and prover (or silent to both),
and neither online party invokes an external service. -/
def ProtoCompatible (prover verifier : Role) {A : Type} : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.flow _ giver getters _ τ x) k =>
      ((giver = prover ∧ verifier ∈ getters ∧ prover ∉ getters ∧ M.Valid τ x) ∨
        (giver ≠ prover ∧ prover ∉ getters ∧ giver ≠ verifier ∧ verifier ∉ getters)) ∧
      ProtoCompatible prover verifier (k ())
  | .call (.given (.coin law) owner hearers _ ins payload τ) k =>
      (hearers = [] ∨
        ((((owner = verifier ∧ prover ∈ hearers) ∨ (owner = prover ∧ verifier ∈ hearers)) ∨
          (owner ≠ prover ∧ prover ∉ hearers ∧ owner ≠ verifier ∧ verifier ∉ hearers)) ∧
          ∃ s, V.law law = some s ∧ s.ins = [] ∧ s.out = τ ∧ ins = [])) ∧
      (∀ v, Allows M (.coin law) ins payload τ v → ProtoCompatible prover verifier (k v))
  | .call (.given (.request _) owner hearers _ _ _ τ) k =>
      (owner ≠ prover ∧ prover ∉ hearers ∧ owner ≠ verifier ∧ verifier ∉ hearers) ∧
      (∀ v, M.Valid τ v → ProtoCompatible prover verifier (k v))

/-- A protocol process never halts along any branch whose replies are allowed by the world. -/
def ProtoNoHalt {A : Type} : Protocol M A → Prop
  | .done _ => True
  | .halt _ => False
  | .call (.flow ..) k => ProtoNoHalt (k ())
  | .call (.given kind _ _ _ ins payload τ) k =>
      ∀ v, Allows M kind ins payload τ v → ProtoNoHalt (k v)

/-- Every answer that `source` gives at a private (non-heard) event is allowed by the world,
for every allowed value of every heard coin (such as challenges squeezed under Fiat-Shamir). -/
def LawfulPrivate (source : Source M) {A : Type} : Protocol M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.flow ..) k => LawfulPrivate source (k ())
  | .call (.given (.coin law) _ (_ :: _) _ ins payload τ) k =>
      ∀ v, Allows M (.coin law) ins payload τ v → LawfulPrivate source (k v)
  | .call (.given kind _ _ at_ ins payload τ) k =>
      ∀ v, source at_ τ = some v → Allows M kind ins payload τ v ∧ LawfulPrivate source (k v)

private theorem alone_map {source : Source M} {r : Role} {H A B : Type} {f : A → B}
    {p : Process (RSig M) H A} {record : List (Happened M)} {a : A}
    (h : Alone M source r p record (.returned a)) :
    Alone M source r (p.map f) record (.returned (f a)) := by
  generalize he : Ending.returned a = end_ at h
  induction h with
  | done => cases he; exact .done
  | halt => cases he
  | waits => cases he
  | give _ ih => exact .give (ih he)
  | own hs _ ih => exact .own hs (ih he)
  | hear hs _ ih => exact .hear hs (ih he)
  | begin _ ih => exact .begin (ih he)
  | settle _ ih => exact .settle (ih he)

private theorem alone_mapHalt {source : Source M} {r : Role} {H H' A : Type} {f : H → H'}
    {p : Process (RSig M) H A} {record : List (Happened M)} {a : A}
    (h : Alone M source r p record (.returned a)) :
    Alone M source r (p.mapHalt f) record (.returned a) := by
  generalize he : Ending.returned a = end_ at h
  induction h with
  | done => cases he; exact .done
  | halt => cases he
  | waits => cases he
  | give _ ih => exact .give (ih he)
  | own hs _ ih => exact .own hs (ih he)
  | hear hs _ ih => exact .hear hs (ih he)
  | begin _ ih => exact .begin (ih he)
  | settle _ ih => exact .settle (ih he)

private theorem alone_bind {source : Source M} {r : Role} {H A B : Type}
    {p : Process (RSig M) H A} {k : A → Process (RSig M) H B}
    {rec1 rec2 : List (Happened M)} {a : A} {ending : Ending B H}
    (h1 : Alone M source r p rec1 (.returned a))
    (h2 : Alone M source r (k a) rec2 ending) :
    Alone M source r (p.bind k) (rec1 ++ rec2) ending := by
  generalize he : Ending.returned a = end_ at h1
  induction h1 with
  | done => cases he; exact h2
  | halt => cases he
  | waits => cases he
  | give _ ih => exact .give (ih he)
  | own hs _ ih => exact .own hs (ih he)
  | hear hs _ ih => exact .hear hs (ih he)
  | begin _ ih => exact .begin (ih he)
  | settle _ ih => exact .settle (ih he)

/-- Peeling leading attempt marks (`.begins`/`.settles`) on the verifier's `Proj` when the
protocol is `.done`. -/
private theorem peel_verifier_done {codecs : ValidCodecs M} {tm : TranscriptModel V M}
    {prover verifier : Role} {source : Source M} {A B : Type} {postV : A → B → Prop}
    {out : A} {vProg : Program M B} (hv : Proj M verifier postV (.done out) vProg)
    (st : tm.State) (buf : List Nat) :
    ∃ outV recV,
      Alone M source verifier
        ((verifierHandler M codecs tm prover).run (retryOf M none) vProg (st, buf))
        recV (.returned (outV, (st, buf))) ∧
      postV out outV := by
  generalize hp : (Process.done out : Protocol M A) = proto at hv
  induction hv with
  | done hpost =>
      cases hp
      exact ⟨_, [], .done, hpost⟩
  | stopsHere => cases hp
  | stopsElsewhere => cases hp
  | gave => cases hp
  | got => cases hp
  | passed => cases hp
  | owned => cases hp
  | heard => cases hp
  | unheard => cases hp
  | @begins at_beg _ _ _ ih =>
      obtain ⟨outV, recV, halone, hpost⟩ := ih hp
      refine ⟨outV, .began verifier at_beg :: recV, ?_, hpost⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.begin halone
  | @settles at_set _ _ _ ih =>
      obtain ⟨outV, recV, halone, hpost⟩ := ih hp
      refine ⟨outV, .settled verifier at_set :: recV, ?_, hpost⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.settle halone

/-- Lift an `Alone` run across leading attempt marks on the verifier's `Proj` at a `.flow`
where the verifier receives from the prover. -/
private theorem peel_verifier_got {codecs : ValidCodecs M} {tm : TranscriptModel V M}
    {prover verifier : Role} {source : Source M} {A B : Type} {postV : A → B → Prop}
    {kind : FlowKind} {getters : List Role} {at_ : Occurrence} {τ : V.Ty} {x : M.Val τ}
    {k : Unit → Protocol M A} {vProg : Program M B}
    (hneq : prover ≠ verifier) (hmem : verifier ∈ getters)
    (hv : Proj M verifier postV (.call (.flow kind prover getters at_ τ x) k) vProg) :
    ∃ kV : M.Val τ → Program M B,
      Proj M verifier postV (k ()) (kV x) ∧
      ∀ (s : tm.State × List Nat) (recV : List (Happened M)) (endV : Ending (B × (tm.State × List Nat)) (Stop × (tm.State × List Nat))),
        Alone M source verifier
          ((verifierHandler M codecs tm prover).run (retryOf M none) (.call (.get kind prover at_ τ) kV) s)
          recV endV →
        ∃ recV',
          Alone M source verifier
            ((verifierHandler M codecs tm prover).run (retryOf M none) vProg s)
            recV' endV := by
  generalize hp : (Process.call (.flow kind prover getters at_ τ x) k : Protocol M A) = proto at hv
  induction hv with
  | done => cases hp
  | stopsHere => cases hp
  | stopsElsewhere => cases hp
  | gave hr _ =>
      cases hp
      exact absurd rfl hneq
  | got _ _ hv' =>
      cases hp
      exact ⟨_, hv', fun _ recV _ h => ⟨recV, h⟩⟩
  | passed _ hnm _ =>
      cases hp
      exact absurd hmem hnm
  | owned => cases hp
  | heard => cases hp
  | unheard => cases hp
  | @begins at_beg _ _ _ ih =>
      obtain ⟨kV, hv', hlift⟩ := ih hp
      refine ⟨kV, hv', fun s recV endV halone => ?_⟩
      obtain ⟨recV', halone'⟩ := hlift s recV endV halone
      refine ⟨.began verifier at_beg :: recV', ?_⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.begin halone'
  | @settles at_set _ _ _ ih =>
      obtain ⟨kV, hv', hlift⟩ := ih hp
      refine ⟨kV, hv', fun s recV endV halone => ?_⟩
      obtain ⟨recV', halone'⟩ := hlift s recV endV halone
      refine ⟨.settled verifier at_set :: recV', ?_⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.settle halone'

/-- Lift across leading attempt marks on the verifier's `Proj` at a silent `.flow`. -/
private theorem peel_verifier_passed {codecs : ValidCodecs M} {tm : TranscriptModel V M}
    {prover verifier : Role} {source : Source M} {A B : Type} {postV : A → B → Prop}
    {kind : FlowKind} {giver : Role} {getters : List Role} {at_ : Occurrence} {τ : V.Ty} {x : M.Val τ}
    {k : Unit → Protocol M A} {vProg : Program M B}
    (hng : giver ≠ verifier) (hnm : verifier ∉ getters)
    (hv : Proj M verifier postV (.call (.flow kind giver getters at_ τ x) k) vProg) :
    ∃ vProg' : Program M B,
      Proj M verifier postV (k ()) vProg' ∧
      ∀ (s : tm.State × List Nat) (recV : List (Happened M)) (endV : Ending (B × (tm.State × List Nat)) (Stop × (tm.State × List Nat))),
        Alone M source verifier
          ((verifierHandler M codecs tm prover).run (retryOf M none) vProg' s)
          recV endV →
        ∃ recV',
          Alone M source verifier
            ((verifierHandler M codecs tm prover).run (retryOf M none) vProg s)
            recV' endV := by
  generalize hp : (Process.call (.flow kind giver getters at_ τ x) k : Protocol M A) = proto at hv
  induction hv with
  | done => cases hp
  | stopsHere => cases hp
  | stopsElsewhere => cases hp
  | gave => cases hp; exact absurd rfl hng
  | got _ hm _ => cases hp; exact absurd hm hnm
  | passed _ _ hv' => cases hp; exact ⟨_, hv', fun _ recV _ h => ⟨recV, h⟩⟩
  | owned => cases hp
  | heard => cases hp
  | unheard => cases hp
  | @begins at_beg _ _ _ ih =>
      obtain ⟨vProg', hv', hlift⟩ := ih hp
      refine ⟨vProg', hv', fun s recV endV halone => ?_⟩
      obtain ⟨recV', halone'⟩ := hlift s recV endV halone
      refine ⟨.began verifier at_beg :: recV', ?_⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.begin halone'
  | @settles at_set _ _ _ ih =>
      obtain ⟨vProg', hv', hlift⟩ := ih hp
      refine ⟨vProg', hv', fun s recV endV halone => ?_⟩
      obtain ⟨recV', halone'⟩ := hlift s recV endV halone
      refine ⟨.settled verifier at_set :: recV', ?_⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.settle halone'

/-- Lift across leading attempt marks on the verifier's `Proj` when the verifier owns a `.given`. -/
private theorem peel_verifier_owned {codecs : ValidCodecs M} {tm : TranscriptModel V M}
    {prover verifier : Role} {source : Source M} {A B : Type} {postV : A → B → Prop}
    {kind : GivenKind V} {hearers : List Role} {at_ : Occurrence}
    {ins : List V.Ty} {payload : HList M.Val ins} {τ : V.Ty}
    {k : M.Val τ → Protocol M A} {vProg : Program M B}
    (hv : Proj M verifier postV (.call (.given kind verifier hearers at_ ins payload τ) k) vProg) :
    ∃ kV : M.Val τ → Program M B,
      (∀ v, Proj M verifier postV (k v) (kV v)) ∧
      ∀ (s : tm.State × List Nat) (recV : List (Happened M)) (endV : Ending (B × (tm.State × List Nat)) (Stop × (tm.State × List Nat))),
        Alone M source verifier
          ((verifierHandler M codecs tm prover).run (retryOf M none)
            (.call (.own kind hearers at_ ins payload τ) kV) s)
          recV endV →
        ∃ recV',
          Alone M source verifier
            ((verifierHandler M codecs tm prover).run (retryOf M none) vProg s)
            recV' endV := by
  generalize hp : (Process.call (.given kind verifier hearers at_ ins payload τ) k : Protocol M A) = proto at hv
  induction hv with
  | done => cases hp
  | stopsHere => cases hp
  | stopsElsewhere => cases hp
  | gave => cases hp
  | got => cases hp
  | passed => cases hp
  | owned hv' => cases hp; exact ⟨_, hv', fun _ recV _ h => ⟨recV, h⟩⟩
  | heard hne _ _ => cases hp; exact absurd rfl hne
  | unheard hne _ _ => cases hp; exact absurd rfl hne
  | @begins at_beg _ _ _ ih =>
      obtain ⟨kV, hv', hlift⟩ := ih hp
      refine ⟨kV, hv', fun s recV endV halone => ?_⟩
      obtain ⟨recV', halone'⟩ := hlift s recV endV halone
      refine ⟨.began verifier at_beg :: recV', ?_⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.begin halone'
  | @settles at_set _ _ _ ih =>
      obtain ⟨kV, hv', hlift⟩ := ih hp
      refine ⟨kV, hv', fun s recV endV halone => ?_⟩
      obtain ⟨recV', halone'⟩ := hlift s recV endV halone
      refine ⟨.settled verifier at_set :: recV', ?_⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.settle halone'

/-- Lift across leading attempt marks on the verifier's `Proj` when the verifier hears a `.given`. -/
private theorem peel_verifier_heard {codecs : ValidCodecs M} {tm : TranscriptModel V M}
    {prover verifier : Role} {source : Source M} {A B : Type} {postV : A → B → Prop}
    {kind : GivenKind V} {owner : Role} {hearers : List Role} {at_ : Occurrence}
    {ins : List V.Ty} {payload : HList M.Val ins} {τ : V.Ty}
    {k : M.Val τ → Protocol M A} {vProg : Program M B}
    (hne : owner ≠ verifier) (hm : verifier ∈ hearers)
    (hv : Proj M verifier postV (.call (.given kind owner hearers at_ ins payload τ) k) vProg) :
    ∃ kV : M.Val τ → Program M B,
      (∀ v, Proj M verifier postV (k v) (kV v)) ∧
      ∀ (s : tm.State × List Nat) (recV : List (Happened M)) (endV : Ending (B × (tm.State × List Nat)) (Stop × (tm.State × List Nat))),
        Alone M source verifier
          ((verifierHandler M codecs tm prover).run (retryOf M none)
            (.call (.hear kind owner at_ τ) kV) s)
          recV endV →
        ∃ recV',
          Alone M source verifier
            ((verifierHandler M codecs tm prover).run (retryOf M none) vProg s)
            recV' endV := by
  generalize hp : (Process.call (.given kind owner hearers at_ ins payload τ) k : Protocol M A) = proto at hv
  induction hv with
  | done => cases hp
  | stopsHere => cases hp
  | stopsElsewhere => cases hp
  | gave => cases hp
  | got => cases hp
  | passed => cases hp
  | owned => cases hp; exact absurd rfl hne
  | heard _ _ hv' => cases hp; exact ⟨_, hv', fun _ recV _ h => ⟨recV, h⟩⟩
  | unheard _ hnm _ => cases hp; exact absurd hm hnm
  | @begins at_beg _ _ _ ih =>
      obtain ⟨kV, hv', hlift⟩ := ih hp
      refine ⟨kV, hv', fun s recV endV halone => ?_⟩
      obtain ⟨recV', halone'⟩ := hlift s recV endV halone
      refine ⟨.began verifier at_beg :: recV', ?_⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.begin halone'
  | @settles at_set _ _ _ ih =>
      obtain ⟨kV, hv', hlift⟩ := ih hp
      refine ⟨kV, hv', fun s recV endV halone => ?_⟩
      obtain ⟨recV', halone'⟩ := hlift s recV endV halone
      refine ⟨.settled verifier at_set :: recV', ?_⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.settle halone'

/-- Lift across leading attempt marks on the verifier's `Proj` when a `.given` is unheard by the
verifier. -/
private theorem peel_verifier_unheard {codecs : ValidCodecs M} {tm : TranscriptModel V M}
    {prover verifier : Role} {source : Source M} {A B : Type} {postV : A → B → Prop}
    {kind : GivenKind V} {owner : Role} {hearers : List Role} {at_ : Occurrence}
    {ins : List V.Ty} {payload : HList M.Val ins} {τ : V.Ty}
    {k : M.Val τ → Protocol M A} {vProg : Program M B}
    (hne : owner ≠ verifier) (hnm : verifier ∉ hearers)
    (hv : Proj M verifier postV (.call (.given kind owner hearers at_ ins payload τ) k) vProg) :
    ∃ vProg' : Program M B,
      (∀ v, Proj M verifier postV (k v) vProg') ∧
      ∀ (s : tm.State × List Nat) (recV : List (Happened M)) (endV : Ending (B × (tm.State × List Nat)) (Stop × (tm.State × List Nat))),
        Alone M source verifier
          ((verifierHandler M codecs tm prover).run (retryOf M none) vProg' s)
          recV endV →
        ∃ recV',
          Alone M source verifier
            ((verifierHandler M codecs tm prover).run (retryOf M none) vProg s)
            recV' endV := by
  generalize hp : (Process.call (.given kind owner hearers at_ ins payload τ) k : Protocol M A) = proto at hv
  induction hv with
  | done => cases hp
  | stopsHere => cases hp
  | stopsElsewhere => cases hp
  | gave => cases hp
  | got => cases hp
  | passed => cases hp
  | owned => cases hp; exact absurd rfl hne
  | heard _ hm _ => cases hp; exact absurd hm hnm
  | unheard _ _ hv' => cases hp; exact ⟨_, hv', fun _ recV _ h => ⟨recV, h⟩⟩
  | @begins at_beg _ _ _ ih =>
      obtain ⟨vProg', hv', hlift⟩ := ih hp
      refine ⟨vProg', hv', fun s recV endV halone => ?_⟩
      obtain ⟨recV', halone'⟩ := hlift s recV endV halone
      refine ⟨.began verifier at_beg :: recV', ?_⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.begin halone'
  | @settles at_set _ _ _ ih =>
      obtain ⟨vProg', hv', hlift⟩ := ih hp
      refine ⟨vProg', hv', fun s recV endV halone => ?_⟩
      obtain ⟨recV', halone'⟩ := hlift s recV endV halone
      refine ⟨.settled verifier at_set :: recV', ?_⟩
      simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
        proofReaderHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.settle halone'

/-- Joint simulation of the deployed prover and verifier handlers driven by `Proj` on a
compatible non-halting protocol process. -/
private theorem deploy_simulate {codecs : ValidCodecs M} {tm : TranscriptModel V M}
    (htm : tm.Lawful) {prover verifier : Role} (hdistinct : prover ≠ verifier)
    {A BP BV : Type} {postP : A → BP → Prop} {postV : A → BV → Prop}
    {proto : Protocol M A} {pProg : Program M BP}
    (hp : Proj M prover postP proto pProg) :
    ∀ {vProg : Program M BV}, Proj M verifier postV proto vProg →
      ∀ (source : Source M),
      ProtoCompatible M prover verifier proto →
      ProtoNoHalt M proto →
      LawfulPrivate M source proto →
      Fed M source proto →
      ∀ (st : tm.State) (prefixBuf tailBuf : List Nat),
        ∃ out outP outV proofDelta stFinal recordP recordV,
          (∀ b, b ∈ proofDelta → b < 256) ∧
          Alone M source prover
            ((proverHandler M codecs tm verifier).run (retryOf M none) pProg (st, prefixBuf))
            recordP (.returned (outP, (stFinal, prefixBuf ++ proofDelta))) ∧
          Alone M source verifier
            ((verifierHandler M codecs tm prover).run (retryOf M none) vProg (st, proofDelta ++ tailBuf))
            recordV (.returned (outV, (stFinal, tailBuf))) ∧
          postP out outP ∧ postV out outV := by
  induction hp with
  | done hpostP =>
      intro vProg hv source _ _ _ _ st prefixBuf tailBuf
      obtain ⟨outV, recV, haloneV, hpostV⟩ :=
        peel_verifier_done M (codecs := codecs) (tm := tm) (prover := prover) (source := source) hv st tailBuf
      refine ⟨_, _, outV, [], st, [], recV, (fun _ h => nomatch h), ?_, ?_, hpostP, hpostV⟩
      · simpa only [Handler.run, List.append_nil] using Alone.done
      · simpa only [List.nil_append] using haloneV
  | stopsHere =>
      intro _ _ _ _ hnohalt _ _ _ _ _
      exact False.elim hnohalt
  | stopsElsewhere =>
      intro _ _ _ _ hnohalt _ _ _ _ _
      exact False.elim hnohalt
  | @gave kind getters at_ τ x k kP hr _ ih =>
      intro vProg hv source hcomp hnohalt hlaw hfed st prefixBuf tailBuf
      obtain ⟨hflow, hcomp'⟩ := hcomp
      rcases hflow with ⟨_, hmemV, _, hxValid⟩ | ⟨hneP, _, _, _⟩
      · obtain ⟨kV, hv', hliftV⟩ :=
          peel_verifier_got M (codecs := codecs) (tm := tm) (prover := prover) (source := source)
            hdistinct hmemV hv
        let msgBytes := (canonicalFormat M codecs τ).write x
        let st' := tm.absorb st (messageLabel at_) msgBytes
        obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
          ih hv' source hcomp' hnohalt hlaw hfed st' (prefixBuf ++ msgBytes) tailBuf
        have haloneVStep :
            Alone M source verifier
              ((verifierHandler M codecs tm prover).run (retryOf M none)
                (.call (.get kind prover at_ τ) kV) (st, (msgBytes ++ delta) ++ tailBuf))
              recV (.returned (outV, (stFinal, tailBuf))) := by
          have hread : (canonicalFormat M codecs τ).read (msgBytes ++ (delta ++ tailBuf)) =
              some (x, delta ++ tailBuf) :=
            (canonicalFormat_lawful M codecs τ).reads x (delta ++ tailBuf) hxValid
          simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
            proofReaderHandler, ↓reduceIte, Handler.answer, Process.mapHalt, Process.bind,
            List.append_assoc, hread] using haloneV
        obtain ⟨recV', haloneV'⟩ := hliftV (st, (msgBytes ++ delta) ++ tailBuf) recV _ haloneVStep
        refine ⟨out, outP, outV, msgBytes ++ delta, stFinal, recP, recV', ?_, ?_, haloneV', hpostP, hpostV⟩
        · intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact (canonicalFormat_lawful M codecs τ).bytes x hxValid b hb
          · exact hbytes b hb
        · simpa only [Handler.run, retryOf, proverHandler, Handler.over, fsProverHandler,
            proofWriterHandler, hmemV, ↓reduceIte, Handler.answer, Process.mapHalt, Process.bind,
            List.append_assoc] using haloneP
      · exact absurd rfl hneP
  | got hneP hmP _ _ =>
      intro _ _ _ hcomp _ _ _ _ _ _
      obtain ⟨hflow, _⟩ := hcomp
      rcases hflow with ⟨_, _, hnp, _⟩ | ⟨_, hnp, _, _⟩
      · exact absurd hmP hnp
      · exact absurd hmP hnp
  | @passed kind giver getters at_ τ x k q hneP hnmP _ ih =>
      intro vProg hv source hcomp hnohalt hlaw hfed st prefixBuf tailBuf
      obtain ⟨hflow, hcomp'⟩ := hcomp
      rcases hflow with ⟨hg, _, _, _⟩ | ⟨_, _, hneV, hnmV⟩
      · exact absurd hg hneP
      · obtain ⟨vProg', hv', hliftV⟩ :=
          peel_verifier_passed M (codecs := codecs) (tm := tm) (prover := prover) (source := source)
            hneV hnmV hv
        obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
          ih hv' source hcomp' hnohalt hlaw hfed st prefixBuf tailBuf
        obtain ⟨recV', haloneV'⟩ := hliftV (st, delta ++ tailBuf) recV _ haloneV
        exact ⟨out, outP, outV, delta, stFinal, recP, recV', hbytes, haloneP, haloneV', hpostP, hpostV⟩
  | @owned kind hearers at_ ins payload τ k kP _ ih =>
      intro vProg hv source hcomp hnohalt hlaw hfed st prefixBuf tailBuf
      cases kind with
      | coin law =>
          obtain ⟨hcoin, hcomp'⟩ := hcomp
          rcases hcoin with hpriv | ⟨hparties, s, hsLaw, hsIns, hsOut, hInsEq⟩
          · subst hpriv
            obtain ⟨v, hsrc, hfed'⟩ := hfed
            obtain ⟨hallows, hlaw'⟩ := hlaw v hsrc
            obtain ⟨vProg', hv', hliftV⟩ :=
              peel_verifier_unheard M (codecs := codecs) (tm := tm) (prover := prover) (source := source)
                hdistinct (by simp) hv
            obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
              ih v (hv' v) source (hcomp' v hallows) (hnohalt v hallows) hlaw' hfed' st prefixBuf tailBuf
            obtain ⟨recV', haloneV'⟩ := hliftV (st, delta ++ tailBuf) recV _ haloneV
            refine ⟨out, outP, outV, delta, stFinal, .owned prover (.coin law) at_ τ v :: recP, recV',
              hbytes, ?_, haloneV', hpostP, hpostV⟩
            simpa only [Handler.run, retryOf, proverHandler, Handler.over, fsProverHandler,
              proofWriterHandler, List.not_mem_nil, ↓reduceIte, Handler.answer, Process.mapHalt,
              Process.bind] using Alone.own hsrc haloneP
          · rcases hparties with (⟨hpeqv, _⟩ | ⟨_, hmV⟩) | ⟨hneP, _, _, _⟩
            · exact absurd hpeqv hdistinct
            · subst hInsEq
              cases payload
              obtain ⟨kV, hv', hliftV⟩ :=
                peel_verifier_heard M (codecs := codecs) (tm := tm) (prover := prover) (source := source)
                  hdistinct hmV hv
              obtain ⟨c, st', hsq, hallows⟩ := htm st law s hsLaw hsIns τ hsOut (coinLabel at_)
              have hfed' : Fed M source (k c) := by
                cases hearers with
                | nil => cases hmV
                | cons _ _ => exact hfed c hallows
              have hlaw' : LawfulPrivate M source (k c) := by
                cases hearers with
                | nil => cases hmV
                | cons _ _ => exact hlaw c hallows
              obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
                ih c (hv' c) source (hcomp' c hallows) (hnohalt c hallows) hlaw' hfed'
                  st' prefixBuf tailBuf
              have haloneVStep :
                  Alone M source verifier
                    ((verifierHandler M codecs tm prover).run (retryOf M none)
                      (.call (.hear (.coin law) prover at_ τ) kV) (st, delta ++ tailBuf))
                    recV (.returned (outV, (stFinal, tailBuf))) := by
                simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
                  proofReaderHandler, ↓reduceIte, hsq, Handler.answer, Process.mapHalt,
                  Process.bind] using haloneV
              obtain ⟨recV', haloneV'⟩ := hliftV (st, delta ++ tailBuf) recV _ haloneVStep
              refine ⟨out, outP, outV, delta, stFinal, recP, recV', hbytes, ?_, haloneV', hpostP, hpostV⟩
              simpa only [Handler.run, retryOf, proverHandler, Handler.over, fsProverHandler,
                proofWriterHandler, hmV, ↓reduceIte, hsq, Handler.answer, Process.mapHalt,
                Process.bind] using haloneP
            · exact absurd rfl hneP
      | request service =>
          obtain ⟨⟨hneP, _, _, _⟩, _⟩ := hcomp
          exact absurd rfl hneP
  | @heard kind owner hearers at_ ins payload τ k kP hneP hmP _ ih =>
      intro vProg hv source hcomp hnohalt hlaw hfed st prefixBuf tailBuf
      cases kind with
      | coin law =>
          obtain ⟨hcoin, hcomp'⟩ := hcomp
          rcases hcoin with hpriv | ⟨hparties, s, hsLaw, hsIns, hsOut, hInsEq⟩
          · subst hpriv; cases hmP
          · rcases hparties with (⟨hownerV, _⟩ | ⟨hownerP, _⟩) | ⟨_, hnmP, _, _⟩
            · subst owner
              subst hInsEq
              cases payload
              obtain ⟨kV, hv', hliftV⟩ :=
                peel_verifier_owned M (codecs := codecs) (tm := tm) (prover := prover) (source := source) hv
              obtain ⟨c, st', hsq, hallows⟩ := htm st law s hsLaw hsIns τ hsOut (coinLabel at_)
              have hfed' : Fed M source (k c) := by
                cases hearers with
                | nil => cases hmP
                | cons _ _ => exact hfed c hallows
              have hlaw' : LawfulPrivate M source (k c) := by
                cases hearers with
                | nil => cases hmP
                | cons _ _ => exact hlaw c hallows
              obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
                ih c (hv' c) source (hcomp' c hallows) (hnohalt c hallows) hlaw' hfed'
                  st' prefixBuf tailBuf
              have haloneVStep :
                  Alone M source verifier
                    ((verifierHandler M codecs tm prover).run (retryOf M none)
                      (.call (.own (.coin law) hearers at_ [] .nil τ) kV) (st, delta ++ tailBuf))
                    recV (.returned (outV, (stFinal, tailBuf))) := by
                simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
                  proofReaderHandler, hmP, ↓reduceIte, hsq, Handler.answer, Process.mapHalt,
                  Process.bind] using haloneV
              obtain ⟨recV', haloneV'⟩ := hliftV (st, delta ++ tailBuf) recV _ haloneVStep
              refine ⟨out, outP, outV, delta, stFinal, recP, recV', hbytes, ?_, haloneV', hpostP, hpostV⟩
              simpa only [Handler.run, retryOf, proverHandler, Handler.over, fsProverHandler,
                proofWriterHandler, ↓reduceIte, hsq, Handler.answer, Process.mapHalt,
                Process.bind] using haloneP
            · exact absurd hownerP hneP
            · exact absurd hmP hnmP
      | request service =>
          obtain ⟨⟨_, hnmP, _, _⟩, _⟩ := hcomp
          exact absurd hmP hnmP
  | @unheard kind owner hearers at_ ins payload τ k q hneP hnmP _ ih =>
      intro vProg hv source hcomp hnohalt hlaw hfed st prefixBuf tailBuf
      cases kind with
      | coin law =>
          obtain ⟨hcoin, hcomp'⟩ := hcomp
          rcases hcoin with hpriv | ⟨hparties, s, hsLaw, hsIns, hsOut, hInsEq⟩
          · subst hpriv
            obtain ⟨v, hsrc, hfed'⟩ := hfed
            obtain ⟨hallows, hlaw'⟩ := hlaw v hsrc
            if hownV : owner = verifier then
              subst owner
              obtain ⟨kV, hv', hliftV⟩ :=
                peel_verifier_owned M (codecs := codecs) (tm := tm) (prover := prover) (source := source) hv
              obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
                ih v (hv' v) source (hcomp' v hallows) (hnohalt v hallows) hlaw' hfed' st prefixBuf tailBuf
              have haloneVStep :
                Alone M source verifier
                  ((verifierHandler M codecs tm prover).run (retryOf M none)
                    (.call (.own (.coin law) [] at_ ins payload τ) kV) (st, delta ++ tailBuf))
                  (.owned verifier (.coin law) at_ τ v :: recV)
                  (.returned (outV, (stFinal, tailBuf))) := by
                simpa only [Handler.run, retryOf, verifierHandler, Handler.over, fsVerifierHandler,
                  proofReaderHandler, List.not_mem_nil, ↓reduceIte, Handler.answer, Process.mapHalt,
                  Process.bind] using Alone.own hsrc haloneV
              obtain ⟨recV', haloneV'⟩ := hliftV (st, delta ++ tailBuf) _ _ haloneVStep
              exact ⟨out, outP, outV, delta, stFinal, recP, recV', hbytes, haloneP, haloneV', hpostP, hpostV⟩
            else
              obtain ⟨vProg', hv', hliftV⟩ :=
                peel_verifier_unheard M (codecs := codecs) (tm := tm) (prover := prover) (source := source)
                  hownV (by simp) hv
              obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
                ih v (hv' v) source (hcomp' v hallows) (hnohalt v hallows) hlaw' hfed' st prefixBuf tailBuf
              obtain ⟨recV', haloneV'⟩ := hliftV (st, delta ++ tailBuf) recV _ haloneV
              exact ⟨out, outP, outV, delta, stFinal, recP, recV', hbytes, haloneP, haloneV', hpostP, hpostV⟩
          · rcases hparties with (⟨_, hmP⟩ | ⟨hoP, _⟩) | ⟨_, _, hneV, hnmV⟩
            · exact absurd hmP hnmP
            · exact absurd hoP hneP
            · subst hInsEq
              cases payload
              cases hearers with
              | nil =>
                  obtain ⟨v, hsrc, hfed'⟩ := hfed
                  obtain ⟨hallows, hlaw'⟩ := hlaw v hsrc
                  obtain ⟨vProg', hv', hliftV⟩ :=
                    peel_verifier_unheard M (codecs := codecs) (tm := tm) (prover := prover) (source := source)
                      hneV hnmV hv
                  obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
                    ih v (hv' v) source (hcomp' v hallows) (hnohalt v hallows) hlaw' hfed' st prefixBuf tailBuf
                  obtain ⟨recV', haloneV'⟩ := hliftV (st, delta ++ tailBuf) recV _ haloneV
                  exact ⟨out, outP, outV, delta, stFinal, recP, recV', hbytes, haloneP, haloneV', hpostP, hpostV⟩
              | cons _ _ =>
                  obtain ⟨v, _, _, hallows⟩ := htm st law s hsLaw hsIns τ hsOut []
                  obtain ⟨vProg', hv', hliftV⟩ :=
                    peel_verifier_unheard M (codecs := codecs) (tm := tm) (prover := prover) (source := source)
                      hneV hnmV hv
                  obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
                    ih v (hv' v) source (hcomp' v hallows) (hnohalt v hallows)
                      (hlaw v hallows) (hfed v hallows) st prefixBuf tailBuf
                  obtain ⟨recV', haloneV'⟩ := hliftV (st, delta ++ tailBuf) recV _ haloneV
                  exact ⟨out, outP, outV, delta, stFinal, recP, recV', hbytes, haloneP, haloneV', hpostP, hpostV⟩
      | request service =>
          obtain ⟨⟨_, _, hneV, hnmV⟩, hcomp'⟩ := hcomp
          obtain ⟨v, hsrc, hfed'⟩ := hfed
          obtain ⟨hallows, hlaw'⟩ := hlaw v hsrc
          obtain ⟨vProg', hv', hliftV⟩ :=
            peel_verifier_unheard M (codecs := codecs) (tm := tm) (prover := prover) (source := source)
              hneV hnmV hv
          obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
            ih v (hv' v) source (hcomp' v hallows) (hnohalt v hallows) hlaw' hfed' st prefixBuf tailBuf
          obtain ⟨recV', haloneV'⟩ := hliftV (st, delta ++ tailBuf) recV _ haloneV
          exact ⟨out, outP, outV, delta, stFinal, recP, recV', hbytes, haloneP, haloneV', hpostP, hpostV⟩
  | @begins at_beg _ _ _ ih =>
      intro vProg hv source hcomp hnohalt hlaw hfed st prefixBuf tailBuf
      obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
        ih hv source hcomp hnohalt hlaw hfed st prefixBuf tailBuf
      refine ⟨out, outP, outV, delta, stFinal, .began prover at_beg :: recP, recV, hbytes, ?_, haloneV, hpostP, hpostV⟩
      simpa only [Handler.run, retryOf, proverHandler, Handler.over, fsProverHandler,
        proofWriterHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.begin haloneP
  | @settles at_set _ _ _ ih =>
      intro vProg hv source hcomp hnohalt hlaw hfed st prefixBuf tailBuf
      obtain ⟨out, outP, outV, delta, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
        ih hv source hcomp hnohalt hlaw hfed st prefixBuf tailBuf
      refine ⟨out, outP, outV, delta, stFinal, .settled prover at_set :: recP, recV, hbytes, ?_, haloneV, hpostP, hpostV⟩
      simpa only [Handler.run, retryOf, proverHandler, Handler.over, fsProverHandler,
        proofWriterHandler, Handler.answer, Process.mapHalt, Process.bind] using
        Alone.settle haloneP

/-- Completeness of non-interactive deployment: for any validated `DeploymentPlan` without
retry, any lawful `ValidCodecs` and lawful `TranscriptModel`, any inputs on which the entry
protocol is deployment-compatible and never halts, and any source lawfully feeding private
coins, the deployed prover produces canonical proof bytes (`< 256`) that the deployed
verifier accepts with zero trailing bytes, returning each party's projected outputs of the
protocol run. -/
theorem deploy_complete (plan : DeploymentPlan V) (hretry : plan.declaration.retry = none)
    (codecs : ValidCodecs M) (tm : TranscriptModel V M) (htm : tm.Lawful)
    (ins : HList (LVal M) plan.entry.ins) (source : Source M)
    (hcomp : ProtoCompatible M plan.prover plan.verifier
      (protocolMeaning M plan.admitted.program plan.callee [] ins))
    (hnohalt : ProtoNoHalt M
      (protocolMeaning M plan.admitted.program plan.callee [] ins))
    (hlaw : LawfulPrivate M source
      (protocolMeaning M plan.admitted.program plan.callee [] ins))
    (hfed : Fed M source
      (protocolMeaning M plan.admitted.program plan.callee [] ins)) :
    ∃ (out : HList (LVal M) plan.entry.outs × plan.entry.record.Val M) (proof : List Nat)
      (recordP recordV : List (Happened M)),
      (∀ b, b ∈ proof → b < 256) ∧
      Alone M source plan.prover
        (plan.proverProcess M codecs tm (hideAll M plan.prover ins))
        recordP (.returned (hideAll M plan.prover out.1, proof)) ∧
      Alone M source plan.verifier
        (plan.verifierProcess M codecs tm (hideAll M plan.verifier ins) proof)
        recordV (.returned (hideAll M plan.verifier out.1)) := by
  have hp := projection M plan.admitted.program plan.callee plan.prover [] ins
  have hv := projection M plan.admitted.program plan.callee plan.verifier [] ins
  let st₀ := startTranscript M codecs tm plan.identity
    (statementValues M plan.prover plan.verifier plan.prover (.inl rfl) (hideAll M plan.prover ins))
  obtain ⟨out, outP, outV, proof, stFinal, recP, recV, hbytes, haloneP, haloneV, hpostP, hpostV⟩ :=
    deploy_simulate M htm plan.distinctParties hp hv source hcomp hnohalt hlaw hfed st₀ [] []
  subst hpostP
  subst hpostV
  refine ⟨out, proof, recP, recV, hbytes, ?_, ?_⟩
  · unfold DeploymentPlan.proverProcess
    rw [hretry]
    simpa only [List.nil_append] using
      alone_map M (alone_mapHalt M haloneP)
  · unfold DeploymentPlan.verifierProcess
    rw [hretry, ← statementValues_prover_eq_verifier M plan.prover plan.verifier ins]
    have haloneV' :
        Alone M source plan.verifier
          (((verifierHandler M codecs tm plan.prover).run (retryOf M none)
            (roleMeaning M plan.admitted.program plan.callee plan.verifier []
              (hideAll M plan.verifier ins))
            (st₀, proof)).mapHalt Prod.fst)
          recV (.returned (hideAll M plan.verifier out.1, (stFinal, []))) := by
      simpa only [List.append_nil] using alone_mapHalt M haloneV
    have hfin := alone_bind M haloneV' (k := fun out =>
      if out.2.2.isEmpty then .done out.1
      else .halt (.declared .reject ⟨[], plan.declaration.entry⟩)) (rec2 := []) (by
        simp only [List.isEmpty_nil, ↓reduceIte]
        exact Alone.done)
    simpa only [List.append_nil] using hfin

end Completeness

end Zkc.Core
