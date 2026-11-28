module

public import Zkc.Frontend.Deploy.SuitePlan
public import Zkc.Frontend.Emit.Root
public import Zkc.Frontend.Emit.Refusal
public import Zkc.Core.Scheme.Deploy.Compile
public import Zkc.Vocabulary.Encoder

@[expose] public section
set_option autoImplicit false

/-!
# Frontend scheme IR emission (`Zkc.Frontend.Deploy.Emit`)

Lowers a `SchemePlan` and its frontend protocol instance into an extended `Project.Bindings`,
a Core `NamedProgram` containing:
1. the reachable frontend definitions (with any `context` lines lowered directly into `@(P, V)`
   entry protocol ports so `declaration.context = []`),
2. suite member functions (`SuiteSlot.{start, absorb, encode, derive}`) — using **pure Core IR**
   with standard vocabulary rows for `zkc::suites::HashChain<H, F>` and project-bound runtime rows
   for catalogue suites (`Merlin3`, `Poseidon2`, `CFRG SHAKE128 / TurboSHAKE128`, `schnorr-signature`),
3. canonical byte layout functions (`LayoutSlot.{write, read, equal}`),
4. derived private-sample adapters (`samples derived by`), and
5. compact-layout commitment recovery functions (`recover sites.<name> by <path>`, emitted in pure
   Core group IR for Schnorr commitment recovery `base * z - point * c`),

together with the resolved `Core.Declaration`.
-/

namespace Zkc.Frontend.Deploy

open Zkc.Core
open Zkc.Vocabulary
open Zkc.Vocabulary.Project

/-- Canonical byte type `fin 256` in any project-linked vocabulary. -/
abbrev linkedByteTy : LinkedType := .fin 256

/-- Canonical byte-sequence type `[byte]` in any project-linked vocabulary. -/
abbrev linkedBytesTy : LinkedType := .seq linkedByteTy none

/-- Canonical `KoalaBear` prime-field type in any project-linked vocabulary. -/
abbrev linkedKoalaBearTy : LinkedType := .nominal (.inl (.field .koalaBear))

/-- Canonical `BLS12-381 G1` group type in any project-linked vocabulary. -/
abbrev linkedG1Ty : LinkedType := .nominal (.inl (.group .g1))

/-- Canonical `BLS12-381 Fr` scalar-field type in any project-linked vocabulary. -/
abbrev linkedFrTy : LinkedType := .nominal (.inl (.field .bls12381Fr))

/-! ## Canonical `Parameter` encoding of `LinkedType` for collision-free project row keys -/

def typeKeyTag : TypeKey → String
  | .field .koalaBear => "std.field.koala-bear"
  | .field .koalaBear4 => "std.field.koala-bear4"
  | .field .bls12381Fr => "std.field.bls12-381-fr"
  | .nonzero .koalaBear => "std.nonzero.koala-bear"
  | .nonzero .koalaBear4 => "std.nonzero.koala-bear4"
  | .nonzero .bls12381Fr => "std.nonzero.bls12-381-fr"
  | .group .g1 => "std.group.g1"
  | .group .g2 => "std.group.g2"
  | .group .gt => "std.group.gt"

mutual
  /-- Encode any `LinkedType` canonically as a `Project.Parameter` so monomorphized suite and
  layout rows (`encode<τ>`, `write<τ>`, `try_read<τ>`, `equal<τ>`, `derive<law>`) receive
  distinct `PrimitiveName` keys in `Project.Bindings`. -/
  def linkedTypeToParam : LinkedType → Parameter
    | .bool => .type .bool .nil
    | .nat => .type .nat .nil
    | .fin bound => .type (.index bound) .nil
    | .seq item size => .type (.seq size) (.cons (linkedTypeToParam item) .nil)
    | .tuple items => .type .tuple (linkedTysToParams items)
    | .record key _ fields => .type (.record key.number) (linkedTysToParams fields)
    | .variant key alts => .type (.variant key.number) (linkedTysToParams alts)
    | .nominal (.inl k) => .type (.nominal (typeKeyTag k)) .nil
    | .nominal (.inr p) => p

  def linkedTysToParams : Core.Tys (Sum TypeKey Parameter) → Parameters
    | .nil => .nil
    | .cons head rest => .cons (linkedTypeToParam head) (linkedTysToParams rest)
end

/-- Encode a list of `LinkedType`s into `Parameters`. -/
def linkedTypeListToParams : List LinkedType → Parameters
  | [] => .nil
  | t :: ts => .cons (linkedTypeToParam t) (linkedTypeListToParams ts)

/-! ## Maximum `Key` and `Core.Name` scanners -/

def maxDefKey {V : Core.Vocabulary} (defs : List (Definition V)) : Nat :=
  defs.foldl (fun acc d => max acc d.key.number) 0

mutual
  def maxInstrName {Op Who : Type} : Instruction Op Who → Nat
    | .op _ rs _ ops => max (rs.foldl max 0) (ops.foldl max 0)
    | .guard _ _ c _ => c
    | .choose _ _ c rs t f => max c (max (rs.foldl max 0) (max (maxRegionName t) (maxRegionName f)))
    | .cases _ _ s rs arms => max s (max (rs.foldl max 0) (maxRegionsName arms))
    | .loop _ _ times carried rs body =>
        let tm := match times with | .fixed _ => 0 | .count n => n
        max tm (max (carried.foldl max 0) (max (rs.foldl max 0) (maxRegionName body)))
    | .block _ _ rs body => max (rs.foldl max 0) (maxRegionName body)
    | .attempt _ _ rs body => max (rs.foldl max 0) (maxRegionName body)

  def maxInstrsName {Op Who : Type} : List (Instruction Op Who) → Nat
    | [] => 0
    | i :: is => max (maxInstrName i) (maxInstrsName is)

  def maxRegionName {Op Who : Type} : Region Op Who → Nat
    | .mk ins body exit => max (ins.foldl max 0) (max (maxInstrsName body) (exit.foldl max 0))

  def maxRegionsName {Op Who : Type} : List (Region Op Who) → Nat
    | [] => 0
    | r :: rs => max (maxRegionName r) (maxRegionsName rs)
end

/-! ## Injecting `context` lines directly as `@(prover, verifier)` entry protocol ports -/

/-- Append `contexts` as statement ports held by `[prover, verifier]` to the entry protocol
definition `entryKey`. Preserves body instructions, keys, shape, and straight-line structure. -/
def injectContextPorts {V : Core.Vocabulary} (entryKey : Key) (prover verifier : Role)
    (contexts : List (String × V.Ty)) (defs : List (Definition V)) : List (Definition V) :=
  if contexts.isEmpty then defs
  else
    let ctxHolders := Holders.ofList [prover, verifier]
    defs.map fun d =>
      match d with
      | .protocol key roles ins outs (.mk bodyIns body exit) =>
          if key == entryKey then
            let baseName := maxRegionName (.mk bodyIns body exit) + 1
            let extraLTys : List (LTy V) := contexts.map fun (_, τ) => ⟨τ, ctxHolders⟩
            let extraNames : List Core.Name := (List.range contexts.length).map (· + baseName)
            .protocol key roles (ins ++ extraLTys) outs (.mk (bodyIns ++ extraNames) body exit)
          else d
      | other => other

/-! ## Pure helper builders for `Definition.fn` -/

/-- Insert a project row into `Bindings` or fail cleanly on conflicting signature. -/
def insertRow (b : Bindings) (prim : PrimitiveName) (ins outs : List LinkedType) :
    Except String Bindings :=
  match b.insert prim ⟨ins, outs⟩ with
  | .ok b' => .ok b'
  | .error k => .error s!"conflicting project row binding for `{k.name}`"

/-- Emit a 1-instruction total unconditional function calling a single project row. -/
def mkRowFn (b : Bindings) (fnKey : Key) (prim : PrimitiveName) (ins outs : List LinkedType) :
    Definition b.vocabulary :=
  let inNames := List.range ins.length
  let outNames := (List.range outs.length).map (· + ins.length)
  let instr : Instruction (LocalRaw b.vocabulary) Unit :=
    .op ⟨0⟩ outNames (.row (.inr prim)) inNames
  .fn fnKey ins outs false none ⟨[], []⟩ (.mk inNames [instr] outNames)

/-- Emit a 2-instruction stopping layout reader wrapping `layout.canonical.try_read`. -/
def mkCanonicalReadFn (b : Bindings) (fnKey : Key) (tryReadPrim : PrimitiveName)
    (τ : LinkedType) : Definition b.vocabulary :=
  let i0 : Instruction (LocalRaw b.vocabulary) Unit :=
    .op ⟨0⟩ [2, 3, 4] (.row (.inr tryReadPrim)) [0, 1]
  let i1 : Instruction (LocalRaw b.vocabulary) Unit :=
    .guard ⟨1⟩ () 2 .reject
  .fn fnKey [linkedBytesTy, .nat] [τ, .nat] true none ⟨[], []⟩ (.mk [0, 1] [i0, i1] [3, 4])

/-! ## Pure Core IR emission for source suite `zkc::suites::HashChain<H, F>` -/

/-- Digest byte width of a standard hash primitive. -/
def hashDigestSize : Zkc.Vocabulary.Hash → Nat
  | .sha256 => 32
  | .keccak256 => 32
  | .shake128 n => n
  | .shake256 n => n

/-- State type of `HashChain<H, F>` in Core IR: `[byte; H::Size]`. -/
def hashChainStateTy (hash : Zkc.Vocabulary.Hash) : LinkedType :=
  .seq linkedByteTy (some (hashDigestSize hash))

/-- Pure Core IR `HashChain::start : [byte] → [byte; H::Size]`. -/
def mkHashChainStartFn (b : Bindings) (fnKey : Key) (hash : Zkc.Vocabulary.Hash) :
    Definition b.vocabulary :=
  let stateTy := hashChainStateTy hash
  let i0 : Instruction (LocalRaw b.vocabulary) Unit :=
    .op ⟨0⟩ [1] (.row (.inl (.hash hash))) [0]
  .fn fnKey [linkedBytesTy] [stateTy] false none ⟨[], []⟩ (.mk [0] [i0] [1])

/-- Pure Core IR `HashChain::absorb : ([byte; H::Size], [byte], [byte]) → [byte; H::Size]`.
Computes `H(state ++ [0] ++ label ++ [0] ++ msg)` using only standard `RowKey.hash` and owned ops. -/
def mkHashChainAbsorbFn (b : Bindings) (fnKey : Key) (hash : Zkc.Vocabulary.Hash) :
    Definition b.vocabulary :=
  let stateTy := hashChainStateTy hash
  let ops : List (Instruction (LocalRaw b.vocabulary) Unit) := [
    .op ⟨0⟩ [3] (.owned .seqUnsized [stateTy] []) [0],
    .op ⟨1⟩ [4] (.literal linkedBytesTy [1, 0]) [],
    .op ⟨2⟩ [5] (.owned .seqConcat [linkedBytesTy, linkedBytesTy] []) [3, 4],
    .op ⟨3⟩ [6] (.owned .seqConcat [linkedBytesTy, linkedBytesTy] []) [5, 1],
    .op ⟨4⟩ [7] (.owned .seqConcat [linkedBytesTy, linkedBytesTy] []) [6, 4],
    .op ⟨5⟩ [8] (.owned .seqConcat [linkedBytesTy, linkedBytesTy] []) [7, 2],
    .op ⟨6⟩ [9] (.row (.inl (.hash hash))) [8]
  ]
  .fn fnKey [stateTy, linkedBytesTy, linkedBytesTy] [stateTy] false none ⟨[], []⟩
    (.mk [0, 1, 2] ops [9])

structure LocalIRBuilder (b : Bindings) where
  nextKey : Nat := 0
  nextName : Nat := 0
  instrs : Array (Instruction (LocalRaw b.vocabulary) Unit) := #[]

def LocalIRBuilder.emit {b : Bindings} (st : LocalIRBuilder b)
    (op : LocalRaw b.vocabulary) (operands : List Core.Name) (numOuts : Nat) :
    List Core.Name × LocalIRBuilder b :=
  let outs := (List.range numOuts).map (· + st.nextName)
  let instr : Instruction (LocalRaw b.vocabulary) Unit :=
    .op ⟨st.nextKey⟩ outs op operands
  (outs, { nextKey := st.nextKey + 1, nextName := st.nextName + numOuts, instrs := st.instrs.push instr })

def LocalIRBuilder.emit1 {b : Bindings} (st : LocalIRBuilder b)
    (op : LocalRaw b.vocabulary) (operands : List Core.Name) :
    Core.Name × LocalIRBuilder b :=
  let (outs, st') := st.emit op operands 1
  (outs.headD 0, st')

/-- Emit Horner little-endian byte folding `∑ i, bytes[i] * 256^i` as pure straight-line Core IR
using `finToNat`, `natMul`, and `natAdd` (zero loops, zero fact obligations). -/
def emitHornerLeNat {b : Bindings} (st : LocalIRBuilder b) (byteNames : List Core.Name) :
    Core.Name × LocalIRBuilder b := Id.run do
  let (acc0, st) := st.emit1 (.literal .nat [0]) []
  let (c256, st) := st.emit1 (.literal .nat [256]) []
  let mut acc := acc0
  let mut cur := st
  for bn in byteNames.reverse do
    let (vNat, s1) := cur.emit1 (.owned .finToNat [linkedByteTy] []) [bn]
    let (shifted, s2) := s1.emit1 (.owned .natMul [] []) [acc, c256]
    let (nextAcc, s3) := s2.emit1 (.owned .natAdd [] []) [shifted, vNat]
    acc := nextAcc
    cur := s3
  return (acc, cur)

/-- Pure Core IR `HashChain::derive : ([byte; H::Size], [byte]) → (τ, [byte; H::Size])`.
Computes two 32-byte squeeze blocks `b0 = H(st ++ [1] ++ lbl ++ [0])` and
`b1 = H(st ++ [1] ++ lbl ++ [1])` plus next state `st' = H(st ++ [2] ++ lbl)`, unpacks the
bytes via total `takeSeq`, folds them via Horner's rule, and reduces via `FieldRow.fromNat`
(or `fromComponents` for `KoalaBear4`, or `< 128` for `bool`). Zero opaque suite rows! -/
def mkHashChainDeriveFn (b : Bindings) (fnKey : Key) (hash : Zkc.Vocabulary.Hash)
    (τ : LinkedType) : Except String (Definition b.vocabulary) := do
  let dSize := hashDigestSize hash
  if dSize == 0 then throw "HashChain requires positive digest size"
  let stateTy := hashChainStateTy hash
  let st0 : LocalIRBuilder b := { nextKey := 0, nextName := 2 }
  let (stU, st) := st0.emit1 (.owned .seqUnsized [stateTy] []) [0]
  let (sep1, st) := st.emit1 (.literal linkedBytesTy [1, 1]) []
  let (sep2, st) := st.emit1 (.literal linkedBytesTy [1, 2]) []
  let (ctr0, st) := st.emit1 (.literal linkedBytesTy [1, 0]) []
  let (ctr1, st) := st.emit1 (.literal linkedBytesTy [1, 1]) []
  let (s1, st) := st.emit1 (.owned .seqConcat [linkedBytesTy, linkedBytesTy] []) [stU, sep1]
  let (pre1, st) := st.emit1 (.owned .seqConcat [linkedBytesTy, linkedBytesTy] []) [s1, 1]
  let (in0, st) := st.emit1 (.owned .seqConcat [linkedBytesTy, linkedBytesTy] []) [pre1, ctr0]
  let (in1, st) := st.emit1 (.owned .seqConcat [linkedBytesTy, linkedBytesTy] []) [pre1, ctr1]
  let (b0, st) := st.emit1 (.row (.inl (.hash hash))) [in0]
  let (b1, st) := st.emit1 (.row (.inl (.hash hash))) [in1]
  let (s2, st) := st.emit1 (.owned .seqConcat [linkedBytesTy, linkedBytesTy] []) [stU, sep2]
  let (inNext, st) := st.emit1 (.owned .seqConcat [linkedBytesTy, linkedBytesTy] []) [s2, 1]
  let (nextSt, st) := st.emit1 (.row (.inl (.hash hash))) [inNext]
  let (d0s, st) := st.emit (.owned .take [stateTy] []) [b0] dSize
  let (d1s, st) := st.emit (.owned .take [stateTy] []) [b1] dSize
  let allBytes := d0s ++ d1s
  match τ with
  | .nominal (.inl (.field .bls12381Fr)) =>
      let (acc, st) := emitHornerLeNat st (allBytes.take 48)
      let (ch, st) := st.emit1 (.row (.inl (.field .fromNat .bls12381Fr .all))) [acc]
      .ok (.fn fnKey [stateTy, linkedBytesTy] [τ, stateTy] false none ⟨[], []⟩
        (.mk [0, 1] st.instrs.toList [ch, nextSt]))
  | .nominal (.inl (.field .koalaBear)) =>
      let (acc, st) := emitHornerLeNat st (allBytes.take 16)
      let (ch, st) := st.emit1 (.row (.inl (.field .fromNat .koalaBear .all))) [acc]
      .ok (.fn fnKey [stateTy, linkedBytesTy] [τ, stateTy] false none ⟨[], []⟩
        (.mk [0, 1] st.instrs.toList [ch, nextSt]))
  | .nominal (.inl (.field .koalaBear4)) =>
      let (a0, st) := emitHornerLeNat st (allBytes.take 16)
      let (a1, st) := emitHornerLeNat st ((allBytes.drop 16).take 16)
      let (a2, st) := emitHornerLeNat st ((allBytes.drop 32).take 16)
      let (a3, st) := emitHornerLeNat st ((allBytes.drop 48).take 16)
      let (c0, st) := st.emit1 (.row (.inl (.field .fromNat .koalaBear .all))) [a0]
      let (c1, st) := st.emit1 (.row (.inl (.field .fromNat .koalaBear .all))) [a1]
      let (c2, st) := st.emit1 (.row (.inl (.field .fromNat .koalaBear .all))) [a2]
      let (c3, st) := st.emit1 (.row (.inl (.field .fromNat .koalaBear .all))) [a3]
      let (arr, st) := st.emit1 (.owned .make [.seq linkedKoalaBearTy (some 4)] []) [c0, c1, c2, c3]
      let (ch, st) := st.emit1 (.row (.inl (.field .fromComponents .koalaBear4 .all))) [arr]
      .ok (.fn fnKey [stateTy, linkedBytesTy] [τ, stateTy] false none ⟨[], []⟩
        (.mk [0, 1] st.instrs.toList [ch, nextSt]))
  | .bool =>
      let bFirst := allBytes.headD 0
      let (vNat, st) := st.emit1 (.owned .finToNat [linkedByteTy] []) [bFirst]
      let (c128, st) := st.emit1 (.literal .nat [128]) []
      let (ch, st) := st.emit1 (.owned .natLess [] []) [vNat, c128]
      .ok (.fn fnKey [stateTy, linkedBytesTy] [τ, stateTy] false none ⟨[], []⟩
        (.mk [0, 1] st.instrs.toList [ch, nextSt]))
  | _ =>
      .error s!"HashChain pure Core IR derive does not yet support target type {reprStr (linkedTypeToParam τ)}"

/-! ## Pure Core IR Schnorr commitment recovery (`base * response - point * challenge`) -/

def findIndicesOf {α : Type} [BEq α] (xs : List α) (target : α) : List Nat :=
  (xs.zipIdx).filterMap fun (x, i) => if x == target then some i else none

/-- Emit a compact-layout recovery function `stmtTys ++ wireTys → [recTy]`.
When recovering a BLS12-381 `G1` commitment from a statement containing `(base : G1, point : G1)`
and wire values containing `(challenge : Fr, response : Fr)`, emits **pure Core IR**
`base * response - point * challenge` using standard `GroupRow.scale` / `GroupRow.sub`! -/
def mkRecoverFn (b : Bindings) (fnKey : Key) (stmtTys wireTys : List LinkedType)
    (recTy : LinkedType) (fallbackPrim? : Option PrimitiveName) :
    Except String (Definition b.vocabulary) := do
  let ins := stmtTys ++ wireTys
  let inNames := List.range ins.length
  let g1StmtIdxs := findIndicesOf stmtTys linkedG1Ty
  let frWireIdxs := (findIndicesOf wireTys linkedFrTy).map (· + stmtTys.length)
  if recTy == linkedG1Ty && g1StmtIdxs.length >= 2 && frWireIdxs.length >= 2 then
    let iBase := g1StmtIdxs[0]!
    let iPoint := g1StmtIdxs[1]!
    let iChal := frWireIdxs[frWireIdxs.length - 2]!
    let iResp := frWireIdxs[frWireIdxs.length - 1]!
    let n0 := ins.length
    let ops : List (Instruction (LocalRaw b.vocabulary) Unit) := [
      .op ⟨0⟩ [n0] (.row (.inl (.group .scale (.group .g1)))) [iBase, iResp],
      .op ⟨1⟩ [n0 + 1] (.row (.inl (.group .scale (.group .g1)))) [iPoint, iChal],
      .op ⟨2⟩ [n0 + 2] (.row (.inl (.group .sub (.group .g1)))) [n0, n0 + 1]
    ]
    .ok (.fn fnKey ins [recTy] false none ⟨[], []⟩ (.mk inNames ops [n0 + 2]))
  else
    match fallbackPrim? with
    | some prim => .ok (mkRowFn b fnKey prim ins [recTy])
    | none => .error "unsupported compact recovery signature"

/-! ## Site resolution from frontend `ProtocolCode.sites` + Core `ShapeEvent`s -/

/-- Resolve a frontend `SiteRef` (`sites.<name>`) to its Core `Site` inside `events`. -/
def resolveSiteRef {V : Core.Vocabulary} (state : Compile.State) (protocolInst : InstanceId)
    (admitted : Core.Admitted V) (entryKey : Key) (events : List (ShapeEvent V))
    (siteNames : List String) : Except String Core.Site := do
  let some targetName := siteNames.getLast?
    | throw "empty site reference in scheme line"
  let siteAddr? := Emit.SiteAddresses.forProtocol admitted.program entryKey
  match state.results.body? protocolInst with
  | some (.protocol code) =>
      let matching := code.sites.filter fun s =>
        s.name == some targetName || s.fieldName == targetName
      match matching.toList with
      | entry :: _ =>
          -- Try exact instruction-key match in Core `ShapeEvent`s
          match entry.instruction with
          | some kNum =>
              match events.find? fun e => e.site.key.number == kNum with
              | some ev => .ok ev.site
              | none =>
                  -- Try `SiteAddresses` resolution
                  match siteAddr?.bind (·.resolve entry) with
                  | some (_, k) =>
                      match events.find? fun e => e.site.key == k with
                      | some ev => .ok ev.site
                      | none => .ok ⟨[], k⟩
                  | none =>
                      -- Check attempt sites (for `retry ... from sites.<name>`)
                      .ok ⟨[], ⟨kNum⟩⟩
          | none =>
              match events[entry.event]? with
              | some ev => .ok ev.site
              | none => throw s!"site `{targetName}` has no emitted Core instruction"
      | [] =>
          -- Fallback: check if `targetName` matches an attempt site or indexed event
          throw s!"site `sites.{".".intercalate siteNames}` not found in protocol `{code.name}`"
  | _ => throw s!"protocol instance {protocolInst} has no checked protocol summary"

/-- Resolve a retry target `sites.<name>` against both `ProtocolCode.sites` and `entry.shape.attemptSites`. -/
def resolveAttemptSiteRef {V : Core.Vocabulary} (state : Compile.State) (protocolInst : InstanceId)
    (admitted : Core.Admitted V) (entryKey : Key) (entry : ProtocolHeader V) (prover : Role)
    (siteNames : List String) : Except String Core.Site := do
  let events := entry.shape.events [] id
  match resolveSiteRef state protocolInst admitted entryKey events siteNames with
  | .ok s =>
      if s ∈ entry.shape.proverAttemptSites prover [] then .ok s
      else
        match entry.shape.proverAttemptSites prover [] with
        | [only] => .ok only
        | _ => .ok s
  | .error msg =>
      match entry.shape.proverAttemptSites prover [] with
      | [only] => .ok only
      | _ => .error msg

/-! ## Emitting reachable definitions directly under any extended `Bindings` -/

def emitReachableUnder (state : Compile.State) (found : Emit.Reachable)
    (bindings : Bindings) : Except String (Core.NamedProgram bindings.vocabulary) :=
  match (do
    let context ← Emit.bodyContext bindings
    let mut definitions := #[]
    for (inst, source) in found.bodies do
      let key : Core.Key := ⟨inst⟩
      let definition ← match source with
        | .fn body out => do
            let (definition, _) ← Emit.Named.functionDefinition context key out body
            pure definition
        | .protocol body roles => do
            let result ← Emit.Named.emitProtocol context ⟨roles, body.roster⟩ key body
            pure result.definition
      definitions := definitions.push definition
    return (⟨definitions.toList⟩ : Core.NamedProgram bindings.vocabulary)).run state with
  | .ok prog => .ok prog
  | .error e => .error s!"failed to emit protocol definitions: {reprStr e}"

/-! ## Catalogue suite row prefixes and unit types -/

def catalogueSuitePrefix : SuiteSpec → Option String
  | .merlin3 => some "suite.merlin3"
  | .poseidon2 => some "suite.poseidon2"
  | .schnorrSignature => some "suite.schnorr-signature"
  | .cfrgShake128 false => some "suite.cfrg.shake128"
  | .cfrgShake128 true => some "suite.cfrg.shake128.raw"
  | .cfrgTurboShake128 false => some "suite.cfrg.turboshake128"
  | .cfrgTurboShake128 true => some "suite.cfrg.turboshake128.raw"
  | .hashChain .. => none

def suiteUnitTy : SuiteSpec → LinkedType
  | .poseidon2 => linkedKoalaBearTy
  | _ => linkedByteTy

def suiteStateTy : SuiteSpec → LinkedType
  | .hashChain hash _ => hashChainStateTy hash
  | spec =>
      let tag := (catalogueSuitePrefix spec).getD "suite.unknown"
      .nominal (.inr (.type (.nominal s!"{tag}.state") .nil))

/-! ## Full scheme emission result -/

/-- Result of emitting a scheme's extended `Bindings`, `NamedProgram`, and `Core.Declaration`. -/
structure EmittedScheme where
  bindings : Bindings
  named : Core.NamedProgram bindings.vocabulary
  declaration : Core.Declaration
  proverRole? : Option Core.Role
  verifierRole? : Option Core.Role

def dedupList {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs =>
      let rest := dedupList xs
      if x ∈ rest then rest else x :: rest

/-- Emit the complete linked `Bindings`, `Core.NamedProgram`, and `Core.Declaration` for `plan`. -/
def emitSchemeProgram (state : Compile.State) (plan : SchemePlan) : Except String EmittedScheme := do
  -- 1. Gather reachable frontend bodies for the entry protocol instance
  let found ← match (Emit.visit plan.protocol [] {}).run state with
    | .ok f => .ok f
    | .error e => .error s!"cannot emit protocol instance {plan.protocol}: {reprStr e}"
  let entryKey : Core.Key := ⟨plan.protocol⟩
  let baseNamed ← emitReachableUnder state found found.bindings
  let baseAdmitted ← match Core.admit baseNamed ⟨[], [], [], [], []⟩ with
    | .ok a => .ok a
    | .error errs =>
        let pkg : SourcePackage := ⟨found.bindings, baseNamed, ⟨[], [], [], [], []⟩⟩
        .error s!"core refused base protocol package: {pkg.describeRefusals errs}"
  let some ⟨baseEntry, _⟩ := baseAdmitted.program.findProtocol entryKey
    | throw s!"entry protocol key {entryKey.number} missing from admitted program"

  -- 2. Resolve role kinds and optional declared prover index
  let kinds : List RoleKind := List.replicate baseEntry.roles .online
  let proverOpt? : Option Core.Role ←
    match plan.proverRole with
    | none => .ok none
    | some rName =>
        match state.results.body? plan.protocol with
        | some (.protocol code) =>
            match code.roles.toList.idxOf? rName with
            | some idx => .ok (some idx)
            | none => .error s!"prover role `{rName}` not found in protocol `{code.name}`"
        | _ => .error s!"cannot resolve prover role `{rName}` without protocol summary"

  -- Preliminary declaration to compute (prover, verifier) via Core's `proverAndVerifier`
  let probeDecl : Core.Declaration := {
    key := ⟨maxDefKey baseNamed.definitions + 1⟩
    entry := entryKey
    kinds
    construction := .interactive
    prover := proverOpt?
    layout := none
    retry := none
    samples := none
    context := []
    grinds := []
    commits := []
    pins := []
    application := plan.application
  }

  -- Fast path: interactive scheme (no suite, no layout, no context injection needed unless present)
  match plan.construction with
  | .interactive =>
      if !plan.contexts.isEmpty then
        throw "interactive scheme cannot declare non-empty `context` lines"
      let decl : Core.Declaration := { probeDecl with construction := .interactive }
      return {
        bindings := found.bindings
        named := baseNamed
        declaration := decl
        proverRole? := proverOpt?
        verifierRole? := none
      }
  | _ => pure ()

  -- 3. Determine (prover, verifier) for non-interactive (`derived` / `authored`) schemes
  let some (prover, verifier) := Core.onlineParties baseEntry kinds false proverOpt?
    | throw s!"could not identify unique (prover, verifier) roles for scheme `{plan.name}`"

  -- 4. Compute statement, flow, draw, and private-coin types (including any `context` ports)
  let events := baseEntry.shape.events [] id
  let baseStmtTys : List LinkedType :=
    baseEntry.ins.filterMap fun lt =>
      if prover ∈ lt.holders && verifier ∈ lt.holders then some (lt.ty : LinkedType) else none
  let ctxTys : List LinkedType := plan.contexts.map Prod.snd
  let stmtTys : List LinkedType := baseStmtTys ++ ctxTys
  let heldPTys : List LinkedType :=
    (baseEntry.ins.filterMap fun lt => if prover ∈ lt.holders then some (lt.ty : LinkedType) else none) ++ ctxTys
  let flowTys : List LinkedType :=
    events.filterMap fun e =>
      match e.cls with
      | .flow _ giver getters => if giver = prover ∧ verifier ∈ getters then some (e.τ : LinkedType) else none
      | _ => none
  let drawSpecs : List (Zkc.Vocabulary.LawKey × LinkedType) :=
    dedupList <| events.filterMap fun e =>
      match e.cls with
      | .given (.coin law) owner hearers =>
          if owner = verifier ∧ prover ∈ hearers then some (law, (e.τ : LinkedType)) else none
      | _ => none
  let privCoinTys : List LinkedType :=
    dedupList <| events.filterMap fun e =>
      match e.cls with
      | .given (.coin _) owner [] => if owner = prover then some (e.τ : LinkedType) else none
      | _ => none

  let allEncodeTys : List LinkedType := dedupList (stmtTys ++ flowTys ++ drawSpecs.map Prod.snd)
  let allLayoutTys : List LinkedType := dedupList (flowTys ++ drawSpecs.map Prod.snd)

  -- 5. Resolve `carry`, `recover`, and `retry` sites
  let layoutPlan := plan.layout.getD { layoutName := "zkc::layout::canonical" }
  let carrySites ← layoutPlan.carry.mapM fun names =>
    resolveSiteRef state plan.protocol baseAdmitted entryKey events names
  let recoverResolved ← layoutPlan.recover.mapM fun rp => do
    let site ← resolveSiteRef state plan.protocol baseAdmitted entryKey events rp.siteNames
    let some ev := events.find? fun e => e.site == site
      | throw s!"recovered site `{".".intercalate rp.siteNames}` not found in protocol shape"
    return (site, (ev.τ : LinkedType), rp.recoveryPath)
  let retryResolved ← match plan.retry with
    | none => .ok none
    | some (bound, siteNames) => do
        let site ← resolveAttemptSiteRef state plan.protocol baseAdmitted entryKey baseEntry prover siteNames
        .ok (some (bound, site))

  -- Compute compact wire types (in exact event order matching `collectCompactWire`)
  let recoverSites := recoverResolved.map Prod.fst
  let wireTys : List LinkedType :=
    events.filterMap fun e =>
      match e.cls with
      | .flow _ giver getters =>
          if giver = prover ∧ verifier ∈ getters then
            if e.site ∈ recoverSites then none else some (e.τ : LinkedType)
          else none
      | .given (.coin _) owner hearers =>
          if owner = verifier ∧ prover ∈ hearers then
            if e.site ∈ carrySites then some (e.τ : LinkedType) else none
          else none
      | _ => none

  -- 6. Extend `Project.Bindings` with all needed rows BEFORE emitting the final `NamedProgram`
  let mut extBindings := found.bindings

  -- 6a. Layout `canonical` rows (`write`, `try_read`, `equal`)
  for τ in allLayoutTys do
    let pArg : Parameters := .cons (linkedTypeToParam τ) .nil
    extBindings ← insertRow extBindings ⟨"layout.canonical.write", pArg⟩ [τ] [linkedBytesTy]
    extBindings ← insertRow extBindings ⟨"layout.canonical.try_read", pArg⟩
      [linkedBytesTy, .nat] [.bool, τ, .nat]
    extBindings ← insertRow extBindings ⟨"layout.canonical.equal", pArg⟩ [τ, τ] [.bool]

  -- 6b. Suite rows (for catalogue suites; `HashChain` needs only `layout.canonical.write` for `encode`!)
  match plan.construction with
  | .derived spec _ =>
      match catalogueSuitePrefix spec with
      | some pfx =>
          let stTy := suiteStateTy spec
          let uTy := suiteUnitTy spec
          extBindings ← insertRow extBindings ⟨s!"{pfx}.start", .nil⟩ [linkedBytesTy] [stTy]
          extBindings ← insertRow extBindings ⟨s!"{pfx}.absorb", .nil⟩
            [stTy, linkedBytesTy, .seq uTy none] [stTy]
          for τ in allEncodeTys do
            let pArg : Parameters := .cons (linkedTypeToParam τ) .nil
            extBindings ← insertRow extBindings ⟨s!"{pfx}.encode", pArg⟩ [τ] [.seq uTy none]
          for (_, τ) in drawSpecs do
            let pArg : Parameters := .cons (linkedTypeToParam τ) .nil
            extBindings ← insertRow extBindings ⟨s!"{pfx}.derive", pArg⟩
              [stTy, linkedBytesTy] [τ, stTy]
      | none =>
          -- Pure Core IR `HashChain`: ensure `layout.canonical.write` is bound for all absorbed types
          for τ in allEncodeTys do
            let pArg : Parameters := .cons (linkedTypeToParam τ) .nil
            extBindings ← insertRow extBindings ⟨"layout.canonical.write", pArg⟩ [τ] [linkedBytesTy]
  | _ => pure ()

  -- 6c. `samples derived by` row (if declared)
  let samplesPrim? : Option (PrimitiveName × LinkedType) ←
    match plan.samplesPath, privCoinTys with
    | some _, coinTy :: _ =>
        let ins := heldPTys ++ [linkedBytesTy, linkedBytesTy, .nat, .nat]
        let prim : PrimitiveName := ⟨"signature.nonce_scalar", linkedTypeListToParams (coinTy :: ins)⟩
        extBindings ← insertRow extBindings prim ins [coinTy]
        .ok (some (prim, coinTy))
    | some _, [] =>
        let ins := heldPTys ++ [linkedBytesTy, linkedBytesTy, .nat, .nat]
        let prim : PrimitiveName := ⟨"signature.nonce_scalar", linkedTypeListToParams (linkedFrTy :: ins)⟩
        extBindings ← insertRow extBindings prim ins [linkedFrTy]
        .ok (some (prim, linkedFrTy))
    | none, _ => .ok none

  -- 6d. Compact-layout recovery fallback row (only needed when not pure Schnorr G1 recovery)
  let mut recoverFallbacks : List (Core.Site × LinkedType × Option PrimitiveName) := []
  let g1StmtIdxs := findIndicesOf stmtTys linkedG1Ty
  let frWireIdxs := findIndicesOf wireTys linkedFrTy
  for (site, recTyRaw, _) in recoverResolved do
    let recTy : LinkedType := recTyRaw
    if recTy == linkedG1Ty && g1StmtIdxs.length >= 2 && frWireIdxs.length >= 2 then
      recoverFallbacks := recoverFallbacks ++ [(site, recTy, none)]
    else
      let ins := stmtTys ++ wireTys
      let prim : PrimitiveName := ⟨"signature.recover_commitment", linkedTypeListToParams (recTy :: ins)⟩
      extBindings ← insertRow extBindings prim ins [recTy]
      recoverFallbacks := recoverFallbacks ++ [(site, recTy, some prim)]

  -- 7. Re-emit reachable definitions directly under `extBindings` and inject `context` ports
  let baseExtNamed ← emitReachableUnder state found extBindings
  let entryDefs := injectContextPorts entryKey prover verifier plan.contexts baseExtNamed.definitions

  -- 8. Synthesize helper `Definition.fn`s with deterministic fresh keys above `maxDefKey`
  let mut nextKeyNum := maxDefKey entryDefs + 1
  let mut helperDefs : List (Definition extBindings.vocabulary) := []

  -- 8a. Layout `canonical` functions
  let mut layoutMembers : List (Key × Key) := []
  for τ in allLayoutTys do
    let pArg : Parameters := .cons (linkedTypeToParam τ) .nil
    let wKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
    let rKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
    let eKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
    helperDefs := helperDefs ++ [
      mkRowFn extBindings wKey ⟨"layout.canonical.write", pArg⟩ [τ] [linkedBytesTy],
      mkCanonicalReadFn extBindings rKey ⟨"layout.canonical.try_read", pArg⟩ τ,
      mkRowFn extBindings eKey ⟨"layout.canonical.equal", pArg⟩ [τ, τ] [.bool]
    ]
    layoutMembers := layoutMembers ++ [
      (LayoutSlot.write, wKey),
      (LayoutSlot.read, rKey),
      (LayoutSlot.equal, eKey)
    ]

  -- 8b. Recovery functions (`recover sites.<name> by ...`)
  let mut recoverEntries : List (Core.Site × Key) := []
  for (site, recTy, fbPrim?) in recoverFallbacks do
    let recKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
    let recFn ← mkRecoverFn extBindings recKey stmtTys wireTys recTy fbPrim?
    helperDefs := helperDefs ++ [recFn]
    recoverEntries := recoverEntries ++ [(site, recKey)]

  -- 8c. Suite functions (`SuiteSlot.{start, absorb, encode, derive}`)
  let enc := Project.linkedEncoder extBindings
  let coreConstruction : Core.Construction ←
    match plan.construction with
    | .interactive => .ok .interactive
    | .authored => .ok .authored
    | .derived spec sessionTag =>
        let mut suiteMembers : List (Key × Key) := []
        let mut suiteLawMembers : List (Key × List Nat × Key) := []
        match spec with
        | .hashChain hash _ =>
            let sKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
            let aKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
            helperDefs := helperDefs ++ [
              mkHashChainStartFn extBindings sKey hash,
              mkHashChainAbsorbFn extBindings aKey hash
            ]
            suiteMembers := suiteMembers ++ [(SuiteSlot.start, sKey), (SuiteSlot.absorb, aKey)]
            for τ in allEncodeTys do
              let pArg : Parameters := .cons (linkedTypeToParam τ) .nil
              let eKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
              helperDefs := helperDefs ++ [
                mkRowFn extBindings eKey ⟨"layout.canonical.write", pArg⟩ [τ] [linkedBytesTy]
              ]
              suiteMembers := suiteMembers ++ [(SuiteSlot.encode, eKey)]
            for (law, τ) in drawSpecs do
              let dKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
              let derFn ← mkHashChainDeriveFn extBindings dKey hash τ
              helperDefs := helperDefs ++ [derFn]
              suiteMembers := suiteMembers ++ [(SuiteSlot.derive, dKey)]
              suiteLawMembers := suiteLawMembers ++ [(SuiteSlot.derive, enc.lawKey law, dKey)]
            .ok (.derived ⟨suiteMembers, suiteLawMembers⟩ sessionTag)
        | _ =>
            let some pfx := catalogueSuitePrefix spec
              | throw s!"internal error: missing catalogue prefix for {spec.describe}"
            let stTy := suiteStateTy spec
            let uTy := suiteUnitTy spec
            let sKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
            let aKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
            helperDefs := helperDefs ++ [
              mkRowFn extBindings sKey ⟨s!"{pfx}.start", .nil⟩ [linkedBytesTy] [stTy],
              mkRowFn extBindings aKey ⟨s!"{pfx}.absorb", .nil⟩ [stTy, linkedBytesTy, .seq uTy none] [stTy]
            ]
            suiteMembers := suiteMembers ++ [(SuiteSlot.start, sKey), (SuiteSlot.absorb, aKey)]
            for τ in allEncodeTys do
              let pArg : Parameters := .cons (linkedTypeToParam τ) .nil
              let eKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
              helperDefs := helperDefs ++ [
                mkRowFn extBindings eKey ⟨s!"{pfx}.encode", pArg⟩ [τ] [.seq uTy none]
              ]
              suiteMembers := suiteMembers ++ [(SuiteSlot.encode, eKey)]
            for (law, τ) in drawSpecs do
              let pArg : Parameters := .cons (linkedTypeToParam τ) .nil
              let dKey : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
              helperDefs := helperDefs ++ [
                mkRowFn extBindings dKey ⟨s!"{pfx}.derive", pArg⟩ [stTy, linkedBytesTy] [τ, stTy]
              ]
              suiteMembers := suiteMembers ++ [(SuiteSlot.derive, dKey)]
              suiteLawMembers := suiteLawMembers ++ [(SuiteSlot.derive, enc.lawKey law, dKey)]
            .ok (.derived ⟨suiteMembers, suiteLawMembers⟩ sessionTag)

  -- 8d. `samples derived by` function (if present)
  let samplesKey? : Option Key ←
    match samplesPrim? with
    | none => .ok none
    | some (prim, coinTy) =>
        let sk : Key := ⟨nextKeyNum⟩; nextKeyNum := nextKeyNum + 1
        let ins := heldPTys ++ [linkedBytesTy, linkedBytesTy, .nat, .nat]
        helperDefs := helperDefs ++ [mkRowFn extBindings sk prim ins [coinTy]]
        .ok (some sk)

  let declKey : Key := ⟨nextKeyNum⟩
  let coreLayout : Option Core.Layout :=
    match plan.construction with
    | .interactive => none
    | _ => some {
        «module» := ⟨layoutMembers, []⟩
        carry := carrySites
        recover := recoverEntries
      }
  let declaration : Core.Declaration := {
    key := declKey
    entry := entryKey
    kinds
    construction := coreConstruction
    prover := proverOpt?
    layout := coreLayout
    retry := retryResolved
    samples := samplesKey?
    context := []
    grinds := []
    commits := []
    pins := []
    application := plan.application
  }
  return {
    bindings := extBindings
    named := ⟨entryDefs ++ helperDefs⟩
    declaration
    proverRole? := some prover
    verifierRole? := some verifier
  }

end Zkc.Frontend.Deploy
