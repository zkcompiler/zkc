module

public import Zkc.Core.Scheme.Deploy.Compile
public import Zkc.Core.Program.EraseProgram

@[expose] public section

/-!
# Constructed and serialized Core materialization (`Zkc.Core.Scheme.Materialize`)

Prototype stage materializers turning an admitted interactive protocol and a `.derived` scheme
`Declaration` into standalone, re-admittable `Core.NamedProgram` artifacts without duplicating any
slot resolution or declaration validation logic (reusing `prepareDerivedBody`, `findSuite*`,
`findLayout*`, `eventsWithAbsorb`, and `finishGuardKey` directly):

1. `materializeConstructed`: emits the **constructed Core** program (`docs/spec/core/stages.md`):
   - keeps all erased helper functions (`Definition.fn`) in dependency order;
   - binds the resolved `sessBytes` (which embeds `schemeIdentity enc a declaration`, including
     layout choices) into dual role-local transcript states (`stP @[prover]`, `stV @[verifier]`);
   - absorbs every statement input in positional order (`stmtLabel 0, 1, …`);
   - retains prover→verifier flows and emits role-local `encode` + `absorb` updates on both roles
     whenever `eventsWithAbsorb` marks a flow as needed before a later draw;
   - eliminates every verifier→prover public coin draw into synchronized role-local `derive` calls.

2. `materializeSerialized`: emits the **serialized Core** program (`docs/spec/core/stages.md`):
   - prepends the proof input port `⟨.seq layUnitTy none, [verifier]⟩` to `ins` and the proof
     output port `⟨.seq layUnitTy none, [prover]⟩` to `outs`;
   - eliminates every prover→verifier flow into prover `write` + `seqConcat` (onto the proof
     buffer) and verifier `read` (advancing the cursor from `0`), preserving `read`-before-`absorb`
     order so verifier stops match `Core.deploy`'s `d.run` identically;
   - emits the verifier trailing-byte guard (`offV == seqLength(proof)`) at `finishGuardKey events`
     (when fresh) so trailing-byte rejection occurrences match `d.run` identically;
   - contains zero inter-role flows and zero verifier→prover public coin draws.

Both materializers are total (`0 partial`), strictly two-axiom (`propext`, `Quot.sound`), and
fail-closed on unsupported control structures or non-streaming layouts in `materializeSerialized`.
-/

namespace Zkc.Core

open LayerBuild

namespace MaterializeDetail

section
variable {V : Vocabulary}

/-! ## Pure name/key scanning and per-role variable mapping -/

mutual
  def maxInstrKey {Op Who : Type} : Instruction Op Who → Nat
    | .op k _ _ _ => k.number
    | .guard k _ _ _ => k.number
    | .choose k _ _ _ t f => max k.number (max (maxRegionKey t) (maxRegionKey f))
    | .cases k _ _ _ arms => max k.number (maxRegionsKey arms)
    | .loop k _ _ _ _ body => max k.number (maxRegionKey body)
    | .block k _ _ body => max k.number (maxRegionKey body)
    | .attempt k _ _ body => max k.number (maxRegionKey body)

  def maxInstrsKey {Op Who : Type} : List (Instruction Op Who) → Nat
    | [] => 0
    | i :: is => max (maxInstrKey i) (maxInstrsKey is)

  def maxRegionKey {Op Who : Type} : Region Op Who → Nat
    | .mk _ body _ => maxInstrsKey body

  def maxRegionsKey {Op Who : Type} : List (Region Op Who) → Nat
    | [] => 0
    | r :: rs => max (maxRegionKey r) (maxRegionsKey rs)
end

mutual
  def collectInstrKeys {Op Who : Type} : Instruction Op Who → List Key
    | .op k _ _ _ => [k]
    | .guard k _ _ _ => [k]
    | .choose k _ _ _ t f => k :: (collectRegionKeys t ++ collectRegionKeys f)
    | .cases k _ _ _ arms => k :: collectRegionsKeys arms
    | .loop k _ _ _ _ body => k :: collectRegionKeys body
    | .block k _ _ body => k :: collectRegionKeys body
    | .attempt k _ _ body => k :: collectRegionKeys body

  def collectInstrsKeys {Op Who : Type} : List (Instruction Op Who) → List Key
    | [] => []
    | i :: is => collectInstrKeys i ++ collectInstrsKeys is

  def collectRegionKeys {Op Who : Type} : Region Op Who → List Key
    | .mk _ body _ => collectInstrsKeys body

  def collectRegionsKeys {Op Who : Type} : List (Region Op Who) → List Key
    | [] => []
    | r :: rs => collectRegionKeys r ++ collectRegionsKeys rs
end

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

/-- Lookup a renamed variable in an association map, defaulting to the original name. -/
def lookupVar (m : List (Name × Name)) (x : Name) : Name :=
  match m.find? (fun p => p.1 == x) with
  | some (_, y) => y
  | none => x

/-- Lookup whether a top-level flow at key `k` needs transcript absorption before a subsequent draw. -/
def lookupNeedAbs (eventsAbs : List (ShapeEvent V × Bool)) (k : Key) : Bool :=
  match eventsAbs.find? (fun p => p.1.site == ⟨[], k⟩) with
  | some (_, needAbs) => needAbs
  | none => true

/-- Pure state threaded while materializing a straight-line protocol body. -/
structure MatState (V : Vocabulary) where
  nextKey : Nat
  nextName : Nat
  stP : Name
  stV : Name
  bufP : Name
  offV : Name
  envP : List (Name × Name)
  envV : List (Name × Name)
  revInstrs : List (Instruction (ProtocolRaw V) (List Role))

def MatState.freshKey (s : MatState V) : Key × MatState V :=
  (⟨s.nextKey⟩, { s with nextKey := s.nextKey + 1 })

def MatState.freshName (s : MatState V) : Name × MatState V :=
  (s.nextName, { s with nextName := s.nextName + 1 })

def MatState.freshNames (s : MatState V) : Nat → List Name × MatState V
  | 0 => ([], s)
  | n + 1 =>
      let (x, s1) := s.freshName
      let (xs, s2) := s1.freshNames n
      (x :: xs, s2)

def MatState.push (s : MatState V) (i : Instruction (ProtocolRaw V) (List Role)) : MatState V :=
  { s with revInstrs := i :: s.revInstrs }

def MatState.emitCompute1 (s : MatState V) (roles : List Role) (o : LocalRaw V)
    (ops : List Name) : Name × MatState V :=
  let (k, s1) := s.freshKey
  let (r, s2) := s1.freshName
  (r, s2.push (.op k [r] (.compute roles o) ops))

def MatState.emitCompute2 (s : MatState V) (roles : List Role) (o : LocalRaw V)
    (ops : List Name) : Name × Name × MatState V :=
  let (k, s1) := s.freshKey
  let (r1, s2) := s1.freshName
  let (r2, s3) := s2.freshName
  (r1, r2, s3.push (.op k [r1, r2] (.compute roles o) ops))

/-- Emit role-local `lbl ← literal label; enc ← call encKey [val]; st' ← call absorbKey [st, lbl, enc]`. -/
def MatState.emitAbsorb (s : MatState V) (role : Role) (label : List Nat)
    (encKey absorbKey : Key) (st val : Name) : Name × MatState V :=
  let (lblN, s1) := s.emitCompute1 [role] (.literal bytesTy (label.length :: label)) []
  let (encN, s2) := s1.emitCompute1 [role] (.call encKey) [val]
  s2.emitCompute1 [role] (.call absorbKey) [st, lblN, encN]

/-- Emit role-local `lbl ← literal label; (coin, st') ← call derKey [st, lbl]`. -/
def MatState.emitDerive (s : MatState V) (role : Role) (label : List Nat)
    (derKey : Key) (st : Name) : Name × Name × MatState V :=
  let (lblN, s1) := s.emitCompute1 [role] (.literal bytesTy (label.length :: label)) []
  s1.emitCompute2 [role] (.call derKey) [st, lblN]

/-- Emit statement absorptions on both `prover` and `verifier` in exact positional order matching
`statementPositions` and `LayerBuild.constructionStart`. -/
def emitStmtAbsorptions (a : Admitted V) (suite : ModuleRef) (suiteUnitTy : V.Ty)
    (absorbKey : Key) (prover verifier : Role) (declKey : Key) :
    Nat → List (LTy V × Name) → MatState V → Except (List (ProgramRefusal V)) (MatState V)
  | _, [], s => .ok s
  | idx, (lt, inName) :: rest, s =>
      if prover ∈ lt.holders ∧ verifier ∈ lt.holders then
        match findSuiteEncode a suite suiteUnitTy lt.ty with
        | none => .error (deployErr declKey .callee)
        | some encRef =>
            let lbl := stmtLabel idx
            let (stP', s1) := s.emitAbsorb prover lbl encRef.hdr.key absorbKey s.stP inName
            let (stV', s2) := s1.emitAbsorb verifier lbl encRef.hdr.key absorbKey s1.stV inName
            emitStmtAbsorptions a suite suiteUnitTy absorbKey prover verifier declKey
              (idx + 1) rest { s2 with stP := stP', stV := stV' }
      else
        emitStmtAbsorptions a suite suiteUnitTy absorbKey prover verifier declKey idx rest s

/-- Whether `roles` contains exactly `prover` and `verifier` (in either order). -/
def isPairRoles (prover verifier : Role) (roles : List Role) : Bool :=
  (roles == [prover, verifier]) || (roles == [verifier, prover])

/-- Rewrite a single straight-line protocol instruction into constructed (`serialize = false`) or
serialized (`serialize = true`) form. -/
def materializeInstr (enc : VocabEncoder V) (a : Admitted V) (suite : ModuleRef)
    (stateTy suiteUnitTy : V.Ty) (absorbKey : Key)
    (layoutOpt : Option (Layout × V.Ty × Name))
    (prover verifier : Role) (declKey : Key)
    (eventsAbs : List (ShapeEvent V × Bool))
    (instr : Instruction (ProtocolRaw V) (List Role)) (s : MatState V) :
    Except (List (ProgramRefusal V)) (MatState V) :=
  match instr with
  | .op k res (.compute roles o) ops =>
      if roles == [prover] then
        .ok (s.push (.op k res (.compute [prover] o) (ops.map (lookupVar s.envP))))
      else if roles == [verifier] then
        .ok (s.push (.op k res (.compute [verifier] o) (ops.map (lookupVar s.envV))))
      else if prover ∈ roles ∨ verifier ∈ roles then
        let opsP := ops.map (lookupVar s.envP)
        let opsV := ops.map (lookupVar s.envV)
        if opsP == ops && opsV == ops then
          .ok (s.push (.op k res (.compute roles o) ops))
        else if isPairRoles prover verifier roles then
          let (kP, s1) := s.freshKey
          let (resP, s2) := s1.freshNames res.length
          let (resV, s3) := s2.freshNames res.length
          let s4 := s3.push (.op kP resP (.compute [prover] o) opsP)
          let s5 := s4.push (.op k resV (.compute [verifier] o) opsV)
          .ok { s5 with
            envP := (res.zip resP) ++ s5.envP
            envV := (res.zip resV) ++ s5.envV
          }
        else
          .error (deployErr declKey .protocol)
      else
        .ok (s.push (.op k res (.compute roles o) ops))
  | .op k res (.narrow roles) ops =>
      if roles == [prover] then
        .ok (s.push (.op k res (.narrow [prover]) (ops.map (lookupVar s.envP))))
      else if roles == [verifier] then
        .ok (s.push (.op k res (.narrow [verifier]) (ops.map (lookupVar s.envV))))
      else if prover ∈ roles ∨ verifier ∈ roles then
        let opsP := ops.map (lookupVar s.envP)
        let opsV := ops.map (lookupVar s.envV)
        if opsP == ops && opsV == ops then
          .ok (s.push (.op k res (.narrow roles) ops))
        else if isPairRoles prover verifier roles then
          let (kP, s1) := s.freshKey
          let (resP, s2) := s1.freshNames res.length
          let (resV, s3) := s2.freshNames res.length
          let s4 := s3.push (.op kP resP (.narrow [prover]) opsP)
          let s5 := s4.push (.op k resV (.narrow [verifier]) opsV)
          .ok { s5 with
            envP := (res.zip resP) ++ s5.envP
            envV := (res.zip resV) ++ s5.envV
          }
        else
          .error (deployErr declKey .protocol)
      else
        .ok (s.push (.op k res (.narrow roles) ops))
  | .op k res (.event cls τ) ops =>
      match cls with
      | .flow kind giver getters =>
          if giver = prover ∧ getters = [verifier] then
            match ops, res with
            | [x], [y] =>
                let xP := lookupVar s.envP x
                let needAbs := lookupNeedAbs eventsAbs k
                match layoutOpt with
                | none =>
                    -- Constructed Core: retain flow, then absorb on both roles when `needAbs`.
                    let s1 := s.push (.op k [y] (.event (.flow kind prover [verifier]) τ) [xP])
                    if needAbs then
                      match findSuiteEncode a suite suiteUnitTy τ with
                      | none => .error (deployErr declKey .callee)
                      | some encRef =>
                          let lbl := msgLabel ⟨[], k⟩
                          let (stP', s2) := s1.emitAbsorb prover lbl encRef.hdr.key absorbKey s1.stP y
                          let (stV', s3) := s2.emitAbsorb verifier lbl encRef.hdr.key absorbKey s2.stV y
                          .ok { s3 with stP := stP', stV := stV' }
                    else
                      .ok s1
                | some (layout, layUnitTy, proofInName) =>
                    -- Serialized Core: eliminate flow into prover `write` + `seqConcat` and
                    -- verifier `read` (strictly BEFORE verifier `absorb` so stops match `d.run`).
                    match findLayoutWrite a layout.module layUnitTy τ,
                          findLayoutRead a layout.module layUnitTy τ with
                    | some wRef, some rRef => do
                        let s1 ←
                          if needAbs then
                            match findSuiteEncode a suite suiteUnitTy τ with
                            | none => .error (deployErr declKey .callee)
                            | some encRef =>
                                let lbl := msgLabel ⟨[], k⟩
                                let (stP', sA) := s.emitAbsorb prover lbl encRef.hdr.key absorbKey s.stP xP
                                .ok { sA with stP := stP' }
                          else .ok s
                        let (chunkP, s2) := s1.emitCompute1 [prover] (.call wRef.hdr.key) [xP]
                        let laySeqTy : V.Ty := .seq layUnitTy none
                        let (bufP', s3) := s2.emitCompute1 [prover]
                          (.owned .seqConcat [laySeqTy, laySeqTy] []) [s2.bufP, chunkP]
                        let (msgV, offV', s4) := s3.emitCompute2 [verifier]
                          (.call rRef.hdr.key) [proofInName, s3.offV]
                        let s5 ←
                          if needAbs then
                            match findSuiteEncode a suite suiteUnitTy τ with
                            | none => .error (deployErr declKey .callee)
                            | some encRef =>
                                let lbl := msgLabel ⟨[], k⟩
                                let (stV', sA) := s4.emitAbsorb verifier lbl encRef.hdr.key absorbKey s4.stV msgV
                                .ok { sA with stV := stV' }
                          else .ok s4
                        .ok { s5 with
                          bufP := bufP'
                          offV := offV'
                          envP := (y, xP) :: s5.envP
                          envV := (y, msgV) :: s5.envV
                        }
                    | _, _ => .error (deployErr declKey .callee)
            | _, _ => .error (deployErr declKey .operands)
          else if giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters then
            .ok (s.push (.op k res (.event cls τ) ops))
          else
            .error (deployErr declKey .protocol)
      | .given (.coin law) owner hearers =>
          if owner = verifier ∧ hearers = [prover] then
            match ops, res with
            | [], [y] =>
                match V.law law with
                | none => .error (deployErr declKey .row)
                | some sig =>
                    if sig.ins = [] ∧ sig.out = τ then
                      match findSuiteDerive enc a suite stateTy law [] τ with
                      | none => .error (deployErr declKey .callee)
                      | some derRef =>
                          let lbl := drawLabel ⟨[], k⟩
                          let (cP, stP', s1) := s.emitDerive prover lbl derRef.hdr.key s.stP
                          let (cV, stV', s2) := s1.emitDerive verifier lbl derRef.hdr.key s1.stV
                          .ok { s2 with
                            stP := stP'
                            stV := stV'
                            envP := (y, cP) :: s2.envP
                            envV := (y, cV) :: s2.envV
                          }
                    else
                      .error (deployErr declKey .operands)
            | _, _ => .error (deployErr declKey .operands)
          else if hearers = [] then
            let ops' := if owner = prover then ops.map (lookupVar s.envP)
                        else if owner = verifier then ops.map (lookupVar s.envV)
                        else ops
            .ok (s.push (.op k res (.event cls τ) ops'))
          else
            .error (deployErr declKey .protocol)
      | .given (.request _) owner hearers =>
          if (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) then
            let ops' := if owner = prover then ops.map (lookupVar s.envP)
                        else if owner = verifier then ops.map (lookupVar s.envV)
                        else ops
            .ok (s.push (.op k res (.event cls τ) ops'))
          else
            .error (deployErr declKey .protocol)
  | .guard k who cond why =>
      if who == [prover] then
        .ok (s.push (.guard k [prover] (lookupVar s.envP cond) why))
      else if who == [verifier] then
        .ok (s.push (.guard k [verifier] (lookupVar s.envV cond) why))
      else if prover ∈ who ∨ verifier ∈ who then
        let cP := lookupVar s.envP cond
        let cV := lookupVar s.envV cond
        if cP == cond && cV == cond then
          .ok (s.push (.guard k who cond why))
        else if isPairRoles prover verifier who then
          let (kP, s1) := s.freshKey
          let s2 := s1.push (.guard kP [prover] cP why)
          .ok (s2.push (.guard k [verifier] cV why))
        else
          .error (deployErr declKey .protocol)
      else
        .ok (s.push (.guard k who cond why))
  | _ => .error (deployErr declKey .protocol)

def materializeInstrs (enc : VocabEncoder V) (a : Admitted V) (suite : ModuleRef)
    (stateTy suiteUnitTy : V.Ty) (absorbKey : Key)
    (layoutOpt : Option (Layout × V.Ty × Name))
    (prover verifier : Role) (declKey : Key)
    (eventsAbs : List (ShapeEvent V × Bool)) :
    List (Instruction (ProtocolRaw V) (List Role)) → MatState V →
    Except (List (ProgramRefusal V)) (MatState V)
  | [], s => .ok s
  | i :: is, s => do
      let s1 ← materializeInstr enc a suite stateTy suiteUnitTy absorbKey layoutOpt
        prover verifier declKey eventsAbs i s
      materializeInstrs enc a suite stateTy suiteUnitTy absorbKey layoutOpt
        prover verifier declKey eventsAbs is s1

/-- Remap original protocol exit names using per-role variable maps, failing closed if a shared
output was split across `prover` and `verifier`. -/
def remapExit (prover verifier : Role) (declKey : Key)
    (envP envV : List (Name × Name)) :
    List (LTy V × Name) → Except (List (ProgramRefusal V)) (List Name)
  | [] => .ok []
  | (lt, x) :: rest => do
      let x' ←
        if prover ∈ lt.holders ∧ verifier ∈ lt.holders then
          if lookupVar envP x == x && lookupVar envV x == x then .ok x
          else .error (deployErr declKey .protocol)
        else if prover ∈ lt.holders then
          .ok (lookupVar envP x)
        else if verifier ∈ lt.holders then
          .ok (lookupVar envV x)
        else
          .ok x
      let rest' ← remapExit prover verifier declKey envP envV rest
      .ok (x' :: rest')

/-- Locate the erased entry protocol definition by key. -/
def findErasedProtocol (defs : List (Definition V)) (entryKey : Key) :
    Option (Nat × List (LTy V) × List (LTy V) × Region (ProtocolRaw V) (List Role)) :=
  defs.findSome? fun d =>
    match d with
    | .protocol k roles ins outs body => if k == entryKey then some (roles, ins, outs, body) else none
    | .fn .. => none

end

end MaterializeDetail

section
variable {V : Vocabulary}
open MaterializeDetail

/-- Shared core materializer parameterized by `serialize : Bool` (`false` = constructed Core,
`true` = serialized Core). Reuses `prepareDerivedBody` and all strict `Lookup` helpers directly. -/
def materializeCore (serialize : Bool) (enc : VocabEncoder V) (a : Admitted V)
    (declaration : Declaration) : Except (List (ProgramRefusal V)) (NamedProgram V) := do
  match a.program.findProtocol declaration.entry with
  | none => .error (deployErr declaration.key .callee)
  | some foundPair =>
      let entry := foundPair.1
      if !checkDeclarationSupported entry declaration then
        .error (deployErr declaration.key .protocol)
      else if !declaration.samples.isNone || !declaration.retry.isNone then
        .error (deployErr declaration.key .protocol)
      else
        match declaration.construction with
        | .derived suite sessionTag =>
            let prep ← prepareDerivedBody enc a declaration entry sessionTag
            let prover := prep.prover
            let verifier := prep.verifier
            let layout := prep.layout
            if serialize && (!layout.carry.isEmpty || !layout.recover.isEmpty) then
              .error (deployErr declaration.key .protocol)
            else
              match findSuiteStart a suite with
              | none => .error (deployErr declaration.key .callee)
              | some ⟨stateTy, startRef⟩ =>
                  if Ty.isLinear V stateTy then
                    .error (deployErr declaration.key .linear)
                  else
                    match findSuiteAbsorb a suite stateTy with
                    | none => .error (deployErr declaration.key .callee)
                    | some ⟨suiteUnitTy, absorbRef⟩ =>
                        if Ty.isLinear V suiteUnitTy then
                          .error (deployErr declaration.key .linear)
                        else
                          let erasedDefs := (erase a.program).definitions
                          let fnDefs := erasedDefs.filter fun d =>
                            match d with | .fn .. => true | .protocol .. => false
                          match findErasedProtocol erasedDefs declaration.entry with
                          | none => .error (deployErr declaration.key .callee)
                          | some (roles, origInsLTy, origOutsLTy, origRegion@(.mk origInNames origBody origExit)) =>
                              let events := entry.shape.events [] id
                              let eventsAbs := entry.shape.eventsWithAbsorb prover verifier [] id false
                              let origKeys := collectRegionKeys origRegion
                              let finKeyCandidate := finishGuardKey events
                              let baseKey := max (maxRegionKey origRegion) finKeyCandidate.number + 1
                              let baseName := maxRegionName origRegion + 1
                              let layoutInfo? ←
                                if serialize then
                                  match findLayoutUnit a layout.module with
                                  | none => .error (deployErr declaration.key .callee)
                                  | some ⟨layUnitTy, _⟩ => .ok (some (layout, layUnitTy, baseName))
                                else .ok none
                              let nextName0 := if serialize then baseName + 1 else baseName
                              let s0 : MatState V := {
                                nextKey := baseKey
                                nextName := nextName0
                                stP := 0
                                stV := 0
                                bufP := 0
                                offV := 0
                                envP := []
                                envV := []
                                revInstrs := []
                              }
                              -- Initialize dual transcript states with `prep.sessBytes`.
                              let (sessP, s1) := s0.emitCompute1 [prover]
                                (.literal bytesTy (prep.sessBytes.length :: prep.sessBytes)) []
                              let (stP0, s2) := s1.emitCompute1 [prover] (.call startRef.hdr.key) [sessP]
                              let (sessV, s3) := s2.emitCompute1 [verifier]
                                (.literal bytesTy (prep.sessBytes.length :: prep.sessBytes)) []
                              let (stV0, s4) := s3.emitCompute1 [verifier] (.call startRef.hdr.key) [sessV]
                              let s5 ← emitStmtAbsorptions a suite suiteUnitTy absorbRef.hdr.key
                                prover verifier declaration.key 0 (origInsLTy.zip origInNames)
                                { s4 with stP := stP0, stV := stV0 }
                              -- Initialize proof buffer & cursor in serialized Core.
                              let s6 :=
                                match layoutInfo? with
                                | none => s5
                                | some (_, layUnitTy, _) =>
                                    let emptyTy : V.Ty := .seq layUnitTy (some 0)
                                    let (emptySized, sA) := s5.emitCompute1 [prover] (.owned .make [emptyTy] []) []
                                    let (bufP0, sB) := sA.emitCompute1 [prover] (.owned .seqUnsized [emptyTy] []) [emptySized]
                                    let (offV0, sC) := sB.emitCompute1 [verifier] (.literal .nat [0]) []
                                    { sC with bufP := bufP0, offV := offV0 }
                              -- Materialize entry body instructions.
                              let s7 ← materializeInstrs enc a suite stateTy suiteUnitTy absorbRef.hdr.key
                                layoutInfo? prover verifier declaration.key eventsAbs origBody s6
                              -- Emit trailing-byte guard and finalize signature/exit.
                              let remExit ← remapExit prover verifier declaration.key s7.envP s7.envV
                                (origOutsLTy.zip origExit)
                              match layoutInfo? with
                              | none =>
                                  let matProto : Definition V :=
                                    .protocol declaration.entry roles origInsLTy origOutsLTy
                                      (.mk origInNames s7.revInstrs.reverse remExit)
                                  .ok ⟨fnDefs ++ [matProto]⟩
                              | some (_, layUnitTy, proofInName) =>
                                  let laySeqTy : V.Ty := .seq layUnitTy none
                                  let (lenV, s8) := s7.emitCompute1 [verifier]
                                    (.owned .seqLength [laySeqTy] []) [proofInName]
                                  let (eqV, s9) := s8.emitCompute1 [verifier]
                                    (.owned .natEqual [] []) [s8.offV, lenV]
                                  let (finKey, s10) :=
                                    if finKeyCandidate ∈ origKeys then s9.freshKey
                                    else (finKeyCandidate, s9)
                                  let s11 := s10.push (.guard finKey [verifier] eqV .reject)
                                  let newIns := ⟨laySeqTy, [verifier]⟩ :: origInsLTy
                                  let newOuts := ⟨laySeqTy, [prover]⟩ :: origOutsLTy
                                  let matProto : Definition V :=
                                    .protocol declaration.entry roles newIns newOuts
                                      (.mk (proofInName :: origInNames) s11.revInstrs.reverse
                                        (s11.bufP :: remExit))
                                  .ok ⟨fnDefs ++ [matProto]⟩
        | _ => .error (deployErr declaration.key .protocol)

/-- Materialize a `.derived` scheme declaration into a standalone, re-admittable **constructed Core**
`NamedProgram` (explicit `sessBytes`, dual role-local transcript states, flows retained with
`absorb`, public draws eliminated into synchronized `derive` calls). -/
def materializeConstructed (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration) :
    Except (List (ProgramRefusal V)) (NamedProgram V) :=
  materializeCore false enc a declaration

/-- Materialize a streaming `.derived` scheme declaration into a standalone, re-admittable
**serialized Core** `NamedProgram` (proof input `@[verifier]` first, proof output `@[prover]` first,
flows replaced by `write`/`read` + trailing-byte guard, zero inter-role flows and zero public
draws). -/
def materializeSerialized (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration) :
    Except (List (ProgramRefusal V)) (NamedProgram V) :=
  materializeCore true enc a declaration

end

end Zkc.Core
