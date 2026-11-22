import ZkcFormalTests.Reuse.Common

namespace ZkcFormalTests.Reuse.Manual
open Zkc.Core Zkc.Frontend ZkcFormal.Interactive.Sumcheck ReductionRound
open SourcePairMembers (sourceRows)

-- This file passes between the meaning of a program and its tables by definitional unfolding.
unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning


private def pairOps (b : Zkc.Vocabulary.Project.Bindings) (i : Nat) : Operations b.vocabulary :=
  let message := if i == 0 then 13 else 15 + 8*i
  let bind := if i == 0 then 16 else 17 + 8*i
  ⟨.call ⟨message⟩,.call ⟨15⟩,.call ⟨bind⟩,.call ⟨22⟩⟩

private def gateOps (b : Zkc.Vocabulary.Project.Bindings) (i : Nat) : Operations b.vocabulary :=
  let row (name : String) := Emit.primitiveName ⟨name,#[.type (StandardNames.fieldType .bls12381Fr),.nat (3-i)]⟩
  ⟨.row (.inr (row "circuit.gate_message")),.call ⟨22⟩,.row (.inr (row "circuit.gate_bind")),.row (.inr gateRow)⟩

private def block {V : Zkc.Core.Vocabulary} {hs : Headers V} {t : V.Ty} {Γ : Ctx (LTy V)} {mid : List (LTy V)}
    (unique : (hs.fns.map (·.key)).Nodup) (events : Events t) (ops : Operations V) (offset i : Nat) (state : V.Ty)
    (claim : Var Γ (shared t)) (inside : Term (protocolDialect V hs) Γ mid) :
    Option (Located state events claim inside) := do
  let ⟨msg,residual,members⟩ ← ops.members hs state t
  let sites := fun j => Key.mk (offset+12*i+j)
  if types : mid = outputs residual t then
    let ⟨same⟩ ← StraightLine.compare (BodyAnalysis.roleChecks 1) (BodyAnalysis.roleChecks_lawful unique)
      [(2,claim.name)] (project 1 (body members events (emptyPoint t) sites)) (project 1 (types ▸ inside))
    return ⟨msg,residual,members,sites,types,same⟩
  else none

/-- Supply the operation references and the iteration-to-site mapping for these emitted loops. -/
private def rounds {V : Zkc.Core.Vocabulary} {hs : Headers V} {t : V.Ty}
    (unique : (hs.fns.map (·.key)).Nodup) (events : Events t) (ops : Nat → Operations V) (offset : Nat) :
    (n i : Nat) → {Γ : Ctx (LTy V)} → {outs : List (LTy V)} → (state : V.Ty) → (claim : Var Γ (shared t)) →
    (term : Term (protocolDialect V hs) Γ outs) → Option (Sequence hs events state claim term n)
  | 0, _, _, _, _, _, term => some (.done term)
  | n+1, i, _, _, state, claim, .block key index inside ns rest => do
    guard (index == i && key.number == offset+12*i+11)
    let round ← block unique events (ops i) offset i state claim inside
    let binders ← readResults _ ns round.residual t round.types
    let tail ← rounds unique events ops offset n (i+1) round.residual binders.claim rest
    return .more round key index ns binders tail
  | _+1, _, _, _, _, _, _ => none

private def reduction {V : Zkc.Core.Vocabulary} (p : Zkc.Core.Typed V) (red : Key) (state t residual : V.Ty)
    (n : Nat) (events : Events t) (ops : Nat → Operations V) (offset : Nat := 0) : Option (Linked p red state t residual 0 n events) := do
  let ⟨shape,ref⟩ ← ProtocolEntry.locatePorts p.headers red 2 (inputs state (.seq t (some 0)) t) (PointReturn.ports t residual (0+n))
  let entry := p.defs.protocolEntry p.distinct (show Member _ (ReductionRound.reduction red state t residual 0 n shape) from ref)
  let source ← entry.atInputs (initialNames state t 0)
  let unique := (List.nodup_append.mp entry.distinct).1
  let trace ← rounds unique events ops offset n 0 state (initialClaim state t 0) source.body
  let ⟨exit⟩ ← PointReturn.checkReduction unique trace (initialPoint state t 0) []
  return ⟨shape,ref,entry,source,trace,exit⟩

def sumcheck (c : SourceProtocolRoots.ReadbackFixture) (affine : Bool) (offset : Nat := 0) : Option (SumEndpoint c ⟨7⟩ ⟨94⟩) := do
  let p := c.evidence.admitted.program
  let b := c.emission.bindings
  let rows := sourceRows b
  let t := rows.scalarTy
  let ⟨shape,root⟩ ← ProtocolEntry.locatePorts p.headers ⟨c.id⟩ 2 [shared (TableHalves.table t 10),shared t] []
  let entry := p.defs.protocolEntry p.distinct (show Member _ (TableVerifier.header t 10 ⟨c.id⟩ shape) from root)
  let trace ← reduction (earlier entry) ⟨7⟩ (TableHalves.table t 10) t (TableHalves.table t 0) 10 (events b) (pairOps b) offset
  let ⟨members⟩ ← checkPairSequence rows trace.entry.definitions (List.nodup_append.mp trace.entry.distinct).1
    (implementation rows affine) trace.rounds
  let ⟨eval,tableLaw⟩ ← TableEvaluation.check (V := b.vocabulary) (t := t) rows.free (vectors b) entry.definitions (List.nodup_append.mp entry.distinct).1 ⟨94⟩ 10 (0+10)
  let target := TableVerifier.witness (events b) trace.ref eval ⟨c.id⟩ shape
  let ⟨meaning⟩ ← entry.recognize 1 target (fun run => ∀ M path inputs, run M path inputs = target.meaning entry.definitions 1 M path inputs)
    (fun _ _ _ => rfl)
  return ⟨shape,root,entry,trace,members,eval,tableLaw,meaning⟩

def gkr (c : SourceProtocolRoots.CheckedRoot) (args : List Name) (loopKey : Key) :
    Option (GateEndpoint c.emission.bindings c.evidence.admitted.program ⟨c.id⟩ ⟨17⟩ ⟨11⟩ loopKey args) := do
  let p := c.evidence.admitted.program
  let b := c.emission.bindings
  let [⟨hdr,root⟩] := Member.withKey ProtocolHeader.key ⟨c.id⟩ p.headers.protocols | none
  if selected : hdr.key = ⟨c.id⟩ then
    let entry := p.defs.protocolEntry p.distinct root
    let [⟨callee,_⟩] := Member.withKey ProtocolHeader.key ⟨17⟩ entry.earlier.protocols | none
    let [st,_,_] := callee.ins | none
    let [_,_,out] := callee.outs | none
    let trace ← reduction (earlier entry) ⟨17⟩ st.ty (sourceRows b).scalarTy out.ty 4 (events b) (gateOps b)
    let ⟨found⟩ ← OperationSite.read (BodyAnalysis.roleChecks 1) (BodyAnalysis.roleChecks_lawful (List.nodup_append.mp entry.distinct).1)
      ⟨11⟩ trace.application args (loopRoute 4 loopKey 4 7) (project 1 entry.body)
    return ← installGate root selected ⟨entry,trace,found⟩
  else none

end ZkcFormalTests.Reuse.Manual
