module

public import Zkc.Formal.Interactive.HonestPairs

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.HonestPairs
open Core
open TableHalves (table)
variable {V : Vocabulary} {hs : Headers V} (rows : ScalarRows V) {n : Nat}
variable (sr : SumRow rows n) (vec : TableRestriction.Rows rows.scalarTy n)
variable (ds : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup)
local macro "vAt " n:term:max : term => `(⟨$n,rfl⟩)

/-- Read the one-call wrapper against its own predecessor table. -/
def checkMessage (k : Key) : Option {ref : Member hs.fns (messageHeader rows k n) //
    MessageLaw rows sr k (fun M => Defs.fnTable M ds _ ref)} := do
  let ref ← FunctionEntry.resolve hs.fns (messageHeader rows k n)
  let e := ds.functionEntry unique ref
  let .mk _ [.op _ _ (.call target) _] _ := eraseFn e.inputs e.body | none
  let ⟨callee,law⟩ ← (sumsReadback rows sr target).locate e.definitions e.distinct
  let body : Fn V e.earlier.fns (messageHeader rows k n) (.cons 0 .nil) :=
    .op ⟨0⟩ (.call callee) (.cons (vAt 0) .nil) (.cons 1 .nil) (.ret (.cons (vAt 1) .nil))
  let ⟨proved⟩ ← e.recognize ⟨_,body,rfl⟩ (MessageLaw rows sr k) (by
    intro M _ math x
    change (Defs.fnTable M e.definitions _ callee (.cons (Cube.flatten (n+1) x) .nil)).bind _ = _
    have h := law M math x
    dsimp only at h
    rw [h]
    rfl)
  return ⟨ref,proved⟩

def checkBind (k : Key) : Option {ref : Member hs.fns (TableRestriction.header rows.scalarTy k n) //
    TableRestriction.Law vec k (fun M => Defs.fnTable M ds _ ref)} := do
  let ref ← FunctionEntry.resolve hs.fns (TableRestriction.header rows.scalarTy k n)
  let e := ds.functionEntry unique ref
  let .mk _ [.op _ _ (.call target) _] _ := eraseFn e.inputs e.body | none
  let ⟨callee,law⟩ ← TableRestriction.check vec rows.free e.definitions e.distinct target
  let body : Fn V e.earlier.fns (TableRestriction.header rows.scalarTy k n) (.cons 0 (.cons 1 .nil)) :=
    .op ⟨0⟩ (.call callee) (.cons (vAt 0) (.cons (vAt 1) .nil)) (.cons 2 .nil) (.ret (.cons (vAt 2) .nil))
  let ⟨proved⟩ ← e.recognize ⟨_,body,rfl⟩ (TableRestriction.Law vec k) (by
    intro M _ math x r
    change (Defs.fnTable M e.definitions _ callee (.cons (Cube.flatten (n+1) x) (.cons r .nil))).bind _ = _
    have h := law M math x r
    dsimp only at h
    rw [h]
    rfl)
  return ⟨ref,proved⟩

abbrev Ops := ReductionRound.Members hs rows.scalarTy rows.pair (table rows.scalarTy (n+1)) (table rows.scalarTy n)

structure Members (ops : Ops (hs := hs) (n := n) rows) where
  messageKey : Key
  message : MessageLaw rows sr messageKey (fun M => localOp M (Defs.fnTable M ds) ops.sendValue)
  bindKey : Key
  bound : TableRestriction.Law vec bindKey (fun M => localOp M (Defs.fnTable M ds) ops.bindState)
  pair : ReductionRound.PairLaws rows ds ops

def readMembers (raw : ReductionRound.Operations V)
    (evaluation : ∀ k, FunctionReadback _ (rows.EvaluationLaw k)) :
    Option ((ops : Ops (hs := hs) (n := n) rows) × Members rows sr vec ds ops) := do
  let .call mk := raw.message | none
  let .call bk := raw.bindState | none
  let ⟨m,ml⟩ ← checkMessage rows sr ds unique mk
  let ⟨b,bl⟩ ← checkBind rows vec ds unique bk
  let ops : Ops rows := ⟨.call m,.call b,← ReductionRound.atType hs.fns raw.boundary [rows.pair] rows.scalarTy,
    ← ReductionRound.atType hs.fns raw.evaluate [rows.pair,rows.scalarTy] rows.scalarTy⟩
  let ⟨pl⟩ ← ReductionRound.certifyPairs rows ds unique ops evaluation
  return ⟨ops,⟨mk,ml,bk,bl,pl⟩⟩

#print axioms readMembers
end Zkc.Formal.Interactive.Sumcheck.HonestPairs
