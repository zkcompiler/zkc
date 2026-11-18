module

public import Zkc.Core.Facts.Domains.Rules
public import Zkc.Core.Facts.Contracts.Stored
public import Zkc.Core.Facts.Contracts.LocalOperations
public import Zkc.Core.Facts.Local

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary}

/-- Checked clauses carry the translation certificate for their original declaration. -/
abbrev CheckedHeader (h : FnHeader V) :=
  { c : Contract (LocalRaw V) // HeaderContracts.translate h.ins h.outs h.summary = some c }

/-- Report the original clause as soon as its reader fails. On success the proof
records the full translation without a second traversal. -/
def readClauses (ctx : List V.Ty) : (source : List (HeaderClause V)) →
    Except (HeaderClause V) {cs // source.mapM (HeaderContracts.checkClause ctx) = some cs}
  | [] => .ok ⟨[], rfl⟩
  | q :: qs => do
    match one : HeaderContracts.checkClause ctx q with
    | none => .error q
    | some c =>
      let ⟨rest, more⟩ ← readClauses ctx qs
      return ⟨c :: rest, by simp [List.mapM_cons, one, more]⟩

def readHeader (h : FnHeader V) : Except (HeaderClause V) (CheckedHeader h) := do
  let ⟨pre, before⟩ ← readClauses h.ins h.summary.requires
  let ⟨post, after_⟩ ← readClauses (h.ins ++ h.outs) h.summary.ensures
  return ⟨⟨pre, post⟩, by simp [HeaderContracts.translate, before, after_]⟩

private theorem readClauses_complete (ctx : List V.Ty) :
    ∀ (source : List (HeaderClause V)) {cs} (ok : source.mapM (HeaderContracts.checkClause ctx) = some cs),
      readClauses ctx source = .ok ⟨cs, ok⟩
  | [], _, ok => by cases ok; rfl
  | q :: qs, _, ok => by
    obtain ⟨c, one, rest, more, rfl⟩ := (by
      simpa only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] using ok)
    unfold readClauses
    split
    · simp_all
    · rename_i c' eq
      obtain rfl := Option.some.inj (eq.symm.trans one)
      rw [readClauses_complete ctx qs more]
      rfl

/-- Every successful specification result is returned by the diagnostic reader. -/
theorem readHeader_complete (h : FnHeader V) {c} (ok : HeaderContracts.translate h.ins h.outs h.summary = some c) :
    readHeader h = .ok ⟨c, ok⟩ := by
  obtain ⟨pre, before, post, after_, rfl⟩ := (by simpa only [HeaderContracts.translate,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] using ok)
  unfold readHeader
  rw [readClauses_complete _ _ before, readClauses_complete _ _ after_]
  rfl

inductive HeaderError (V : Vocabulary) where
  | duplicateKeys
  | invalidSummary (key : Key) (source : HeaderClause V)
  deriving DecidableEq

structure FunctionContracts (hs : List (FnHeader V)) where
  entries : HList CheckedHeader hs
  distinct : (hs.map (·.key)).Nodup

def checkHeaders : (hs : List (FnHeader V)) → Except (HeaderError V) (HList CheckedHeader hs)
  | [] => .ok .nil
  | h :: hs => do
    let checked ← (readHeader h).mapError (.invalidSummary h.key)
    return .cons checked (← checkHeaders hs)

def FunctionContracts.check (hs : List (FnHeader V)) : Except (HeaderError V) (FunctionContracts hs) :=
  if keys : (hs.map (·.key)).Nodup then (checkHeaders hs).map (fun checked => ⟨checked,keys⟩)
  else .error .duplicateKeys

/-- Nested operands of builtin conditions apply a single-result operation to selected input positions. -/
def argumentExpressions {Raw : Type} : List Nat → Exprs Raw
  | [] => .nil
  | p :: ps => .cons (.arg p) (argumentExpressions ps)

def builtinOperand : Operand (LocalRaw V) → Expr (LocalRaw V)
  | .arg n => .arg n
  | .apply w ps => .apply w (argumentExpressions ps) 0

/-- Builtin numeric operands are naturals. The operation catalog includes sequence lengths
and the predicate row of a restricted vocabulary operation. -/
def builtinClause (q : Requirement (LocalRaw V)) : ContractClause (LocalRaw V) :=
  HeaderContracts.clauseWith (m := Id) builtinOperand builtinOperand q

namespace LocalIndex
def atIteration (n : Nat) : Expr (LocalRaw V) := .apply (.literal .nat [n]) .nil 0
def fromCount : Expr (LocalRaw V) := .arg 0
def next : Expr (LocalRaw V) := .apply (.owned .natAdd [] []) (.cons (.arg 0) (.cons (atIteration 1) .nil)) 0

end LocalIndex

namespace FunctionContracts
variable {hs : List (FnHeader V)}

def entry {h : FnHeader V} (contracts : FunctionContracts hs) (member : Member hs h) : CheckedHeader h :=
  let rec get {items : List (FnHeader V)} {header : FnHeader V} :
      HList CheckedHeader items → Member items header → CheckedHeader header
    | .cons v _, .head => v
    | .cons _ vs, .tail m => get vs m
  get contracts.entries member

/-- Calls read only from a uniquely resolved, checked header. -/
def call? (contracts : FunctionContracts hs) (key : Key) : Option (Contract (LocalRaw V)) :=
  match Member.withKey (·.key) key hs with
  | [⟨_,member⟩] => some (contracts.entry member).val
  | _ => none

def contract (contracts : FunctionContracts hs) : LocalRaw V → Contract (LocalRaw V)
  | .call key => (contracts.call? key).getD ⟨[⟨.apply (.literal .bool [0]) .nil 0, none⟩],[]⟩
  | raw => ⟨((localOpFacts hs).requires raw).map builtinClause, ((localOpFacts hs).ensures raw).map builtinClause⟩

/-- Test the resolved callee's own preconditions. For builtins, emptiness can be
read directly from the requirements before constructing assertion syntax. -/
def eligible (contracts : FunctionContracts hs) {ins outs} (op : LocalOp V hs ins outs)
    (raw : LocalRaw V) : Bool :=
  !op.canStop && match op with
    | .call member => (contracts.entry member).val.preconditions.isEmpty
    | _ => ((localOpFacts hs).requires raw).isEmpty

/-- Stored summaries may mention only table-stable operations. An expression used in a body
can also call a resolved, non-stopping function with no preconditions. -/
def assertable (contracts : FunctionContracts hs) (raw : LocalRaw V) : Bool :=
  match resolveLocal hs raw with
  | some ⟨_,_,typed⟩ => contracts.eligible typed raw
  | none => false

/-- Use the input and output signature recovered by the same admission lookup. -/
def assertionArity (contracts : FunctionContracts hs) (op : LocalRaw V) : Option Nat :=
  match resolveLocal hs op with
  | some ⟨_, outs, typed⟩ =>
    if contracts.eligible typed op then some outs.length else none
  | none => none

def rules (contracts : FunctionContracts hs) : Rules (localDialect V hs) (LocalRaw V) where
  written := LocalOp.print
  shared op := !op.canStop
  commutes := LocalRaw.commutes
  place := localPlace
  results := localResultCount hs
  contract := contracts.contract
  assertable := contracts.assertable
  assertionArity := contracts.assertionArity
  assertionArity_eq op := by
    unfold assertionArity assertable localResultCount
    cases resolveLocal hs op with
    | none => rfl
    | some sig => obtain ⟨_, _, _⟩ := sig; rfl
  numbered _ := true
  indexAt _ n := some (LocalIndex.atIteration n)
  indexFromCount _ := some LocalIndex.fromCount
  indexNext _ := some LocalIndex.next

end FunctionContracts
end Zkc.Core.BodyAnalysis
