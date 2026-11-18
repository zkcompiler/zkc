module

public import Zkc.Formal.Interactive.HonestReduction
public import Zkc.Formal.Interactive.TableVerifier
public import Zkc.Formal.Interactive.TableEvaluation

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.HonestPairs
open Core ReductionRound JointEntry
open TableHalves (table)
open PointReturn (point ports)
variable {V : Vocabulary} {hs : Headers V} (rows : ScalarRows V)
variable (sums : (n : Nat) → SumRow rows n) (vectors : (n : Nat) → TableRestriction.Rows rows.scalarTy n)
variable (events : Events rows.scalarTy)

def args (M : Model V) (n : Nat) (xs : List (rows.F M)) (v : rows.F M) :
    HList (LVal M) [shared (table rows.scalarTy n),shared rows.scalarTy] := .cons xs (.cons v .nil)

def reduceArgs (M : Model V) (n : Nat) (xs : List (rows.F M)) (v : rows.F M) :
    HList (LVal M) (inputs (table rows.scalarTy n) (.seq rows.scalarTy (some 0)) rows.scalarTy) := .cons xs (.cons [] (.cons v .nil))

variable (ds : Defs V hs) {n : Nat} {red eval : Key} {shape : Shape V}
variable (callee : Member hs.protocols (TableVerifier.reduction rows.scalarTy n red shape))
variable (evaluate : Member hs.fns (TableEvaluation.header rows.scalarTy eval n (0+n)))

def CalleeReturns : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)],
    Arithmetic rows sums vectors events n M → ∀ path (x : Cube (rows.F M) n),
    Returns (Defs.gTable M ds _ callee path (reduceArgs rows M n (Cube.flatten n x) (Cube.sum n x)))
      (fun out => ∃ rs v, Cube.evaluate n x rs = some v ∧ out.1 = fullResult M rs v)

def checkCallee (distinct : hs.keys.Nodup) (evaluation : ∀ k, FunctionReadback _ (rows.EvaluationLaw k)) :
    Option (PLift (CalleeReturns rows sums vectors events ds callee)) := do
  let entry := JointEntry.locate ds distinct callee
  let ns := initialNames (table rows.scalarTy n) rows.scalarTy 0
  if matchNames : entry.candidate.1.toList = ns.toList then
    have eqNames : entry.candidate.1 = ns := by
      have h := Names.ofList_toList entry.candidate.1
      rw [matchNames,Names.ofList_toList] at h
      exact (Option.some.inj h).symm
    let actual : Prot V entry.earlier (TableVerifier.reduction rows.scalarTy n red shape) ns := eqNames ▸ entry.candidate.2.1
    let st : Var (Ctx.empty.extend ns) (⟨table rows.scalarTy n,[0]⟩ : LTy V) := ⟨0,rfl⟩
    let ⟨law⟩ ← readReduction rows sums vectors events entry.definitions entry.distinct evaluation n st
      (initialPoint (table rows.scalarTy n) rows.scalarTy 0) (initialClaim (table rows.scalarTy n) rows.scalarTy 0) [] actual
    return ⟨by
      intro M _ _ math path x
      apply (returns_map _ Prod.fst (fun vs => ∃ rs v, Cube.evaluate n x rs = some v ∧ vs = fullResult M rs v)).mp
      rw [entry.meaning]
      have transport {as bs : Names (inputs (table rows.scalarTy n) (.seq rows.scalarTy (some 0)) rows.scalarTy)}
          (eq : as = bs) (term : Prot V entry.earlier (TableVerifier.reduction rows.scalarTy n red shape) as)
          (vs : HList (LVal M) _) :
          term.denote (protocolSem M (Defs.fnTable M entry.definitions) (Defs.gTable M entry.definitions))
            path (Env.empty.extend as vs) =
          (eq ▸ term : Prot V entry.earlier (TableVerifier.reduction rows.scalarTy n red shape) bs).denote
            (protocolSem M (Defs.fnTable M entry.definitions) (Defs.gTable M entry.definitions))
            path (Env.empty.extend bs vs) := by cases eq; rfl
      rw [transport eqNames]
      exact law M math path (Env.empty.extend ns (reduceArgs rows M n (Cube.flatten n x) (Cube.sum n x))) x rfl rfl rfl⟩
  else none

def RootLaw (p : Core.Typed V) {key : Key} {s : Shape V}
    (root : Member p.headers.protocols (TableVerifier.header rows.scalarTy n key s)) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)],
    Arithmetic rows sums vectors events n M → ∀ path (x : Cube (rows.F M) n) (claim : rows.F M),
    claim = (Cube.flatten n x).sum →
    Returns (protocolMeaning M p root path (args rows M n (Cube.flatten n x) claim)) (fun out => out.1 = .nil)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem callerReturns (key : Key) (sh : Shape V) (law : CalleeReturns rows sums vectors events ds callee)
    (tableLaw : TableEvaluation.Law vectors eval n (0+n) (fun M => Defs.fnTable M ds _ evaluate))
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)]
    (math : Arithmetic rows sums vectors events n M) (path : List Frame) (x : Cube (rows.F M) n) :
    Returns ((TableVerifier.body events callee evaluate key sh).denote
      (protocolSem M (Defs.fnTable M ds) (Defs.gTable M ds)) path
      (Env.empty.extend (.cons 0 (.cons 1 .nil)) (args rows M n (Cube.flatten n x) (Cube.sum n x))))
      (fun vs => vs = .nil) := by
  let inner := path ++ [.application ⟨1⟩]
  let run := Defs.gTable M ds _ callee inner (reduceArgs rows M n (Cube.flatten n x) (Cube.sum n x))
  change Returns (((mapG M peerMap.to run).map _).bind _) _
  rw [Process.bind_map]
  apply (Process.every_bind ..).mpr
  apply Process.every_mono _ _ _ (fun _ h => h) (returns_mapG M peerMap.to run _ (law M math inner x))
  rintro ⟨_,record⟩ ⟨rs,v,ev,rfl⟩
  have computed := tableLaw M math.vector x rs v ev
  dsimp only at computed
  change Returns (((liftLocal _ (Defs.fnTable M ds _ evaluate (.cons (Cube.flatten n x) (.cons rs .nil)))).map _).bind _) _
  rw [computed]
  have equality : localOp M (Defs.fnTable M ds) (.row events.equal _ events.equalType)
      (.cons v (.cons v .nil)) = .done (.cons true .nil) := by simp [localOp,math.equal v v]
  change Returns (((liftLocal _ (localOp M (Defs.fnTable M ds) (.row events.equal _ events.equalType)
    (.cons v (.cons v .nil)))).map _).bind _) _
  rw [equality]
  rfl

/-- A successful readback carries the every-reply return theorem on the admitted joint root. -/
def certify (p : Core.Typed V) (key red eval : Key) (n : Nat)
    (evaluation : ∀ k, FunctionReadback _ (rows.EvaluationLaw k)) :
    Option ((sh : Shape V) × (root : Member p.headers.protocols (TableVerifier.header rows.scalarTy n key sh)) ×'
      RootLaw rows sums vectors events p root) := do
  let ⟨sh,root⟩ ← ProtocolEntry.locatePorts p.headers key 2 [shared (table rows.scalarTy n),shared rows.scalarTy] []
  let entry := JointEntry.locate p.defs p.distinct (show Member _ (TableVerifier.header rows.scalarTy n key sh) from root)
  let ⟨rs,ref⟩ ← ProtocolEntry.locatePorts entry.earlier red 2 (inputs (table rows.scalarTy n) (.seq rows.scalarTy (some 0)) rows.scalarTy)
    (ports rows.scalarTy (table rows.scalarTy 0) (0+n))
  let ⟨law⟩ ← checkCallee rows sums vectors events entry.definitions
    (show Member _ (TableVerifier.reduction rows.scalarTy n red rs) from ref) entry.distinct evaluation
  let ⟨ev,tableLaw⟩ ← TableEvaluation.check (V := V) (t := rows.scalarTy) rows.free vectors entry.definitions (List.nodup_append.mp entry.distinct).1 eval n (0+n)
  let candidate := TableVerifier.witness events ref ev key sh
  if same : eraseProtocol entry.candidate.1 entry.candidate.2.1 = eraseProtocol candidate.1 candidate.2.1 then
    have eq := ProtocolEntry.eq_of_erase_eq entry.distinct entry.candidate candidate same
    return ⟨sh,root,by
      intro M _ _ math path x claim valid
      rw [Cube.sum_flatten] at valid
      subst claim
      apply (returns_map (protocolMeaning M p root path (args rows M n (Cube.flatten n x) (Cube.sum n x))) Prod.fst (fun vs : HList (LVal M) [] => vs = .nil)).mp
      change Returns ((Defs.gTable M p.defs _ root path _).map Prod.fst) _
      rw [entry.meaning,eq]
      exact callerReturns rows sums vectors events entry.definitions ref ev key sh law tableLaw M math path x⟩
  else none

#print axioms certify
end Zkc.Formal.Interactive.Sumcheck.HonestPairs
