module

public import Zkc.Formal.Interactive.PairReadback
public import Zkc.Formal.Interactive.RoundFamily
public import Zkc.Formal.Interactive.Quadratic

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.Gate
open Core ReductionRound
variable {V : Vocabulary} (rows : ScalarRows V)

abbrev fields : Tys V.TypeKey := .cons rows.scalarTy (.cons rows.scalarTy (.cons rows.scalarTy .nil))
abbrev message : V.Ty := .tuple (fields rows)
abbrev signature : RowSignature V.TypeKey V.RowKey := ⟨[message rows,rows.scalarTy],[rows.scalarTy],.pure⟩

def boundaryBody (fns : List (FnHeader V)) (k : Key) :
    Fn V fns (rows.scalarHeader k [message rows]) (Names.counting 0 _) :=
  let free : Tys.anyLinear V (fields rows) = false := by simp [Tys.anyLinear,Ty.isLinear,rows.free]
  .op ⟨0⟩ (.owned (.getTuple (fields rows) .head free)) (.cons ⟨0,rfl⟩ .nil) (.cons 1 .nil) <|
  .op ⟨1⟩ (.owned (.getTuple (fields rows) (.tail .head) free)) (.cons ⟨0,rfl⟩ .nil) (.cons 2 .nil) <|
  .op ⟨2⟩ (.row rows.add rows.signature rows.addType) (.cons ⟨1,rfl⟩ (.cons ⟨2,rfl⟩ .nil)) (.cons 3 .nil) <|
  .ret (.cons ⟨3,rfl⟩ .nil)

def Boundary (k : Key) (run : FunctionMeaning (rows.scalarHeader k [message rows])) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M → ∀ m : M.Val (message rows),
    run M (.cons m .nil) = .done (.cons (m.1+m.2.1) .nil)

def boundaryReadback (k : Key) : FunctionReadback _ (Boundary rows k) where
  inputs := Names.counting 0 _
  body fns := boundaryBody rows fns k
  armed _ := rfl
  holds := by
    intro fns tables M _ math m
    change (localOp M (tables M) (.row rows.add rows.signature rows.addType) (.cons m.1 (.cons m.2.1 .nil))).bind _ = _
    simp [localOp,math.add,Process.bind]
    rfl

/-- The deployment supplies a polynomial interpretation of its declared project row. -/
structure Evaluation (key : V.RowKey) (bound : V.row key = some (signature rows))
    (M : Model V) [Lean.Grind.Field (rows.F M)] where
  polynomial : M.Val (message rows) → Quadratic (rows.F M)
  ends : ∀ m, (polynomial m).boundary = m.1+m.2.1
  apply : ∀ m r, M.apply key (signature rows) bound (.cons m (.cons r .nil)) =
    some (.cons ((polynomial m).eval r) .nil)

def triple (M : Model V) {msg : V.Ty} (same : msg = message rows) (m : M.Val msg) : M.Val (message rows) :=
  cast (congrArg M.Val same) m

structure Laws (key : V.RowKey) (bound : V.row key = some (signature rows))
    {hs : Headers V} (defs : Defs V hs) {msg st residual} (ops : Members hs rows.scalarTy msg st residual) : Prop where
  same : msg = message rows
  ends : ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M → ∀ m,
    localOp M (Defs.fnTable M defs) ops.boundary (.cons m .nil) =
      .done (.cons ((triple rows M same m).1 + (triple rows M same m).2.1) .nil)
  atPoint : ∀ (M : Model V) [Lean.Grind.Field (rows.F M)] (model : Evaluation rows key bound M) m r,
    localOp M (Defs.fnTable M defs) ops.evaluate (.cons m (.cons r .nil)) =
      .done (.cons ((model.polynomial (triple rows M same m)).eval r) .nil)

def check (key : V.RowKey) (bound : V.row key = some (signature rows)) {hs : Headers V}
    (defs : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup) {msg st residual} (ops : Members hs rows.scalarTy msg st residual) :
    Option (PLift (Laws rows key bound defs ops)) := do
  if same : msg = message rows then
    return ← show Option _ from by
      subst msg
      exact do
        let .call b := ops.boundary.print | none
        let ⟨ends⟩ ← (boundaryReadback rows b).atOperation defs unique ops.boundary
        let wanted := LocalOp.row (fns := hs.fns) key (signature rows) bound
        let ⟨equal⟩ ← ops.evaluate.same? wanted unique
        return ⟨rfl,ends,by
          intro M _ model m r
          rw [equal]
          simp [wanted,localOp,model.apply,triple]⟩
  else none

variable {hs : Headers V} {ds : Defs V hs} {msg st residual} {ops : Members hs rows.scalarTy msg st residual}
variable {key : V.RowKey} {bound : V.row key = some (signature rows)}

def Laws.interpretOn (laws : Laws rows key bound ds ops) (M : Model V) [Lean.Grind.Field (rows.F M)]
    [DecidableEq (rows.F M)] (math : rows.Arithmetic M) (model : Evaluation rows key bound M)
    (q : Claims (rows.F M)) {ι : Type} (depth : ι → Nat) (honest : ∀ i, q.State (depth i + 1) → Quadratic (rows.F M))
    (sum : ∀ i x, q.value (depth i + 1) x = (honest i x).boundary)
    (restricted : ∀ i x r, q.value (depth i) (q.restrict (depth i) x r) = (honest i x).eval r)
    (points : List (rows.F M)) (distinct : points.Nodup)
    (collisions : CollisionBound (Quadratic.boundary (F := rows.F M)) Quadratic.eval 2 := Quadratic.collisions) :
    RoundInterpretationOn M (Defs.fnTable M ds) q points 2 ops depth where
  boundary m := (model.polynomial (triple rows M laws.same m)).boundary
  evaluate m := (model.polynomial (triple rows M laws.same m)).eval
  ends m := (laws.ends M math m).trans (by rw [model.ends])
  atPoint := laws.atPoint M model
  roots i x m wrong := by
    simp only [restricted i]
    apply collisions _ _ _ _ distinct
    rwa [← sum i]

/-- The uniform instance remains available for claims indexed by all natural depths. -/
abbrev Laws.interpret (laws : Laws rows key bound ds ops) (M : Model V) [Lean.Grind.Field (rows.F M)]
    [DecidableEq (rows.F M)] (math : rows.Arithmetic M) (model : Evaluation rows key bound M)
    (q : Claims (rows.F M)) :=
  Laws.interpretOn rows laws M math model q (id : Nat → Nat)

variable {Γ : Ctx (LTy V)} {events : Events rows.scalarTy} {running : Var Γ (shared rows.scalarTy)}
variable {outs : List (LTy V)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat}

theorem sound (rounds : Sequence hs events st running term count)
    (checked : rounds.AllMembers (fun ops => Laws rows key bound ds ops)) (M : Model V)
    [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] (math : rows.Arithmetic M)
    (model : Evaluation rows key bound M) (equalLaw : ScalarEquality.Law rows.scalarTy events.equal events.equalType M)
    (q : Claims (rows.F M)) (honest : ∀ n : Fin count, q.State (n.val+1) → Quadratic (rows.F M))
    (sum : ∀ n x, q.value (n.val+1) x = (honest n x).boundary)
    (restricted : ∀ n x r, q.value n.val (q.restrict n.val x r) = (honest n x).eval r)
    {σ : Type} (K : Experiment (RSig M) σ) (points : List (rows.F M)) (distinct : points.Nodup) (positive : 0 < points.length)
    (fresh : ∀ path key s, Fresh K points positive (challenge M events path key) s) (path : List Frame)
    (env : Env (RV M 1) Γ) (s : σ) (x : q.State count)
    (wrong : Sequence.scalar M env running ≠ q.value count x) :
    K.probability (rounds.collect M (Defs.fnTable M ds) (Defs.rTable M ds) path env) s
      (fun (_,rs,value) _ => decide (q.evaluate count x rs = some value)) ≤ (count : Mass) * roundCost 2 points := by
  apply rounds.sound M _ _ K q _ path _ _ env s x wrong
  · exact Mass.mul_nonneg Mass.natCast_nonneg (Mass.le_of_lt (Mass.inv_pos.mpr (Mass.natCast_pos.mpr positive)))
  · exact rounds.boundsOfMembers _ checked M _ _ _ points positive 2
      (fun _ laws => Laws.interpretOn rows laws M math model q Fin.val honest sum restricted points distinct) equalLaw K fresh path

#print axioms sound
#print axioms check
#print axioms Laws.interpret
end Zkc.Formal.Interactive.Sumcheck.Gate
