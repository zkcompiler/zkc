module

public import Zkc.Formal.Interactive.RoundPrefix
public import Zkc.Formal.Interactive.PairReadback

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Core
variable {V : Vocabulary} (rows : ScalarRows V)

def endpoints (M : Model V) {msg : V.Ty} (aligned : msg = rows.pair) (m : M.Val msg) : rows.F M × rows.F M :=
  let tuple := cast (congrArg M.Val aligned) m
  (tuple.1,tuple.2.1)

structure PairLaws {hs : Headers V} (defs : Defs V hs) {msg state residual : V.Ty}
    (ops : Members hs rows.scalarTy msg state residual) where
  aligned : msg = rows.pair
  boundary : ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M → ∀ m,
    localOp M (Defs.fnTable M defs) ops.boundary (.cons m .nil) =
      .done (.cons ((endpoints rows M aligned m).1 + (endpoints rows M aligned m).2) .nil)
  evaluate : ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M → ∀ m r,
    localOp M (Defs.fnTable M defs) ops.evaluate (.cons m (.cons r .nil)) =
      .done (.cons (line (endpoints rows M aligned m) r) .nil)

def certifyPairs {hs : Headers V} (defs : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup)
    {msg state residual : V.Ty} (ops : Members hs rows.scalarTy msg state residual)
    (evaluation : ∀ k, FunctionReadback _ (rows.EvaluationLaw k)) : Option (PLift (PairLaws rows defs ops)) := do
  if same : msg = rows.pair then
    return ← show Option _ from by
      subst msg
      exact do
        let .call b := ops.boundary.print | none
        let .call e := ops.evaluate.print | none
        let ⟨boundary⟩ ← (rows.boundaryReadback b).atOperation defs unique ops.boundary
        let ⟨evaluate⟩ ← (evaluation e).atOperation defs unique ops.evaluate
        return ⟨⟨rfl,fun M _ math m => boundary M math m.1 m.2.1, fun M _ math m r => evaluate M math m.1 m.2.1 r⟩⟩
  else none

/-- Probability of correcting a false partial sum at this occurrence. The certificate
identifies both member meanings and the original block continuation in the linked caller. -/
theorem PairLaws.round_bound {hs : Headers V} {ds : Defs V hs} {key state point outs shape}
    {ref : Member hs.protocols (caller key state point rows.scalarTy outs shape)} {events : Events rows.scalarTy}
    (cert : Prefix ds ref events) (laws : PairLaws rows cert.entry.definitions cert.members)
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] (math : rows.Arithmetic M)
    (equalLaw : ScalarEquality.Law rows.scalarTy events.equal events.equalType M)
    {σ : Type} (K : Experiment (RSig M) σ) (s : σ) (points : List (rows.F M))
    (distinct : points.Nodup) (positive : 0 < points.length)
    (path : List Frame) (hidden : RV M 1 ⟨state,[0]⟩) (initialPoint : M.Val point)
    (claim : rows.F M) (honest : rows.F M × rows.F M) (wrong : claim ≠ honest.1+honest.2)
    (fresh : ∀ m s', K.Reaches (receive M cert.message (path ++ [.iteration cert.block.key cert.block.index])) s m s' →
      (endpoints rows M laws.aligned m).1 + (endpoints rows M laws.aligned m).2 = claim →
      Fresh K points positive (challenge M events (path ++ [.iteration cert.block.key cert.block.index])) s') :
    let inside := path ++ [.iteration cert.block.key cert.block.index]
    let sem := roleSem M 1 (Defs.fnTable M cert.entry.definitions) (Defs.rTable M cert.entry.definitions)
    let args := HList.cons hidden (.cons (hide M 1 ⟨point,[0,1]⟩ initialPoint)
      (.cons (hide M 1 ⟨rows.scalarTy,[0,1]⟩ claim) .nil))
    K.probability ((project 1 (body cert.members events point)).denote sem inside (Env.empty.extend names args)) s
      (fun (.cons _ (.cons next (.cons r .nil))) _ => decide
        (reveal M (r := 1) (a := ⟨rows.scalarTy,[0,1]⟩) (by simp) next =
          line honest (reveal M (r := 1) (a := ⟨rows.scalarTy,[0,1]⟩) (by simp) r))) ≤ roundCost 1 points := by
  dsimp only
  rw [verifier cert.members events point M _ _ _ _ equalLaw (laws.boundary M math) (laws.evaluate M math)]
  simp only [Experiment.probability,Process.map_eq_bind,Experiment.expect_bind,Experiment.expect]
  apply verifierRound_le K s points positive _ _ _ _ _ (line honest) claim 1 fresh
  intro m passed
  apply count_unique points distinct
  intro r s atR atS
  exact line_unique_collision _ honest r s (passed ▸ wrong) (of_decide_eq_true atR) (of_decide_eq_true atS)

#print axioms PairLaws.round_bound
end Zkc.Formal.Interactive.Sumcheck.ReductionRound
