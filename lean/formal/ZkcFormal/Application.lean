module

public import ZkcFormal.ProcessJudgment
public import Zkc.Core.Meaning.Role
public import Zkc.Core.Meaning.Fold
public import Zkc.Core.Evidence.FunctionEntry

@[expose] public section
set_option autoImplicit false

/-! Renaming the roles of a process and of a judgment of its effects. -/

namespace Zkc.Core
variable {V : Vocabulary} {M : Model V}

/-- An effect with its peers renamed, as `mapR` renames them. -/
def renameOp (ρ : Role → Role) : ROp M → ROp M
  | .give kind getters at_ τ x => .give kind (getters.map ρ) at_ τ x
  | .get kind giver at_ τ => .get kind (ρ giver) at_ τ
  | .own kind hearers at_ ins payload τ => .own kind (hearers.map ρ) at_ ins payload τ
  | .hear kind owner at_ τ => .hear kind (ρ owner) at_ τ
  | .begin at_ => .begin at_
  | .settle at_ => .settle at_

/-- A function of the replies of an effect, as a function of the replies of the renamed effect:
the replies are the same. -/
def carryReply {L : Type} (ρ : Role → Role) :
    (op : ROp M) → ((RSig M).Reply op → L) → (RSig M).Reply (renameOp ρ op) → L
  | .give .., f => f
  | .get .., f => f
  | .own .., f => f
  | .hear .., f => f
  | .begin _, f => f
  | .settle _, f => f

/-- A judgment with the peers of every effect renamed before it reads them: what it says of an
effect is what the judgment says of the renamed effect. It is written by the constructor of the
effect, so that at a known effect a text that unfolds it (`intro`, `obtain`) is left with the
judgment of the renamed effect on the same replies, and with no word of this module in its
goal. -/
def ProcessJudgment.renamed {L : Type} (j : ProcessJudgment (RSig M) L) (ρ : Role → Role) :
    ProcessJudgment (RSig M) L :=
  ⟨fun op => match op with
    | .give kind getters at_ τ x => fun next => j.node (.give kind (getters.map ρ) at_ τ x) next
    | .get kind giver at_ τ => fun next => j.node (.get kind (ρ giver) at_ τ) next
    | .own kind hearers at_ ins payload τ => fun next =>
        j.node (.own kind (hearers.map ρ) at_ ins payload τ) next
    | .hear kind owner at_ τ => fun next => j.node (.hear kind (ρ owner) at_ τ) next
    | .begin at_ => fun next => j.node (.begin at_) next
    | .settle at_ => fun next => j.node (.settle at_) next⟩

/-- What a renamed judgment says of an effect, for every effect. -/
theorem ProcessJudgment.renamed_node {L : Type} (j : ProcessJudgment (RSig M) L) (ρ : Role → Role)
    (op : ROp M) (next : (RSig M).Reply op → L) :
    (j.renamed ρ).node op next = j.node (renameOp ρ op) (carryReply ρ op next) := by
  cases op <;> rfl

/-- Renamings compose, as nested applications stack them. -/
theorem ProcessJudgment.renamed_renamed {L : Type} (j : ProcessJudgment (RSig M) L)
    (ρ σ : Role → Role) : (j.renamed ρ).renamed σ = j.renamed (ρ ∘ σ) := by
  cases j with
  | mk node =>
    refine congrArg ProcessJudgment.mk (funext fun op => funext fun next => ?_)
    cases op with
    | give kind getters at_ τ value =>
      exact congrArg (fun gs => node (.give kind gs at_ τ value) next) List.map_map
    | own kind hearers at_ ins payload τ =>
      exact congrArg (fun hs => node (.own kind hs at_ ins payload τ) next) List.map_map
    | _ => rfl

/-- The identity renaming changes nothing. -/
theorem ProcessJudgment.renamed_id {L : Type} (j : ProcessJudgment (RSig M) L) :
    j.renamed id = j := by
  cases j with
  | mk node =>
    refine congrArg ProcessJudgment.mk (funext fun op => funext fun next => ?_)
    cases op with
    | give kind getters at_ τ value =>
      exact congrArg (fun gs => node (.give kind gs at_ τ value) next) (List.map_id getters)
    | own kind hearers at_ ins payload τ =>
      exact congrArg (fun hs => node (.own kind hs at_ ins payload τ) next) (List.map_id hearers)
    | _ => rfl

/-- A renamed judgment is monotone when the judgment is: a loop in a callee is taken by an
invariant under it as under the judgment. -/
theorem ProcessJudgment.Monotone.renamed {T : Type} {j : ProcessJudgment (RSig M) (T → Prop)}
    (mono : j.Monotone) (ρ : Role → Role) : (j.renamed ρ).Monotone := by
  intro op p q imp t
  rw [ProcessJudgment.renamed_node, ProcessJudgment.renamed_node]
  exact mono (renameOp ρ op) (carryReply ρ op p) (carryReply ρ op q) (by cases op <;> exact imp) t

/-- **Renaming the peers of a program is renaming what the judgment reads**, for every
judgment. It is the fold of a free program over a relabelling of its operations. With a stop
read as an operation without a reply, a process is a program of PolyFun's free monad,
`Process.interpret` is its `PFunctor.FreeM.wpFold`, `mapR` is `mapLens` along the lens that
`renameOp` and `carryReply` are, and this theorem is `PFunctor.FreeM.wpFold_mapLens`. VCVio's
`simulateQ_mapLens` is the same law for a handler into a monad; a fold is the handler into the
continuation monad. The core has no dependency, so the correspondence is not the definition
here. -/
theorem interpret_mapR {L B : Type} (ρ : Role → Role) (j : ProcessJudgment (RSig M) L)
    (done : B → L) (halt : Stop → L) (p : Program M B) :
    (mapR M ρ p).interpret j done halt = p.interpret (j.renamed ρ) done halt := by
  induction p with
  | done | halt => rfl
  | call op k ih => cases op <;> simp only [mapR, Process.interpret, ih] <;> rfl

/-- A judgment that reads no peer of an effect. -/
def Blind {L : Type} (ρ : Role → Role) (j : ProcessJudgment (RSig M) L) : Prop :=
  ∀ op (next : (RSig M).Reply op → L), j.node (renameOp ρ op) (carryReply ρ op next) = j.node op next

/-- A judgment reads no peer exactly where it is the judgment with its peers renamed. -/
theorem blind_iff_renamed_eq {L : Type} {ρ : Role → Role} {j : ProcessJudgment (RSig M) L} :
    Blind ρ j ↔ j.renamed ρ = j := by
  constructor
  · intro blind
    cases j with
    | mk node =>
      refine congrArg ProcessJudgment.mk (funext fun op => funext fun next => ?_)
      exact (ProcessJudgment.renamed_node ⟨node⟩ ρ op next).trans (blind op next)
  · intro same op next
    rw [← ProcessJudgment.renamed_node, same]

/-- A judgment that reads no peer is the judgment with its peers renamed. -/
theorem Blind.renamed_eq {L : Type} {ρ : Role → Role} {j : ProcessJudgment (RSig M) L}
    (blind : Blind ρ j) : j.renamed ρ = j :=
  blind_iff_renamed_eq.mp blind

/-- **Renaming the peers changes no judgment that reads no peer.** -/
theorem interpret_mapR_blind {L B : Type} (ρ : Role → Role) (j : ProcessJudgment (RSig M) L)
    (blind : Blind ρ j) (done : B → L) (halt : Stop → L) (p : Program M B) :
    (mapR M ρ p).interpret j done halt = p.interpret j done halt := by
  rw [interpret_mapR, blind.renamed_eq]

end Zkc.Core
