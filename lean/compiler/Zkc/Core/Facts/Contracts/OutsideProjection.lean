module

public import Zkc.Core.Facts.Contracts.ProjectedEffect
public import Zkc.Core.Facts.Loops
public import Zkc.Core.Program.Project

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts

variable {V : Vocabulary} {hs : Headers V} {r : Role}

private def passiveOp {ins outs} : RoleOp V hs r ins outs → Prop
  | .absent .. | .keep .. | .apply .. => True
  | _ => False

/-- The operations and regions an undeclared role can reach. A call still enters
the actual projected callee at the role selected by its role map. -/
private inductive Passive : {Γ : Ctx (LTy V)} → {outs : List (LTy V)} →
    Term (roleDialect V hs r) Γ outs → Prop where
  | ret (xs) : Passive (.ret xs)
  | op {ins res : List (LTy V)} {o : RoleOp V hs r ins res} {args key results rest} :
      passiveOp o → Passive rest → Passive (.op key o args results rest)
  | block {key number body results rest} :
      Passive body → Passive rest → Passive (.block key number body results rest)
  | attempt {key w inputs body results rest} :
      r ∉ w → Passive body → Passive rest →
      Passive (.attempt key w trivial inputs body results rest)

private theorem projectOp_passive {parts : List Role} (outside : r ∉ parts)
    {Γ : Ctx (LTy V)} {ins res outs : List (LTy V)} (key : Key) (o : ProtocolOp V hs ins res)
    (args : HList (Var Γ) ins) (results : Names res)
    {rest : Term (roleDialect V hs r) (Γ.extend results) outs}
    (within : o.Within parts) (tail : Passive rest) :
    Passive (o.project r key args results rest) := by
  cases o with
  | compute R op operands types held =>
    have no : r ∉ R := fun h => outside (within r h)
    simp only [ProtocolOp.project, dite_eq_right no]
    exact .op trivial tail
  | flow kind giver getters holds unique =>
    have ng : r ≠ giver := fun e => outside (e ▸ within.1)
    have ns : r ∉ getters := fun h => outside (within.2 r h)
    simp only [ProtocolOp.project, dite_eq_right ng, dite_eq_right ns]
    exact .op trivial tail
  | given kind owner hearers operands ty typed held unique =>
    have ng : r ≠ owner := fun e => outside (e ▸ within.1)
    have ns : r ∉ hearers := fun h => outside (within.2 r h)
    simp only [ProtocolOp.project, dite_eq_right ng, dite_eq_right ns]
    exact .op trivial tail
  | narrow R among =>
    by_cases held : r ∈ R <;> simp only [ProtocolOp.project, held, dite_true, dite_false] <;>
      exact .op trivial tail
  | apply => exact .op trivial tail

private theorem project_passive {parts : List Role} (outside : r ∉ parts) :
    ∀ {Γ : Ctx (LTy V)} {outs : List (LTy V)} (t : Term (protocolDialect V hs) Γ outs),
      Within parts t → Passive (project r t)
  | _, _, .ret xs, _ => .ret xs
  | _, _, .op key o args results rest, w =>
    projectOp_passive outside key o args results w.1 (project_passive outside rest w.2)
  | _, _, .guard _ ps _ _ _ rest, w => by
    have no : r ∉ ps := fun h => outside (w.1 r h)
    simp only [project, dite_eq_right no]
    exact project_passive outside rest w.2
  | _, _, .choose _ ps _ _ _ _ _ _ rest, w => by
    have no : r ∉ ps := fun h => outside (w.1 r h)
    simp only [project, dite_eq_right no]
    exact .op trivial (project_passive outside rest w.2.2.2)
  | _, _, .cases _ ps _ _ _ _ _ rest, w => by
    have no : r ∉ ps := fun h => outside (w.1 r h)
    simp only [project, dite_eq_right no]
    exact .op trivial (project_passive outside rest w.2.2)
  | _, _, .loop _ ps _ _ _ _ _ _ rest, w => by
    have no : r ∉ ps := fun h => outside (w.1 r h)
    simp only [project, dite_eq_right no]
    exact .op trivial (project_passive outside rest w.2.2)
  | _, _, .block _ _ body _ rest, w =>
    .block (project_passive outside body w.1) (project_passive outside rest w.2)
  | _, _, .attempt _ _ _ _ body _ rest, w =>
    .attempt (fun h => outside (w.1 r h)) (project_passive outside body w.2.1)
      (project_passive outside rest w.2.2)

variable (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
private abbrev sem := roleSem M r fns roles

private theorem passiveOp_safe (rcallees : RCallees M roles) {ins outs} (op : RoleOp V hs r ins outs)
    (passive : passiveOp op) (key : Key) (path : List Frame) (args : HList (RV M r) ins)
    (valid : args.All (RV.Valid M r)) :
    ((sem M fns roles).op key op path args).Every (Permitted M)
      (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) := by
  cases op with
  | compute | give | get | own | hear => cases passive
  | absent items out => exact nothings_valid M r out
  | keep H same =>
    obtain ⟨v, rfl⟩ := HList.one args
    exact ⟨(valid_carry M same v).mpr valid.1, trivial⟩
  | apply callee peers distinct covers operands fits =>
    exact application_safe M r fns roles rcallees callee peers distinct covers _ fits key path args valid

private theorem passive_safe (rcallees : RCallees M roles)
    {Γ outs} {t : Term (roleDialect V hs r) Γ outs} (passive : Passive t) :
    ∀ path (env : Env (RV M r) Γ), (∀ τ (x : Var Γ τ), RV.Valid M r τ (env.get x)) →
      (t.denote (sem M fns roles) path env).Every (Permitted M)
        (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) := by
  induction passive with
  | ret xs =>
    intro path env valid
    exact ((sem M fns roles).dyns_valid_iff (Valid := RoleValueValid M r) _).mp (env_all_valid valid xs)
  | op pass tail ih =>
    intro path env valid
    rw [Term.denote_op, Process.every_bind]
    apply Process.every_mono _ _ (fun ys v => ih path _ (Env.extend_preserves valid _ ys v))
      (fun _ h => h)
    exact passiveOp_safe M fns roles rcallees _ pass _ _ _
      (((sem M fns roles).dyns_valid_iff (Valid := RoleValueValid M r) _).mp (env_all_valid valid _))
  | block body rest b tail =>
    intro path env valid
    rw [Term.denote_block, Process.every_bind]
    exact Process.every_mono _ _ (fun ys v => tail path _ (Env.extend_preserves valid _ ys v))
      (fun _ h => h) (b _ env valid)
  | attempt no body rest b tail =>
    intro path env valid
    rw [Term.denote_attempt]
    simp only [sem, roleSem, ite_eq_right no, Process.bind]
    rw [Process.every_bind]
    apply Process.every_mono _ _ (fun ys v => tail path _ (Env.extend_preserves valid _ ys v))
      (fun _ h => h)
    exact b path _ (Env.extend_preserves valid _ _ ⟨valid_out M r no _, trivial⟩)

private theorem passive_bounded (B : List (Key × Nat) → Key → Nat → Prop)
    {Γ outs} {t : Term (roleDialect V hs r) Γ outs} (passive : Passive t) :
    ∀ path blocks env, t.EveryLoop (sem M fns roles) (Permitted M) B path blocks env := by
  induction passive with
  | ret => intros; trivial
  | op pass tail ih =>
    intro path blocks env
    exact ⟨trivial, Process.every_mono _ _ (fun _ _ => ih path blocks _) (fun _ _ => trivial)
      (Process.every_true _ _)⟩
  | block body rest b tail =>
    intro path blocks env
    exact ⟨b _ _ _, Process.every_mono _ _ (fun _ _ => tail path blocks _) (fun _ _ => trivial)
      (Process.every_true _ _)⟩
  | attempt no body rest b tail =>
    intro path blocks env
    exact ⟨Process.every_mono _ _ (fun _ _ => b path blocks _) (fun _ _ => trivial)
      (Process.every_true _ _), Process.every_mono _ _ (fun _ _ => tail path blocks _)
        (fun _ _ => trivial) (Process.every_true _ _)⟩

/-- Every call reached by an outside role uses the certified callee table. Locally this
projection reaches no dynamic or static loops, so any loop bound predicate holds. -/
theorem outsideProjection {parts : List Role} (outside : r ∉ parts) (rcallees : RCallees M roles)
    {Γ outs} (t : Term (protocolDialect V hs) Γ outs) (within : Within parts t)
    (path : List Frame) (env : Env (RV M r) Γ) (valid : ∀ τ (x : Var Γ τ), RV.Valid M r τ (env.get x))
    (B : List (Key × Nat) → Key → Nat → Prop) (blocks : List (Key × Nat)) :
    ((project r t).denote (roleSem M r fns roles) path env).Every (Permitted M)
      (fun ys => ys.All (RV.Valid M r)) (· ≠ .undefined) ∧
      (project r t).EveryLoop (roleSem M r fns roles) (Permitted M) B path blocks env := by
  have passive := project_passive outside t within
  exact ⟨passive_safe M fns roles rcallees passive path env valid,
    passive_bounded M fns roles B passive path blocks env⟩

end Zkc.Core.BodyAnalysis.RoleContracts
