module

public import Zkc.Formal.ProcessJudgment
public import Zkc.Core.Meaning.Role
public import Zkc.Core.Meaning.Fold
public import Zkc.Core.Evidence.FunctionEntry

@[expose] public section
set_option autoImplicit false

/-!
The application of a protocol by a role, under a judgment.

A role that applies a protocol runs the callee's program of the role that it plays there, at
the path of the application, with every peer of an effect renamed to the caller's role and the
results carried back (`roleSem`, the case of an application). Renaming the peers of a program
is renaming what the judgment reads (`interpret_mapR`, for every judgment). So an application
followed by the rest is the callee's program, not renamed, under the judgment with its peers
renamed (`ProcessJudgment.renamed`), whose condition at the end is the judgment of the rest on
what the role holds of the results (`Process.interpret_applied`): the passage of a region, with
one more equation. A judgment that reads no peer of an effect (`Blind`) is its own renaming,
and the callee is then judged as the caller is (`Process.interpret_applied_blind`). The walk
goes into an application by the rule, as it goes into the arm of a choice.

Inside the callee a function is read in the table of the definitions before the callee, and a
law of the function is stated once, in another table. The core's `fnMeaning_entry`
(`Zkc/Core/Evidence/FunctionEntry.lean`) is the equation by which a call in one table is the
call in another.
-/

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
effect is what the judgment says of the renamed effect. -/
def ProcessJudgment.renamed {L : Type} (j : ProcessJudgment (RSig M) L) (ρ : Role → Role) :
    ProcessJudgment (RSig M) L :=
  ⟨fun op next => j.node (renameOp ρ op) (carryReply ρ op next)⟩

/-- **Renaming the peers of a program is renaming what the judgment reads**, for every
judgment. (The fold of a free program over a relabelling of its operations: PolyFun states it
for its own free monad as `PFunctor.FreeM.wpFold_mapLens`, and VCVio for a monad as
`OracleComp.simulateQ_mapLens`.) -/
theorem interpret_mapR {L B : Type} (ρ : Role → Role) (j : ProcessJudgment (RSig M) L)
    (done : B → L) (halt : Stop → L) (p : Program M B) :
    (mapR M ρ p).interpret j done halt = p.interpret (j.renamed ρ) done halt := by
  induction p with
  | done | halt => rfl
  | call op k ih => cases op <;> simp only [mapR, Process.interpret, ih] <;> rfl

/-- A judgment that reads no peer of an effect. -/
def Blind {L : Type} (ρ : Role → Role) (j : ProcessJudgment (RSig M) L) : Prop :=
  ∀ op (next : (RSig M).Reply op → L), j.node (renameOp ρ op) (carryReply ρ op next) = j.node op next

/-- A judgment that reads no peer is the judgment with its peers renamed. -/
theorem Blind.renamed_eq {L : Type} {ρ : Role → Role} {j : ProcessJudgment (RSig M) L}
    (blind : Blind ρ j) : j.renamed ρ = j := by
  cases j with
  | mk node => exact congrArg ProcessJudgment.mk (funext fun op => funext fun next => blind op next)

/-- **Renaming the peers changes no judgment that reads no peer.** -/
theorem interpret_mapR_blind {L B : Type} (ρ : Role → Role) (j : ProcessJudgment (RSig M) L)
    (blind : Blind ρ j) (done : B → L) (halt : Stop → L) (p : Program M B) :
    (mapR M ρ p).interpret j done halt = p.interpret j done halt := by
  rw [interpret_mapR, blind.renamed_eq]

/-- What an application denotes for a role: the callee's program of the role that the role
plays there, at the path of the application, with its peers renamed and its results carried
back. -/
theorem Instr.denote_apply_role {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {Γ : Ctx (LTy V)} {hdr : ProtocolHeader V} (key : Key)
    (callee : Member hs.protocols hdr) (roles : List Role) (distinct : roles.Nodup)
    (covers : roles.length = hdr.roles) (operands : List (LTy V))
    (fits : Fits operands (hdr.ins.map (LTy.map (RoleMap.ofList roles distinct).to)))
    (args : HList (Var Γ) operands) (path : List Frame) (env : Env (RV M r) Γ) :
    (Instr.op (D := roleDialect V hs r)
        (RoleOp.apply callee roles distinct covers operands fits) args).denote
        (roleSem M r fnTable rTable) key path env =
      (mapR M (RoleMap.ofList roles distinct).to
        (rTable _ callee ((RoleMap.ofList roles distinct).back r) (path ++ [.application key])
          (enterAll M (RoleMap.ofList roles distinct) r (fitAllRV M fits (env.all args))))).map
        (leaveAll M (RoleMap.ofList roles distinct) r) :=
  rfl

/-- **The rule of an application, for every judgment.** A callee's program with its peers
renamed and its results carried, followed by a rest, is judged as the callee's program, under
the judgment with its peers renamed, whose condition at the end is the judgment of the rest on
the results carried. The rest is judged as it was: only the callee's effects are renamed. -/
theorem Process.interpret_applied {L B C D : Type} (ρ : Role → Role)
    (j : ProcessJudgment (RSig M) L) (done : D → L) (halt : Stop → L)
    (leave : B → C) (rest : C → Program M D) (callee : Program M B) :
    (((mapR M ρ callee).map leave).bind rest).interpret j done halt =
      callee.interpret (j.renamed ρ) (fun outs => (rest (leave outs)).interpret j done halt) halt := by
  rw [Process.interpret_bind, Process.map_eq_bind, Process.interpret_bind, interpret_mapR]
  rfl

/-- **The rule of an application under a judgment that reads no peer**: the callee's program
is judged as it stands. -/
theorem Process.interpret_applied_blind {L B C D : Type} (ρ : Role → Role)
    (j : ProcessJudgment (RSig M) L) (blind : Blind ρ j) (done : D → L) (halt : Stop → L)
    (leave : B → C) (rest : C → Program M D) (callee : Program M B) :
    (((mapR M ρ callee).map leave).bind rest).interpret j done halt =
      callee.interpret j (fun outs => (rest (leave outs)).interpret j done halt) halt := by
  rw [Process.interpret_applied, blind.renamed_eq]

end Zkc.Core
