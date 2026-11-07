module

public import ZkcArkLibExamples.Fri.CommitDomain
public import ZkcArkLibExamples.Fri.CommitLoop
public import ZkcExamples.Structured.FriCommitAdmission
public meta import Zkc.Source.RegionReturnProjection

@[expose] public section

/-! The receiver derives the inputs of the three publication rounds from
Commit's own parameters and the original checked source operations. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitIngress
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceViews FriSourceBodies FriCommitAdmission
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open OracleProtocol (concrete)
open FriCommitRound (roundSite)
attribute [local implicit_reducible] Op.arguments Op.results Op.regions ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions

private theorem missingLength (i : Nat) :
    ProtocolCalculation.strict model (OracleProtocol.demand model) 1 RetainedFold.helpers .indexEqual
      (.cons none (.cons (concrete model .index i) .nil)) rfl = .done (.cons none .nil) := rfl

private theorem fieldOne :
    ProtocolCalculation.strict model (OracleProtocol.demand model) 1 RetainedFold.helpers (.fieldConstant extension 1)
      .nil rfl = .done (.cons (concrete model (.field extension) (1 : Octic)) .nil) := by
  erw [ProtocolCalculation.strict_embed model (OracleProtocol.demand model) 1 RetainedFold.helpers
    (.fieldConstant extension 1) .nil rfl]
  change PIR.Process.done (I := OracleProtocol.Interface model)
    (Values.cons (concrete model (.field extension) (Nat.cast 1 : Octic)) .nil) = _
  rw [Nat.cast_one]

private theorem fieldTwo :
    ProtocolCalculation.strict model (OracleProtocol.demand model) 1 RetainedFold.helpers (.fieldAdd extension)
      (.cons (concrete model (.field extension) (1 : Octic)) (.cons (concrete model (.field extension) (1 : Octic)) .nil)) rfl =
      .done (.cons (concrete model (.field extension) (2 : Octic)) .nil) := by
  erw [ProtocolCalculation.strict_embed model (OracleProtocol.demand model) 1 RetainedFold.helpers
    (.fieldAdd extension) (.cons (some (1 : Octic)) (.cons (some (1 : Octic)) .nil)) rfl]
  change PIR.Process.done (I := OracleProtocol.Interface model)
    (Values.cons (concrete model (.field extension) ((1 + 1 : Octic))) .nil) = _
  rw [one_add_one_eq_two]

variable {M : Type → Type} [Monad M] [LawfulMonad M] {Aux E : Type}
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2400000 in
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (shift : Octic) (nz : shift ≠ 0) (service : Nat) (original : CommitIteration.Store Aux) (role : original.self = 1) :
    Region.ReturnsSatisfying (CommitLoop.handler network choose) (fun state ↦ state.oracle = original)
      ((verifierAlgebra model).meaning (verifierTable model) context 1)
      admission (arguments model shift service).get (fun live ↦
        roundSite.operands.eval live.get = .cons (concrete model .index 3)
          ((CommitLoop.packed 5 shift [] []).append (CommitLoop.captures service)) ∧
        live.get shiftPort = concrete model (.field extension) shift ∧
        live.get sizePort = concrete model .index 32 ∧ live.get countPort = concrete model .index 3) := by
  have domain := OracleProtocol.owned_returned (helper := helper1Helper) RetainedFold.helpers receiver _ _ (CommitDomain.installed shift nz)
  have root := OracleProtocol.owned_returned (helper := helper3Helper) RetainedFold.helpers receiver _ _ (CommitGeometry.generator 5 (by decide))
  have half := OracleProtocol.owned_returned (helper := helper4Helper) RetainedFold.helpers receiver _ _ (CommitGeometry.inverse (2 : Octic) HolderFold.two_nonzero)
  repeat' first
    | (project_step ProtocolOp.mark
       apply PIR.Process.ReturnsUnder.call
       exact ReceiverForwarding.mark checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
         (PublishedWords.publishM choose) original _ _
       apply PIR.Process.ReturnsUnder.done)
    | (project_step ProtocolOp.calculate [Op.indexConstant]
       apply PIR.Process.ReturnsUnder.done)
    | (project_step ProtocolOp.calculate [Op.indexEqual]
       first | (apply Region.returnsOfLaw; apply OracleProtocol.equalIndex model)
             | (dsimp only [Operands.eval, Values.get, Values.append, Values.present, Values.absent,
                  ProtocolValue.embedComponents, Op.results, Op.arguments, Option.map, ProtocolOp.results,
                  protocolDialect, dialect, extension]
                exact PIR.Process.ReturnsUnder.ofEquation (missingLength 32) (.done _)))
    | (project_step ProtocolOp.guard
       apply Region.returnsOfLaw
       first | apply OracleProtocol.guardInactive model separate.symm | apply OracleProtocol.guardTrue model)
    | (project_step ProtocolOp.assemble
       exact PIR.Process.ReturnsUnder.ofEquation (OracleProtocol.assembleSecond model separate.symm receiver _ _) (.done _))
    | (project_step ProtocolOp.localCall
       first
       | (apply Region.returnsOfLaw; apply OracleProtocol.localCallInactive model _ _ separate.symm)
       | exact PIR.Process.ReturnsUnder.ofEquation domain (.done _)
       | exact PIR.Process.ReturnsUnder.ofEquation root (.done _)
       | exact PIR.Process.ReturnsUnder.ofEquation half (.done _))
    | (project_step ProtocolOp.oracle [OracleOp.sequenceEmpty]
       apply ReceiverForwarding.sequenceEmptyAt role
       · simp [receiver]
       · decide)
    | (project_step ProtocolOp.calculate [Op.fieldConstant]
       exact PIR.Process.ReturnsUnder.ofEquation fieldOne (.done _))
    | (project_step ProtocolOp.calculate [Op.fieldAdd]
       exact PIR.Process.ReturnsUnder.ofEquation fieldTwo (.done _))
  apply Region.ReturnsSatisfying.ret
  exact ⟨rfl, rfl, rfl, rfl⟩

end ZkcSecurity.ArkLib.Fri.CommitIngress
