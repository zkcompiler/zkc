import Zkc.Core.Admission.Theorems
import Zkc.Core.Run.Specialize.Sound
import Zkc.Core.Scheme.Deploy.Elim
import Zkc.Core.Scheme.Materialize
import Zkc.Core.Scheme.Proof.CompletenessHelpers
import Zkc.Kernel
import Zkc.Tests.Core.Deployment.Materialize
import ZkcFormal.Form.Produce
import ZkcFormal.Reading
import ZkcFormal.Value

/-!
End-to-end verification and empirical comparison of `constructed Core` and `serialized Core`
materialization (`Zkc.Core.Scheme.Materialize`) against `Core.deploy` / `Core.specialize` and
the formal reading/value/form libraries (`ZkcFormal.Reading`, `ZkcFormal.Value`,
`ZkcFormal.Form.Produce`):

1. Generic `Reading.read` and `Value.value` preservation across `Core.specialize` and `d.run` for
   BOTH concrete (`Core.deploy`) and ideal random-oracle (`Core.deployIdeal`) deployments.
2. Kernel-elaborated `@[reducible]` installations of the interactive (`baseInstalled`),
   `constructed Core` (`constructedInstalled`), and `serialized Core` (`serializedInstalled`)
   Schnorr protocols with `ElaboratedFrom` readback theorems and closure-invariance verification
   (`baseDeployed.identity = schnorrDeployed.identity`).
3. Direct `form_of_role` extraction on ALL THREE verifier roles (`BaseVerifier`,
   `ConstructedVerifier`, `SerializedVerifier`), empirically documenting the `maxRecDepth` and
   AST-size impact of embedding an 844-byte unhashed pre-image literal (`sessBytes`).
4. Universal exact `Process` equality (`∀ (Y : Nat) (proof : List Nat)`) proving that the
   re-admitted `serialized Core` verifier, `Core.deploy` (`baseDeployed.run`), and
   `Core.specialize` (`(specialize baseDeployed 1).denote`) denote the EXACT SAME `Process`
   (including every bounds/range/verification/trailing-byte `Stop` occurrence), hence preserve
   `Reading.read` and `Value.value` unconditionally across all samplers, reply predicates, and
   bad-return events.
-/

namespace ZkcFormal.Checks.ConstructedStage

open Zkc.Core Zkc.Core.Tests.Deployment ZkcFormal

/-! ## 1. Generic `Reading.read` and `Value.value` preservation for `deploy` and `deployIdeal` -/

section GenericPreservation

variable {V : Vocabulary} (M : Model V)

theorem specialize_deploy_reading_eq (enc : VocabEncoder V) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V) (hDep : deploy enc a declaration = .ok d)
    (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r))) :
    Reading.read ((specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken) =
      Reading.read (d.run M r ins taken) :=
  congrArg Reading.read (specialize_deploy_sound M enc a declaration d hDep r ins taken)

theorem specialize_deploy_value_eq (enc : VocabEncoder V) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V) (hDep : deploy enc a declaration = .ok d)
    (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r)))
    (samplers : ProbabilisticProcess.Samplers (RSig M))
    (allowed : ∀ o, (RSig M).Reply o → Prop)
    (bad : HList (RV M r) d.entry.outs × HList M.Val (Stack.Gives (d.stack r)) → Prop) :
    Value.value samplers allowed bad
        ((specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken) =
      Value.value samplers allowed bad (d.run M r ins taken) :=
  congrArg (Value.value samplers allowed bad)
    (specialize_deploy_sound M enc a declaration d hDep r ins taken)

theorem specialize_deployIdeal_reading_eq (enc : VocabEncoder V) (serviceKey : Key)
    (a : Admitted V) (declaration : Declaration) (d : Deployed V)
    (hDep : deployIdeal enc serviceKey a declaration = .ok d)
    (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r))) :
    Reading.read ((specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken) =
      Reading.read (d.run M r ins taken) :=
  congrArg Reading.read
    (specialize_deployIdeal_sound M enc serviceKey a declaration d hDep r ins taken)

theorem specialize_deployIdeal_value_eq (enc : VocabEncoder V) (serviceKey : Key)
    (a : Admitted V) (declaration : Declaration) (d : Deployed V)
    (hDep : deployIdeal enc serviceKey a declaration = .ok d)
    (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r)))
    (samplers : ProbabilisticProcess.Samplers (RSig M))
    (allowed : ∀ o, (RSig M).Reply o → Prop)
    (bad : HList (RV M r) d.entry.outs × HList M.Val (Stack.Gives (d.stack r)) → Prop) :
    Value.value samplers allowed bad
        ((specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken) =
      Value.value samplers allowed bad (d.run M r ins taken) :=
  congrArg (Value.value samplers allowed bad)
    (specialize_deployIdeal_sound M enc serviceKey a declaration d hDep r ins taken)

end GenericPreservation

/-! ## 2. Kernel-elaborated `@[reducible]` installations and readback -/

/-- Minimal standalone Schnorr program (the 10 shared suite/layout helpers + `schnorrProto`). -/
def baseSchnorrProgram : NamedProgram deployVocab :=
  ⟨suiteAndLayoutDefs ++ [schnorrProto]⟩

private theorem baseSchnorr_admit_isSome :
    (admit baseSchnorrProgram noAssociation).toOption.isSome = true := by
  decide +kernel

def baseSchnorrAdmitted : Admitted deployVocab :=
  (admit baseSchnorrProgram noAssociation).toOption.get baseSchnorr_admit_isSome

theorem baseSchnorr_admit_ok :
    admit baseSchnorrProgram noAssociation = .ok baseSchnorrAdmitted :=
  except_toOption_get_ok _ baseSchnorr_admit_isSome

private theorem baseSchnorr_deploy_isSome :
    (deploy deployEncoder baseSchnorrAdmitted schnorrDecl).toOption.isSome = true := by
  decide +kernel

def baseDeployed : Deployed deployVocab :=
  (deploy deployEncoder baseSchnorrAdmitted schnorrDecl).toOption.get baseSchnorr_deploy_isSome

theorem baseSchnorr_deploy_ok :
    deploy deployEncoder baseSchnorrAdmitted schnorrDecl = .ok baseDeployed :=
  except_toOption_get_ok _ baseSchnorr_deploy_isSome

/-- Canonical reachability-closure invariance: dropping all 9 unrelated protocols from
`deployTestProgram` produces the exact same bound deployment identity. -/
theorem base_identity_eq_suite : baseDeployed.identity = schnorrDeployed.identity := by
  decide +kernel

noncomputable section

def prog0 : Typed deployVocab := Typed.empty

kernel_ok elab0 with hdr0 names0 body0 : Elaborated deployVocab prog0.headers :=
  elaborateDefinition prog0.headers fnStart
attribute [reducible] hdr0
def prog1 : Typed deployVocab := prog0.add elab0

kernel_ok elab1 with hdr1 names1 body1 : Elaborated deployVocab prog1.headers :=
  elaborateDefinition prog1.headers fnAbsorb
attribute [reducible] hdr1
def prog2 : Typed deployVocab := prog1.add elab1

kernel_ok elab2 with hdr2 names2 body2 : Elaborated deployVocab prog2.headers :=
  elaborateDefinition prog2.headers fnEncodeScalar
attribute [reducible] hdr2
def prog3 : Typed deployVocab := prog2.add elab2

kernel_ok elab3 with hdr3 names3 body3 : Elaborated deployVocab prog3.headers :=
  elaborateDefinition prog3.headers fnEncodePoint
attribute [reducible] hdr3
def prog4 : Typed deployVocab := prog3.add elab3

kernel_ok elab4 with hdr4 names4 body4 : Elaborated deployVocab prog4.headers :=
  elaborateDefinition prog4.headers fnDeriveScalar
attribute [reducible] hdr4
def prog5 : Typed deployVocab := prog4.add elab4

kernel_ok elab5 with hdr5 names5 body5 : Elaborated deployVocab prog5.headers :=
  elaborateDefinition prog5.headers fnReadScalar
attribute [reducible] hdr5
def prog6 : Typed deployVocab := prog5.add elab5

kernel_ok elab6 with hdr6 names6 body6 : Elaborated deployVocab prog6.headers :=
  elaborateDefinition prog6.headers fnReadPoint
attribute [reducible] hdr6
def prog7 : Typed deployVocab := prog6.add elab6

kernel_ok elab7 with hdr7 names7 body7 : Elaborated deployVocab prog7.headers :=
  elaborateDefinition prog7.headers fnEqScalar
attribute [reducible] hdr7
def prog8 : Typed deployVocab := prog7.add elab7

kernel_ok elab8 with hdr8 names8 body8 : Elaborated deployVocab prog8.headers :=
  elaborateDefinition prog8.headers fnRecoverCommit
attribute [reducible] hdr8
def prog9 : Typed deployVocab := prog8.add elab8

kernel_ok elab9 with hdr9 names9 body9 : Elaborated deployVocab prog9.headers :=
  elaborateDefinition prog9.headers fnSamples
attribute [reducible] hdr9
def fnInstalled : Typed deployVocab := prog9.add elab9

kernel_ok elabBase with hdrBase namesBase bodyBase : Elaborated deployVocab fnInstalled.headers :=
  elaborateDefinition fnInstalled.headers schnorrProto
attribute [reducible] hdrBase
def baseInstalled : Typed deployVocab := fnInstalled.add elabBase

theorem base_elaborated : ElaboratedFrom Typed.empty baseSchnorrProgram.definitions baseInstalled :=
  .cons elab0.eq (.cons elab1.eq (.cons elab2.eq (.cons elab3.eq (.cons elab4.eq
  (.cons elab5.eq (.cons elab6.eq (.cons elab7.eq (.cons elab8.eq (.cons elab9.eq
  (.cons elabBase.eq (.nil _)))))))))))

theorem base_readback : baseSchnorrAdmitted.program = baseInstalled :=
  admitted_eq_of_elaborated baseSchnorr_admit_ok base_elaborated

/-- Defeq-transparent view of `baseSchnorrAdmitted` backed directly by `baseInstalled`. -/
@[reducible] def baseAdmittedFast : Admitted deployVocab :=
  ⟨baseInstalled, baseSchnorrAdmitted.annotation,
   base_readback ▸ baseSchnorrAdmitted.association,
   base_readback ▸ baseSchnorrAdmitted.assured⟩

private theorem admitted_eq_mk {V : Vocabulary} (p : Admitted V) {prog : Typed V}
    (h : p.program = prog) :
    Admitted.mk prog p.annotation (h ▸ p.association) (h ▸ p.assured) = p := by
  cases p; cases h; rfl

theorem baseAdmittedFast_eq : baseAdmittedFast = baseSchnorrAdmitted :=
  admitted_eq_mk baseSchnorrAdmitted base_readback

kernel_ok baseConProg : NamedProgram deployVocab :=
  materializeConstructed deployEncoder baseAdmittedFast schnorrDecl

kernel_ok baseSerProg : NamedProgram deployVocab :=
  materializeSerialized deployEncoder baseAdmittedFast schnorrDecl

kernel_normal conEntryDef : Definition deployVocab :=
  baseConProg.definitions.getLastD schnorrProto

kernel_normal serEntryDef : Definition deployVocab :=
  baseSerProg.definitions.getLastD schnorrProto

theorem baseConProg_defs_eq :
    baseConProg.definitions = suiteAndLayoutDefs ++ [conEntryDef] := by
  kernel_rfl

theorem baseSerProg_defs_eq :
    baseSerProg.definitions = suiteAndLayoutDefs ++ [serEntryDef] := by
  kernel_rfl

theorem schnorrConstructedProg_eq_baseConProg : schnorrConstructedProg = baseConProg := by
  have hSuite : materializeConstructed deployEncoder baseSchnorrAdmitted schnorrDecl =
      materializeConstructed deployEncoder admittedSuite schnorrDecl := by
    decide +kernel
  have hOk : materializeConstructed deployEncoder baseSchnorrAdmitted schnorrDecl = .ok baseConProg := by
    rw [← baseAdmittedFast_eq]
    exact baseConProg.eq
  exact Except.ok.inj (schnorr_constructed_ok.symm.trans (hSuite.symm.trans hOk))

theorem schnorrSerializedProg_eq_baseSerProg : schnorrSerializedProg = baseSerProg := by
  have hSuite : materializeSerialized deployEncoder baseSchnorrAdmitted schnorrDecl =
      materializeSerialized deployEncoder admittedSuite schnorrDecl := by
    decide +kernel
  have hOk : materializeSerialized deployEncoder baseSchnorrAdmitted schnorrDecl = .ok baseSerProg := by
    rw [← baseAdmittedFast_eq]
    exact baseSerProg.eq
  exact Except.ok.inj (schnorr_serialized_ok.symm.trans (hSuite.symm.trans hOk))

kernel_ok elabCon with hdrCon namesCon bodyCon : Elaborated deployVocab fnInstalled.headers :=
  elaborateDefinition fnInstalled.headers conEntryDef
attribute [reducible] hdrCon
def constructedInstalled : Typed deployVocab := fnInstalled.add elabCon

kernel_ok elabSer with hdrSer namesSer bodySer : Elaborated deployVocab fnInstalled.headers :=
  elaborateDefinition fnInstalled.headers serEntryDef
attribute [reducible] hdrSer
def serializedInstalled : Typed deployVocab := fnInstalled.add elabSer

theorem con_elaborated : ElaboratedFrom Typed.empty schnorrConstructedProg.definitions constructedInstalled := by
  rw [schnorrConstructedProg_eq_baseConProg, baseConProg_defs_eq]
  exact .cons elab0.eq (.cons elab1.eq (.cons elab2.eq (.cons elab3.eq (.cons elab4.eq
    (.cons elab5.eq (.cons elab6.eq (.cons elab7.eq (.cons elab8.eq (.cons elab9.eq
    (.cons elabCon.eq (.nil _)))))))))))

theorem ser_elaborated : ElaboratedFrom Typed.empty schnorrSerializedProg.definitions serializedInstalled := by
  rw [schnorrSerializedProg_eq_baseSerProg, baseSerProg_defs_eq]
  exact .cons elab0.eq (.cons elab1.eq (.cons elab2.eq (.cons elab3.eq (.cons elab4.eq
    (.cons elab5.eq (.cons elab6.eq (.cons elab7.eq (.cons elab8.eq (.cons elab9.eq
    (.cons elabSer.eq (.nil _)))))))))))

theorem constructed_readback : schnorrConstructedAdmitted.program = constructedInstalled :=
  admitted_eq_of_elaborated schnorr_constructed_admit_ok con_elaborated

theorem serialized_readback : schnorrSerializedAdmitted.program = serializedInstalled :=
  admitted_eq_of_elaborated schnorr_serialized_admit_ok ser_elaborated

abbrev baseRoot : Member baseInstalled.headers.protocols hdrBase := Member.head
abbrev conRoot : Member constructedInstalled.headers.protocols hdrCon := Member.head
abbrev serRoot : Member serializedInstalled.headers.protocols hdrSer := Member.head

end

/-! ## 3. `form_of_role` extraction across all three stages -/

-- Interactive Schnorr succeeds at Lean's default `maxRecDepth` (512).
form_of_role BaseVerifier : baseInstalled, baseRoot, 1

-- Empirical finding: `materializeConstructed` and `materializeSerialized` embed the full
-- 844-byte unhashed `sessBytes` pre-image as an inline `[byte]` literal (`845` `List.cons`
-- nodes > default `maxRecDepth = 512`). Raising `maxRecDepth` lets `form_of_role` complete
-- on BOTH re-admitted stage artifacts so we can inspect and measure them directly.
set_option maxRecDepth 8000 in
form_of_role ConstructedVerifier : constructedInstalled, conRoot, 1

set_option maxRecDepth 8000 in
form_of_role SerializedVerifier : serializedInstalled, serRoot, 1

form_of_function FnStartForm : serializedInstalled, SerializedVerifier.function100
form_of_function FnAbsorbForm : serializedInstalled, SerializedVerifier.function101
form_of_function FnEncPointForm : serializedInstalled, SerializedVerifier.function103
form_of_function FnDeriveForm : serializedInstalled, SerializedVerifier.function104
form_of_function FnReadScalarForm : serializedInstalled, SerializedVerifier.function105
form_of_function FnReadPointForm : serializedInstalled, SerializedVerifier.function106

#print axioms BaseVerifier.reads
#print axioms ConstructedVerifier.reads
#print axioms SerializedVerifier.reads

/-! ## 4. Universal `∀ Y proof` exact `Process`, `Reading.read`, and `Value.value` equivalence -/

section UniversalEquivalence

/-- Type-preserving embeddings between `Nat` and `deployModel.Val dPoint` / `dScalar` so
`rw`/`simp` preserve `implicit`-level type-correctness without unfolding `deployModel`. -/
def toPoint (n : Nat) : deployModel.Val dPoint := n
def toScalar (n : Nat) : deployModel.Val dScalar := n
def fromPoint (p : deployModel.Val dPoint) : Nat := p
def fromScalar (s : deployModel.Val dScalar) : Nat := s

@[simp] theorem fromPoint_toPoint (n : Nat) : fromPoint (toPoint n) = n := rfl
@[simp] theorem fromScalar_toScalar (n : Nat) : fromScalar (toScalar n) = n := rfl

/-- Helper-function semantic characterizations on `deployModel` proved from `form_of_function`
+ `Reading.read_injective` (without unsealing `fnMeaning`). -/
theorem fnStart_eval (bs : List Nat) :
    fnMeaning deployModel serializedInstalled SerializedVerifier.function100 (.cons bs .nil) =
      .done (.cons (mixBytes 1 bs) .nil) := by
  apply Reading.read_injective
  rw [FnStartForm.reads]
  rfl

theorem fnAbsorb_eval (st : Nat) (lbl enc : List Nat) :
    fnMeaning deployModel serializedInstalled SerializedVerifier.function101
        (.cons st (.cons lbl (.cons enc .nil))) =
      .done (.cons (mixBytes (mixBytes st lbl) enc) .nil) := by
  apply Reading.read_injective
  rw [FnAbsorbForm.reads]
  rfl

theorem fnEncPoint_eval (p : deployModel.Val dPoint) :
    fnMeaning deployModel serializedInstalled SerializedVerifier.function103 (.cons p .nil) =
      .done (.cons [fromPoint p % 256] .nil) := by
  apply Reading.read_injective
  rw [FnEncPointForm.reads]
  rfl

theorem fnDerive_eval (st : Nat) (lbl : List Nat) :
    fnMeaning deployModel serializedInstalled SerializedVerifier.function104
        (.cons st (.cons lbl .nil)) =
      .done (.cons (toScalar (mixBytes st (0xFF :: lbl) % 11))
        (.cons (mixBytes st (0xFF :: lbl)) .nil)) := by
  apply Reading.read_injective
  rw [FnDeriveForm.reads]
  rfl

theorem fnReadPoint_eval_nil :
    fnMeaning deployModel serializedInstalled SerializedVerifier.function106
        (.cons ([] : List Nat) (.cons 0 .nil)) =
      .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  apply Reading.read_injective
  rw [FnReadPointForm.reads]
  rfl

theorem fnReadPoint_eval_cons (b0 : Nat) (rest : List Nat) :
    fnMeaning deployModel serializedInstalled SerializedVerifier.function106
        (.cons (b0 :: rest) (.cons 0 .nil)) =
      if b0 < 23 then .done (.cons (toPoint (b0 % 23)) (.cons 1 .nil))
      else .halt (.declared .reject ⟨[], ⟨8⟩⟩) := by
  apply Reading.read_injective
  rw [FnReadPointForm.reads]
  by_cases h : b0 < 23 <;> (simp [FnReadPointForm.form, deployModel, toPoint,
    ZkcFormal.Form.optionE, ZkcFormal.Form.headV, ZkcFormal.Form.tailV, Reading.read_done,
    Reading.read_halt, Nat.blt_eq, h])

theorem fnReadScalar_eval_singleton (b0 : Nat) :
    fnMeaning deployModel serializedInstalled SerializedVerifier.function105
        (.cons ([b0] : List Nat) (.cons 1 .nil)) =
      .halt (.declared .reject ⟨[], ⟨3⟩⟩) := by
  apply Reading.read_injective
  rw [FnReadScalarForm.reads]
  rfl

theorem fnReadScalar_eval_cons2 (b0 b1 : Nat) (rest : List Nat) :
    fnMeaning deployModel serializedInstalled SerializedVerifier.function105
        (.cons (b0 :: b1 :: rest) (.cons 1 .nil)) =
      if b1 < 11 then .done (.cons (toScalar (b1 % 11)) (.cons 2 .nil))
      else .halt (.declared .reject ⟨[], ⟨8⟩⟩) := by
  apply Reading.read_injective
  rw [FnReadScalarForm.reads]
  by_cases h : b1 < 11 <;> (simp [FnReadScalarForm.form, deployModel, toScalar,
    ZkcFormal.Form.optionE, ZkcFormal.Form.headV, ZkcFormal.Form.tailV, Reading.read_done,
    Reading.read_halt, Nat.blt_eq, h])

private theorem deploy_eq_of_eq {V : Vocabulary} {enc : VocabEncoder V} {a₁ a₂ : Admitted V}
    {decl : Declaration} {d₁ d₂ : Deployed V}
    (ha : a₁ = a₂) (h1 : deploy enc a₁ decl = .ok d₁) (h2 : deploy enc a₂ decl = .ok d₂) :
    d₁ = d₂ := by
  subst ha
  exact Except.ok.inj (h1.symm.trans h2)

def castClosedRole {V : Vocabulary} {fns₁ fns₂ : List (FnHeader V)} {r : Role}
    {ins₁ ins₂ outs₁ outs₂ : List (LTy V)} {t₁ t₂ g₁ g₂ : List V.Ty}
    (hf : fns₁ = fns₂) (hi : ins₁ = ins₂) (ho : outs₁ = outs₂) (ht : t₁ = t₂) (hg : g₁ = g₂)
    (cr : ClosedRole V fns₁ r ins₁ outs₁ t₁ g₁) :
    ClosedRole V fns₂ r ins₂ outs₂ t₂ g₂ :=
  hf ▸ hi ▸ ho ▸ ht ▸ hg ▸ cr

theorem castClosedRole_denote_unit {V : Vocabulary} (M : Model V)
    {fns₁ fns₂ : List (FnHeader V)} {r : Role}
    {ins₁ ins₂ outs₁ outs₂ : List (LTy V)} {t₁ t₂ g₁ g₂ : List V.Ty}
    (hf : fns₁ = fns₂) (hi : ins₁ = ins₂) (ho : outs₁ = outs₂) (ht : t₁ = t₂) (hg : g₁ = g₂)
    (ft₁ : FnTable M fns₁) (ft₂ : FnTable M fns₂) (hft : hf ▸ ft₁ = ft₂)
    (cr : ClosedRole V fns₁ r ins₁ outs₁ t₁ g₁)
    (ins : HList (RV M r) ins₂) (taken : HList M.Val t₂) :
    ((castClosedRole hf hi ho ht hg cr).denote M ft₂ ins taken).map (fun _ => ()) =
      (cr.denote M ft₁ (hi.symm ▸ ins) (ht.symm ▸ taken)).map (fun _ => ()) := by
  subst hf; subst hi; subst ho; subst ht; subst hg; subst hft; rfl

noncomputable section

private theorem baseDeployedFast_isSome :
    (deploy deployEncoder baseAdmittedFast schnorrDecl).toOption.isSome = true := by
  rw [baseAdmittedFast_eq]
  exact baseSchnorr_deploy_isSome

def baseDeployedFast : Deployed deployVocab :=
  (deploy deployEncoder baseAdmittedFast schnorrDecl).toOption.get baseDeployedFast_isSome

theorem baseDeployedFast_ok :
    deploy deployEncoder baseAdmittedFast schnorrDecl = .ok baseDeployedFast :=
  except_toOption_get_ok _ baseDeployedFast_isSome

theorem baseDeployedFast_eq : baseDeployedFast = baseDeployed :=
  deploy_eq_of_eq baseAdmittedFast_eq baseDeployedFast_ok baseSchnorr_deploy_ok

theorem baseDeployedFast_fns_eq :
    baseDeployedFast.admitted.program.headers.fns = fnInstalled.headers.fns := by
  kernel_rfl

theorem baseDeployedFast_ins_eq :
    baseDeployedFast.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] := by
  kernel_rfl

theorem baseDeployedFast_outs_eq :
    baseDeployedFast.entry.outs = [] := by
  kernel_rfl

theorem baseDeployedFast_takes_eq :
    Stack.Takes (baseDeployedFast.stack 1) = [dBytes] := by
  kernel_rfl

theorem baseDeployedFast_gives_eq :
    Stack.Gives (baseDeployedFast.stack 1) = [] := by
  kernel_rfl

private theorem fnTable_eq_of_program_eq {V : Vocabulary} (M : Model V)
    {p₁ p₂ : Typed V} (hp : p₁ = p₂) (hf : p₁.headers.fns = p₂.headers.fns) :
    hf ▸ Defs.fnTable M p₁.defs = Defs.fnTable M p₂.defs := by
  subst hp; rfl

theorem baseDeployedFast_fnTable_eq :
    baseDeployedFast_fns_eq ▸ Defs.fnTable deployModel baseDeployedFast.admitted.program.defs =
      Defs.fnTable deployModel fnInstalled.defs := by
  have hProg : baseDeployedFast.admitted.program = baseInstalled := by
    have hAdm : baseDeployedFast.admitted = baseAdmittedFast :=
      (deploy_keeps deployEncoder baseAdmittedFast schnorrDecl baseDeployedFast baseDeployedFast_ok).1
    rw [hAdm]
  exact fnTable_eq_of_program_eq deployModel hProg baseDeployedFast_fns_eq

kernel_normal sessBytesNorm : List Nat := 0 :: baseDeployedFast.identity
kernel_normal st0Val : Nat := mixBytes 1 sessBytesNorm

/-- Exact mathematical specification of the Schnorr verifier `Process` for ANY `Y : Nat` and
ANY proof byte list `proof : List Nat` (including exact `Stop` occurrences on every failure). -/
def schnorrVerifierSpec (Y : Nat) (proof : List Nat) : Process (RSig deployModel) Stop Unit :=
  match proof with
  | [] => .halt (.declared .reject ⟨[], ⟨3⟩⟩)
  | [b0] =>
      if b0 < 23 then .halt (.declared .reject ⟨[], ⟨3⟩⟩)
      else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
  | b0 :: b1 :: rest =>
      if b0 < 23 then
        if b1 < 11 then
          let st1 := mixBytes (mixBytes st0Val (stmtLabel 0)) [Y % 256]
          let st2 := mixBytes (mixBytes st1 (msgLabel ⟨[], ⟨12⟩⟩)) [(b0 % 23) % 256]
          let c := mixBytes st2 (0xFF :: drawLabel ⟨[], ⟨13⟩⟩) % 11
          if decide (powMod 2 (b1 % 11) 23 = ((b0 % 23) * powMod Y c 23) % 23) then
            match rest with
            | [] => .done ()
            | _ :: _ => .halt (.declared .reject ⟨[], ⟨29⟩⟩)
          else
            .halt (.declared .reject ⟨[], ⟨21⟩⟩)
        else
          .halt (.declared .reject ⟨[], ⟨8⟩⟩)
      else
        .halt (.declared .reject ⟨[], ⟨8⟩⟩)

/-- Verifier process of the re-admitted `serialized Core` Schnorr protocol. -/
def serVerifierProc (Y : Nat) (proof : List Nat) : Process (RSig deployModel) Stop Unit :=
  (roleMeaning deployModel serializedInstalled serRoot 1 []
    (.cons proof (.cons () (.cons Y .nil)))).map (fun _ => ())

/-- Verifier process of `Core.deploy` (`baseDeployedFast.run`). -/
def depVerifierProc (Y : Nat) (proof : List Nat) : Process (RSig deployModel) Stop Unit :=
  (baseDeployedFast.run deployModel 1
    (baseDeployedFast_ins_eq.symm ▸ (.cons () (.cons Y .nil)))
    (baseDeployedFast_takes_eq.symm ▸ (.cons proof .nil))).map (fun _ => ())

/-- Verifier process of `Core.specialize` on `baseDeployedFast`. -/
def specVerifierProc (Y : Nat) (proof : List Nat) : Process (RSig deployModel) Stop Unit :=
  ((specialize baseDeployedFast 1).denote deployModel
    (Defs.fnTable deployModel baseDeployedFast.admitted.program.defs)
    (baseDeployedFast_ins_eq.symm ▸ (.cons () (.cons Y .nil)))
    (baseDeployedFast_takes_eq.symm ▸ (.cons proof .nil))).map (fun _ => ())

theorem specVerifierProc_eq_depVerifierProc (Y : Nat) (proof : List Nat) :
    specVerifierProc Y proof = depVerifierProc Y proof :=
  congrArg (Process.map (fun _ => ()))
    (specialize_deploy_sound deployModel deployEncoder baseAdmittedFast schnorrDecl
      baseDeployedFast baseDeployedFast_ok 1 _ _)

private theorem mixBytes_eq_st0Val (bs : List Nat) (h : bs = sessBytesNorm) :
    mixBytes 1 bs = st0Val := by
  rw [h, ← st0Val.eq]

private theorem liftEmpty_read_done {S : Sig} {A : Type} (a : A) :
    ZkcFormal.Form.liftEmpty S id (Reading.read (.done a)) =
      (pure a : Reading.Comp S Stop A) := rfl

private theorem liftEmpty_read_halt {S : Sig} {A : Type} (s : Stop) :
    ZkcFormal.Form.liftEmpty S id (Reading.read (.halt s)) =
      (throw s : Reading.Comp S Stop A) := rfl

private theorem map_throw_comp {S : Sig} {A B : Type} (f : A → B) (s : Stop) :
    (f <$> (throw s : Reading.Comp S Stop A)) = throw s := rfl

private theorem map_pure_comp {S : Sig} {A B : Type} (f : A → B) (a : A) :
    (f <$> (pure a : Reading.Comp S Stop A)) = pure (f a) := rfl

private theorem throw_bind_comp {S : Sig} {A B : Type} (s : Stop) (k : A → Reading.Comp S Stop B) :
    ((throw s : Reading.Comp S Stop A) >>= k) = throw s := rfl

private theorem pure_bind_comp {S : Sig} {A B : Type} (a : A) (k : A → Reading.Comp S Stop B) :
    ((pure a : Reading.Comp S Stop A) >>= k) = k a := rfl

private theorem liftEmpty_optionE_some {S : Sig} {A : Type} (a : A) :
    ZkcFormal.Form.liftEmpty S id (ZkcFormal.Form.optionE (S := NoSig) (some a) id) =
      (pure a : Reading.Comp S Stop A) := rfl

private theorem deployModel_apply_base
    (h : deployVocab.row DeployRow.base = some ⟨[dScalar], [dPoint], .pure⟩)
    (z : deployModel.Val dScalar) :
    deployModel.apply DeployRow.base ⟨[dScalar], [dPoint], .pure⟩ h (.cons z .nil) =
      some (.cons (toPoint (powMod 2 (fromScalar z) 23)) .nil) := rfl

private theorem deployModel_apply_scale
    (h : deployVocab.row DeployRow.scale = some ⟨[dScalar, dPoint], [dPoint], .pure⟩)
    (c : deployModel.Val dScalar) (y : deployModel.Val dPoint) :
    deployModel.apply DeployRow.scale ⟨[dScalar, dPoint], [dPoint], .pure⟩ h
      (.cons c (.cons y .nil)) =
      some (.cons (toPoint (powMod (fromPoint y) (fromScalar c) 23)) .nil) := rfl

private theorem deployModel_apply_plus
    (h : deployVocab.row DeployRow.plus = some ⟨[dPoint, dPoint], [dPoint], .pure⟩)
    (a b : deployModel.Val dPoint) :
    deployModel.apply DeployRow.plus ⟨[dPoint, dPoint], [dPoint], .pure⟩ h
      (.cons a (.cons b .nil)) =
      some (.cons (toPoint ((fromPoint a * fromPoint b) % 23)) .nil) := rfl

private theorem deployModel_apply_same
    (h : deployVocab.row DeployRow.same = some ⟨[dPoint, dPoint], [.bool], .pure⟩)
    (a b : deployModel.Val dPoint) :
    deployModel.apply DeployRow.same ⟨[dPoint, dPoint], [.bool], .pure⟩ h
      (.cons a (.cons b .nil)) =
      some (.cons (decide (fromPoint a = fromPoint b)) .nil) := rfl

private theorem nat_beq_two_add3 (n : Nat) : Nat.beq 2 (n + 3) = false := rfl

private theorem hStmtLbl0 :
    stmtLabel 0 = [15, 122, 107, 99, 46, 99, 111, 114, 101, 46, 115, 116, 109, 116, 47, 48, 0] := by
  kernel_rfl

private theorem hMsgLbl12 :
    msgLabel ⟨[], ⟨12⟩⟩ = [14, 122, 107, 99, 46, 99, 111, 114, 101, 46, 109, 115, 103, 47, 48, 0, 12] := by
  kernel_rfl

private theorem hDrawLbl13 :
    drawLabel ⟨[], ⟨13⟩⟩ = [15, 122, 107, 99, 46, 99, 111, 114, 101, 46, 100, 114, 97, 119, 47, 48, 0, 13] := by
  kernel_rfl

set_option maxRecDepth 8000 in
/-- Universal exact `Process` characterization of re-admitted `serialized Core` verifier. -/
theorem serVerifierProc_eq_spec (Y : Nat) (proof : List Nat) :
    serVerifierProc Y proof = schnorrVerifierSpec Y proof := by
  have hHeadY : ZkcFormal.Form.headV
      (HList.cons (V := RV deployModel 1) (a := (⟨dPoint, [0, 1]⟩ : LTy deployVocab))
        (rest := []) (toPoint Y) .nil) = toPoint Y := rfl
  apply Reading.read_injective
  unfold serVerifierProc
  rw [Reading.read_map, SerializedVerifier.reads]
  change _ <$> SerializedVerifier.form deployModel [] (.cons proof (.cons () (.cons (toPoint Y) .nil))) = _
  dsimp only [SerializedVerifier.form]
  simp only [ZkcFormal.Form.headV_cons, ZkcFormal.Form.tailV_cons, hHeadY]
  rw [fnStart_eval, mixBytes_eq_st0Val _ (by kernel_rfl), liftEmpty_read_done,
    pure_bind_comp, pure_bind_comp]
  simp only [ZkcFormal.Form.headV_cons]
  rw [fnEncPoint_eval, liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
  simp only [ZkcFormal.Form.headV_cons]
  rw [fnAbsorb_eval, liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
  simp only [ZkcFormal.Form.headV_cons]
  cases proof with
  | nil =>
      rw [fnReadPoint_eval_nil, liftEmpty_read_halt, throw_bind_comp, throw_bind_comp, map_throw_comp]
      rfl
  | cons b0 rest =>
      cases rest with
      | nil =>
          rw [fnReadPoint_eval_cons]
          cases Nat.decLt b0 23 with
          | isTrue h0 =>
              simp only [h0, ↓reduceIte, schnorrVerifierSpec]
              rw [liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
              simp only [ZkcFormal.Form.headV_cons, ZkcFormal.Form.tailV_cons]
              rw [fnEncPoint_eval, liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
              simp only [ZkcFormal.Form.headV_cons]
              rw [fnAbsorb_eval, liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
              simp only [ZkcFormal.Form.headV_cons]
              rw [fnDerive_eval, liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
              simp only [ZkcFormal.Form.headV_cons, ZkcFormal.Form.tailV_cons]
              rw [fnReadScalar_eval_singleton, liftEmpty_read_halt, throw_bind_comp, throw_bind_comp,
                map_throw_comp]
              rfl
          | isFalse h0 =>
              simp only [h0, ↓reduceIte, schnorrVerifierSpec]
              rw [liftEmpty_read_halt, throw_bind_comp, throw_bind_comp, map_throw_comp]
              rfl
      | cons b1 tail =>
          rw [fnReadPoint_eval_cons]
          cases Nat.decLt b0 23 with
          | isTrue h0 =>
              simp only [h0, ↓reduceIte, schnorrVerifierSpec]
              rw [liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
              simp only [ZkcFormal.Form.headV_cons, ZkcFormal.Form.tailV_cons]
              rw [fnEncPoint_eval, liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
              simp only [ZkcFormal.Form.headV_cons]
              rw [fnAbsorb_eval, liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
              simp only [ZkcFormal.Form.headV_cons]
              rw [fnDerive_eval, liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
              simp only [ZkcFormal.Form.headV_cons, ZkcFormal.Form.tailV_cons]
              rw [fnReadScalar_eval_cons2]
              cases Nat.decLt b1 11 with
              | isTrue h1 =>
                  simp only [h1, ↓reduceIte]
                  rw [liftEmpty_read_done, pure_bind_comp, pure_bind_comp]
                  simp only [ZkcFormal.Form.headV_cons, ZkcFormal.Form.tailV_cons]
                  rw [deployModel_apply_base, liftEmpty_optionE_some, pure_bind_comp, pure_bind_comp]
                  simp only [ZkcFormal.Form.headV_cons]
                  rw [deployModel_apply_scale, liftEmpty_optionE_some, pure_bind_comp, pure_bind_comp]
                  simp only [ZkcFormal.Form.headV_cons]
                  rw [deployModel_apply_plus, liftEmpty_optionE_some, pure_bind_comp, pure_bind_comp]
                  simp only [ZkcFormal.Form.headV_cons]
                  rw [deployModel_apply_same, liftEmpty_optionE_some, pure_bind_comp, pure_bind_comp]
                  simp only [ZkcFormal.Form.headV_cons, fromPoint_toPoint, fromScalar_toScalar,
                    ← hStmtLbl0, ← hMsgLbl12, ← hDrawLbl13]
                  cases Nat.decEq (powMod 2 (b1 % 11) 23)
                      ((b0 % 23 * powMod Y (mixBytes (mixBytes (mixBytes (mixBytes (mixBytes st0Val (stmtLabel 0)) [Y % 256]) (msgLabel ⟨[], ⟨12⟩⟩)) [b0 % 23 % 256]) (0xFF :: drawLabel ⟨[], ⟨13⟩⟩) % 11) 23) % 23) with
                  | isTrue hEq =>
                      simp only [hEq, decide_true, ↓reduceIte, pure_bind_comp]
                      cases tail with
                      | nil => rfl
                      | cons b2 more =>
                          simp only [List.length_cons, nat_beq_two_add3, Bool.false_eq_true,
                            ↓reduceIte, throw_bind_comp, map_throw_comp]
                          rfl
                  | isFalse hEq =>
                      simp only [hEq, decide_false, Bool.false_eq_true, ↓reduceIte, throw_bind_comp,
                        map_throw_comp]
                      rfl
              | isFalse h1 =>
                  simp only [h1, ↓reduceIte]
                  rw [liftEmpty_read_halt, throw_bind_comp, throw_bind_comp, map_throw_comp]
                  rfl
          | isFalse h0 =>
              simp only [h0, ↓reduceIte, schnorrVerifierSpec]
              rw [liftEmpty_read_halt, throw_bind_comp, throw_bind_comp, map_throw_comp]
              rfl

/-- Direct 3-effect `Process` characterization of the interactive Schnorr verifier from
`BaseVerifier.reads` (zero `maxRecDepth` override). -/
theorem baseVerifier_process (Y : Nat) :
    roleMeaning deployModel baseInstalled baseRoot 1 [] (.cons () (.cons (toPoint Y) .nil)) =
      .call (ROp.get .message 0 ⟨[], ⟨12⟩⟩ dPoint) fun a =>
        .call (ROp.own (.coin ()) [0] ⟨[], ⟨13⟩⟩ [] .nil dScalar) fun c =>
          .call (ROp.get .message 0 ⟨[], ⟨16⟩⟩ dScalar) fun z =>
            if decide (powMod 2 (fromScalar z) 23 = (fromPoint a * powMod Y (fromScalar c) 23) % 23) then .done .nil
            else .halt (.declared .reject ⟨[], ⟨21⟩⟩) := by
  have hHeadY : ZkcFormal.Form.headV
      (HList.cons (V := RV deployModel 1) (a := (⟨dPoint, [0, 1]⟩ : LTy deployVocab))
        (rest := []) (toPoint Y) .nil) = toPoint Y := rfl
  apply Reading.read_injective
  rw [BaseVerifier.reads]
  dsimp only [BaseVerifier.form]
  simp only [ZkcFormal.Form.tailV_cons, hHeadY]
  rw [Reading.read_call]; congr 1; funext a
  rw [Reading.read_call]; congr 1; funext c
  rw [Reading.read_call]; congr 1; funext z
  rw [deployModel_apply_base, liftEmpty_optionE_some, pure_bind_comp, pure_bind_comp]
  simp only [ZkcFormal.Form.headV_cons]
  rw [deployModel_apply_scale, liftEmpty_optionE_some, pure_bind_comp, pure_bind_comp]
  simp only [ZkcFormal.Form.headV_cons]
  rw [deployModel_apply_plus, liftEmpty_optionE_some, pure_bind_comp, pure_bind_comp]
  simp only [ZkcFormal.Form.headV_cons]
  rw [deployModel_apply_same, liftEmpty_optionE_some, pure_bind_comp, pure_bind_comp]
  simp only [ZkcFormal.Form.headV_cons, fromPoint_toPoint]
  cases Nat.decEq (powMod 2 (fromScalar z) 23) ((fromPoint a * powMod Y (fromScalar c) 23) % 23) with
  | isTrue hEq => simp only [hEq, decide_true, ↓reduceIte, pure_bind_comp]; rfl
  | isFalse hEq => simp only [hEq, decide_false, Bool.false_eq_true, ↓reduceIte, throw_bind_comp]; rfl

unseal Zkc.Core.fnMeaning in
private theorem fnTable_eq_serFnMeaning {hdr : FnHeader deployVocab}
    (f : Member serializedInstalled.headers.fns hdr) :
    Defs.fnTable deployModel baseInstalled.defs hdr f =
      fnMeaning deployModel serializedInstalled f := rfl

private theorem fnStart_table (bs : List Nat) :
    Defs.fnTable deployModel baseInstalled.defs hdr0
      (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head)))))))))
      (.cons bs .nil) = .done (.cons (mixBytes 1 bs) .nil) :=
  (congrFun (fnTable_eq_serFnMeaning SerializedVerifier.function100) _).trans (fnStart_eval bs)

private theorem fnAbsorb_table (st : Nat) (lbl enc : List Nat) :
    Defs.fnTable deployModel baseInstalled.defs hdr1
      (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))))
      (.cons st (.cons lbl (.cons enc .nil))) =
      .done (.cons (mixBytes (mixBytes st lbl) enc) .nil) :=
  (congrFun (fnTable_eq_serFnMeaning SerializedVerifier.function101) _).trans
    (fnAbsorb_eval st lbl enc)

private theorem fnEncPoint_table (p : deployModel.Val dPoint) :
    Defs.fnTable deployModel baseInstalled.defs hdr3
      (.tail (.tail (.tail (.tail (.tail (.tail .head))))))
      (.cons p .nil) = .done (.cons [fromPoint p % 256] .nil) :=
  (congrFun (fnTable_eq_serFnMeaning SerializedVerifier.function103) _).trans (fnEncPoint_eval p)

private theorem fnDerive_table (st : Nat) (lbl : List Nat) :
    Defs.fnTable deployModel baseInstalled.defs hdr4
      (.tail (.tail (.tail (.tail (.tail .head)))))
      (.cons st (.cons lbl .nil)) =
      .done (.cons (toScalar (mixBytes st (0xFF :: lbl) % 11))
        (.cons (mixBytes st (0xFF :: lbl)) .nil)) :=
  (congrFun (fnTable_eq_serFnMeaning SerializedVerifier.function104) _).trans
    (fnDerive_eval st lbl)

private theorem fnReadScalar_table_singleton (b0 : Nat) :
    Defs.fnTable deployModel baseInstalled.defs hdr5
      (.tail (.tail (.tail (.tail .head))))
      (.cons ([b0] : List Nat) (.cons 1 .nil)) =
      .halt (.declared .reject ⟨[], ⟨3⟩⟩) :=
  (congrFun (fnTable_eq_serFnMeaning SerializedVerifier.function105) _).trans
    (fnReadScalar_eval_singleton b0)

private theorem fnReadScalar_table_cons2 (b0 b1 : Nat) (rest : List Nat) :
    Defs.fnTable deployModel baseInstalled.defs hdr5
      (.tail (.tail (.tail (.tail .head))))
      (.cons (b0 :: b1 :: rest) (.cons 1 .nil)) =
      if b1 < 11 then .done (.cons (toScalar (b1 % 11)) (.cons 2 .nil))
      else .halt (.declared .reject ⟨[], ⟨8⟩⟩) :=
  (congrFun (fnTable_eq_serFnMeaning SerializedVerifier.function105) _).trans
    (fnReadScalar_eval_cons2 b0 b1 rest)

private theorem fnReadPoint_table_nil :
    Defs.fnTable deployModel baseInstalled.defs hdr6
      (.tail (.tail (.tail .head)))
      (.cons ([] : List Nat) (.cons 0 .nil)) =
      .halt (.declared .reject ⟨[], ⟨3⟩⟩) :=
  (congrFun (fnTable_eq_serFnMeaning SerializedVerifier.function106) _).trans fnReadPoint_eval_nil

private theorem fnReadPoint_table_cons (b0 : Nat) (rest : List Nat) :
    Defs.fnTable deployModel baseInstalled.defs hdr6
      (.tail (.tail (.tail .head)))
      (.cons (b0 :: rest) (.cons 0 .nil)) =
      if b0 < 23 then .done (.cons (toPoint (b0 % 23)) (.cons 1 .nil))
      else .halt (.declared .reject ⟨[], ⟨8⟩⟩) :=
  (congrFun (fnTable_eq_serFnMeaning SerializedVerifier.function106) _).trans
    (fnReadPoint_eval_cons b0 rest)

private theorem deployed_run_map_eq {V : Vocabulary} (M : Model V) {d₁ d₂ : Deployed V}
    (hEq : d₁ = d₂) (r : Role)
    {ins₀ : List (LTy V)} {t₀ : List V.Ty}
    (hi₁ : d₁.entry.ins = ins₀) (ht₁ : Stack.Takes (d₁.stack r) = t₀)
    (hi₂ : d₂.entry.ins = ins₀) (ht₂ : Stack.Takes (d₂.stack r) = t₀)
    (ins : HList (RV M r) ins₀) (taken : HList M.Val t₀) :
    (d₁.run M r (hi₁.symm ▸ ins) (ht₁.symm ▸ taken)).map (fun _ => ()) =
      (d₂.run M r (hi₂.symm ▸ ins) (ht₂.symm ▸ taken)).map (fun _ => ()) := by
  subst hEq; rfl

private theorem deployed_run_stack_eq {V : Vocabulary} (M : Model V)
    (admitted : Admitted V) (decl : Declaration)
    (found : (admitted.program.findProtocol decl.entry).isSome)
    (stack : (r : Role) → List (Layer V admitted.program.headers r
      ((admitted.program.findProtocol decl.entry).get found).1.ins))
    (identity : List Nat) (r : Role)
    {hdr : ProtocolHeader V} {callee : Member admitted.program.headers.protocols hdr}
    (hPair : (admitted.program.findProtocol decl.entry).get found = ⟨hdr, callee⟩)
    (hNoRetry : (Deployed.mk admitted decl found stack identity).retry = none)
    {stk : List (Layer V admitted.program.headers r hdr.ins)}
    (hEntry : ((admitted.program.findProtocol decl.entry).get found).1 = hdr)
    (hStack : (congrArg ProtocolHeader.ins hEntry ▸ stack r :
      List (Layer V admitted.program.headers r hdr.ins)) = stk)
    {ins₀ : List (LTy V)} {t₀ : List V.Ty}
    (hi : ((admitted.program.findProtocol decl.entry).get found).1.ins = ins₀)
    (ht : Stack.Takes (stack r) = t₀)
    (hi' : hdr.ins = ins₀) (ht' : Stack.Takes stk = t₀)
    (ins : HList (RV M r) ins₀) (taken : HList M.Val t₀) :
    ((Deployed.mk admitted decl found stack identity).run M r (hi.symm ▸ ins) (ht.symm ▸ taken)).map (fun _ => ()) =
      ((Stack.start M (Defs.fnTable M admitted.program.defs) stk (hi'.symm ▸ ins) (ht'.symm ▸ taken)).bind fun first =>
        (((Stack.handler M (Defs.fnTable M admitted.program.defs)
            (Defs.rTable M admitted.program.defs) stk).run (retryOf M none)
            (roleMeaning M admitted.program callee r [] (hi'.symm ▸ ins)) first).mapHalt Prod.fst).bind fun out =>
          (Stack.finish M (Defs.fnTable M admitted.program.defs) stk out.2).map
            fun gives => (out.1, gives)).map (fun _ => ()) := by
  unfold Deployed.run Deployed.entry Deployed.callee
  rw [hNoRetry]; clear hNoRetry
  dsimp only
  revert hStack ht
  generalize stack r = sr
  revert sr hEntry hi hPair
  generalize (admitted.program.findProtocol decl.entry).get found = p
  intro hPair hEntry hi sr hStack ht
  subst hPair
  subst hStack
  rfl

private def stackNil {V : Vocabulary} (M : Model V) {hs : Headers V} {r : Role} {ins : List (LTy V)} :
    HList M.Val (Stack.States ([] : List (Layer V hs r ins))) := .nil

private def stackOne {V : Vocabulary} (M : Model V) {hs : Headers V} {r : Role} {ins : List (LTy V)}
    {l₂ : Layer V hs r ins} (s₂ : M.Val l₂.state) :
    HList M.Val (Stack.States [l₂]) :=
  .cons s₂ .nil

private def stackTwo {V : Vocabulary} (M : Model V) {hs : Headers V} {r : Role} {ins : List (LTy V)}
    {l₁ l₂ : Layer V hs r ins} (s₁ : M.Val l₁.state) (s₂ : M.Val l₂.state) :
    HList M.Val (Stack.States [l₁, l₂]) :=
  .cons s₁ (.cons s₂ .nil)

private theorem stack_start_two_done {V : Vocabulary} (M : Model V) {hs : Headers V}
    {r : Role} {ins : List (LTy V)} (table : FnTable M hs.fns)
    (l₁ l₂ : Layer V hs r ins)
    (hT1 : l₁.takes = []) {τ₂ : V.Ty} (hT2 : l₂.takes = [τ₂])
    (args : HList (RV M r) ins) (x₂ : M.Val τ₂)
    (ht : Stack.Takes [l₁, l₂] = [τ₂])
    {v₁ : HList M.Val [l₁.state]} {v₂ : HList M.Val [l₂.state]}
    (h₁ : l₁.start.denote (localSem M hs.fns table) []
        (Env.positional (hT1.symm ▸ heldValues M r args)) = .done v₁)
    (h₂ : l₂.start.denote (localSem M hs.fns table) []
        (Env.positional (hT2.symm ▸ (HList.cons x₂ .nil).append (heldValues M r args))) = .done v₂) :
    Stack.start M table [l₁, l₂] args (ht.symm ▸ .cons x₂ .nil) =
      .done (stackTwo M v₁.single v₂.single) := by
  cases l₁; cases l₂; dsimp only at hT1 hT2; subst hT1; subst hT2
  dsimp only [Stack.start]
  simp only [HList.split, HList.append]
  erw [h₁, h₂]
  rfl

private theorem clause_answer_cons_ne {V : Vocabulary} (M : Model V) {hs : Headers V}
    {r : Role} {stateTy : V.Ty} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (c : Clause V hs r stateTy) (cs : List (Clause V hs r stateTy))
    (op : ROp M) (s : M.Val stateTy) (hNe : c.site.site ≠ (ROp.occurrence M op).site) :
    Clause.answer M fnTable rTable (c :: cs) op s = Clause.answer M fnTable rTable cs op s := by
  conv_lhs => unfold Clause.answer
  rw [dite_eq_right (fun h => hNe h.1)]

private theorem layoutVReadClause_answer_halt {V : Vocabulary} (M : Model V) {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (rRef : LayerBuild.SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (at_ : Occurrence) (hSite : site = at_.site) (buf : List (M.Val unitTy)) (off : Nat)
    (why : Stop)
    (hR : rRef.eval M fnTable (.cons buf (.cons off .nil)) = .halt why)
    (cs : List (Clause V hs verifier (LayerBuild.streamStateTy unitTy))) :
    Clause.answer M fnTable rTable
        (LayerBuild.layoutVReadClause hfree verifier prover site kind rRef :: cs)
        (.get kind prover at_ τ) (buf, (off, ())) =
      .halt (why, (buf, (off, ()))) := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((LayerBuild.layoutVReadClause hfree verifier prover site kind rRef).code.denote
    (roleSem M verifier fnTable rTable) at_.path
    (Env.positional (aloneIn M verifier (.cons (buf, (off, ())) .nil)))).mapHalt _).map _ = _
  rw [LayerBuild.layoutVReadClause_denote, hR]
  rfl

private theorem stackTwo_clause_step {V : Vocabulary} (M : Model V) {hs : Headers V}
    {r : Role} {ins : List (LTy V)} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (l₁ l₂ : Layer V hs r ins) (op : (RSig M).Op) (s₁ : M.Val l₁.state) (s₂ : M.Val l₂.state) :
    (Stack.handler M fnTable rTable [l₁, l₂]).clause op (stackTwo M s₁ s₂) =
      Process.map (fun out => (out.1, HList.cons out.2.1 out.2.2))
        (Process.mapHalt (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))
          ((((Stack.handler M fnTable rTable [l₂]).answer
              (Clause.answer M fnTable rTable l₁.clauses op s₁) s₁ (stackOne M s₂)).mapHalt
              fun stop => (stop.1, (stop.2.1, stop.2.2))).bind fun out =>
            .done (out.1.1, (out.1.2, out.2)))) := rfl

private theorem stackOne_clause_step {V : Vocabulary} (M : Model V) {hs : Headers V}
    {r : Role} {ins : List (LTy V)} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (l₂ : Layer V hs r ins) (op' : (RSig M).Op) (s₂ : M.Val l₂.state) :
    (Stack.handler M fnTable rTable [l₂]).clause op' (stackOne M s₂) =
      Process.map (fun out => (out.1, HList.cons out.2.1 out.2.2))
        (Process.mapHalt (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))
          ((((Stack.handler M fnTable rTable []).answer
              (Clause.answer M fnTable rTable l₂.clauses op' s₂) s₂ (stackNil M)).mapHalt
              fun stop => (stop.1, (stop.2.1, stop.2.2))).bind fun out =>
            .done (out.1.1, (out.1.2, out.2)))) := rfl

private theorem stackTwo_call_both_done {V : Vocabulary} (M : Model V) {hs : Headers V}
    {r : Role} {ins : List (LTy V)} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (l₁ l₂ : Layer V hs r ins) {A : Type}
    (op op' : (RSig M).Op) (k : (RSig M).Reply op → Process (RSig M) Stop A)
    (s₁ s₁' : M.Val l₁.state) (s₂ s₂' : M.Val l₂.state)
    (v₁ : (RSig M).Reply op) (v₂ : (RSig M).Reply op')
    (k₁ : (RSig M).Reply op' → Process (RSig M) (Stop × M.Val l₁.state) ((RSig M).Reply op × M.Val l₁.state))
    (h₁ : Clause.answer M fnTable rTable l₁.clauses op s₁ = .call op' k₁)
    (h₂ : Clause.answer M fnTable rTable l₂.clauses op' s₂ = .done (v₂, s₂'))
    (hk₁ : k₁ v₂ = .done (v₁, s₁')) :
    (Stack.handler M fnTable rTable [l₁, l₂]).run (retryOf M none) (.call op k) (stackTwo M s₁ s₂) =
      (Stack.handler M fnTable rTable [l₁, l₂]).run (retryOf M none) (k v₁) (stackTwo M s₁' s₂') := by
  change ((Stack.handler M fnTable rTable [l₁, l₂]).clause op (stackTwo M s₁ s₂)).bind
    (fun out => (Stack.handler M fnTable rTable [l₁, l₂]).run (retryOf M none) (k out.1) out.2) = _
  rw [stackTwo_clause_step, h₁]
  dsimp only [Handler.answer]
  rw [stackOne_clause_step, h₂]
  dsimp only [Handler.answer, Process.bind, Process.map, Process.mapHalt]
  rw [hk₁]
  rfl

private theorem stackTwo_call_both_halt {V : Vocabulary} (M : Model V) {hs : Headers V}
    {r : Role} {ins : List (LTy V)} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (l₁ l₂ : Layer V hs r ins) {A : Type}
    (op op' : (RSig M).Op) (k : (RSig M).Reply op → Process (RSig M) Stop A)
    (s₁ : M.Val l₁.state) (s₂ s₂' : M.Val l₂.state) (why : Stop)
    (k₁ : (RSig M).Reply op' → Process (RSig M) (Stop × M.Val l₁.state) ((RSig M).Reply op × M.Val l₁.state))
    (h₁ : Clause.answer M fnTable rTable l₁.clauses op s₁ = .call op' k₁)
    (h₂ : Clause.answer M fnTable rTable l₂.clauses op' s₂ = .halt (why, s₂')) :
    ((Stack.handler M fnTable rTable [l₁, l₂]).run (retryOf M none) (.call op k) (stackTwo M s₁ s₂)).mapHalt Prod.fst =
      .halt why := by
  change (((Stack.handler M fnTable rTable [l₁, l₂]).clause op (stackTwo M s₁ s₂)).bind
    (fun out => (Stack.handler M fnTable rTable [l₁, l₂]).run (retryOf M none) (k out.1) out.2)).mapHalt Prod.fst = _
  rw [stackTwo_clause_step, h₁]
  dsimp only [Handler.answer]
  rw [stackOne_clause_step, h₂]
  rfl

private theorem stackTwo_finish_done {V : Vocabulary} (M : Model V) {hs : Headers V}
    {r : Role} {ins : List (LTy V)} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (l₁ l₂ : Layer V hs r ins) {A : Type} (a : A) (s₁ : M.Val l₁.state) (s₂ : M.Val l₂.state)
    {g₁ : HList M.Val l₁.gives} {g₂ : HList M.Val l₂.gives}
    (h₁ : l₁.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₁ .nil)) = .done g₁)
    (h₂ : l₂.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₂ .nil)) = .done g₂) :
    ((((Stack.handler M fnTable rTable [l₁, l₂]).run (retryOf M none) (.done a) (stackTwo M s₁ s₂)).mapHalt Prod.fst).bind
      fun out => (Stack.finish M fnTable [l₁, l₂] out.2).map fun gives => (out.1, gives)).map (fun _ => ()) =
      .done () := by
  change (((liftLocal id (l₁.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₁ .nil)))).bind
    fun mine1 => ((liftLocal id (l₂.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₂ .nil)))).bind
      fun mine2 => (Process.done .nil).map fun others => HList.append mine2 others).map
        fun others => HList.append mine1 others).map fun gives => (a, gives)).map (fun _ => ()) = _
  rw [h₁, h₂]
  rfl

private theorem stackTwo_finish_halt2 {V : Vocabulary} (M : Model V) {hs : Headers V}
    {r : Role} {ins : List (LTy V)} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (l₁ l₂ : Layer V hs r ins) {A : Type} (a : A) (s₁ : M.Val l₁.state) (s₂ : M.Val l₂.state)
    {g₁ : HList M.Val l₁.gives} {why : Stop}
    (h₁ : l₁.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₁ .nil)) = .done g₁)
    (h₂ : l₂.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₂ .nil)) = .halt why) :
    ((((Stack.handler M fnTable rTable [l₁, l₂]).run (retryOf M none) (.done a) (stackTwo M s₁ s₂)).mapHalt Prod.fst).bind
      fun out => (Stack.finish M fnTable [l₁, l₂] out.2).map fun gives => (out.1, gives)).map (fun _ => ()) =
      .halt why := by
  change (((liftLocal id (l₁.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₁ .nil)))).bind
    fun mine1 => ((liftLocal id (l₂.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₂ .nil)))).bind
      fun mine2 => (Process.done .nil).map fun others => HList.append mine2 others).map
        fun others => HList.append mine1 others).map fun gives => (a, gives)).map (fun _ => ()) = _
  rw [h₁, h₂]
  rfl

private def events0 : List (ShapeEvent deployVocab) := hdrBase.shape.events [] id
private def tk0 : Key := drawToldKey events0 2
private def finKey0 : Key := finishGuardKey events0

private theorem hFinKey0 : finKey0 = ⟨29⟩ := by kernel_rfl
private theorem hTk0Ne12 : ({ through := [], key := ⟨12⟩ } : Site) ≠ ⟨[], tk0⟩ := by decide +kernel
private theorem hTk0Ne16 : ({ through := [], key := tk0 } : Site) ≠ ⟨[], ⟨16⟩⟩ := by decide +kernel

private def startRef0 : LayerBuild.TypedFnRef deployVocab baseInstalled.headers.fns
    [LayerBuild.bytesTy] [.nat] :=
  ⟨hdr0, SerializedVerifier.function100, rfl, rfl, rfl, rfl⟩

private def absorbRef0 : LayerBuild.TypedFnRef deployVocab baseInstalled.headers.fns
    [.nat, LayerBuild.bytesTy, dBytes] [.nat] :=
  ⟨hdr1, SerializedVerifier.function101, rfl, rfl, rfl, rfl⟩

private def encPtRef0 : LayerBuild.TypedFnRef deployVocab baseInstalled.headers.fns
    [dPoint] [dBytes] :=
  ⟨hdr3, SerializedVerifier.function103, rfl, rfl, rfl, rfl⟩

private def derRef0 : LayerBuild.TypedFnRef deployVocab baseInstalled.headers.fns
    [.nat, LayerBuild.bytesTy] [dScalar, .nat] :=
  ⟨hdr4, SerializedVerifier.function104, rfl, rfl, rfl, rfl⟩

private def readScRef0 : LayerBuild.SafeFnRef deployVocab baseInstalled.headers.fns
    [dBytes, .nat] [dScalar, .nat] :=
  ⟨hdr5, SerializedVerifier.function105, rfl, rfl, rfl⟩

private def readPtRef0 : LayerBuild.SafeFnRef deployVocab baseInstalled.headers.fns
    [dBytes, .nat] [dPoint, .nat] :=
  ⟨hdr6, SerializedVerifier.function106, rfl, rfl, rfl⟩

private theorem encPtRef0_eval (p : deployModel.Val dPoint) :
    encPtRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs) (.cons p .nil) =
      .done (.cons [fromPoint p % 256] .nil) :=
  fnEncPoint_table p

private theorem absorbRef0_eval (st : Nat) (lbl enc : List Nat) :
    absorbRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (.cons st (.cons lbl (.cons enc .nil))) =
      .done (.cons (mixBytes (mixBytes st lbl) enc) .nil) :=
  fnAbsorb_table st lbl enc

private theorem derRef0_eval (st : Nat) (lbl : List Nat) :
    derRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (.cons st (.cons lbl .nil)) =
      .done (.cons (toScalar (mixBytes st (0xFF :: lbl) % 11))
        (.cons (mixBytes st (0xFF :: lbl)) .nil)) :=
  fnDerive_table st lbl

private theorem readPtRef0_eval_nil :
    readPtRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (.cons ([] : List Nat) (.cons 0 .nil)) =
      .halt (.declared .reject ⟨[], ⟨3⟩⟩) :=
  fnReadPoint_table_nil

private theorem readPtRef0_eval_cons (b0 : Nat) (rest : List Nat) :
    readPtRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (.cons (b0 :: rest) (.cons 0 .nil)) =
      if b0 < 23 then .done (.cons (toPoint (b0 % 23)) (.cons 1 .nil))
      else .halt (.declared .reject ⟨[], ⟨8⟩⟩) :=
  fnReadPoint_table_cons b0 rest

private theorem readScRef0_eval_singleton (b0 : Nat) :
    readScRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (.cons ([b0] : List Nat) (.cons 1 .nil)) =
      .halt (.declared .reject ⟨[], ⟨3⟩⟩) :=
  fnReadScalar_table_singleton b0

private theorem readScRef0_eval_cons2 (b0 b1 : Nat) (rest : List Nat) :
    readScRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (.cons (b0 :: b1 :: rest) (.cons 1 .nil)) =
      if b1 < 11 then .done (.cons (toScalar (b1 % 11)) (.cons 2 .nil))
      else .halt (.declared .reject ⟨[], ⟨8⟩⟩) :=
  fnReadScalar_table_cons2 b0 b1 rest

private def cV0 : List (Clause deployVocab baseInstalled.headers 1 .nat) := [
  LayerBuild.verifierAbsorbClause (hs := baseInstalled.headers) 1 0 ⟨[], ⟨12⟩⟩ .message
    (msgLabel ⟨[], ⟨12⟩⟩) (msgLabel_bytes _) encPtRef0 absorbRef0,
  LayerBuild.deriveClause (hs := baseInstalled.headers) 1 0 ⟨[], ⟨13⟩⟩
    (.own (.coin ()) [0]) [] tk0 (drawLabel ⟨[], ⟨13⟩⟩) (drawLabel_bytes _) derRef0
]

private def layV0 : Layer deployVocab baseInstalled.headers 1 hdrBase.ins := {
  line := .layout
  state := LayerBuild.streamStateTy dByte
  takes := [dBytes]
  gives := []
  clauses := [
    LayerBuild.layoutVReadClause (hs := baseInstalled.headers) (unitTy := dByte) rfl
      1 0 ⟨[], ⟨12⟩⟩ .message readPtRef0,
    LayerBuild.layoutDropClause (hs := baseInstalled.headers)
      (stateTy := LayerBuild.streamStateTy dByte) (τ := dScalar) 1 ⟨[], tk0⟩ .message [0],
    LayerBuild.layoutVReadClause (hs := baseInstalled.headers) (unitTy := dByte) rfl
      1 0 ⟨[], ⟨16⟩⟩ .message readScRef0
  ]
  again := LayerBuild.restoreAgain (fns := baseInstalled.headers.fns)
    (LayerBuild.streamStateTy dByte)
  start := LayerBuild.layoutVStart (fns := baseInstalled.headers.fns) (r := 1)
    (ins := hdrBase.ins) dByte
  finish := LayerBuild.layoutVFinish (fns := baseInstalled.headers.fns) dByte rfl finKey0
}

private def conVLayer (sessBytes : List Nat) (hSessBytes : ∀ b ∈ sessBytes, b < 256) :
    Layer deployVocab baseInstalled.headers 1 hdrBase.ins := {
  line := .construction
  state := .nat
  takes := []
  gives := []
  clauses := cV0
  again := LayerBuild.restoreAgain (fns := baseInstalled.headers.fns) .nat
  start := LayerBuild.constructionStart (r := 1) (ins := hdrBase.ins)
    sessBytes hSessBytes startRef0 absorbRef0
    [⟨dPoint, ⟨0, rfl⟩, stmtLabel 0, stmtLabel_bytes 0, encPtRef0⟩]
  finish := LayerBuild.emptyFinish .nat
}

private def schnorrVerifierFromSt1 (Y st1 : Nat) (proof : List Nat) : Process (RSig deployModel) Stop Unit :=
  match proof with
  | [] => .halt (.declared .reject ⟨[], ⟨3⟩⟩)
  | [b0] =>
      if b0 < 23 then .halt (.declared .reject ⟨[], ⟨3⟩⟩)
      else .halt (.declared .reject ⟨[], ⟨8⟩⟩)
  | b0 :: b1 :: rest =>
      if b0 < 23 then
        if b1 < 11 then
          let st2 := mixBytes (mixBytes st1 (msgLabel ⟨[], ⟨12⟩⟩)) [(b0 % 23) % 256]
          let c := mixBytes st2 (0xFF :: drawLabel ⟨[], ⟨13⟩⟩) % 11
          if decide (powMod 2 (b1 % 11) 23 = ((b0 % 23) * powMod Y c 23) % 23) then
            match rest with
            | [] => .done ()
            | _ :: _ => .halt (.declared .reject ⟨[], ⟨29⟩⟩)
          else
            .halt (.declared .reject ⟨[], ⟨21⟩⟩)
        else
          .halt (.declared .reject ⟨[], ⟨8⟩⟩)
      else
        .halt (.declared .reject ⟨[], ⟨8⟩⟩)

private theorem verifierAbsorb_k1_done {fnTab : FnTable deployModel baseInstalled.headers.fns}
    {st1 st2 : Nat} {msg : deployModel.Val dPoint} {enc : List Nat} {lbl : List Nat}
    (hEnc : encPtRef0.eval deployModel fnTab (.cons msg .nil) = .done (.cons enc .nil))
    (hAbs : absorbRef0.eval deployModel fnTab (.cons st1 (.cons lbl (.cons enc .nil))) = .done (.cons st2 .nil)) :
    ((((liftLocal (S := RSig deployModel) id (encPtRef0.eval deployModel fnTab (.cons msg .nil))).bind
      fun e => (liftLocal (S := RSig deployModel) id (absorbRef0.eval deployModel fnTab
        (.cons st1 (.cons lbl (.cons e.single .nil))))).map
        fun nextSt => aloneIn deployModel 1 (.cons msg nextSt)).mapHalt
      fun why => (why, st1)).map fun out =>
        let values := HList.split [dPoint] (aloneOut deployModel 1 out)
        (values.1.single, values.2.single)) =
    .done (msg, st2) := by
  rw [hEnc]
  change ((((liftLocal (S := RSig deployModel) id (absorbRef0.eval deployModel fnTab
    (.cons st1 (.cons lbl (.cons enc .nil))))).map
    fun nextSt => aloneIn deployModel 1 (.cons msg nextSt)).mapHalt
    fun why => (why, st1)).map fun out =>
      let values := HList.split [dPoint] (aloneOut deployModel 1 out)
      (values.1.single, values.2.single)) = _
  rw [hAbs]
  change Process.done (let values := HList.split [dPoint] (aloneOut deployModel 1 (aloneIn deployModel 1 (.cons msg (.cons (a := .nat) st2 .nil))))
    (values.1.single, values.2.single)) = _
  rfl

private theorem cV0_derive_answer (st : Nat) {coin : deployModel.Val dScalar} {st' : Nat}
    (hDer : derRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (.cons st (.cons (drawLabel ⟨[], ⟨13⟩⟩) .nil)) = .done (.cons coin (.cons st' .nil))) :
    Clause.answer deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (Defs.rTable deployModel baseInstalled.defs) cV0
      (.own (.coin ()) [0] ⟨[], ⟨13⟩⟩ [] .nil dScalar) st =
      .call (.give .message [0] ⟨[], tk0⟩ dScalar coin) fun _ => .done (coin, st') := by
  unfold cV0
  rw [clause_answer_cons_ne deployModel _ _ _ _ _ _ (by decide)]
  exact deriveClause_answer_own (M := deployModel) _ _ 1 0 ⟨[], ⟨13⟩⟩ () [0] tk0
    (drawLabel ⟨[], ⟨13⟩⟩) (drawLabel_bytes _) derRef0 ⟨[], ⟨13⟩⟩ rfl st coin st' hDer []

private theorem layV0_drop_answer (c : deployModel.Val dScalar) (buf : List Nat) (off : Nat) :
    Clause.answer deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (Defs.rTable deployModel baseInstalled.defs) layV0.clauses
      (.give .message [0] ⟨[], tk0⟩ dScalar c) (buf, (off, ())) =
      .done ((), (buf, (off, ()))) := by
  unfold layV0
  dsimp only
  rw [clause_answer_cons_ne deployModel _ _ _ _ _ _ hTk0Ne12]
  exact layoutDropClause_answer (M := deployModel) (stateTy := LayerBuild.streamStateTy dByte)
    (τ := dScalar) _ _ 1 ⟨[], tk0⟩ .message [0] ⟨[], tk0⟩ rfl c (buf, (off, ())) _

private theorem cV0_step3_pass (st : Nat) :
    Clause.answer deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (Defs.rTable deployModel baseInstalled.defs) cV0
      (.get .message 0 ⟨[], ⟨16⟩⟩ dScalar) st =
      .call (.get .message 0 ⟨[], ⟨16⟩⟩ dScalar) fun z => .done (z, st) := by
  unfold cV0
  rw [clause_answer_cons_ne deployModel _ _ _ _ _ _ (by decide)]
  rw [clause_answer_cons_ne deployModel _ _ _ _ _ _ (by decide)]
  rfl

private theorem layV0_readSc_halt (buf : List Nat) (off : Nat) (why : Stop)
    (hR : readScRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (.cons buf (.cons off .nil)) = .halt why) :
    Clause.answer deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (Defs.rTable deployModel baseInstalled.defs) layV0.clauses
      (.get .message 0 ⟨[], ⟨16⟩⟩ dScalar) (buf, (off, ())) =
      .halt (why, (buf, (off, ()))) := by
  unfold layV0; dsimp only
  rw [clause_answer_cons_ne deployModel _ _ _ _ _ _ (by decide)]
  rw [clause_answer_cons_ne deployModel _ _ _ _ _ _ hTk0Ne16]
  exact layoutVReadClause_answer_halt deployModel _ _ rfl 1 0
    ⟨[], ⟨16⟩⟩ .message readScRef0 ⟨[], ⟨16⟩⟩ rfl buf off why hR []

private theorem layV0_readSc_done (buf : List Nat) (off nextOff : Nat) (v : deployModel.Val dScalar)
    (hR : readScRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (.cons buf (.cons off .nil)) = .done (.cons v (.cons nextOff .nil))) :
    Clause.answer deployModel (Defs.fnTable deployModel baseInstalled.defs)
      (Defs.rTable deployModel baseInstalled.defs) layV0.clauses
      (.get .message 0 ⟨[], ⟨16⟩⟩ dScalar) (buf, (off, ())) =
      .done (v, (buf, (nextOff, ()))) := by
  unfold layV0; dsimp only
  rw [clause_answer_cons_ne deployModel _ _ _ _ _ _ (by decide)]
  rw [clause_answer_cons_ne deployModel _ _ _ _ _ _ hTk0Ne16]
  exact layoutVReadClause_answer (M := deployModel) _ _ rfl 1 0 ⟨[], ⟨16⟩⟩ .message
    readScRef0 ⟨[], ⟨16⟩⟩ rfl buf off nextOff v hR []

private theorem layV0_finish_eq2 (b0 b1 : Nat) :
    layV0.finish.denote (localSem deployModel baseInstalled.headers.fns
        (Defs.fnTable deployModel baseInstalled.defs))
      [] (Env.positional (.cons ([b0, b1], (2, ())) .nil)) = .done .nil := by
  exact (LayerBuild.layoutVFinish_denote deployModel (Defs.fnTable deployModel baseInstalled.defs)
    dByte rfl finKey0 [b0, b1] 2).trans rfl

private theorem layV0_finish_ne2 (b0 b1 b2 : Nat) (more : List Nat) :
    layV0.finish.denote (localSem deployModel baseInstalled.headers.fns
        (Defs.fnTable deployModel baseInstalled.defs))
      [] (Env.positional (.cons (b0 :: b1 :: b2 :: more, (2, ())) .nil)) =
      .halt (.declared .reject ⟨[], ⟨29⟩⟩) := by
  refine (LayerBuild.layoutVFinish_denote deployModel (Defs.fnTable deployModel baseInstalled.defs)
    dByte rfl finKey0 (b0 :: b1 :: b2 :: more) 2).trans ?_
  rw [hFinKey0]
  rfl

private theorem stackTwo_terminal_ite_done {V : Vocabulary} (M : Model V) {hs : Headers V}
    {r : Role} {ins : List (LTy V)} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (l₁ l₂ : Layer V hs r ins) (s₁ : M.Val l₁.state) (s₂ : M.Val l₂.state)
    (cond : Bool) (rejFail : Stop) {g₁ : HList M.Val l₁.gives} {g₂ : HList M.Val l₂.gives}
    (h₁ : l₁.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₁ .nil)) = .done g₁)
    (h₂ : l₂.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₂ .nil)) = .done g₂) :
    ((((Stack.handler M fnTable rTable [l₁, l₂]).run (retryOf M none)
        (if cond = true then .done (HList.nil : HList (RV M r) []) else .halt rejFail)
        (stackTwo M s₁ s₂)).mapHalt Prod.fst).bind fun out =>
      (Stack.finish M fnTable [l₁, l₂] out.2).map fun gives => (out.1, gives)).map (fun _ => ()) =
    (if cond = true then .done () else .halt rejFail) := by
  cases cond with
  | false => rfl
  | true => exact stackTwo_finish_done M fnTable rTable l₁ l₂ (HList.nil : HList (RV M r) []) s₁ s₂ h₁ h₂

private theorem stackTwo_terminal_ite_halt {V : Vocabulary} (M : Model V) {hs : Headers V}
    {r : Role} {ins : List (LTy V)} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (l₁ l₂ : Layer V hs r ins) (s₁ : M.Val l₁.state) (s₂ : M.Val l₂.state)
    (cond : Bool) (rejOk rejFail : Stop) {g₁ : HList M.Val l₁.gives}
    (h₁ : l₁.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₁ .nil)) = .done g₁)
    (h₂ : l₂.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₂ .nil)) = .halt rejOk) :
    ((((Stack.handler M fnTable rTable [l₁, l₂]).run (retryOf M none)
        (if cond = true then .done (HList.nil : HList (RV M r) []) else .halt rejFail)
        (stackTwo M s₁ s₂)).mapHalt Prod.fst).bind fun out =>
      (Stack.finish M fnTable [l₁, l₂] out.2).map fun gives => (out.1, gives)).map (fun _ => ()) =
    (if cond = true then .halt rejOk else .halt rejFail) := by
  cases cond with
  | false => rfl
  | true => exact stackTwo_finish_halt2 M fnTable rTable l₁ l₂ (HList.nil : HList (RV M r) []) s₁ s₂ h₁ h₂

private theorem depVerifierProc_steps (Y : Nat) (proof : List Nat) (st1 : Nat)
    (startC : Term (localDialect deployVocab baseInstalled.headers.fns)
      (Ctx.positional ([] ++ held 1 hdrBase.ins)) [.nat])
    (againC : Term (localDialect deployVocab baseInstalled.headers.fns)
      (Ctx.positional [.nat, .nat, .nat]) [.nat])
    (startL : Term (localDialect deployVocab baseInstalled.headers.fns)
      (Ctx.positional ([dBytes] ++ held 1 hdrBase.ins)) [LayerBuild.streamStateTy dByte])
    (againL : Term (localDialect deployVocab baseInstalled.headers.fns)
      (Ctx.positional [.nat, LayerBuild.streamStateTy dByte, LayerBuild.streamStateTy dByte])
      [LayerBuild.streamStateTy dByte]) :
    let conV0 : Layer deployVocab baseInstalled.headers 1 hdrBase.ins :=
      { line := .construction, state := .nat, takes := [], gives := [],
        clauses := cV0, again := againC, start := startC, finish := LayerBuild.emptyFinish .nat }
    let layV0' : Layer deployVocab baseInstalled.headers 1 hdrBase.ins :=
      { line := .layout, state := LayerBuild.streamStateTy dByte, takes := [dBytes], gives := [],
        clauses := layV0.clauses, again := againL, start := startL, finish := layV0.finish }
    let fnTab := Defs.fnTable deployModel baseInstalled.defs
    let rTab := Defs.rTable deployModel baseInstalled.defs
    ((((Stack.handler deployModel fnTab rTab [conV0, layV0']).run (retryOf deployModel none)
        (roleMeaning deployModel baseInstalled baseRoot 1 [] (.cons () (.cons (toPoint Y) .nil)))
        (stackTwo deployModel st1 (proof, (0, ())))).mapHalt Prod.fst).bind fun out =>
      (Stack.finish deployModel fnTab [conV0, layV0'] out.2).map fun gives => (out.1, gives)).map
      (fun _ => ()) =
      schnorrVerifierFromSt1 Y st1 proof := by
  intro conV0 layV0' fnTab rTab
  rw [baseVerifier_process Y]
  have hStep1L1 : Clause.answer deployModel fnTab rTab conV0.clauses
      (.get .message 0 ⟨[], ⟨12⟩⟩ dPoint) st1 =
      .call (.get .message 0 ⟨[], ⟨12⟩⟩ dPoint) fun msg =>
        (((liftLocal id (encPtRef0.eval deployModel fnTab (.cons msg .nil))).bind fun enc =>
          (liftLocal id (absorbRef0.eval deployModel fnTab
            (.cons st1 (.cons (msgLabel ⟨[], ⟨12⟩⟩) (.cons enc.single .nil))))).map
            fun nextSt => aloneIn deployModel 1 (.cons msg nextSt)).mapHalt fun why => (why, st1)).map
          fun out =>
            let values := HList.split [dPoint] (aloneOut deployModel 1 out)
            (values.1.single, values.2.single) :=
    verifierAbsorbClause_answer (M := deployModel) fnTab rTab 1 0 ⟨[], ⟨12⟩⟩ .message
      (msgLabel ⟨[], ⟨12⟩⟩) (msgLabel_bytes _) encPtRef0 absorbRef0 ⟨[], ⟨12⟩⟩ rfl st1 _
  cases proof with
  | nil =>
      have hStep1L2 : Clause.answer deployModel fnTab rTab layV0'.clauses
          (.get .message 0 ⟨[], ⟨12⟩⟩ dPoint) (([] : List Nat), (0, ())) =
          .halt (.declared .reject ⟨[], ⟨3⟩⟩, (([] : List Nat), (0, ()))) :=
        layoutVReadClause_answer_halt deployModel fnTab rTab rfl 1 0 ⟨[], ⟨12⟩⟩ .message
          readPtRef0 ⟨[], ⟨12⟩⟩ rfl [] 0 (.declared .reject ⟨[], ⟨3⟩⟩) readPtRef0_eval_nil _
      rw [stackTwo_call_both_halt deployModel fnTab rTab conV0 layV0' _ _ _ _ _ _ _ _ hStep1L1 hStep1L2]
      rfl
  | cons b0 rest =>
      have hCons := readPtRef0_eval_cons b0 rest
      cases Nat.decLt b0 23 with
      | isFalse h0 =>
          simp only [h0, ↓reduceIte] at hCons
          have hStep1L2 : Clause.answer deployModel fnTab rTab layV0'.clauses
              (.get .message 0 ⟨[], ⟨12⟩⟩ dPoint) (b0 :: rest, (0, ())) =
              .halt (.declared .reject ⟨[], ⟨8⟩⟩, (b0 :: rest, (0, ()))) :=
            layoutVReadClause_answer_halt deployModel fnTab rTab rfl 1 0 ⟨[], ⟨12⟩⟩ .message
              readPtRef0 ⟨[], ⟨12⟩⟩ rfl (b0 :: rest) 0 (.declared .reject ⟨[], ⟨8⟩⟩) hCons _
          rw [stackTwo_call_both_halt deployModel fnTab rTab conV0 layV0' _ _ _ _ _ _ _ _ hStep1L1 hStep1L2]
          cases rest <;> simp only [h0, ↓reduceIte, schnorrVerifierFromSt1] <;> rfl
      | isTrue h0 =>
          simp only [h0, ↓reduceIte] at hCons
          have hStep1L2 : Clause.answer deployModel fnTab rTab layV0'.clauses
              (.get .message 0 ⟨[], ⟨12⟩⟩ dPoint) (b0 :: rest, (0, ())) =
              .done (toPoint (b0 % 23), (b0 :: rest, (1, ()))) :=
            layoutVReadClause_answer (M := deployModel) fnTab rTab rfl 1 0 ⟨[], ⟨12⟩⟩ .message readPtRef0
              ⟨[], ⟨12⟩⟩ rfl (b0 :: rest) 0 1 (toPoint (b0 % 23)) hCons _
          have hStep1K1 := verifierAbsorb_k1_done
            (encPtRef0_eval (toPoint (b0 % 23)))
            (absorbRef0_eval st1 (msgLabel ⟨[], ⟨12⟩⟩) [fromPoint (toPoint (b0 % 23)) % 256])
          rw [stackTwo_call_both_done deployModel fnTab rTab conV0 layV0' _ _ _
            st1 _ (b0 :: rest, (0, ())) (b0 :: rest, (1, ()))
            (toPoint (b0 % 23)) (toPoint (b0 % 23)) _ hStep1L1 hStep1L2 hStep1K1]
          -- Step 2: `ROp.own (.coin ()) [0] ⟨[], ⟨13⟩⟩ [] .nil dScalar`
          have hStep2L1 := cV0_derive_answer
            (mixBytes (mixBytes st1 (msgLabel ⟨[], ⟨12⟩⟩)) [fromPoint (toPoint (b0 % 23)) % 256])
            (derRef0_eval _ (drawLabel ⟨[], ⟨13⟩⟩))
          rw [stackTwo_call_both_done deployModel fnTab rTab conV0 layV0' _ _ _
            _ _ (b0 :: rest, (1, ())) (b0 :: rest, (1, ())) _ () _ hStep2L1
            (layV0_drop_answer _ (b0 :: rest) 1) rfl]
          -- Step 3: `ROp.get .message 0 ⟨[], ⟨16⟩⟩ dScalar`
          cases rest with
          | nil =>
              rw [stackTwo_call_both_halt deployModel fnTab rTab conV0 layV0' _ _ _ _ _ _ _ _
                (cV0_step3_pass _) (layV0_readSc_halt [b0] 1 _ (readScRef0_eval_singleton b0))]
              simp only [h0, ↓reduceIte, schnorrVerifierFromSt1]
              rfl
          | cons b1 tail =>
              simp only [h0, ↓reduceIte, schnorrVerifierFromSt1]
              have hC2 := readScRef0_eval_cons2 b0 b1 tail
              cases Nat.decLt b1 11 with
              | isFalse h1 =>
                  simp only [h1, ↓reduceIte] at hC2
                  simp only [h1, ↓reduceIte]
                  rw [stackTwo_call_both_halt deployModel fnTab rTab conV0 layV0' _ _ _ _ _ _ _ _
                    (cV0_step3_pass _) (layV0_readSc_halt (b0 :: b1 :: tail) 1 _ hC2)]
                  rfl
              | isTrue h1 =>
                  simp only [h1, ↓reduceIte] at hC2
                  simp only [h1, ↓reduceIte]
                  rw [stackTwo_call_both_done deployModel fnTab rTab conV0 layV0' _ _ _
                    _ _ (b0 :: b1 :: tail, (1, ())) (b0 :: b1 :: tail, (2, ()))
                    (toScalar (b1 % 11)) (toScalar (b1 % 11)) _ (cV0_step3_pass _)
                    (layV0_readSc_done (b0 :: b1 :: tail) 1 2 (toScalar (b1 % 11)) hC2) rfl]
                  simp only [fromPoint_toPoint, fromScalar_toScalar]
                  cases tail with
                  | nil =>
                      exact stackTwo_terminal_ite_done deployModel fnTab rTab conV0 layV0' _
                        ([b0, b1], (2, ())) _ (.declared .reject ⟨[], ⟨21⟩⟩) rfl (layV0_finish_eq2 b0 b1)
                  | cons b2 more =>
                      exact stackTwo_terminal_ite_halt deployModel fnTab rTab conV0 layV0' _
                        (b0 :: b1 :: b2 :: more, (2, ())) _ (.declared .reject ⟨[], ⟨29⟩⟩)
                        (.declared .reject ⟨[], ⟨21⟩⟩) rfl (layV0_finish_ne2 b0 b1 b2 more)

/-- Universal exact `Process` characterization of `Core.deploy` (`baseDeployedFast.run`), proved
by combining `baseVerifier_process` (`BaseVerifier.reads`) with `deploy_ok_elim` and the Core
layer denotation lemmas (`LayerBuild.buildAbsorbChain_denote`, `layoutVStart_denote`,
`verifierAbsorbClause_answer`, `layoutVReadClause_answer`, `deriveClause_answer_own`,
`layoutDropClause_answer`, `emptyFinish_denote`, `layoutVFinish_denote`). -/
theorem depVerifierProc_eq_spec (Y : Nat) (proof : List Nat) :
    depVerifierProc Y proof = schnorrVerifierSpec Y proof := by
  cases hElim : deploy_ok_elim deployEncoder baseAdmittedFast schnorrDecl baseDeployedFast
      baseDeployedFast_ok with
  | interactive w _ => cases w.hCon
  | authored w _ => cases w.hCon
  | derived w hEq =>
      have hInsW : w.toDeployed.entry.ins = [⟨dScalar, [0]⟩, ⟨dPoint, [0, 1]⟩] := by
        rw [← hEq]; exact baseDeployedFast_ins_eq
      have hTakesW : Stack.Takes (w.toDeployed.stack 1) = [dBytes] := by
        rw [← hEq]; exact baseDeployedFast_takes_eq
      unfold depVerifierProc
      rw [deployed_run_map_eq deployModel hEq 1 baseDeployedFast_ins_eq baseDeployedFast_takes_eq
        hInsW hTakesW (.cons () (.cons Y .nil)) (.cons proof .nil)]
      cases w with
      | mk foundPair hFound hSupp suite sessionTag hCon prep hPrep stateTy startRef hStart
          suiteUnitTy absorbRef hAbs stmtP hSP stmtV hSV cPClauses cVClauses hCC =>
        have hSuite : suite = toySuite := (Construction.derived.inj hCon).1.symm
        have hTag : sessionTag = none := (Construction.derived.inj hCon).2.symm
        have hFoundBase : baseInstalled.findProtocol ⟨200⟩ = some ⟨hdrBase, baseRoot⟩ := by
          kernel_rfl
        have hPair : foundPair = ⟨hdrBase, baseRoot⟩ :=
          Option.some.inj (hFound.symm.trans hFoundBase)
        subst hSuite; subst hTag; subst hPair
        cases prep with
        | mk prover verifier hPV hNe hScope hLawsDist layout hLayOpt sessBytes hSessBytes hSess
            sampLayer hSamp layP layV hLay =>
          have hPV0 : proverAndVerifier hdrBase schnorrDecl = some (0, 1) := by kernel_rfl
          have hProver : prover = 0 :=
            (Prod.mk.inj (Option.some.inj (hPV.symm.trans hPV0))).1
          have hVerifier : verifier = 1 :=
            (Prod.mk.inj (Option.some.inj (hPV.symm.trans hPV0))).2
          have hLayout : layout = ⟨toyLayoutModule, [], []⟩ :=
            (Option.some.inj hLayOpt).symm
          subst hProver; subst hVerifier; subst hLayout
          have hStart0 : findSuiteStart baseAdmittedFast toySuite =
              some ⟨.nat, startRef0⟩ := by
            kernel_rfl
          have hStEq : (⟨stateTy, startRef⟩ : (s : deployVocab.Ty) ×
              LayerBuild.TypedFnRef deployVocab baseInstalled.headers.fns [LayerBuild.bytesTy] [s]) =
              ⟨.nat, startRef0⟩ :=
            Option.some.inj (hStart.symm.trans hStart0)
          cases hStEq
          have hAbs0 : findSuiteAbsorb baseAdmittedFast toySuite .nat =
              some ⟨dByte, absorbRef0⟩ := by
            kernel_rfl
          have hAbsEq : (⟨suiteUnitTy, absorbRef⟩ : (u : deployVocab.Ty) ×
              LayerBuild.TypedFnRef deployVocab baseInstalled.headers.fns
                [.nat, LayerBuild.bytesTy, .seq u none] [.nat]) =
              ⟨dByte, absorbRef0⟩ :=
            Option.some.inj (hAbs.symm.trans hAbs0)
          cases hAbsEq
          have hSessEq : sessBytes = sessBytesNorm := by
            have hRes : (resolveSessionBytes deployEncoder baseAdmittedFast schnorrDecl none).map
                PSigma.fst = .ok sessBytesNorm := by
              kernel_rfl
            exact Except.ok.inj ((congrArg (Except.map PSigma.fst) hSess).symm.trans hRes)
          have hSV0 : buildStmtAbsorbItems baseAdmittedFast toySuite dByte 1 0 1 (.inr rfl)
              hdrBase.ins schnorrDecl.key =
              .ok [⟨dPoint, ⟨0, rfl⟩, stmtLabel 0, stmtLabel_bytes 0, encPtRef0⟩] := by
            kernel_rfl
          have hSVEq : stmtV = [⟨dPoint, ⟨0, rfl⟩, stmtLabel 0, stmtLabel_bytes 0, encPtRef0⟩] :=
            Except.ok.inj (hSV.symm.trans hSV0)
          subst hSVEq
          have hCC0 : (buildConstructionClauses deployEncoder baseAdmittedFast toySuite .nat dByte
              absorbRef0 0 1 schnorrDecl.key events0
              (hdrBase.shape.eventsWithAbsorb 0 1 [] id false)).map Prod.snd = .ok cV0 := by
            kernel_rfl
          have hCVEq : cVClauses = cV0 := by
            have hm := congrArg (Except.map Prod.snd) hCC
            exact Except.ok.inj (hm.symm.trans hCC0)
          subst hCVEq
          have hLay0 : (buildLayoutLayers baseAdmittedFast hdrBase ⟨toyLayoutModule, [], []⟩ 0 1
              schnorrDecl.key events0).map Prod.snd = .ok layV0 := by
            kernel_rfl
          have hLayVEq : layV = layV0 := by
            have hm := congrArg (Except.map Prod.snd) hLay
            exact Except.ok.inj (hm.symm.trans hLay0)
          subst hLayVEq
          have hConStart :
              (LayerBuild.constructionStart (r := 1) (ins := hdrBase.ins)
                sessBytes hSessBytes startRef0 absorbRef0
                [⟨dPoint, ⟨0, rfl⟩, stmtLabel 0, stmtLabel_bytes 0, encPtRef0⟩]).denote
                (localSem deployModel baseInstalled.headers.fns (Defs.fnTable deployModel baseInstalled.defs))
                [] (Env.positional (.cons (toPoint Y) .nil)) =
                .done (.cons (mixBytes (mixBytes st0Val (stmtLabel 0)) [Y % 256]) .nil) := by
            unfold LayerBuild.constructionStart
            erw [LayerBuild.letOp1_denote, LayerBuild.localSem_op_literal,
              LayerBuild.bytesLiteral_val deployModel sessBytes hSessBytes]
            simp only [Process.bind, HList.single]
            rw [LayerBuild.letOp1_local_denote]
            simp only [Env.all, LayerBuild.env_get_insert_self]
            change (startRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
              (.cons sessBytes .nil)).bind _ = _
            have hStEv : startRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
                (.cons sessBytes .nil) = .done (.cons st0Val .nil) := by
              change Defs.fnTable deployModel baseInstalled.defs hdr0
                SerializedVerifier.function100 (.cons sessBytes .nil) = _
              rw [hSessEq]
              exact (fnStart_table sessBytesNorm).trans (by rw [← st0Val.eq])
            rw [hStEv]
            simp only [Process.bind, HList.single]
            rw [LayerBuild.buildAbsorbChain_denote deployModel
              (Defs.fnTable deployModel baseInstalled.defs) absorbRef0 1 _ _ _ _ _ rfl]
            rw [LayerBuild.env_get_insert_self]
            erw [LayerBuild.absorbChainFold_reindex deployModel
              (Defs.fnTable deployModel baseInstalled.defs) absorbRef0
              (Env.positional (.cons (toPoint Y) .nil)) _ _
              (fun x => LayerBuild.env_get_insert2_reindex _ (LayerBuild.positional_freshFrom _) _ _ _ x)]
            simp only [LayerBuild.absorbChainFold]
            erw [LayerBuild.env_get_positional_0 (toPoint Y) .nil]
            have hEncEv : encPtRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
                (.cons (toPoint Y) .nil) = .done (.cons [Y % 256] .nil) := fnEncPoint_table (toPoint Y)
            have hAbsEv : absorbRef0.eval deployModel (Defs.fnTable deployModel baseInstalled.defs)
                (.cons st0Val (.cons (stmtLabel 0) (.cons [Y % 256] .nil))) =
                .done (.cons (mixBytes (mixBytes st0Val (stmtLabel 0)) [Y % 256]) .nil) :=
              fnAbsorb_table st0Val (stmtLabel 0) [Y % 256]
            rw [hEncEv, Process.bind, HList.single, hAbsEv]
            rfl
          let w0 : DeployDerived deployEncoder baseAdmittedFast schnorrDecl :=
            ⟨⟨hdrBase, baseRoot⟩, hFound, hSupp, toySuite, none, hCon,
              ⟨0, 1, hPV, hNe, hScope, hLawsDist, ⟨toyLayoutModule, [], []⟩, hLayOpt,
                sessBytes, hSessBytes, hSess, sampLayer, hSamp, layP, layV0, hLay⟩,
              hPrep, .nat, startRef0, hStart, dByte, absorbRef0, hAbs, stmtP, hSP,
              [⟨dPoint, ⟨0, rfl⟩, stmtLabel 0, stmtLabel_bytes 0, encPtRef0⟩], hSV,
              cPClauses, cV0, hCC⟩
          have hEntryW : w0.toDeployed.entry = hdrBase := by
            simp only [Deployed.entry, DeployDerived.toDeployed, w0, hFound, Option.get_some]
          have hStackW : (congrArg ProtocolHeader.ins hEntryW ▸ w0.toDeployed.stack 1 :
              List (Layer deployVocab baseAdmittedFast.program.headers 1 hdrBase.ins)) =
              [conVLayer sessBytes hSessBytes, layV0] := by
            dsimp only [DeployDerived.toDeployed, w0]
            simp only [Nat.one_ne_zero, ↓reduceDIte]
            rfl
          have hPairW : (baseAdmittedFast.program.findProtocol schnorrDecl.entry).get w0.toDeployed.found =
              ⟨hdrBase, baseRoot⟩ := by
            simp only [hFound, Option.get_some]
          change (w0.toDeployed.run deployModel 1 (hInsW.symm ▸ (.cons () (.cons (toPoint Y) .nil)))
            (hTakesW.symm ▸ (.cons proof .nil))).map (fun _ => ()) = _
          rw [deployed_run_stack_eq deployModel baseAdmittedFast schnorrDecl w0.toDeployed.found
            w0.toDeployed.stack w0.toDeployed.identity 1 hPairW rfl hEntryW hStackW
            hInsW hTakesW rfl rfl (.cons () (.cons (toPoint Y) .nil)) (.cons proof .nil)]
          rw [stack_start_two_done deployModel (Defs.fnTable deployModel baseInstalled.defs)
            (conVLayer sessBytes hSessBytes) layV0
            rfl rfl (.cons () (.cons (toPoint Y) .nil)) proof rfl
            hConStart (LayerBuild.layoutVStart_denote deployModel _ dByte _ _)]
          simp only [Process.bind, HList.single]
          exact depVerifierProc_steps Y proof (mixBytes (mixBytes st0Val (stmtLabel 0)) [Y % 256])
            (conVLayer sessBytes hSessBytes).start (conVLayer sessBytes hSessBytes).again
            layV0.start layV0.again

/-- Universal exact `Process` equality between re-admitted `serialized Core` verifier and
`Core.deploy` (`baseDeployedFast.run`) across ALL statements `Y` and ALL proof byte lists `proof`. -/
theorem serialized_eq_deployed_verifier (Y : Nat) (proof : List Nat) :
    serVerifierProc Y proof = depVerifierProc Y proof :=
  (serVerifierProc_eq_spec Y proof).trans (depVerifierProc_eq_spec Y proof).symm

/-- Universal exact `Process` equality between re-admitted `serialized Core` verifier and
`Core.specialize` across ALL statements `Y : Nat` and ALL proof byte lists `proof : List Nat`. -/
theorem serialized_eq_specialized_verifier (Y : Nat) (proof : List Nat) :
    serVerifierProc Y proof = specVerifierProc Y proof :=
  (serialized_eq_deployed_verifier Y proof).trans (specVerifierProc_eq_depVerifierProc Y proof).symm

/-- Universal `Reading.read` preservation between re-admitted `serialized Core` and `Core.deploy`. -/
theorem serialized_eq_deployed_reading (Y : Nat) (proof : List Nat) :
    Reading.read (serVerifierProc Y proof) = Reading.read (depVerifierProc Y proof) :=
  congrArg Reading.read (serialized_eq_deployed_verifier Y proof)

/-- Universal `Value.value` preservation between re-admitted `serialized Core` and `Core.deploy`
for every choice of samplers, permitted-reply predicates, and bad-return event. -/
theorem serialized_eq_deployed_value (Y : Nat) (proof : List Nat)
    (samplers : ProbabilisticProcess.Samplers (RSig deployModel))
    (allowed : ∀ o, (RSig deployModel).Reply o → Prop) (bad : Unit → Prop) :
    Value.value samplers allowed bad (serVerifierProc Y proof) =
      Value.value samplers allowed bad (depVerifierProc Y proof) :=
  congrArg (Value.value samplers allowed bad) (serialized_eq_deployed_verifier Y proof)

end

#print axioms specialize_deploy_reading_eq
#print axioms specialize_deployIdeal_reading_eq
#print axioms baseVerifier_process
#print axioms serVerifierProc_eq_spec
#print axioms serialized_eq_deployed_verifier
#print axioms serialized_eq_deployed_reading

open Lean Meta in
run_meta do
  for name in [`BaseVerifier.form, `ConstructedVerifier.form, `SerializedVerifier.form] do
    let info ← getConstInfo name
    let val := info.value!
    IO.println s!"{name}: sizeWithoutSharing={val.sizeWithoutSharing}"

#eval IO.println s!"(specialize baseDeployed 1).body.astSize={(specialize baseDeployed 1).body.astSize}"

end UniversalEquivalence

end ZkcFormal.Checks.ConstructedStage
