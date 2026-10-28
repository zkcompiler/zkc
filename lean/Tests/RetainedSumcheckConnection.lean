import Tests.RetainedSumcheckLibrary
import Zkc.Construction.ConnectionTargetPrefix
import ZkcTools.ConstructionBindings.Alignment
import ZkcTools.ConstructionBindings.RootRoutes

/-! Structural placement against retained compiler views. These declarations
check actual reduce bodies and projected symbolic state; complete caller/root
composition remains a separate obligation. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace Tests.RetainedSumcheckConnection
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionLibrary ZkcTools.ConstructionBindings
namespace Small
abbrev program := Tests.RetainedSumcheckLibrary.Small.program
abbrev validator := ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact
abbrev producer := ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.artifact
def context : Context := (exportContext program.snapshot validator).getD (.plain "" [] 0 1)
def routing : Original.Routing := RootRoutes.routing program.snapshot context .validator [(3,3)] validator (by decide +kernel)
def calleeContext : ProtocolContext := ({} : ProtocolContext).enter "label_726564756365" [0,1]

def pattern : InputPattern program.payload.protocols[0].inputs :=
  .cons .absent (.cons .absent (.cons .absent (.cons .present (.cons .present
    (.cons .present (.cons (.capability "random.bls12-381.fr/0" 3) .nil))))))
def template : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide +kernel⟩ 1 pattern).toOption.get (by decide +kernel)
abbrev scope : Scope := [.value (.vector "bls12-381.fr"), .value (.field "bls12-381.fr"), .value .index,
  .value (.vector "bls12-381.fr"), .value (.field "bls12-381.fr")]
def layout : Layout scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here))),
   .data (.present (.var (.there (.there .here)))), .history context.suite,
   .data (.present (.var (.there (.there (.there .here))))),
   .data (.present (.var (.there (.there (.there (.there .here))))))]
def arguments : Values (Argument [] scope) pattern.scope :=
  .cons (.var (.there (.there (.there .here))))
    (.cons (.var (.there (.there (.there (.there .here)))))
      (.cons (.var (.there (.there .here))) .nil))
def target : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence
    (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep1 model program context)
    (Domain.View.sequence
      (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep2 model program context)
      (Domain.View.sequence
        (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep3 model program context) Domain.View.empty))

def targetPrefix : ConnectionTargetPrefix.Prefix :=
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep1 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep2 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.bodyStep3 model program context) .empty
example : targetPrefix.block = target := rfl
example (suffix : ConnectionCertificate.Block) (model : DomainModel)
    (environment : Domain.Environment model.toCarriers) :
    targetPrefix.plug suffix model environment = (target model environment).bind (suffix model) :=
  targetPrefix.plug_eq_bind suffix model environment

def placed : ConnectionApplications.Certificate template routing calleeContext arguments
    [.absent,.absent,.absent,.absent,.data 11,.data 12] (some 10) [] layout target where
  distinct := RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel)
  alignment := by derive_connection_alignment


def producerRouting : Original.Routing := RootRoutes.routing program.snapshot context .producer [(3,3)] producer (by decide +kernel)
def producerPattern : InputPattern program.payload.protocols[0].inputs :=
  .cons .present (.cons .present (.cons .present (.cons .absent (.cons .absent
    (.cons .present (.cons .absent .nil))))))
def producerTemplate : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide +kernel⟩ 0 producerPattern).toOption.get (by decide +kernel)
abbrev producerScope : Scope := [.value (.vector "bls12-381.fr"), .value .index, .value .index,
  .value (.vector "bls12-381.fr"), .value .index, .value .index]
def producerLayout : Layout producerScope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here))), .history context.suite,
   .data (.present (.var (.there (.there .here)))),
   .data (.present (.var (.there (.there (.there .here))))),
   .data (.present (.var (.there (.there (.there (.there .here)))))),
   .data (.present (.var (.there (.there (.there (.there (.there .here)))))))]
def producerArguments : Values (Argument [] producerScope) producerPattern.scope :=
  .cons (.var (.there (.there (.there .here))))
    (.cons (.var (.there (.there (.there (.there .here)))))
      (.cons (.var (.there (.there (.there (.there (.there .here))))))
        (.cons (.var (.there .here)) .nil)))
def producerTarget : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence
    (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep2 model program context) <|
  Domain.View.sequence
    (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep3 model program context) <|
  Domain.View.sequence
    (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep4 model program context) <|
  Domain.View.sequence
    (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep5 model program context) <|
  Domain.View.sequence
    (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep6 model program context) <|
  Domain.View.sequence
    (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep7 model program context) <|
  Domain.View.sequence
    (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep8 model program context) <|
  Domain.View.sequence
    (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep9 model program context) <|
  Domain.View.sequence
    (ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.bodyStep10 model program context) <|
  Domain.View.empty

def producerPlaced : ConnectionApplications.Certificate producerTemplate producerRouting calleeContext producerArguments
    [.data 16,.data 13,.data 14,.data 15,.absent,.absent] (some 17) [] producerLayout producerTarget where
  distinct := RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel)
  alignment := by derive_connection_alignment

def simulation := placed.simulation .empty
def producerSimulation := producerPlaced.simulation .empty

#print axioms simulation
#print axioms producerSimulation
#print axioms placed
#print axioms producerPlaced
end Small
namespace Two
abbrev program := Tests.RetainedSumcheckLibrary.Two.program
abbrev validator := ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.artifact
def context : Context := (exportContext program.snapshot validator).getD (.plain "" [] 0 1)
def routing : Original.Routing := RootRoutes.routing program.snapshot context .validator [(5,5)] validator (by decide +kernel)
def pattern : InputPattern program.payload.protocols[0].inputs :=
  .cons .absent (.cons .absent (.cons .absent (.cons .present (.cons .present
    (.cons .present (.cons (.capability "random.bls12-381.fr/0" 5) .nil))))))
def template : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide +kernel⟩ 1 pattern).toOption.get (by decide +kernel)
abbrev scope : Scope := [.value (.vector "bls12-381.fr"), .value (.field "bls12-381.fr"), .value .index]
def arguments : Values (Argument [] scope) pattern.scope :=
  .cons (.var .here) (.cons (.var (.there .here)) (.cons (.var (.there (.there .here))) .nil))
def leftLayout : Layout scope :=
  [.unused,.unused,.unused,.unused,.data (.present (.var (.there (.there .here)))),
   .history context.suite,.data (.present (.var .here)),.data (.present (.var (.there .here)))]
def rightLayout : Layout scope :=
  [.unused,.unused,.unused,.unused,.data (.present (.var (.there (.there .here)))),
   .unused,.unused,.unused,.unused,.unused,.unused,.unused,.history context.suite,.unused,.unused,.unused,
   .data (.present (.var .here)),.data (.present (.var (.there .here)))]
def calleeContext (site : String) : ProtocolContext := ({} : ProtocolContext).enter site [0,1]
def leftTarget : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep1 model program context) <|
  Domain.View.sequence (ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep2 model program context) <|
  Domain.View.sequence (ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep3 model program context) Domain.View.empty

def rightTarget : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep6 model program context) <|
  Domain.View.sequence (ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep7 model program context) <|
  Domain.View.sequence (ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.bodyStep8 model program context) Domain.View.empty

def left : ConnectionApplications.Certificate template routing (calleeContext "label_6c656674") arguments
    [.absent,.absent,.absent,.absent,.data 13,.data 14] (some 12) [] leftLayout leftTarget where
  distinct := RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel)
  alignment := by derive_connection_alignment

def right : ConnectionApplications.Certificate template routing (calleeContext "label_7269676874") arguments
    [.absent,.absent,.absent,.absent,.data 23,.data 24] (some 22) [] rightLayout rightTarget where
  distinct := RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel)
  alignment := by derive_connection_alignment


abbrev producer := ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.artifact
def producerRouting : Original.Routing := RootRoutes.routing program.snapshot context .producer [(5,5)] producer (by decide +kernel)
def producerPattern : InputPattern program.payload.protocols[0].inputs :=
  .cons .present (.cons .present (.cons .present (.cons .absent (.cons .absent
    (.cons .present (.cons .absent .nil))))))
def producerTemplate : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide +kernel⟩ 0 producerPattern).toOption.get (by decide +kernel)
abbrev producerScope : Scope := [.value (.vector "bls12-381.fr"), .value .index, .value .index, .value .index]
def producerArguments : Values (Argument [] producerScope) producerPattern.scope :=
  .cons (.var .here) (.cons (.var (.there .here))
    (.cons (.var (.there (.there .here))) (.cons (.var (.there (.there (.there .here)))) .nil)))
def producerLeftLayout : Layout producerScope :=
  [.unused,.unused,.data (.present (.var (.there (.there (.there .here))))),.history context.suite,.unused,
   .data (.present (.var .here)),.data (.present (.var (.there .here))),
   .data (.present (.var (.there (.there .here))))]
def producerRightLayout : Layout producerScope :=
  [.unused,.unused,.data (.present (.var (.there (.there (.there .here))))),
   .unused,.unused,.unused,.unused,.unused,.unused,.unused,.unused,.unused,.unused,.unused,.unused,.unused,.unused,.unused,
   .history context.suite,.unused,.data (.present (.var .here)),.data (.present (.var (.there .here))),
   .data (.present (.var (.there (.there .here))))]
def producerLeftPrefix : ConnectionTargetPrefix.Prefix :=
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep2 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep3 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep4 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep5 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep6 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep7 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep8 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep9 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep10 model program context) .empty
def producerLeftTarget : ConnectionCertificate.Block := producerLeftPrefix.block
def producerRightPrefix : ConnectionTargetPrefix.Prefix :=
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep13 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep14 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep15 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep16 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep17 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep18 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep19 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep20 model program context) <|
  .step (fun model => ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.bodyStep21 model program context) .empty
def producerRightTarget : ConnectionCertificate.Block := producerRightPrefix.block
def producerLeft : ConnectionApplications.Certificate producerTemplate producerRouting
    (calleeContext "label_6c656674") producerArguments
    [.data 17,.data 14,.data 15,.data 16,.absent,.absent] (some 18) [] producerLeftLayout producerLeftTarget where
  distinct := RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel)
  alignment := by derive_connection_alignment
def producerRight : ConnectionApplications.Certificate producerTemplate producerRouting
    (calleeContext "label_7269676874") producerArguments
    [.data 32,.data 29,.data 30,.data 31,.absent,.absent] (some 33) [] producerRightLayout producerRightTarget where
  distinct := RosterDistinct.ofSeparate (by decide +kernel) (by decide +kernel)
  alignment := by derive_connection_alignment

def leftSimulation := left.simulation .empty
def rightSimulation := right.simulation .empty
def producerLeftSimulation := producerLeft.simulation .empty
def producerRightSimulation := producerRight.simulation .empty
#print axioms leftSimulation
#print axioms rightSimulation
#print axioms producerLeftSimulation
#print axioms producerRightSimulation

#print axioms left
#print axioms right
end Two

end Tests.RetainedSumcheckConnection
