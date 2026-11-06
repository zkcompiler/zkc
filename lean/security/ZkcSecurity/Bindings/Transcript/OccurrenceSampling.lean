module

public import ZkcSecurity.Bindings.Transcript.ServiceSampling

@[expose] public section

/-! The existing occurrence raw-sampling declaration is shared independently of
legacy source-projection proofs. Field consumers retain its exact public name;
scalar and block carriers use the existing finite service sampler. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.OccurrenceReading
open Zkc.Source Zkc.Source.Structured Zkc.Construction
variable {F G : Type} [SampleableType F]

noncomputable abbrev rawSampleable :
    (event : Domain.Event (uniformCarriers F G)) → SampleableType (Domain.Raw event) :=
  ServiceSampling.raw (uniformCarriers F G) (fun _ => inferInstance)


end ZkcSecurity.FiatShamir.OccurrenceReading
