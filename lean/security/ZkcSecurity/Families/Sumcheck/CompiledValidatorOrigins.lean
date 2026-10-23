module

public import ZkcSecurity.Families.Sumcheck.CompiledValidator
public import ZkcSecurity.Families.Sumcheck.RoundDescriptor

@[expose] public section

/-! A checked generated round descriptor supplies all actual nominal origins.
The only remaining source-specific obligation is the append mathematics. -/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.CompiledValidator
open Zkc.Source Zkc.Source.Structured Zkc.Construction TableComponent

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem connectionOfOrigins (plan : ReadbackRound.Plan) (program : Structured.Program)
    (context : Context) (bases : RoundDescriptor.OriginBases)
    (valid : bases.Valid plan context)
    (append : ∀ point challenge,
      Domain.callHelper (ringModel F G) program plan.appendHelper [.data (.vector plan.field)]
        [.data (.vector plan.field point), .data (.field plan.field challenge)] =
          .returned [.data (.vector plan.field (point ++ [challenge]))]) :
    RoundConnection (F := F) (G := G) plan.field program context plan.toPlan
      (RoundDescriptor.OriginBases.schedule valid) where
  lowFound index := (RoundDescriptor.OriginBases.sites valid index).lowFound
  highFound index := (RoundDescriptor.OriginBases.sites valid index).highFound
  queryFound index := (RoundDescriptor.OriginBases.sites valid index).queryFound
  deliveryFound index := (RoundDescriptor.OriginBases.sites valid index).deliveryFound
  lowMessage index := (RoundDescriptor.OriginBases.sites valid index).lowMessage
  highMessage index := (RoundDescriptor.OriginBases.sites valid index).highMessage
  deliveryMessage index := (RoundDescriptor.OriginBases.sites valid index).deliveryMessage
  append := append

end ZkcSecurity.Families.Sumcheck.CompiledValidator
