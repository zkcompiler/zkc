module

public import ZkcSecurity.FiatShamir.HonestReadback
public import Zkc.Construction.OriginalSimulation

@[expose] public section

/-! Successful readback transports through independent original construction
certificates. Full source returns and both actual target returns remain related;
every certified target checkpoint is retained. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.Readback
open Zkc.Source Zkc.Construction

variable {carriers : Structured.Carriers} {A B C D : Type}

theorem original_left {Post : A → B → Prop} {returns : A → C → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A}
    {target : PIR.Process (Domain.effects carriers) C}
    {right : PIR.Process (Domain.effects carriers) B}
    (simulation : Original.Simulation returns live source target)
    (aligned : Readback Post source right) :
    Readback (fun c b => ∃ a, Post a b ∧ returns a c) target right := by
  induction simulation generalizing right with
  | done related =>
    rename_i a c
    generalize equation : PIR.Process.done a = source at aligned
    induction aligned with
    | done holds => cases equation; exact .done ⟨_, holds, related⟩
    | checkpointRight frame _ ih => exact .checkpointRight frame (ih equation)
    | observeRight event _ ih => exact .observeRight event (ih equation)
    | sendRight site schema peer payload _ ih => exact .sendRight site schema peer payload (ih equation)
    | _ => cases equation
  | halt reason =>
    generalize equation : PIR.Process.halt reason = source at aligned
    induction aligned with
    | checkpointRight frame _ ih => exact .checkpointRight frame (ih equation)
    | observeRight event _ ih => exact .observeRight event (ih equation)
    | sendRight site schema peer payload _ ih => exact .sendRight site schema peer payload (ih equation)
    | _ => cases equation
  | checkpoint frame related next ih => exact .checkpointLeft frame (ih aligned)
  | call operation next ih =>
    rename_i sourceNext targetNext
    generalize equation : PIR.Process.call operation sourceNext = source at aligned
    induction aligned with
    | done => cases equation
    | checkpointLeft frame suffix =>
      cases equation
      exact .checkpointLeft frame (ih () suffix)
    | observeLeft event suffix =>
      cases equation
      exact .observeLeft event (ih () suffix)
    | sendReceive site schema peer receiveSite receiveSchema receivePeer payload value decoded suffix =>
      cases equation
      exact .sendReceive site schema peer receiveSite receiveSchema receivePeer payload value decoded
        (ih () suffix)
    | query history origin supported suffix =>
      cases equation
      exact .query history origin supported (fun reply => ih reply (suffix reply))
    | checkpointRight frame _ inner => exact .checkpointRight frame (inner equation)
    | observeRight event _ inner => exact .observeRight event (inner equation)
    | sendRight site schema peer payload _ inner =>
      exact .sendRight site schema peer payload (inner equation)

theorem original_right {Post : A → B → Prop} {returns : B → D → Prop}
    {live : PIR.Process (Domain.effects carriers) B → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) B}
    {target : PIR.Process (Domain.effects carriers) D}
    {left : PIR.Process (Domain.effects carriers) A}
    (simulation : Original.Simulation returns live source target)
    (aligned : Readback Post left source) :
    Readback (fun a d => ∃ b, Post a b ∧ returns b d) left target := by
  induction simulation generalizing left with
  | done related =>
    rename_i b d
    generalize equation : PIR.Process.done b = source at aligned
    induction aligned with
    | done holds => cases equation; exact .done ⟨_, holds, related⟩
    | checkpointLeft frame _ ih => exact .checkpointLeft frame (ih equation)
    | observeLeft event _ ih => exact .observeLeft event (ih equation)
    | _ => cases equation
  | halt reason =>
    generalize equation : PIR.Process.halt reason = source at aligned
    induction aligned with
    | checkpointLeft frame _ ih => exact .checkpointLeft frame (ih equation)
    | observeLeft event _ ih => exact .observeLeft event (ih equation)
    | _ => cases equation
  | checkpoint frame related next ih => exact .checkpointRight frame (ih aligned)
  | call operation next ih =>
    rename_i sourceNext targetNext
    generalize equation : PIR.Process.call operation sourceNext = source at aligned
    induction aligned with
    | done => cases equation
    | checkpointRight frame suffix =>
      cases equation
      exact .checkpointRight frame (ih () suffix)
    | observeRight event suffix =>
      cases equation
      exact .observeRight event (ih () suffix)
    | sendReceive site schema peer receiveSite receiveSchema receivePeer payload value decoded suffix =>
      cases equation
      exact .sendReceive site schema peer receiveSite receiveSchema receivePeer payload value decoded
        (ih value suffix)
    | sendRight site schema peer payload suffix =>
      cases equation
      exact .sendRight site schema peer payload (ih () suffix)
    | query history origin supported suffix =>
      cases equation
      exact .query history origin supported (fun reply => ih reply (suffix reply))
    | checkpointLeft frame _ inner => exact .checkpointLeft frame (inner equation)
    | observeLeft event _ inner => exact .observeLeft event (inner equation)

/-- Independent certificates retain their whole return relations at the exact
actual targets. Matching query histories/origins and every typed reply come
from source readback; stops cannot manufacture a successful terminal. -/
theorem original {Post : A → B → Prop} {returnsP : A → C → Prop} {returnsV : B → D → Prop}
    {liveP : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {liveV : PIR.Process (Domain.effects carriers) B → Domain.Environment carriers → Prop}
    {sourceP : PIR.Process (Domain.effects carriers) A}
    {sourceV : PIR.Process (Domain.effects carriers) B}
    {targetP : PIR.Process (Domain.effects carriers) C}
    {targetV : PIR.Process (Domain.effects carriers) D}
    (producer : Original.Simulation returnsP liveP sourceP targetP)
    (validator : Original.Simulation returnsV liveV sourceV targetV)
    (aligned : Readback Post sourceP sourceV) :
    Readback (fun targetP targetV => ∃ a b,
      Post a b ∧ returnsP a targetP ∧ returnsV b targetV) targetP targetV := by
  apply (original_right validator (original_left producer aligned)).mono
  intro targetP targetV related
  obtain ⟨b, ⟨a, post, returnedP⟩, returnedV⟩ := related
  exact ⟨a, b, post, returnedP, returnedV⟩

end ZkcSecurity.FiatShamir.Readback
