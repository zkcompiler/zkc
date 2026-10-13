module

public import ZkcSecurity.ArkLib.Sumcheck.Message

@[expose] public section

namespace ZkcSecurity.ArkLib.Sumcheck
open _root_.Interaction.Oracle OracleSpec
open _root_.Sumcheck.Interaction

variable {F : Type} [Field F]

/-- Compile every causal coefficient strategy into an ordinary ArkLib prover.
The strategy continuation is invoked only after its corresponding challenge.
Private randomness can be supplied by sampling the entire strategy first. -/
noncomputable def nativeProver : {count : Nat} → Zkc.Protocols.Sumcheck.Strategy F count →
    Prover.Strategy unifSpec (Native.protocol F 2 count).tree
      (Native.protocol F 2 count).roles (fun _ => Unit)
  | _, .done => ()
  | _, .send chosen next =>
      pure ⟨message chosen, fun
        | none => pure ()
        | some challenge => pure (nativeProver (next challenge))⟩

theorem nativeProver_done : nativeProver (F := F) .done = () := rfl

theorem nativeProver_send {count : Nat} (chosen : Zkc.Protocols.AlgebraicRounds.Message F)
    (next : F → Zkc.Protocols.Sumcheck.Strategy F count) :
    nativeProver (.send chosen next) =
      pure ⟨message chosen, fun
        | none => pure ()
        | some challenge => pure (nativeProver (next challenge))⟩ := by
  rw [nativeProver]

end ZkcSecurity.ArkLib.Sumcheck
