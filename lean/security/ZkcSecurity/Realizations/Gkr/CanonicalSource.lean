module

public import ZkcSecurity.Realizations.Gkr.Canonical
public import ZkcSecurity.Realizations.Gkr.RootSource
public import ZkcSecurity.FiatShamir.CostComposition

public section
noncomputable section

/-! The fixed canonical target applied to the actual source validator on every
typed public statement. Compiled execution and canonical experiment receipts
are separate transports of this exact body, not additional target premises. -/
namespace ZkcSecurity.Realizations.Gkr.CanonicalSource
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations
open ZkcSecurity.Obligations ZkcExamples.Structured
open OracleComp OracleSpec

variable {F G : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Canonical falsity is read from the actual validator's complete public
inputs. Neither honest-producer input nor a supplied representation is used. -/
noncomputable def rejected
    (statement : (Canonical.subject (ringModel F G)).validatorArtifacts.Statement (ringModel F G))
    (handle : Nat) (context : Context)
    (charge : History F G → Event F G → ENNReal)
    (charges : Root.Charges {} context (Canonical.invocation (ringModel F G) statement handle).width charge)
    (wrong : (Canonical.validatorSubject (ringModel F G)).FalseStatement statement)
    (history : History F G) :
    Derivation context.interface (boundedEscape charge) (fun _ result => result ≠ some true)
      history (Source.body (Canonical.invocation (ringModel F G) statement handle)) := by
  apply Source.rejected _ context charge charges _ history
  intro correct
  apply wrong
  refine ⟨fun _ _ => none, ?_⟩
  exact (Canonical.holds_all (ringModel F G) statement handle _).mpr correct

/-- A fixed uniform price discharges all source challenge obligations
internally. Invalid statements stop before any query. -/
noncomputable def uniformly_rejected
    (statement : (Canonical.subject (ringModel F G)).validatorArtifacts.Statement (ringModel F G))
    (handle : Nat) (context : Context)
    (wrong : (Canonical.validatorSubject (ringModel F G)).FalseStatement statement)
    (history : History F G) :
    Derivation context.interface (boundedEscape (fun _ _ => 4 / (Fintype.card F : ENNReal)))
      (fun _ result => result ≠ some true)
      history (Source.body (Canonical.invocation (ringModel F G) statement handle)) := by
  let runtime := Canonical.invocation (ringModel F G) statement handle
  by_cases admitted : runtime.Admitted
  · apply rejected statement handle context (fun _ _ => 4 / (Fintype.card F : ENNReal)) _ wrong history
    refine ⟨fun _ => ?_, fun _ _ _ => ?_, fun _ => ?_⟩
    · change (1 : ENNReal) / _ ≤ 4 / _
      exact ENNReal.div_le_div (by norm_num) le_rfl
    · change (2 : ENNReal) / _ ≤ 4 / _
      exact ENNReal.div_le_div (by norm_num) le_rfl
    · change (runtime.width : ENNReal) / _ ≤ 4 / _
      apply ENNReal.div_le_div _ le_rfl
      exact_mod_cast (show runtime.width ≤ 4 from admitted.2.2.1)
  · exact Source.invalid_derivation runtime admitted context.interface _ _ history

end ZkcSecurity.Realizations.Gkr.CanonicalSource
