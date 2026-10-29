module

public import ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations
public import ZkcSecurity.Families.Sumcheck.TableComponentPrimeField

@[expose] public section

/-! The nominal request's existing uniform sampler discharges the source
installation's degree-one conditional distribution obligation. This is a local
fresh-cell law; adaptive oracle consistency belongs to the canonical claims.
-/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourcePublicPrimeField
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction OracleComp OracleSpec
open ZkcSecurity.Domains ZkcSecurity.Algebra.Polynomial

variable (modulus : Nat) [Fact modulus.Prime]
variable [algebra : Field (ZMod modulus)]
local instance : SampleableType (ZMod modulus) := SampleableType.ofFintype _
local instance (event : Domain.Event (uniformCarriers (ZMod modulus) (ZMod modulus))) :
    SampleableType (Domain.Raw event) := Domains.PrimeField.rawSampleable modulus event

theorem polynomial_agreement (field : String) (origin : Origin)
    (request : origin.request = some (.draw field)) (p q : Polynomial (ZMod modulus))
    (different : p ≠ q) (left : p.natDegree ≤ 1) (right : q.natDegree ≤ 1) :
    letI : SampleableType (Domain.Raw (.challenge origin : Domain.Event
        (uniformCarriers (ZMod modulus) (ZMod modulus)))) :=
      Domains.PrimeField.rawSampleable modulus (.challenge origin)
    Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event (uniformCarriers (ZMod modulus) (ZMod modulus))))}[
      p.eval (Original.fieldReply (carriers := uniformCarriers (ZMod modulus) (ZMod modulus)) origin field request raw) =
        q.eval (Original.fieldReply (carriers := uniformCarriers (ZMod modulus) (ZMod modulus)) origin field request raw)] ≤
      1 / (Fintype.card (ZMod modulus) : ENNReal) := by
  rcases origin with ⟨entry, events, selected⟩
  dsimp only at request
  subst selected
  change Pr{let value ← $ᵗ (ZMod modulus)}[p.eval value = q.eval value] ≤ _
  simpa only [max_self, Nat.cast_one] using agreement_uniform_le p q different left right

#print axioms polynomial_agreement
end ZkcSecurity.Realizations.Sumcheck.SourcePublicPrimeField
