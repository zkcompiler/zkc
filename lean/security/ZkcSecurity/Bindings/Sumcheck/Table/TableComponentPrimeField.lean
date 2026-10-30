module

public import ZkcSecurity.Bindings.Sumcheck.Table.TableComponentFrame
public import ZkcSecurity.Bindings.Sumcheck.Table.TableComponentCost
public import ZkcSecurity.Bindings.Models.PrimeField

@[expose] public section

/-! Exact raw-query sampling for the selected finite prime-field model. The
query's nominal request determines its carrier and sampler. A conditional
escape bound therefore follows from the existing degree-one root bound.
-/

set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Families.Sumcheck.TableComponent.PrimeField
open Zkc.Source Zkc.Construction Zkc.Transcript OracleComp OracleSpec
open ZkcSecurity.Domains

variable (modulus : Nat) [Fact modulus.Prime]

local instance fieldSamples : SampleableType (ZMod modulus) :=
  SampleableType.ofFintype _
local instance rawSamples (event : Domain.Event (Structured.uniformCarriers
    (ZMod modulus) (ZMod modulus))) : SampleableType (Domain.Raw event) :=
  Domains.PrimeField.rawSampleable modulus event

theorem query_uniform (field : String) (origin : Origin)
    (request : origin.request = some (.draw field)) (predicate : ZMod modulus → Prop) :
    letI : SampleableType (Domain.Raw (.challenge origin : Domain.Event
      (Structured.uniformCarriers (ZMod modulus) (ZMod modulus)))) :=
      Domains.PrimeField.rawSampleable modulus (.challenge origin)
    Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin :
        Domain.Event (Structured.uniformCarriers (ZMod modulus) (ZMod modulus))))}[
      predicate (by simpa only [Domain.Raw, request, Request.draw] using raw)] =
      Pr{let value ← $ᵗ (ZMod modulus)}[predicate value] := by
  rcases origin with ⟨entry, event, selected⟩
  dsimp only at request
  subst selected
  rfl

variable {Frame : Type}

theorem conditional (field : String) :
    (Nominal.queries (F := ZMod modulus) (G := ZMod modulus) (Frame := Frame) field).ConditionalBound
      (Nominal.layout field).representation 1 1
      (fun _ _ => 1 / (Fintype.card (ZMod modulus) : ENNReal)) := by
  have uniform : ∀ {n} (schedule : Nominal.Schedule field)
      (state : PrefixState (ZMod modulus) Frame (n + 1))
      (message : (Message.endpoints (ZMod modulus)).Carrier) (predicate : ZMod modulus → Prop),
      Pr{let raw ← $ᵗ (Domain.Raw ((Nominal.queries (G := ZMod modulus) field).event
        schedule state message))}[
          predicate ((Nominal.queries field).challenge schedule state message raw)] =
        Pr{let value ← $ᵗ (ZMod modulus)}[predicate value] := by
    intro n schedule state message predicate
    exact query_uniform modulus field (schedule.query state.point.length)
      (schedule.request _) predicate
  intro n
  simpa only [max_self, Nat.cast_one] using
    (QueryInterface.conditional_of_uniform
      (Nominal.queries (F := ZMod modulus) (G := ZMod modulus) (Frame := Frame) field)
      (Nominal.layout field).representation 1 1 uniform (n := n))

/-- Updating the retained full frame leaves the same raw sampler and the same
decoded mathematical table in the conditional escape obligation. -/
theorem conditionalWithFrame (field : String)
    (update : Nominal.FrameUpdate (ZMod modulus) Frame field) :
    (Nominal.queriesWithFrame (G := ZMod modulus) field update).ConditionalBound
      (Nominal.layoutWithFrame field update).representation 1 1
      (fun _ _ => 1 / (Fintype.card (ZMod modulus) : ENNReal)) := by
  intro n context state allowed message history p q different left right
  exact conditional modulus field context state allowed message history p q different left right

end ZkcSecurity.Families.Sumcheck.TableComponent.PrimeField
