module

public import ZkcSecurity.Families.Sumcheck.TableComponentReadbackTactics
public import ZkcSecurity.Families.Sumcheck.CompiledValidator
public import ZkcSecurity.FiatShamir.DomainComposition

@[expose] public section

/-! Unary structural execution reuses the installed component normalizer.
The actual generated view supplies its spine and reached immutable frame;
only source mathematical equations are supplied by clients. -/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.CompiledValidator.Execution
open Zkc.Construction
open TableComponent.Execution

macro "normalize_table_validator " "[" laws:term,* "]"
    " unfolding " "[" definitions:term,* "]" : tactic =>
  `(tactic| normalize_component_process
    [FiatShamir.DomainReduction.ReadingTo.checkpoint,
      FiatShamir.DomainReduction.CoherentTo.checkpoint,
      FiatShamir.DomainReduction.Bridge.checkpoint]
    [$laws,*] unfolding [$definitions,*])


open Zkc.Source Zkc.Source.Structured TableComponent

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Adapt the installed loop bridge to its exact generated source-body equation.
The capture size and complete carry/return maps remain checked arguments. -/
theorem sourceLoop (field : String) (program : Structured.Program) (context : Zkc.Construction.Context)
    (plan : CompiledRound.Plan) (sites : Nominal.Schedule field)
    (connection : CompiledValidator.RoundConnection (F := F) (G := G) field program context plan sites)
    (body : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G))
      (Domain.Environment (uniformCarriers F G)))
    (offset : Nat) (body_eq : body = CompiledRound.block plan program context field offset)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (indices : List Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :
    FiatShamir.DomainReduction.Bridge (Nominal.interface (G := G) field)
      (CompiledValidator.LoopPost (field := field) (context := context) point.length indices.length)
      history
      (Domain.iterate body captured [offset + 21, offset + 26, offset + 20]
        [.data (.vector field), .data (.field field), .transcript context.suite]
        indices (CompiledValidator.carried field context.suite ⟨point, scalar, history⟩))
      ((TableComponent.Execution.run field sites indices ⟨point, scalar, history⟩).bind
        (fun final => .done (CompiledValidator.carried field context.suite final))) := by
  rw [body_eq, ← size]
  exact CompiledValidator.loop_bridge connection captured indices ⟨point, scalar, history⟩


open FiatShamir.DomainReduction

/-- Retain the complete typed state when composing the reached source loop
with its continuation. The encoder/decoder round trip is checked. -/
theorem sourceLoopBind {B : Type}
    (field : String) (program : Structured.Program) (context : Zkc.Construction.Context)
    (plan : CompiledRound.Plan) (sites : Nominal.Schedule field)
    (connection : CompiledValidator.RoundConnection (F := F) (G := G) field program context plan sites)
    (body : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G))
      (Domain.Environment (uniformCarriers F G)))
    (offset : Nat) (body_eq : body = CompiledRound.block plan program context field offset)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (indices : List Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G))
    (Post : Domain.History (uniformCarriers F G) → B → Prop)
    (nextActual : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G)) B)
    (nextPresented : TableComponent.Execution.State F G → PIR.Process (Nominal.signature F field) B)
    (next : ∀ final, final.point.length = point.length + indices.length →
      FiatShamir.DomainReduction.Bridge (Nominal.interface (G := G) field) Post final.history
        (nextActual (CompiledValidator.carried field context.suite final)) (nextPresented final)) :
    FiatShamir.DomainReduction.Bridge (Nominal.interface (G := G) field) Post history
      ((Domain.iterate body captured [offset + 21, offset + 26, offset + 20]
        [.data (.vector field), .data (.field field), .transcript context.suite]
        indices (CompiledValidator.carried field context.suite ⟨point, scalar, history⟩)).bind nextActual)
      ((TableComponent.Execution.run field sites indices ⟨point, scalar, history⟩).bind nextPresented) := by
  apply ZkcSecurity.FiatShamir.DomainReduction.Bridge.bindEncoded
    (CompiledValidator.carried field context.suite) CompiledValidator.decode (fun _ => rfl)
    TableComponent.Execution.State.history (fun final => final.point.length = point.length + indices.length)
    ((sourceLoop field program context plan sites connection body offset body_eq captured size indices point scalar history).weaken ?_)
    nextActual nextPresented next
  intro reached output post
  obtain ⟨final, same, length, outputEq⟩ := post
  exact ⟨final, same.symm, length, outputEq⟩


end ZkcSecurity.Families.Sumcheck.CompiledValidator.Execution
