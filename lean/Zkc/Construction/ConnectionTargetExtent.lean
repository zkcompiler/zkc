module

public import Zkc.Construction.ConnectionTargetPrefix
public import Zkc.Construction.OriginalFrameRelations
public import Zkc.Semantics.Yields

@[expose] public section

/-! Finite physical-extent admission for a flat callee slice. Extents count all
SSA cells, including untracked temporaries. They are independent of source
normalization and never infer success from a refusing computation. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionTargetExtent
open Zkc.Source Zkc.Source.Structured
abbrev TargetBlock := (model : DomainModel) → Domain.View.Block model.toCarriers

inductive Extent : Nat → Nat → TargetBlock → Type 1 where
  | empty (size : Nat) : Extent size size (fun _ => Domain.View.empty)
  | sequence {input middle output : Nat} {first rest : TargetBlock}
      (head : Extent input middle first) (tail : Extent middle output rest) :
      Extent input output (fun model => Domain.View.sequence (first model) (rest model))
  | receive (size : Nat) (site schema peer : String) (ty : Ty) (declared : List ValueSort) :
      Extent size (size + declared.length) (fun _ => Domain.View.receive site schema peer ty declared)
  | send (size : Nat) (site schema peer : String) (reference : Nat) (declared : List ValueSort) :
      Extent size size (fun _ => Domain.View.send site schema peer reference declared)
  | indicesEmpty (size : Nat) (declared : List ValueSort) :
      Extent size (size + declared.length) (fun _ => Domain.View.indicesEmpty declared)
  | indicesAppend (size coordinates index : Nat) (declared : List ValueSort) :
      Extent size (size + declared.length) (fun _ => Domain.View.indicesAppend coordinates index declared)
  | observe (size : Nat) (context : Context) (suite : String) (template : Template)
      (state value coordinates : Nat) (declared : List ValueSort) :
      Extent size (size + declared.length) (fun _ => Domain.View.observe context suite template state value coordinates declared)
  | challenge (size : Nat) (context : Context) (suite field : String) (template : Template)
      (state coordinates : Nat) (declared : List ValueSort) :
      Extent size (size + declared.length) (fun _ => Domain.View.challenge context suite field template state coordinates declared)
  | localService (size : Nat) (context : Context) (port : ServicePort) (request : Request)
      (template : Template) (coordinates references : List Nat) (declared : List ValueSort) :
      Extent size (size + declared.length) (fun _ => Domain.View.localService context port request template coordinates references declared)
  | calculation (size : Nat) (operation : Calculation) (references : List Nat) (declared : List ValueSort) :
      Extent size (size + declared.length) (fun model => Domain.View.calculation model operation references declared)
  | helper (size : Nat) (program : Program) (name : String) (references : List Nat) (declared : List ValueSort) :
      Extent size (size + declared.length) (fun model => Domain.View.helper model program name references declared)
  | guard (size reference : Nat) (declared : List ValueSort) :
      Extent size size (fun _ => Domain.View.guard reference declared)
  | loop (size maximum : Nat) (yielded : List Nat) (count : Nat) (initial : List Nat)
      (declared : List ValueSort) (body : TargetBlock) :
      Extent size (size + declared.length) (fun model => Domain.View.loop maximum yielded count initial declared (body model))

private theorem append_yields {carriers : Carriers} (declared : List ValueSort)
    (environment values : Domain.Environment carriers) :
    PIR.Yields (fun frame => frame.length = environment.length + declared.length)
      (Domain.View.append declared environment values) := by
  unfold Domain.View.append
  split
  · rename_i sorted
    have sorts : values.map Domain.Value.sort = declared := by simpa [Domain.sortsMatch] using sorted
    have lengths := congrArg List.length sorts
    simpa only [PIR.Yields, List.length_append, List.length_map] using congrArg (environment.length + ·) lengths
  · trivial

private theorem append_any {carriers : Carriers} {A : Type} (process : PIR.Process (Domain.effects carriers) A) :
    PIR.Yields (fun _ => True) process := by
  induction process with
  | done | halt => trivial
  | call _ _ ih => exact ih

/-- A finite extent proof covers every reply and every successful return. -/
theorem Extent.yields {input output : Nat} {target : TargetBlock} (certificate : Extent input output target)
    (model : DomainModel) (environment : Domain.Environment model.toCarriers)
    (size : environment.length = input) :
    PIR.Yields (fun frame => frame.length = output) (target model environment) := by
  induction certificate generalizing environment with
  | empty => exact size
  | sequence head tail headIH tailIH =>
    dsimp only [Domain.View.sequence, PIR.Yields]
    intro _
    exact (headIH environment size).bind fun frame bound => fun _ => tailIH frame bound
  | loop size maximum yielded count initial declared body =>
    simp only [Domain.View.loop]
    split
    · split
      · exact (append_any _).bind fun frame _ => by simpa only [size] using append_yields declared environment frame
      · trivial
    · trivial
  | receive | send | indicesEmpty | indicesAppend | calculation | helper | guard | observe | challenge | localService =>
    simp only [Domain.View.receive, Domain.View.send, Domain.View.indicesEmpty,
      Domain.View.indicesAppend, Domain.View.calculation, Domain.View.helper, Domain.View.guard,
      Domain.View.observe, Domain.View.challenge, Domain.View.localService]
    all_goals repeat' first
      | exact size
      | exact trivial
      | (simpa only [size] using append_yields _ environment _)
      | dsimp only [PIR.Yields]
      | split
      | intro _

end Zkc.Construction.ConnectionTargetExtent

namespace Zkc.Construction.Original
open Zkc.Source Zkc.Source.Structured

/-- Strengthen successful returns with an independently checked target fact. -/
noncomputable def Simulation.withTargetInvariant {carriers : Carriers} {A B : Type}
    {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (certificate : Simulation returns live source target) {post : B → Prop}
    (invariant : PIR.Yields post target) :
    Simulation (fun a b => returns a b ∧ post b) live source target := by
  induction certificate with
  | done related => exact .done ⟨related,invariant⟩
  | halt reason => exact .halt reason
  | call operation next ih => exact .call operation fun reply => ih reply (invariant reply)
  | checkpoint frame kept next ih => exact .checkpoint frame kept (ih (invariant ()))

end Zkc.Construction.Original
