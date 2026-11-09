module

public import Zkc.Tools.Protocol.Construction
import Std.Tactic.Do

set_option experimental.vcgen true

open PIR Zkc.Source ProtocolProof Std.WP

@[expose] public section

namespace ProtocolProofExamples.ConstructionPilot

abbrev Service : Signature := ⟨Empty, fun x => nomatch x⟩

def spec : OperationSpec Service Unit Unit := fun x => nomatch x

theorem spec_monotone : spec.Monotone := by intro x; exact nomatch x

noncomputable abbrev proofLogic : WPMonad (Process Service)
    (Potential Unit Unit)ᵒᵈ (Stop → Potential Unit Unit)ᵒᵈ :=
  spec.toUpperWPMonad spec_monotone

attribute [local instance] proofLogic


example (x : Nat) (post : Nat → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post x⦄ (pure x : Process Service Nat) ⦃post; stopped⦄ := by vcgen

example (x : Nat) (post : Nat → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post x⦄ (do let a ← pure x; pure a : Process Service Nat) ⦃post; stopped⦄ := by vcgen

example {A : Type} (p : Process Service A) (post : A → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃wp p post stopped⦄ (do let a ← p; pure a) ⦃post; stopped⦄ := by vcgen

abbrev language : Language where
  Ty := Unit
  Op := Unit
  arguments _ := [(), ()]
  result _ := ()
  condition := ()

abbrev meaning : Interpretation language Service where
  Value _ := Nat
  condition x := x != 0
  operation _ args := .done (args.get .here - args.get (.there .here))

def helper : Region (scalarDialect language) [(), ()] [()] :=
  .letOp (.ordinary ()) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))

def caller : Region (scalarDialect language) [(), ()] [()] :=
  .bind helper (.bind (helper.rename (fun ref => .there ref)) (.ret (.cons .here .nil)))

@[spec] theorem difference (args : Values meaning.Value [(), ()])
    (post : Nat → (Potential Unit Unit)ᵒᵈ) (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (args.get .here - args.get (.there .here))⦄ meaning.operation () args
      ⦃post; stopped⦄ := by
  simpa only [meaning, pure] using
    (Spec.pure (m := Process Service) (post := post) (epost := stopped)
      (args.get .here - args.get (.there .here)))

@[spec] theorem helper_law (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (.singleton (env .here - env (.there .here)))⦄ helper.denote meaning.regionMeaning env
      ⦃post; stopped⦄ := by
  unfold helper
  construct_region

theorem second_call (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ) :
    ⦃post (.singleton (env .here - env (.there .here)))⦄ caller.denote meaning.regionMeaning env
      ⦃post; stopped⦄ := by
  unfold caller
  construct_region

end ProtocolProofExamples.ConstructionPilot
