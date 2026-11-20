module

public import Zkc.Formal.Written.PortSamplers
public import Zkc.Formal.Written.PrimeFive
public import VCVio.OracleComp.Constructions.UniformFinMeasure

@[expose] public section
namespace Zkc.Formal.Written.UniformChallenge
open Core ProbabilisticProcess OracleComp ProbComp
open scoped ENNReal

abbrev M := PrimeFive.model

def port (peers : List Role) (at_ : Occurrence) : InputPort Standard :=
  .own (.coin challengeLaw) peers at_ scalarTy

abbrev draw : ProbComp (ZMod 5) := uniformFin 4

def ask (peers : List Role) (at_ : Occurrence) : Process (RSig M) Unit (ZMod 5) :=
  .call ((port peers at_).operation M) .done

theorem permitted (peers : List Role) (at_ : Occurrence) (v : ZMod 5) :
    Permitted M ((port peers at_).operation M) v :=
  ⟨trivial, ⟨[],scalarTy⟩, rfl, rfl, rfl, trivial⟩

theorem canReturn (peers : List Role) (at_ : Occurrence) (v : ZMod 5) :
    (ask peers at_).CanReturn (Permitted M) v :=
  .call _ v (permitted peers at_ v) (.done _)

theorem returns_uniform (peers : List Role) (at_ : Occurrence) :
    run (serveAt M (port peers at_) draw) (ask peers at_) () =
      (fun v : ZMod 5 ↦ (Outcome.returned v, ())) <$> draw := by
  simp only [run, ask, Process.interpret]
  rw [serves_at M (port peers at_) draw ()]
  change (((fun v : ZMod 5 ↦ (some v,())) <$> draw) >>= fun x : Option (ZMod 5) × Unit ↦
      match x.1 with
      | none => pure (Outcome.unavailable, x.2)
      | some v => pure (Outcome.returned v, x.2)) = _
  rw [bind_map_left]
  exact bind_pure_comp _ _

/-- Exact mass of each challenge in a returning Core computation. -/
theorem probability (peers : List Role) (at_ : Occurrence) (v : ZMod 5) :
    Pr{let out ← run (serveAt M (port peers at_) draw) (ask peers at_) ()}[out.1 = Outcome.returned v] = 1/5 := by
  rw [returns_uniform, prEvent_map]
  change Fin 5 at v
  change Pr{let i ← uniformFin 4}[Outcome.returned (H := Unit) i = .returned v] = _
  rw [prEvent_uniformFin]
  simp only [Outcome.returned.injEq, Finset.filter_eq', Finset.mem_univ, ite_true,
    Finset.card_singleton, Nat.cast_one]
  norm_num

end Zkc.Formal.Written.UniformChallenge
