import Zkc.Tools.Formal.TableBound
import Zkc.Tests.Formal.TableRuntime
import Zkc.Tests.Formal.SourcePairReadback

namespace FixedTableSampling
open Zkc.Core Zkc.Frontend Zkc.Tests.Formal Zkc.Formal.Written
open TableVerifier TableService

#print axioms Certificate.sound
#print axioms Certificate.observedReturn

def admit (root : System.FilePath) (entry : SourceInput) : IO Written.AdmittedRoot := do
  let assembly ← assemble #[entry] (SourcePairReadback.loadModule root .original)
  let state ← IO.ofExcept (Written.sourceState assembly)
  let #[scheme] := state.results.schemes.filter (·.name == "Checked") | throw (IO.userError "missing Checked")
  Written.admitInstance state scheme.protocol default |> IO.ofExcept

/-- The event in the public probability endpoint runs the admitted protocol member. -/
example {s : Written.AdmittedRoot} (c : Certificate s) (M : Model s.emission.bindings.vocabulary)
    [DecidableEq (M.Val c.handle)] [DecidableEq (M.Val (scalar s.emission.bindings))]
    (p : M.Val (polynomial s.emission.bindings)) (d : M.Val c.domain)
    (f : Offer (M.Val c.handle) (M.Val (scalar s.emission.bindings))) (o : Opener _ _)
    (ev : Evaluation c.calls M (Defs.fnTable M c.entry.definitions) p d)
    (few : (Finset.univ.filter fun i => f.data i = ev.expected i).card ≤ 768) :
    𝒟[AnswerTape.answerTape (Fin 1024) 40]
      {t | accepted M c.handle f o t (roleMeaning M s.evidence.admitted.program c.root 1 [] (arguments M p d)) = true}
      ≤ ENNReal.ofReal (c.draw.ceiling : ℝ) :=
  c.sound M p d f o ev few

#eval show IO Unit from do
  let root := (← IO.currentDir) / "../.."
  let path := root / "examples/spot_check.zkc"
  let original ← admit root (← SourcePairReadback.source .original path)
  let some cert := certify original | throw (IO.userError "original verifier certificate refused")
  IO.ofExcept (TableRuntime.controls (compiled original) ⟨original.id⟩ cert.domain cert.handle cert.shape cert.root)
  let text ← IO.FS.readFile path
  let guard := "guard @V ∀ j ∈ 0..q, rows[j] == evaluate(p, domain[positions[j]])"
  unless (text.splitOn guard).length == 2 do throw (IO.userError "missing unique verifier guard")
  let weakened ← admit root ⟨path.toString, Syntax.parseString path.toString (text.replace guard "guard @V true")⟩
  let draw ← IO.ofExcept (Written.declaredDraw weakened.state ⟨weakened.id⟩ "positions")
  unless draw.ceiling == cert.draw.ceiling do throw (IO.userError "guard mutation changed the written charge")
  unless (certify weakened).isNone do throw (IO.userError "weakened guard received the original bound")
  let alternate := text.replace "q = 40, e = 256" "q = 20, e = 448"
  unless alternate != text do throw (IO.userError "missing sampling control")
  let fewerDraws ← admit root ⟨path.toString,Syntax.parseString path.toString alternate⟩
  let equalCost ← IO.ofExcept (Written.declaredDraw fewerDraws.state ⟨fewerDraws.id⟩ "positions")
  unless equalCost.ceiling == cert.draw.ceiling do throw (IO.userError "expected equal rational ceilings")
  unless (certify fewerDraws).isNone do throw (IO.userError "twenty draws received the forty-draw certificate")
  let oracleFile := root / "libraries/zkc/oracle.zkc"
  let library ← IO.FS.readFile oracleFile
  let indexing := "def answer(data, position): data[position]"
  unless (library.splitOn indexing).length == 2 do throw (IO.userError "missing primitive answer control")
  let alteredLibrary := library.replace indexing "def answer(data, position): data[0]"
  let assembly ← assemble #[← SourcePairReadback.source .original path] fun name =>
    if name == #["zkc","oracle"] then
      pure (some ⟨oracleFile.toString,Syntax.parseString oracleFile.toString alteredLibrary⟩)
    else SourcePairReadback.loadModule root .original name
  let state ← IO.ofExcept (Written.sourceState assembly)
  let #[checked] := state.results.schemes.filter (·.name == "Checked") | throw (IO.userError "missing altered Checked")
  if (Written.admitInstance state checked.protocol default).isOk then
    throw (IO.userError "changed Kind.answer admitted with the original indexing semantics")
  IO.println "Checked written table registration, both executions, opening controls and refusal of the weakened guard"

end FixedTableSampling
