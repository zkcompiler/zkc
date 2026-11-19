import Zkc.Tools.Formal.SumcheckGoal
import Zkc.Tests.Formal.SourcePairReadback

open Zkc.Core Zkc.Frontend Zkc.Tools.Formal Zkc.Tests.Formal
open Zkc.Formal.Interactive Zkc.Formal.Interactive.Sumcheck
open Zkc.Formal.Written Zkc.Formal.FiniteService Zkc.Formal.ProbabilisticProcess
open scoped Zkc.Formal.Written.RoundCharge ENNReal

private def sourceRequest (entry : String) (edit : String → String := id) : IO Assembly := do
  let root := (← IO.currentDir) / "../.."
  let file := "sumcheck_example.zkc"
  assemble #[⟨file, Syntax.parseString file entry⟩] fun parts => do
    if parts == #["sumcheck"] then
      let path := root / "examples/sumcheck.zkc"
      return some ⟨path.toString, Syntax.parseString path.toString (edit (← IO.FS.readFile path))⟩
    SourcePairReadback.loadModule root .original parts

private def refused {α} (result : Except String α) (why : String) : IO Unit := do
  let .error message := result | throw (IO.userError s!"expected {why}")
  unless message.contains why do throw (IO.userError s!"expected {why}, got {message}")

#eval show IO Unit from do
  let entry ← IO.FS.readFile "../../examples/sumcheck_example.zkc"
  let name := "written_sound"
  let select (src : String) (edit : String → String := id) :=
    return Written.admitSoundnessGoal (← sourceRequest src edit) name
  let ⟨c, _, g⟩ ← IO.ofExcept (issueSumcheckGoal (← sourceRequest entry) name)
  let order := Zkc.Vocabulary.Field.bls12381Fr.order
  unless g.request.rounds == 10 && g.request.ceiling == some (Rat.divInt 10 order) &&
      g.checked.issued.charge.draws.length == 10 do throw (IO.userError "wrong written goal")
  let twoSchemes := entry ++ "\nscheme Small = Sumcheck<2>:\n    prover P\n    construction interactive\n" ++
    "goal small = soundness(Small) <= 2 / Fr::Order\n"
  let ⟨small, _, smallGoal⟩ ← IO.ofExcept (issueSumcheckGoal (← sourceRequest twoSchemes) "small")
  unless smallGoal.request.rounds == 2 do throw (IO.userError "wrong scheme selected")
  refused (certifySumcheckGoal small name) "different root"
  let impossible ← IO.ofExcept (← select (entry.replace "10 / Fr::Order" "9 / Fr::Order"))
  refused (certifySumcheckGoal impossible name) "GL4"
  let noMaximum ← IO.ofExcept (← select (entry.replace " <= 10 / Fr::Order" ""))
  let reported ← IO.ofExcept (certifySumcheckGoal noMaximum name)
  unless reported.request.bound reported.checked.issued.charge == (10, order) do
    throw (IO.userError "wrong reported bound for an unbudgeted request")
  let renamed ← IO.ofExcept (← select entry fun src =>
    src.replace "proves @V Sum(values, claim)" "proves @V Sum(claim = claim, values = values)")
  let _ ← IO.ofExcept (certifySumcheckGoal renamed name)
  let different ← IO.ofExcept (← select entry fun src =>
    src.replace "proves @V Sum(values, claim)" "proves @V Sum(claim = 0, values = values)")
  refused (certifySumcheckGoal different name) "written sum relation"
  refused (← select (entry.replace "written_sound = soundness" "written_sound = completeness")) "GL3"
  refused (certifySumcheckGoal c "sound") "WK-GOAL"
  refused (certifySumcheckGoal c "complete") "WK-GOAL"
  refused (← select (entry.replace "statement = fixed, stage = written" "stage = written")) "GL3"
  refused (← select (entry.replace "statement = fixed" "model = random_oracle(queries = 1)")) "WK-GOAL"
  refused (← select (entry.replace "stage = written" "stage = constructed")) "WK-GOAL"
  -- The callee's charge reads two same-typed proof parameters through its application.
  let weightedEntry := (entry.replace "statement = fixed" "spec top = 2, spec bottom = 1, statement = fixed").replace
    "10 / Fr::Order" "20 / Fr::Order"
  let weighted := fun (reverse : Bool) (src : String) =>
    ((((src.replace "Sumcheck<n: nat>" "Sumcheck<n: nat, spec top: nat, spec bottom: nat>").replace
      "k: nat, rounds: nat> roles" "k: nat, rounds: nat, spec num: nat, spec den: nat> roles").replace
      "Reduce<Pairs, rounds = n>" (if reverse then "Reduce<Pairs, rounds = n, spec num = bottom, spec den = top>"
                                  else "Reduce<Pairs, rounds = n, spec den = bottom, spec num = top>")).replace
      "charge sites.challenge <= R::Degree / F::Order" "charge sites.challenge <= R::Degree * num / (den * F::Order)")
  let scaled ← IO.ofExcept (← select weightedEntry (weighted false))
  let scaledGoal ← IO.ofExcept (certifySumcheckGoal scaled name)
  unless scaledGoal.checked.issued.charge.numerator == 2 do throw (IO.userError "lost callee proof arguments")
  let swapped ← IO.ofExcept (← select weightedEntry (weighted true))
  refused (certifySumcheckGoal swapped name) "too small"
  IO.println "Named written Sumcheck verified its source ceiling, reordered relation operands and refusal controls."

-- Spell out the program inputs and event independently of the issuer's argument packer.
private noncomputable def acceptance {c : Written.AdmittedRoot} {goal : String}
    (g : CertifiedSumcheckGoal c goal) (advance : Occurrence → Scalar → Scalar → Scalar)
    (other : Slots (RSig scalarModel) Scalar) (path : List Zkc.Core.Frame)
    (state : Scalar) (table : Cube Scalar g.request.rounds) (claim : Scalar) (event : Bool) :=
  let cert := (g.checked.standardVerifier g.plain).1
  let inputs := HList.cons (hide scalarModel 1 _ (Cube.flatten _ table))
    (.cons (hide scalarModel 1 _ claim) .nil)
  prEvent (observed (fun _ _ => event) <$> run
    (service (RoundService.withChallenge scalarModel ArithmeticModel.events
      (ZMod.finEquiv Zkc.Vocabulary.Field.bls12381Fr.order) advance other))
    (roleMeaning scalarModel _ cert.root 1 path inputs) state)

example {assembly : Assembly} {goal : String} (issued : IssuedSumcheckGoal assembly goal)
    (root : Written.AdmittedRoot) (sourceAdmission : Written.admitSoundnessGoal assembly goal = .ok root)
    (request : SumcheckRequest) (sourceRead : readSumcheckRequest root goal = .ok request)
    (q : Rat) (sourceBudget : request.ceiling = some q)
    (advance : Occurrence → Scalar → Scalar → Scalar) (other : Slots (RSig scalarModel) Scalar)
    (path : List Zkc.Core.Frame) (state : Scalar) (table : Cube Scalar issued.certified.request.rounds) (claim : Scalar)
    (wrong : claim ≠ Cube.sum _ table) (_alsoWrong : state ≠ Cube.sum _ table) :
    acceptance issued.certified advance other path state table claim true ≤ (q.num.toNat : ℝ≥0∞) / q.den := by
  let g := issued.certified
  have actualRoot : issued.root = root := Except.ok.inj (issued.admitted.symm.trans sourceAdmission)
  subst root
  have selected : g.request = request := Except.ok.inj (g.selected.symm.trans sourceRead)
  have ceiling : g.request.ceiling = some q := selected ▸ sourceBudget
  fail_if_success exact True.intro
  have weaker (h : acceptance g advance other path state table claim false ≤ (q.num.toNat : ℝ≥0∞) / q.den) :
      acceptance g advance other path state table claim false ≤ (q.num.toNat : ℝ≥0∞) / q.den := h
  fail_if_success apply weaker
  -- Both calls are well typed. Even supplying the matching false-claim hypothesis for the
  -- swapped public claim cannot prove the statement about the original strategy state.
  have certFor (st v : Scalar) (h : v ≠ Cube.sum _ table) :
      acceptance g advance other path st table v true ≤ (q.num.toNat : ℝ≥0∞) / q.den := by
    have certified := g.falseAcceptance advance other path st table v h
    dsimp only at certified
    simp only [SumcheckRequest.bound, ceiling] at certified
    unfold acceptance
    exact certified
  fail_if_success exact certFor claim state _alsoWrong
  exact certFor state claim wrong
