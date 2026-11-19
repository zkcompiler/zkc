module

public import Zkc.Formal.Written.TableGuard
public import Zkc.Formal.Written.TableService

@[expose] public section
namespace Zkc.Formal.Written.TableVerifier
open Core Frontend.Emit TableService

variable {b : Bindings} {hs : Headers b.vocabulary} {domain handle : b.vocabulary.Ty}
variable (calls : Calls hs domain) (M : Model b.vocabulary) (fns : FnTable M hs.fns)
variable (roles : RTable M hs.protocols) (h : M.Val handle)
variable (p : M.Val (polynomial b)) (dom : M.Val domain)
variable [DecidableEq (M.Val (scalar b))] (eval : Evaluation calls M fns p dom)
variable (tape : Tape) (data : Fin 1024 → M.Val (scalar b))

abbrev result (pass : Bool) : Program M (HList (RV M 1) []) :=
  bif pass then .done .nil else .halt (.declared .reject ⟨[],⟨17⟩⟩)

theorem guard_result :
    (project 1 (loopBody calls handle)).denote (sem M fns roles) []
      (startEnv M h p dom (indices tape) (batch tape data)) =
    result M (prefixMatches (fun j => decide (data (tape j) = eval.expected (tape j))) 40) := by
  let f := fun j => decide (data (tape j) = eval.expected (tape j))
  have initial : prefixMatches f 0 = true := by simp [prefixMatches]
  unfold loopBody
  simp only [project, projectLoop, List.mem_cons_self, dite_true]
  rw [Term.denote_loop]
  change (Process.iterate 40 (step calls M fns roles h p dom (indices tape) (batch tape data))
    0 (accumulator M fns roles true)).bind _ = _
  have iter := loop_value calls M fns roles h p dom eval tape data (n := 40) (i := 0) (by decide)
  change Process.iterate _ _ _ (accumulator M fns roles (prefixMatches f 0)) = _ at iter
  rw [initial] at iter
  rw [iter]
  change _ = result M (prefixMatches f (0+40))
  generalize prefixMatches f (0+40) = pass
  cases pass <;> rfl

abbrev arguments : HList (RV M 1) (ports domain) := .cons p (.cons dom .nil)
abbrev prefixProgram (tail : Term (protocolDialect b.vocabulary hs) (ready domain handle) []) := (project 1 (withTail calls handle tail)).denote (sem M fns roles) [] (Env.empty.extend (names domain) (arguments M p dom))

variable [DecidableEq (M.Val handle)]
variable (offer : Offer (M.Val handle) (M.Val (scalar b))) (opener : Opener (M.Val handle) (M.Val (scalar b)))

variable (tail : Term (protocolDialect b.vocabulary hs) (ready domain handle) [])
omit [DecidableEq (M.Val (scalar b))] [DecidableEq (M.Val handle)] in
set_option maxHeartbeats 1000000 in
private theorem prefix_process :
    prefixProgram (handle := handle) calls M fns roles p dom tail =
    .call (.hear (.request ⟨0⟩) 0 ⟨[],⟨1⟩⟩ handle) fun h =>
    .call (.own (.coin (.uniform (.seq (.fin 1024) (some 40)))) [0] ⟨[],⟨2⟩⟩ [] .nil (positions b)) fun ps =>
    .call (.hear (.request ⟨1⟩) 0 ⟨[],⟨4⟩⟩ (rows b)) fun rs =>
    .call (.own (.request ⟨2⟩) [] ⟨[],⟨6⟩⟩ [.tuple (claim handle)] (.cons (h,ps,rs,()) .nil) .bool) fun ok =>
    bif ok then (project 1 tail).denote (sem M fns roles) [] (startEnv M h p dom ps rs)
    else .halt (.declared .reject ⟨[],⟨7⟩⟩) := by
  unfold prefixProgram withTail
  simp (config := {decide := true}) only [project, ProtocolOp.project, dite_true, dite_false, Term.denote_op, Term.denote_guard]
  apply congrArg (Process.call _)
  funext h
  apply congrArg (Process.call _)
  funext ps
  apply congrArg (Process.call _)
  funext rs
  apply congrArg (Process.call _)
  funext ok
  cases ok <;> rfl

private theorem after_requests :
    accepted M handle offer opener tape (prefixProgram (handle := handle) calls M fns roles p dom tail) =
      let proposal := opener offer.handle (request tape)
      let pass := opens offer tape proposal offer.handle (request tape) proposal.2
      bif pass then returned (outcome (answer M handle offer opener tape)
        ((project 1 tail).denote (sem M fns roles) []
          (startEnv M offer.handle p dom (request tape) proposal.2)) .closed) else false := by
  let rs := opener offer.handle (request tape)
  let replay := answer M handle offer opener tape
  have reg : replay (.hear (.request ⟨0⟩) 0 ⟨[],⟨1⟩⟩ handle) .empty = (some offer.handle,.registered offer) := by
    exact congrArg (·, State.registered offer) (deliver_self M offer.handle)
  have draw : replay (.own (.coin (.uniform (.seq (.fin 1024) (some 40)))) [0] ⟨[],⟨2⟩⟩ [] .nil (positions b))
      (.registered offer) = (some (request tape),.drawn offer tape) := by exact congrArg (·, State.drawn offer tape) (deliver_self M (t := positions b) (request tape))
  have rowsAt : replay (.hear (.request ⟨1⟩) 0 ⟨[],⟨4⟩⟩ (rows b)) (.drawn offer tape) =
      (some rs.2,.answered offer tape rs.1 rs.2) := by exact congrArg (·, State.answered offer tape rs.1 rs.2) (deliver_self M (t := rows b) rs.2)
  let packet : M.Val (.tuple (claim handle)) := (offer.handle,request tape,rs.2,())
  let check := opens offer tape rs offer.handle (request tape) rs.2
  have opened : replay (.own (.request ⟨2⟩) [] ⟨[],⟨6⟩⟩ [.tuple (claim handle)] (.cons packet .nil) .bool)
      (.answered offer tape rs.1 rs.2) = (some check,.closed) := by
    change (if eq : Ty.tuple (claim handle) = Ty.tuple (claim handle) then _ else _) = _
    rw [dite_eq_left rfl]
    exact congrArg (·, State.closed) (deliver_self M (t := .bool) check)
  dsimp only [replay] at reg draw rowsAt opened
  dsimp only [packet] at opened
  rw [prefix_process]
  unfold accepted outcome
  simp only [Process.interpret, reg, draw, rowsAt, opened]
  change returned (outcome _ (bif check then _ else _) State.closed) = (bif check then _ else false)
  generalize check = pass
  cases pass <;> rfl

abbrev program := prefixProgram (handle := handle) calls M fns roles p dom (loopBody calls handle)

theorem accepts_iff :
    accepted M handle offer opener tape (program (handle := handle) calls M fns roles p dom) = true ↔
    opens offer tape (opener offer.handle (request tape)) offer.handle (request tape)
      (opener offer.handle (request tape)).2 = true ∧
      ∀ j, offer.data (tape j) = eval.expected (tape j) := by
  unfold program
  rw [after_requests]
  dsimp only
  let proposal := opener offer.handle (request tape)
  by_cases ok : opens offer tape proposal offer.handle (request tape) proposal.2 = true
  · have actual : proposal.2 = values offer.data tape := (of_decide_eq_true ok).2.2.2.2
    change (bif opens offer tape proposal offer.handle (request tape) proposal.2 then _ else false) = true ↔ _
    rw [ok]
    simp only [Bool.cond_true]
    change returned (outcome (answer M handle offer opener tape)
      ((project 1 (loopBody calls handle)).denote (sem M fns roles) []
        (startEnv M offer.handle p dom (indices tape) proposal.2)) .closed) = true ↔ _
    rw [actual]
    erw [guard_result calls M fns roles offer.handle p dom eval tape offer.data]
    let f := fun j => decide (offer.data (tape j) = eval.expected (tape j))
    have final : (prefixMatches f 40 = true) ↔ ∀ j, offer.data (tape j) = eval.expected (tape j) := by
      simp only [prefixMatches, decide_eq_true_eq, Fin.is_lt, true_implies, f]
    change returned (outcome _ (result M (prefixMatches f 40)) _) = true ↔ _
    cases e : prefixMatches f 40 <;> simp_all [result, outcome, Process.interpret, returned, proposal]
  · have fail := Bool.eq_false_iff.mpr ok
    change (bif opens offer tape proposal offer.handle (request tape) proposal.2 then _ else false) = true ↔ _
    rw [fail]
    simp

end Zkc.Formal.Written.TableVerifier
