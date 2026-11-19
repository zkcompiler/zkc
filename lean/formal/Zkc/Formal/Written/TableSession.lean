module

public import Zkc.Formal.Written.TableService

@[expose] public section
namespace Zkc.Formal.Written.TableService
open Core Frontend.Emit TableVerifier ProbabilisticProcess

/-- The registration payload is delivered by the actual prover operation.
Keeping this function over the received list freezes its contents at that event. -/
def freeze {R H : Type} (handle : H) (payload : List R) : Option (Offer H R) :=
  if n : payload.length = 1024 then some ⟨handle, fun i => payload[i.val]'(by rw [n]; exact i.isLt)⟩
  else none

variable {b : Bindings} (M : Model b.vocabulary) (handle : b.vocabulary.Ty)
variable [DecidableEq (M.Val handle)] [DecidableEq (M.Val (scalar b))]

/-- Joint ideal service for the two roles. On the rows request the opener sees exactly
the indices in the incoming packet. The reader's opening uses the same session state. -/
def jointAnswer (fresh : M.Val handle) (propose : Offer (M.Val handle) (M.Val (scalar b)) → Opener (M.Val handle) (M.Val (scalar b)))
    (ps : Draw) (op : GOp M) (state : Session M handle) : Option ((GSig M).Reply op) × Session M handle :=
  match op, state with
  | .given (.request ⟨0⟩) 0 [1] ⟨[],⟨1⟩⟩ [_] (.cons data .nil) t, .empty =>
    match deliver M (u := table b) data >>= freeze fresh with
    | some fixed => (deliver M (u := t) fresh, .registered fixed)
    | none => (none,state)
  | .given (.coin law) 1 [0] addr [] .nil t, .registered fixed =>
    answer M handle fixed (propose fixed) ps (.own (.coin law) [0] addr [] .nil t) state
  | .given (.request ⟨1⟩) 0 [1] ⟨[],⟨4⟩⟩ [_] (.cons packet .nil) t, .drawn fixed ix =>
    match deliver M (u := .tuple (pair handle)) packet with
    | some (h,indices,()) =>
      if h = fixed.handle ∧ indices = request ix then
        let proposal := propose fixed h indices
        (deliver M (t := rows b) (u := t) proposal.2,.answered fixed ix proposal.1 proposal.2)
      else (none,state)
    | none => (none,state)
  | .given (.request ⟨2⟩) 1 [] addr ins args t, .answered fixed .. =>
    answer M handle fixed (propose fixed) ps (.own (.request ⟨2⟩) [] addr ins args t) state
  | _, _ => (none,state)

def jointService (fresh : M.Val handle) (propose : Offer (M.Val handle) (M.Val (scalar b)) → Opener (M.Val handle) (M.Val (scalar b)))
    (ps : Draw) : Service (GSig M) (Session M handle) :=
  fun op state => pure (jointAnswer M handle fresh propose ps op state)

end Zkc.Formal.Written.TableService
