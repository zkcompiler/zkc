module

public import Zkc.IR.Source.Structured.Participant

@[expose] public section

/-! Deterministic replies for one role-local run.

A script answers each receive by its type and site and each field draw by
its site; sends are acknowledged. The sender of a receive and the field domain
and operands of a draw are not inspected, but every request is recorded
verbatim, in order. A request outside the script is a mismatch, as for the
structured observer's scripted replies, and stops `refused`. Index and index-block
service operations are outside this field-reply script and also stop `refused`. A script is an
experiment choice, not a provider law or a scheduler: it fixes the replies of
one run, for example the messages and challenges of one public-coin transcript,
so that the participant's actual returned outputs can be observed. Sites
distinguish messages of the same type; a script gives one reply per type and
site. -/

set_option autoImplicit false

namespace Zkc.Source.Structured

structure ReplyScript (F G : Type) where
  receive : (ty : Ty) → String → Option (assignment F G ty)
  draw : String → Option F

namespace ReplyScript
variable {F G : Type}

def handler (script : ReplyScript F G) :
    PIR.Handler (participantInterface F G) Unit (participantInterface F G).Op
  | action@(.send ..), state => ⟨.returned (), state, [action]⟩
  | action@(.receive ty site _), state =>
      match script.receive ty site with
      | some value => ⟨.returned value, state, [action]⟩
      | none => ⟨.stopped .refused, state, [action]⟩
  | action@(.query site (.draw _) _), state =>
      match script.draw site with
      | some value => ⟨.returned value, state, [action]⟩
      | none => ⟨.stopped .refused, state, [action]⟩
  | action@(.query _ (.sampleIndex _) _), state
  | action@(.query _ (.sampleIndices _) _), state =>
      ⟨.stopped .refused, state, [action]⟩

/-- One run of a role-local process against the script. -/
def run (script : ReplyScript F G) {A : Type} (process : PIR.Process (participantInterface F G) A) :
    PIR.Execution Unit (participantInterface F G).Op A :=
  process.run script.handler ()

end ReplyScript

end Zkc.Source.Structured
