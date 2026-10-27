module

public import Zkc.Executable.Framing
public import Zkc.Protocols.Sumcheck.Multilinear.Fold

@[expose] public section

/-! Honest Sumcheck messages depend on a transcript interface and mathematical
table restriction, independently of a compiled artifact or its proof method. -/
set_option autoImplicit false
namespace ZkcExamples.Executable.SumcheckMessages
open Zkc.Construction Zkc.Executable Zkc.Polynomial.Multilinear

structure Transcript where
  scalar : String
  firstMessage : Origin
  secondMessage : Origin
  draw : Origin
  delivery : Origin

namespace Transcript
variable (transcript : Transcript)

def drawn {F G : Type} (history : History F G) (low high : F) : History F G :=
  history ++ [.message transcript.firstMessage (.field transcript.scalar low)] ++
    [.message transcript.secondMessage (.field transcript.scalar high)] ++ [.challenge transcript.draw]

def delivered {F G : Type} (history : History F G) (low high answer : F) : History F G :=
  transcript.drawn history low high ++ [.message transcript.delivery (.field transcript.scalar answer)]
end Transcript

variable {F G : Type} [Field F]

def lowSum (table : List F) : F := (table.take (table.length / 2)).sum

def highSum (table : List F) : F := (table.drop (table.length / 2)).sum

/-- Two half sums per round, followed by restriction at the absorbed challenge. -/
def honestRounds (transcript : Transcript) (oracle : History F G → F) :
    History F G → List F → Nat → List F
  | _, _, 0 => []
  | history, table, count + 1 =>
      lowSum table :: highSum table ::
        honestRounds transcript oracle
          (transcript.delivered history (lowSum table) (highSum table)
            (oracle (transcript.drawn history (lowSum table) (highSum table))))
          (restrictValues table (oracle (transcript.drawn history (lowSum table) (highSum table)))) count

theorem honestRounds_length (transcript : Transcript) (oracle : History F G → F) :
    ∀ (history : History F G) (table : List F) (count : Nat),
      (honestRounds transcript oracle history table count).length = 2 * count
  | _, _, 0 => rfl
  | history, table, count + 1 => by
      simp only [honestRounds, List.length_cons, honestRounds_length transcript oracle _ _ count]
      omega

omit [Field F] in
/-- The existing length-framed field messages, preceded by magic and binding. -/
def honestBytes (encode : F → List UInt8) (binding : List UInt8) (messages : List F) : List UInt8 :=
  messageBytes encode binding messages

end ZkcExamples.Executable.SumcheckMessages
