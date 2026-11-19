module

public import Zkc.Core.Scheme.Deployed
public import Zkc.Core.Facts.Contracts.RoleOperations

@[expose] public section

namespace Zkc.Frontend.Constructed
open Core

/-- Site keys in the selected entry. This profile handles one straight-line draw. -/
structure Sites where
  entry : Key
  commitment : Key
  challenge : Key
  response : Key
  /-- First key outside the entry's instruction addresses. -/
  fresh : Nat
  deriving DecidableEq, Repr

/-- The transcript is an ordered sequence of (operation, label bytes, data bytes).
The operation distinguishes an append from a squeeze even at the same label. -/
abbrev bytes {V : Vocabulary} : V.Ty := .seq (.fin 256) none
abbrev transcript {V : Vocabulary} : V.Ty :=
  .seq (.tuple (.cons .nat (.cons bytes (.cons bytes .nil)))) none
abbrev pair {V : Vocabulary} (a b : V.Ty) : V.Ty := .tuple (.cons a (.cons b .nil))

inductive MemberOp where | absorbPoint | squeeze | absorbScalar
  deriving DecidableEq, Repr

def MemberOp.key : MemberOp → Key
  | .absorbPoint => ⟨0⟩
  | .squeeze => ⟨1⟩
  | .absorbScalar => ⟨2⟩

def Sites.request (s : Sites) (member : MemberOp) : Key := ⟨s.fresh + member.key.number⟩

section
variable {V : Vocabulary} {hs : Headers V} {r : Role}

abbrev mine (r : Role) (t : V.Ty) : LTy V := ⟨t,[r]⟩

def pack (a b : V.Ty) : RoleOp V hs r [mine r a, mine r b] [mine r (pair a b)] :=
  .compute [r] (.owned (.makeTuple (.cons a (.cons b .nil)))) _ rfl (by simp)
    (by intro x h; simp [mine] at h; rcases h with rfl | rfl <;> simp)

def unpack (a b : V.Ty) : RoleOp V hs r [mine r (pair a b)] [mine r a, mine r b] :=
  .compute [r] (.owned (.takeTuple (.cons a (.cons b .nil)))) _ rfl (by simp)
    (by intro x h; simp at h; subst x; simp)

def request (member : MemberOp) (a b : V.Ty) : RoleOp V hs r [mine r a] [mine r b] :=
  .own (.request member.key) [] _ b rfl (by intro x h; simp at h; subst x; simp)

/-- Forward the actual receive at its original occurrence, pair the current transcript
with the received value, and keep the transcript returned by the suite. -/
def receiveClause (s : Sites) (p : Role) (site : Key) (t : V.Ty) (member : MemberOp) :
    Clause V hs r transcript where
  site := ⟨⟨[],site⟩,.get .message p,[],[t]⟩
  code :=
    .op site (.get t [] .message p [r] (by simp)) .nil (.cons 1 .nil) <|
    .op ⟨s.fresh + 3⟩ (pack transcript t) (.cons ⟨0,rfl⟩ (.cons ⟨1,rfl⟩ .nil)) (.cons 2 .nil) <|
    .op (s.request member) (request member (pair transcript t) transcript)
      (.cons ⟨2,rfl⟩ .nil) (.cons 3 .nil) <|
    .ret (.cons ⟨1,rfl⟩ (.cons ⟨3,rfl⟩ .nil))

def challengeClause (s : Sites) (p : Role) (law : V.LawKey) (t : V.Ty) :
    Clause V hs r transcript where
  site := ⟨⟨[],s.challenge⟩,.own (.coin law) [p],[],[t]⟩
  code :=
    .op (s.request .squeeze) (request .squeeze transcript (pair t transcript))
      (.cons ⟨0,rfl⟩ .nil) (.cons 1 .nil) <|
    .op ⟨s.fresh + 3⟩ (unpack t transcript) (.cons ⟨1,rfl⟩ .nil) (.cons 2 (.cons 3 .nil)) <|
    .ret (.cons ⟨2,rfl⟩ (.cons ⟨3,rfl⟩ .nil))

/-- The verifier entry prepares the first transcript from its own inputs. Returning the
last transcript makes even the post-challenge absorption observable. -/
def verifierLayer (s : Sites) (p r : Role) (point scalar : V.Ty) (law : V.LawKey)
    (ins : List (LTy V)) : Layer V hs r ins where
  line := .construction
  state := transcript
  takes := [transcript]
  gives := [transcript]
  clauses := [receiveClause s p s.commitment point .absorbPoint,
    challengeClause s p law scalar, receiveClause s p s.response scalar .absorbScalar]
  start := .ret (.cons ⟨0, by rw [Ctx.find?_positional]; rfl⟩ .nil)
  again := .ret (.cons ⟨1,rfl⟩ .nil)
  finish := .ret (.cons ⟨0,rfl⟩ .nil)

end
end Zkc.Frontend.Constructed
