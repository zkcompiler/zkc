module

public import ZkcArkLib.Fri.ObservedFold

@[expose] public section

/-! The scalar-segment entry history determines all preceding clear layers:
one full word, one draw and its delivered field value per round, followed by
the terminal coefficients. The earlier public history stays opaque. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.ObservedLayers
open Zkc.Source Zkc.Source.Structured Zkc.Construction ObservedFold
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcExamples.Structured.FriSource (extension)

structure Round where
  word : Origin
  draw : Origin
  delivery : Origin

structure Sites where
  round : Nat → Round
  terminal : Origin

def observations (sites : Sites) (ordinal : Nat) : {n r : Nat} → Layers Octic n r → History
  | _, _, .final coeffs => [.message sites.terminal (.vector extension coeffs)]
  | _, _, .fold word beta tail =>
      let site := sites.round ordinal
      .message site.word (.vector extension (List.ofFn word)) :: .challenge site.draw ::
        .message site.delivery (.field extension beta) :: observations sites (ordinal + 1) tail

theorem length_observations (sites : Sites) (ordinal : Nat) {n r : Nat} (layers : Layers Octic n r) :
    (observations sites ordinal layers).length = 3 * r + 1 := by
  induction layers generalizing ordinal with
  | final => simp [observations]
  | fold _ _ _ ih => simp only [observations, List.length_cons, ih]; omega

def decode (sites : Sites) : (n r ordinal : Nat) → History → Option (Layers Octic n r)
  | _, 0, _, [.message origin payload] => do
      guard (origin = sites.terminal)
      return .final (← payload.value (.vector extension))
  | n + 1, r + 1, ordinal, .message publication word :: .challenge draw ::
      .message delivery answer :: rest => do
      let site := sites.round ordinal
      guard (publication = site.word ∧ draw = site.draw ∧ delivery = site.delivery)
      let cells ← word.value (.vector extension)
      let fixed ← sizedWord (2 ^ (n + 1)) cells
      let beta ← answer.value (.field extension)
      return .fold fixed beta (← decode sites n r (ordinal + 1) rest)
  | _, _, _, _ => none

theorem decode_observations (sites : Sites) (ordinal : Nat) {n r : Nat}
    (layers : Layers Octic n r) :
    decode sites n r ordinal (observations sites ordinal layers) = some layers := by
  induction layers generalizing ordinal with
  | final coefficients => simp [observations, decode, Domain.Payload.value]; rfl
  | fold word beta tail ih =>
    simp [observations, decode, Domain.Payload.value, ih]
    erw [sizedWord_ofFn word]
    rfl

/-- Parse exactly the pre-query suffix, leaving any earlier history and its
nominal data untouched. A forged suffix with valid shape also fixes just one
set of mathematical layers, independently of the answer table. -/
def atRoot (sites : Sites) (n r : Nat) (history : History) : Option (Layers Octic n r) :=
  decode sites n r 0 (history.drop (history.length - (3 * r + 1)))

theorem atRoot_observations (sites : Sites) {n r : Nat} (prior : History) (layers : Layers Octic n r) :
    atRoot sites n r (prior ++ observations sites 0 layers) = some layers := by
  simp [atRoot, length_observations, decode_observations]

end ZkcSecurity.ArkLib.Fri.ObservedLayers
