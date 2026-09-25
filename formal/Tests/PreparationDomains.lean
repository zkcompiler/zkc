import Zkc.Semantics.Preparation.Emission

set_option autoImplicit false

namespace Tests.PreparationDomains

open PIR Zkc.Modules

/-- Preparation carries word results with different widths, not field casts. -/
def provider (word : BitVec 64) : (BitVec 64 × BitVec 128) × Nat :=
  ((word ^^^ (word <<< 1), word.zeroExtend 128 * word.zeroExtend 128), 9)

def prices : Preparation.Prices (BitVec 64) (BitVec 64 × BitVec 128) :=
  ⟨fun _ _ => 1, fun _ _ => 1⟩

def program (word : BitVec 64) :
    Proc (PIR.Preparation.signature (BitVec 64) (BitVec 64 × BitVec 128)
      (PIR.Preparation.Emission.signature (BitVec 64 × BitVec 128))) (BitVec 64 × BitVec 128) :=
  .call (.prepare word) fun first =>
    .call (.external first) fun _ =>
      .call (.prepare word) fun second => .done second

def run (mode : Preparation.Mode) (word : BitVec 64) :=
  (program word).run (PIR.Preparation.handler provider prices mode PIR.Preparation.Emission.handler)
    (Preparation.empty, ())

theorem preserved (word : BitVec 64) :
    Related (PIR.Preparation.StateRel provider) PIR.Preparation.view PIR.Preparation.view
      (run .direct word) (run .memo word) :=
  PIR.Preparation.contextual_memo provider prices PIR.Preparation.Emission.handler
    (program word) _ _ ⟨ImmutableCache.empty_valid provider, ImmutableCache.empty_valid provider, rfl⟩

theorem actual_word_result :
    (run .memo 3).outcome = .returned (5, 9) ∧
    observeEvents PIR.Preparation.view (run .memo 3).events = [(5, 9)] := by decide

theorem width_and_operator_matter :
    (3 : BitVec 64) ^^^ 6 ≠ 3 + 6 ∧
    (BitVec.ofNat 64 (2 ^ 63) <<< 1) = 0 ∧
    (provider (BitVec.ofNat 64 (2 ^ 63))).1.2 = BitVec.ofNat 128 (2 ^ 126) := by decide

end Tests.PreparationDomains
