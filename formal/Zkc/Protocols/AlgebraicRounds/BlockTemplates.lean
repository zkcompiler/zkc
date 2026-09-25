import Zkc.Protocols.AlgebraicRounds.Early

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates
open Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Protocols.AlgebraicRounds.BlockEvaluation Zkc.Protocols.AlgebraicRounds.Early Zkc.Compiler.Blocks
-- Generated from the actual Zkc.Compiler.Blocks request. This is a literal-free body schema;
-- its algebraic interpretation is supplied by the consumer's CommRing instance.
def source {F : Type} : Block F := [
  (4, (.apply "field.mul" (.input 1) (.input 3))),
  (5, (.apply "field.mul" (.input 3) (.input 3))),
  (6, (.apply "field.mul" (.input 2) (.input 5))),
  (7, (.apply "field.add" (.input 4) (.input 6))),
  (8, (.apply "field.add" (.input 0) (.input 7)))]

def target {F : Type} : Block F := [
  (4, (.apply "field.mul" (.input 2) (.input 3))),
  (5, (.apply "field.add" (.input 1) (.input 4))),
  (6, (.apply "field.mul" (.input 5) (.input 3))),
  (7, (.apply "field.add" (.input 0) (.input 6)))]

def hostile {F : Type} [One F] : Block F := [
  (4, (.apply "field.mul" (.input 2) (.input 3))),
  (5, (.apply "field.add" (.input 1) (.input 4))),
  (6, (.apply "field.mul" (.input 5) (.input 3))),
  (7, (.apply "field.add" (.literal 1) (.input 6)))]

theorem admitted {F : Type} [DecidableEq F] :
    Zkc.Compiler.Blocks.hornerCheck (source : Block F) target 8 7 = true := by rfl

theorem hostile_refused :
    Zkc.Compiler.Blocks.hornerCheck (source : Block Int) hostile 8 7 = false := by decide

theorem family_stopping {F S Q : Type} [CommRing F] [DecidableEq F]
    (send : S → Message F × S) (react : S → F → S) (draw : Q → F × Q)
    (k : Nat) (claim : F) (ps : S) (qs : Q) :
    early (moduleValue target 7) send react draw k claim ps qs =
    early value send react draw k claim ps qs :=
  checked_early source target 8 7 admitted send react draw k claim ps qs


end Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates
