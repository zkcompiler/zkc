import Zkc.Source.Constructed.Format

open Zkc.Source Zkc.Source.Constructed

private def sample : Snapshot where
  source := "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  candidate := "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
  entry := "entry"
  role := "validator"
  participant := "actual"
  policy := "selected"
  handlers := []
  inputs := ["i1"]
  outputs := ["i1"]
  instructions := [.guard 0 "source guard"]
  returned := [0]

example : sample.check.isOk = true := by decide +kernel
example : ({sample with returned := [1]}).check.isOk = false := by decide +kernel
example : ({sample with inputs := ["field"]}).check.isOk = false := by decide +kernel
example : ({sample with instructions := [.project ["i1"] 1 0]}).check.isOk = false := by decide +kernel
example : ({sample with instructions := [.stop .abort "authored"], returned := []}).check.isOk = true := by decide +kernel
example : ({sample with instructions := [.stop .abort "authored", .guard 0 "unreachable"], returned := []}).check.isOk = false := by decide +kernel

private def empty : PIR.Signature where
  Op := Empty
  Reply := Empty.elim

private abbrev tokens : Meaning empty where
  Value := fun _ => Nat
  condition := fun n => n != 0
  primitive := fun _ _ => .halt .refused

private def admitted : Imported sample := sample.imported (by decide +kernel)

example : admitted.denote tokens (.cons (.cons 0 .nil) .nil) = .halt .reject := by
  rfl
example : admitted.denote tokens (.cons (.cons 1 .nil) .nil) = .done (.cons 1 .nil) := by
  rfl

#print axioms Zkc.Source.Constructed.Snapshot.check_exact
#print axioms Zkc.Source.Constructed.Snapshot.check_elaborate
#print axioms Zkc.Source.Constructed.Snapshot.check_denotation_unique
#print axioms Zkc.Source.Constructed.Snapshot.imported_checked
#print axioms Zkc.Source.Constructed.Imported.reelaborate
#print axioms Zkc.Source.Constructed.project_reply
#print axioms Zkc.Source.Constructed.pack_reply
