import Zkc.Source.Mathematical.ManifestAdmission
import Tests.Checks

set_option autoImplicit false
namespace Tests.MathematicalManifest
open Zkc.Source.Mathematical ManifestAdmission

-- SHA-256 of the exact ASCII descriptors below. These are finite test
-- installations; their functions are supplied here, independently of hashes.
-- test.counter/v1:Nat->Nat:n+1
-- test.twice/v1:Nat->Nat:2*n:requires=test.counter/v1
def counterIdentity : Raw.Identity := ⟨"test.counter", "1",
  "fae7f9ead5ef50d415b9c75bcb6d1363892d72827e9495e7b01472d9eff510e0"⟩
def twiceIdentity : Raw.Identity := ⟨"test.twice", "1",
  "a8313de64d3733913f89a3ae068eb53df4fb9d836800beaf54fe86cc62ba5f3d"⟩

def installation : Installation (fun _ => Nat → Nat)
  | .service => ⟨[⟨counterIdentity, (· + 1), []⟩], by simp⟩
  | .operation => ⟨[⟨twiceIdentity, (2 * ·), [⟨.service, counterIdentity⟩]⟩], by simp⟩
  | .domain | .wire | .law => ⟨[], by simp⟩

def subject : Raw.Manifest := ⟨[], [twiceIdentity], [], [counterIdentity], []⟩

def admitted (source : Raw.Manifest) (budget : Nat := 1000000) :=
  (admit installation source).run' budget

-- The selected value has the actual interpretation from the installation.
-- This is a kernel-checked certificate projection, independent of test runs.
example {source : Raw.Manifest} (result : Admitted installation source)
    (index : Fin source.operations.length) :
    ((result.selected .operation).get index).package ∈ (installation .operation).packages :=
  ((result.selected .operation).get index).registered

example {source : Raw.Manifest} (result : Admitted installation source)
    (index : Fin source.operations.length) :
    ((result.selected .operation).get index).package.identity = source.operations[index] :=
  ((result.selected .operation).get index).exactIdentity

def refuses (source : Raw.Manifest) (reason : Error) (budget : Nat := 1000000) : Bool :=
  match admitted source budget with
  | .error error => error == reason
  | .ok _ => false

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (match admitted subject with
    | .ok result =>
        let selected := (result.selected .operation).get ⟨0, by decide⟩
        selected.package.interpretation 5 == 10
    | .error _ => false) "selected installed function"
  checks.holds (refuses { subject with services := [] } .prerequisite) "missing prerequisite"
  checks.holds (refuses { subject with services := [{ counterIdentity with version := "2" }] } .prerequisite)
    "prerequisite requires exact version"
  checks.holds (refuses { subject with operations := [{ twiceIdentity with digest := counterIdentity.digest }] } .package)
    "same name and version with substituted digest"
  checks.holds (refuses { subject with operations := [{ twiceIdentity with digest := "ABC" }] } .digest)
    "invalid digest spelling"
  checks.holds (refuses { subject with operations := [twiceIdentity, twiceIdentity] } .duplicate)
    "duplicate name and version"
  checks.holds (refuses { subject with operations := [twiceIdentity, { twiceIdentity with digest := counterIdentity.digest }] }
    .duplicate) "changed digest does not make a distinct package key"
  checks.holds (refuses { subject with domains := [twiceIdentity] } .package) "wrong package category"
  checks.holds (refuses { subject with wires := [⟨"uninstalled", "1", counterIdentity.digest⟩] } .package)
    "unused manifest package still checked"
  checks.holds (refuses subject .resource 0) "shared allowance"
  checks.finish "mathematical manifest admission"

#eval run
end Tests.MathematicalManifest
