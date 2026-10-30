module

@[expose] public section

/-! Generated SHA-256 identities of exact retained export and identity bytes.
Refresh and check with lean/checks/check_subject_roots.py --exports DIRECTORY.
Current participant exports are independently checked against the selected pair. -/
namespace ZkcSecurity.Generation.Roots

def exportDigests : List (String × String × String × String) := [
  ("SmallSumcheck", "sha256:6902d499b5e9984f122dea039a651f2ea32a05e8edbb49f45c28900b27001a20", "sha256:966355c25a8cd7ec3a89fcc0ec7f2b5131d1bf5681bf557f674553b66a022cfb", "sha256:d846cde8e5acaa8352f2370f00ac2443a5709e43238b8fef9c49d4442c5934c4"),
  ("TwoSums", "sha256:7d2908d3289b179b13c3f076a28469bfe48e31f4555c3de227a2cecd0b4850b5", "sha256:e3a01344251e0dec9cd26c2f3ffa5196803446d2dc690e151ec9a5c7cfd1dc6c", "sha256:3dd7c3e1657ea6b89f6a25cc378ae3a11b33a85d13c27cb88a4e31793ec4137f")]

end ZkcSecurity.Generation.Roots
