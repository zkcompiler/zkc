module

@[expose] public section

/-! Generated SHA-256 identities of exact retained export and identity bytes.
Refresh and check with lean/checks/check_subject_roots.py --exports DIRECTORY.
Current participant exports are independently checked against the selected pair. -/
namespace ZkcSecurity.Generation.Roots

def exportDigests : List (String × String × String × String) := [
  ("SmallSumcheck", "sha256:e3ae53d4706b17e7f5a468996a1dbf8cc57a06576986392388b288fffe1a99af", "sha256:e9afef0c1e7775fed0f4d1abdf389d52495e5ae66efdf60a8a0394321461f7fa", "sha256:ea0efdd843435f477577106f7c7bcb9df6b2a19067491b95530c5cc154875bcd"),
  ("TwoSums", "sha256:ff5b4060dd0ad94db9061d59d7560152b8db7dc820b1d25f3b358433a6e78732", "sha256:0bd526cfbc6d29aef756e4b0389d9fb6fe40d3ba76c557aab569266471957942", "sha256:f1110f3e53e1ab652a83adb2c5e4311a42961b4c21b4ed6c9ed6cbda3efe9fe0")]

end ZkcSecurity.Generation.Roots
