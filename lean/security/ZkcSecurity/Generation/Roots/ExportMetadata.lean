module

@[expose] public section

/-! Generated SHA-256 identities of exact retained export and identity bytes.
Refresh and check with lean/checks/check_subject_roots.py --exports DIRECTORY.
Current participant exports are independently checked against the selected pair. -/
namespace ZkcSecurity.Generation.Roots

def exportDigests : List (String × String × String × String) := [
  ("SmallSumcheck", "sha256:fb282fe4e154be4758a77367ab78fbf1ee2208fc7b228265bfade3b0156c38ea", "sha256:b457486ad69563be86b8c11dd0191a56adf884aef3f01fb004960818ab5244fd", "sha256:c1121c9102bb3df5de2d450379f397b723ba038f8fce886dac1f6dd9c7599de7"),
  ("TwoSums", "sha256:b7c445ced5507c57ef64313edb9e3a4e9871246ae79cd06e70f6fbf45cba856d", "sha256:3e4b4f4d763644eda2f73ffc28d8a5de618ed92c34da200600361fb0a6771f08", "sha256:f181cadf666f9ba9782eff86556cbec714ce7d89e91088ab6912af0a38d8cbc5")]

end ZkcSecurity.Generation.Roots
