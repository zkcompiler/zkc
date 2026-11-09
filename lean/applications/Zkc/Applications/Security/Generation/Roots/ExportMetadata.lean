module

@[expose] public section

/-! Generated SHA-256 identities of exact retained export and identity bytes.
Refresh and check with lean/checks/check_subject_roots.py --exports DIRECTORY.
Current participant exports are independently checked against the selected pair. -/
namespace ZkcSecurity.Generation.Roots

def exportDigests : List (String × String × String × String) := [
  ("SmallSumcheck", "sha256:76491dbfe0d0d4ce888fe45e0b7bfe329ae6446201a1bca31ad864304035c97f", "sha256:694479c30ff4872aab5f26f7ca9c6bb483a49e2acbee415f27dfc47330bf29c9", "sha256:2443672f4de15c8fbc2cde0400ef343ff08637c40b14fded6d6d716ee8cad54b"),
  ("TwoSums", "sha256:2a0351c54dc5de3d1b3cebb46e0172df3fff348683601797ad7fe58e349a2a96", "sha256:2bcc01b85b6ea57e3b71fb6c4f4fa3b7797ee4d1b1d0e09bfd1cda8fea18883e", "sha256:106ab6342905e53d8ecd73b1c1c87a5cd176a2019840a04ae705c7595c53bbf6")]

end ZkcSecurity.Generation.Roots
