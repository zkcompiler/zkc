module

@[expose] public section

/-! Generated SHA-256 identities of exact retained export and identity bytes.
Refresh and check with lean/checks/check_subject_roots.py --exports DIRECTORY.
Current participant exports are independently checked against the selected pair. -/
namespace ZkcSecurity.Generation.Roots

def exportDigests : List (String × String × String × String) := [
  ("SmallSumcheck", "sha256:fb282fe4e154be4758a77367ab78fbf1ee2208fc7b228265bfade3b0156c38ea", "sha256:55df6c32aa4373247b79a57ba0d6619723e9c259e4faae2f9b14f907e5bbb353", "sha256:ca64cb6b215b4df039f48121ab4fc732b77003ab43c072755123dd5f746028c0"),
  ("TwoSums", "sha256:b7c445ced5507c57ef64313edb9e3a4e9871246ae79cd06e70f6fbf45cba856d", "sha256:2746cb64f9b490c75c9050a5e0059c6535325f49b007428c2b0d92fe6f1c18ef", "sha256:8a3ad598b0ef67b7f790a34afde2c4a8d5d7ceb148dc99535fe7b32e4f3c22d9")]

end ZkcSecurity.Generation.Roots
