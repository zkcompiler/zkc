// A hand-crafted artifact whose first program op is a read: the
// container verifier requires exactly one init and a final decide,
// but not init-first, so this shape is loadable and only the
// interpreter's verdict discipline keeps a statement-binding failure
// from being overwritten by a later reject.
oir.artifact "masked" id "37471e34aaf74018637d2b5513a2bf6deeb0fda0d50246137bf0828f1e168f7d" source "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" endpoint "verifier" {
  oir.program attributes {codecs = {tg = "tg_be8"}, statement_labels = ["y"]} {
  ^bb0(%arg0: !oir.val<"tg", "public">, %arg1: !oir.stream):
    %out, %val = oir.read %arg1 "m" : "tg" src [0]
    %0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %1 = oir.absorb %0, %val : <"tg", "wire"> src [0]
    oir.expect_end %out
    oir.decide %1
  }
}
