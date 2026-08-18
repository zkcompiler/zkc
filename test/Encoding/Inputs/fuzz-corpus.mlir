pir.protocol "fuzz0" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:172d217055a3f397e475bdc2d8424cab5c9fcb048d26d1c0f4c3640b31b3eac2"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %public_0 = pir.bind %t0 "public_0" : "scalar" stage instance
  %t2, %public_1 = pir.bind %t1 "public_1" : "scalar" stage instance
  %t3, %statement = pir.bind %t2 "statement" : "tg" stage instance
  %t4, %message_0 = pir.slot %t3 "message_0" : "scalar"
  %t5, %message_1 = pir.slot %t4 "message_1" : "scalar"
  %t6, %commitment = pir.slot %t5 "commitment" : "tg" in "sig" as "a"
  %t7, %challenge = pir.chal %t6 deps(%public_0, %statement, %message_0, %message_1, %commitment : !pir.val<"scalar">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.0.challenge" space "2147483648"
  %t8, %response = pir.slot %t7 "response" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t8
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:172d217055a3f397e475bdc2d8424cab5c9fcb048d26d1c0f4c3640b31b3eac2"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:172d217055a3f397e475bdc2d8424cab5c9fcb048d26d1c0f4c3640b31b3eac2" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz1" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:3c8463502706627e4e1cc341f2742d1346ad680e719c01cc7b3db408f7141595"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %statement = pir.bind %t0 "statement" : "tg" stage instance
  %t2, %message_0 = pir.slot %t1 "message_0" : "tg"
  %t3, %message_1 = pir.slot %t2 "message_1" : "scalar"
  %t4, %commitment = pir.slot %t3 "commitment" : "tg" in "sig" as "a"
  %t5, %challenge = pir.chal %t4 deps(%statement, %message_0, %message_1, %commitment : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.1.challenge" space "1024"
  %t6, %response = pir.slot %t5 "response" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t6
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:3c8463502706627e4e1cc341f2742d1346ad680e719c01cc7b3db408f7141595"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:3c8463502706627e4e1cc341f2742d1346ad680e719c01cc7b3db408f7141595" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz2" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:4c9828b0da14e1ec05dab1aec85660ed2320b7febc29cd3c1883dcdd997b0524"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %public_0 = pir.bind %t0 "public_0" : "tg" stage instance
  %t2, %public_1 = pir.bind %t1 "public_1" : "tg" stage instance
  %t3, %statement = pir.bind %t2 "statement" : "tg" stage instance
  %t4, %message_0 = pir.slot %t3 "message_0" : "tg"
  %t5, %commitment = pir.slot %t4 "commitment" : "tg" in "sig" as "a"
  %t6, %challenge = pir.chal %t5 deps(%public_1, %statement, %commitment : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.2.challenge" space "2305843009213693952"
  %t7, %response = pir.slot %t6 "response" : "scalar"
  %t8, %trailer = pir.slot %t7 "trailer" : "tg" unabsorbed
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t8
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:4c9828b0da14e1ec05dab1aec85660ed2320b7febc29cd3c1883dcdd997b0524"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:4c9828b0da14e1ec05dab1aec85660ed2320b7febc29cd3c1883dcdd997b0524" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz3" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:074f7031d531e3518a5627e5117af149f7af68b981d355e9c50858c7ef18aabc"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %public_0 = pir.bind %t0 "public_0" : "scalar" stage instance
  %t2, %statement = pir.bind %t1 "statement" : "tg" stage instance
  %t3, %commitment = pir.slot %t2 "commitment" : "tg" in "sig" as "a"
  %t4, %challenge = pir.chal %t3 deps(%public_0, %statement, %commitment : !pir.val<"scalar">, !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.3.challenge" space "2305843009213693952"
  %t5, %response = pir.slot %t4 "response" : "scalar"
  %t6, %trailer = pir.slot %t5 "trailer" : "tg" unabsorbed
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t6
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:074f7031d531e3518a5627e5117af149f7af68b981d355e9c50858c7ef18aabc"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:074f7031d531e3518a5627e5117af149f7af68b981d355e9c50858c7ef18aabc" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz4" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:5ee9982aa374c7480a316c13f3a3fd3dcfb23eb53d6e85419c1724c5e8aa77c0"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %public_0 = pir.bind %t0 "public_0" : "tg" stage instance
  %t2, %public_1 = pir.bind %t1 "public_1" : "scalar" stage instance
  %t3, %statement = pir.bind %t2 "statement" : "tg" stage instance
  %t4, %message_0 = pir.slot %t3 "message_0" : "scalar"
  %t5, %message_1 = pir.slot %t4 "message_1" : "scalar"
  %t6, %commitment = pir.slot %t5 "commitment" : "tg" in "sig" as "a"
  %t7, %challenge = pir.chal %t6 deps(%public_1, %statement, %commitment : !pir.val<"scalar">, !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.4.challenge" space "2147483648"
  %t8, %response = pir.slot %t7 "response" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t8
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:5ee9982aa374c7480a316c13f3a3fd3dcfb23eb53d6e85419c1724c5e8aa77c0"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:5ee9982aa374c7480a316c13f3a3fd3dcfb23eb53d6e85419c1724c5e8aa77c0" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz5" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a7219244e42e2db1535ffe098f01e330a2a528160e2a1f3c98a36927544e760d"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %public_0 = pir.bind %t0 "public_0" : "tg" stage instance
  %t2, %statement = pir.bind %t1 "statement" : "tg" stage instance
  %t3, %message_0 = pir.slot %t2 "message_0" : "tg"
  %t4, %commitment = pir.slot %t3 "commitment" : "tg" in "sig" as "a"
  %t5, %challenge = pir.chal %t4 deps(%statement, %message_0, %commitment : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.5.challenge" space "2305843009213693952"
  %t6, %response = pir.slot %t5 "response" : "scalar"
  %t7, %trailer = pir.slot %t6 "trailer" : "scalar" unabsorbed
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t7
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:a7219244e42e2db1535ffe098f01e330a2a528160e2a1f3c98a36927544e760d"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:a7219244e42e2db1535ffe098f01e330a2a528160e2a1f3c98a36927544e760d" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz6" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:8c69998f2dc282b9865f14641fc5fee9ab8253483b501918f0d7ab5777573e7a"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %public_0 = pir.bind %t0 "public_0" : "scalar" stage instance
  %t2, %statement = pir.bind %t1 "statement" : "tg" stage instance
  %t3, %message_0 = pir.slot %t2 "message_0" : "scalar"
  %t4, %message_1 = pir.slot %t3 "message_1" : "tg"
  %t5, %commitment = pir.slot %t4 "commitment" : "tg" in "sig" as "a"
  %t6, %challenge = pir.chal %t5 deps(%statement, %message_0, %message_1, %commitment : !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.6.challenge" space "2147483648"
  %t7, %response = pir.slot %t6 "response" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t7
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:8c69998f2dc282b9865f14641fc5fee9ab8253483b501918f0d7ab5777573e7a"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:8c69998f2dc282b9865f14641fc5fee9ab8253483b501918f0d7ab5777573e7a" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz7" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:7138ef517cc21353d7771d2e8ffae9ab47a9acef7d1b201b307a1e26016daed0"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %public_0 = pir.bind %t0 "public_0" : "scalar" stage instance
  %t2, %statement = pir.bind %t1 "statement" : "tg" stage instance
  %t3, %message_0 = pir.slot %t2 "message_0" : "tg"
  %t4, %message_1 = pir.slot %t3 "message_1" : "scalar"
  %t5, %commitment = pir.slot %t4 "commitment" : "tg" in "sig" as "a"
  %t6, %challenge = pir.chal %t5 deps(%public_0, %statement, %message_0, %commitment : !pir.val<"scalar">, !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.7.challenge" space "61"
  %t7, %response = pir.slot %t6 "response" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t7
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:7138ef517cc21353d7771d2e8ffae9ab47a9acef7d1b201b307a1e26016daed0"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:7138ef517cc21353d7771d2e8ffae9ab47a9acef7d1b201b307a1e26016daed0" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz8" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:41f512384ddadb5828d2046693dff7488eb4c0826b8ecf8b3ac3106570ff0153"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %statement = pir.bind %t0 "statement" : "tg" stage instance
  %t2, %message_0 = pir.slot %t1 "message_0" : "scalar"
  %t3, %commitment = pir.slot %t2 "commitment" : "tg" in "sig" as "a"
  %t4, %challenge = pir.chal %t3 deps(%statement, %commitment : !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.8.challenge" space "2305843009213693952"
  %t5, %response = pir.slot %t4 "response" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t5
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:41f512384ddadb5828d2046693dff7488eb4c0826b8ecf8b3ac3106570ff0153"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:41f512384ddadb5828d2046693dff7488eb4c0826b8ecf8b3ac3106570ff0153" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz9" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:4a087d726164572a8fde37e26f6ae415848d64451a4b3ce9703b41db01f3cd1a"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %public_0 = pir.bind %t0 "public_0" : "tg" stage instance
  %t2, %public_1 = pir.bind %t1 "public_1" : "scalar" stage instance
  %t3, %statement = pir.bind %t2 "statement" : "tg" stage instance
  %t4, %commitment = pir.slot %t3 "commitment" : "tg" in "sig" as "a"
  %t5, %challenge = pir.chal %t4 deps(%public_0, %statement, %commitment : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.9.challenge" space "2147483648"
  %t6, %response = pir.slot %t5 "response" : "scalar"
  %t7, %trailer = pir.slot %t6 "trailer" : "scalar" unabsorbed
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t7
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:4a087d726164572a8fde37e26f6ae415848d64451a4b3ce9703b41db01f3cd1a"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:4a087d726164572a8fde37e26f6ae415848d64451a4b3ce9703b41db01f3cd1a" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz10" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:73b9a274b79e75f04f89c060b43ce075e250b2d94a9b40ccab5d045b4a8ba10a"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %public_0 = pir.bind %t0 "public_0" : "tg" stage instance
  %t2, %statement = pir.bind %t1 "statement" : "tg" stage instance
  %t3, %commitment = pir.slot %t2 "commitment" : "tg" in "sig" as "a"
  %t4, %challenge = pir.chal %t3 deps(%public_0, %statement, %commitment : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.10.challenge" space "61"
  %t5, %response = pir.slot %t4 "response" : "scalar"
  %t6, %trailer = pir.slot %t5 "trailer" : "scalar" unabsorbed
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t6
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:73b9a274b79e75f04f89c060b43ce075e250b2d94a9b40ccab5d045b4a8ba10a"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:73b9a274b79e75f04f89c060b43ce075e250b2d94a9b40ccab5d045b4a8ba10a" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
pir.protocol "fuzz11" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:e3dc1c6ed9884f2bed13fafe507b42fec40dd50c0eca1b66748b51db43a9e523"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %statement = pir.bind %t0 "statement" : "tg" stage instance
  %t2, %message_0 = pir.slot %t1 "message_0" : "tg"
  %t3, %commitment = pir.slot %t2 "commitment" : "tg" in "sig" as "a"
  %t4, %challenge = pir.chal %t3 deps(%statement, %message_0, %commitment : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fuzz.11.challenge" space "2147483648"
  %t5, %response = pir.slot %t4 "response" : "scalar"
  %t6, %trailer = pir.slot %t5 "trailer" : "tg" unabsorbed
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t6
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:e3dc1c6ed9884f2bed13fafe507b42fec40dd50c0eca1b66748b51db43a9e523"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:e3dc1c6ed9884f2bed13fafe507b42fec40dd50c0eca1b66748b51db43a9e523" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
