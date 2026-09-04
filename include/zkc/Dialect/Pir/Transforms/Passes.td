//===- Passes.td - Protocol IR passes -----------------------*- tablegen
//-*-===//
#ifndef ZKC_DIALECT_PIR_TRANSFORMS_PASSES_TD
#define ZKC_DIALECT_PIR_TRANSFORMS_PASSES_TD

include "mlir/Pass/PassBase.td"

def PirSeal : Pass<"pir-seal", "mlir::ModuleOp"> {
  let summary = "seal open protocols into content-addressed artifacts";
  let description = [{
    The seal boundary (docs/spec/kernel.md §7, boundaries.md §1): the
    fail-closed conjunction WF ∧ LIN ∧ BIND ∧ COV_obl ∧
    ReductionClosureOK ∧ TerminalClosureOK
    over each
    `pir.protocol`, producing an immutable `pir.sealed` whose id is the
    SHA-256 of the canonical encoding. The container verifier already
    owns the structural halves (layout, thread continuity, claim
    single-use); this pass owns the semantic halves:

      producer boundary — input contains at least one open `pir.protocol`
        and no authored `pir.sealed`; only this pass may mint sealed
        containers (zkc-E202);
      BIND — every challenge dependency is absorbed (zkc-E211); no
        unabsorbed slot precedes a challenge — the generalized
        Frozen-Heart condition (zkc-E212); every reduce round's
        generated requirements precede their challenge absorbed
        (kernel §5.2 requirement generation, zkc-E213); every
        statement binding precedes the first challenge (kernel §5.3,
        zkc-E214);
      LIN policy — terminal sinks are permitted by the SealPolicy
        (zkc-E201); unknown policies fail closed (zkc-E224);
      WF profile — every payload class has a codec in kappa.codecs
        (zkc-E221), the kappa axis set is closed (zkc-E225), and the
        encoding domain holds (zkc-E228);
      COV_obl (obligation derivability) — check contracts resolve in the
        protocol vocabulary with their declared mode (zkc-E222, zkc-E226);
      reductions — schemas resolve (zkc-E320),
        claim profiles and arity match the exact ReductionContract
        (zkc-E320), dep slots bind positionally
        with the right classes (zkc-E243), message roles bind with
        declared multiplicity (zkc-E244), and challenges are not
        silently shared between reduces (zkc-E245);
      and the later-grown judgments: segment decompositions
        (zkc-E215), challenge-domain distinctness (zkc-E216), anchor
        derived-output equality and sink completeness
        (zkc-E326/zkc-E247), and the construction-profile content pin
        (zkc-E229); and
      TerminalClosureOK — every claim profile, contract, terminal rule,
        role-selected check, semantic attachment, and material binding is
        reconstructed against the cross-admitted protocol vocabulary.
        The battery source is authoritative for the full inventory.

    The battery accumulates: every violation in a protocol is reported,
    then the pass fails; a failed seal produces no artifact.
  }];
  let options =
      [Option<"protocolVocabulary", "protocol-vocabulary", "std::string",
              /*default=*/[{""}],
              "Path to the cross-admitted protocol vocabulary (claim profiles, "
              "check contracts, reduction schemas, and terminal rules)">,
       Option<"constructionProfileRegistry", "construction-profile-registry",
              "std::string", /*default=*/[{""}],
              "Path to the construction-profile registry (required whenever "
              "kappa consumes a sponge or codec)">,
  ];
}

def PirRecheck : Pass<"pir-recheck", "mlir::ModuleOp"> {
  let summary = "re-run the seal battery over loaded sealed artifacts";
  let description = [{
    The consumer contract's second leg (docs/spec/boundaries.md §0):
    consumers recompute identity on load — the fail-closed loader's
    job — and re-run the judgment battery, which is this pass. It
    runs the full seal battery over each `pir.sealed` body without
    re-sealing, and requires the artifact's one exact five-section resolved
    vocabulary table to match the loaded protocol and
    construction-profile authorities. TerminalClosureOK is reconstructed as
    part of the same battery. Verdict-only: the artifact is never mutated;
    failure produces diagnostics.
  }];
  let options =
      [Option<"protocolVocabulary", "protocol-vocabulary", "std::string",
              /*default=*/[{""}],
              "Path to the cross-admitted protocol vocabulary">,
       Option<"constructionProfileRegistry", "construction-profile-registry",
              "std::string", /*default=*/[{""}],
              "Path to the construction-profile registry">,
  ];
}

def PirBatchOpen : Pass<"pir-batch-open", "mlir::ModuleOp"> {
  let summary = "batch same-point opening claims through the kzg_batch "
                "reduction";
  let description = [{
    The reduce-producing transform (docs/spec/compiler.md,
    `same_point_kzg_batch`):
    `single_opening` claims that share one evaluation point and are each
    closed by the admitted KZG single-opening rule become one kzg_batch
    reduction instance - a batch challenge sampled after every
    commitment and claimed evaluation, one batched proof slot, one
    KZG batch-opening check, and one `batch_opening` claim whose `members`
    anchor is the claim-vector digest of the sorted complete input descriptors.

    Deterministic and conservative: groups are keyed by point anchor
    and processed in sorted order; a group whose shape the transform
    cannot decompose (checks not in the (commitment, point, value,
    proof) input convention, mixed proof classes/suites, distinct point
    values, or duplicate full descriptors) is DECLINED or refused before any
    rewrite. Labels and the challenge domain are content-derived from the
    descriptor vector. The pass is a convenience wrapper over the reusable
    exact-application core: transform providers may discover and recognize one
    canonical group, realize only that group, and check it by deterministic
    replay against the actual predecessor. The optional discardable
    `pir.pass_manifest` remains non-authoritative provenance, outside identity
    and outside the replay judgment.
  }];
  let options = [Option<
                     "batchSpace", "batch-space", "std::string",
                     /*default=*/[{""}],
                     "Exact cardinality of the batch-challenge sample space "
                     "(minimal decimal; required - the transform does not read "
                     "registries)">,
  ];
}

def PirLink : Pass<"pir-link", "mlir::ModuleOp"> {
  let summary = "compose two judged open protocols and their local routes";
  let description = [{
    Static linking for the currently represented fresh/local-challenge
    carrier. Both OPEN inputs are judged under one protocol environment. The
    producer spine precedes the consumer spine; face prefixes namespace labels,
    challenge domains, construction instances, witnesses, and every local
    route reference. Constants and stable semantic-material references retain
    their authored meaning. Producer exports fuse only with a unique consumer
    source carrying the same claim descriptor. Kappa merges axis-wise, witness
    ABI order is producer then consumer, and the consumer policy governs the
    resulting OPEN protocol. The complete composite is judged before it is
    returned; failure leaves both inputs intact and no partial output.

    Imported-challenge origins, external requirement references, and an
    explicit seam-obligation carrier are not represented yet, so general
    protocol composition remains outside this boundary.
  }];
  let options =
      [Option<"producer", "producer", "std::string", /*default=*/[{""}],
              "protocol_name of the producer operand">,
       Option<"consumer", "consumer", "std::string", /*default=*/[{""}],
              "protocol_name of the consumer operand">,
       Option<"producerPrefix", "producer-prefix", "std::string",
              /*default=*/[{"left"}], "Face prefix for producer names">,
       Option<"consumerPrefix", "consumer-prefix", "std::string",
              /*default=*/[{"right"}], "Face prefix for consumer names">,
       Option<"protocolVocabulary", "protocol-vocabulary", "std::string",
              /*default=*/[{""}],
              "Path to the cross-admitted protocol vocabulary">,
       Option<"constructionProfileRegistry", "construction-profile-registry",
              "std::string", /*default=*/[{""}],
              "Path to the construction-profile registry">,
  ];
}

def PirProject : Pass<"pir-project", "mlir::ModuleOp"> {
  let summary = "development adapter for projecting raw sealed PIR";
  let description = [{
    A textual-development adapter over the production artifact projection
    boundary. Each raw `pir.sealed` input is independently snapshotted and
    admitted against one loaded ProtocolEnvironment before projection. Persisted
    artifacts use `zkc-project`, which accepts artifact input and carries admission
    as an opaque capability.

    Every admitted protocol becomes one `oir.artifact` — the Fiat-Shamir
    handler image of the sealed spine, with provenance embedded per op (`src` =
    canonical event positions). Realization coverage (COV_realized, kernel.md
    §6.2) is proved where both artifacts are in hand:
    the emitted program's coverage must equal the projection obligation
    set — every obligation realized by ops of its licensed families,
    no phantom `src` positions — refusing otherwise (zkc-E237).
    Fail-closed per axis: unknown endpoint kind (zkc-E231); missing
    sponge or iv profile axis (zkc-E232). Challenge class, count, domain,
    sampling rule, and space are carried from the admitted capability.

    The prover endpoint (docs/spec/endpoints.md §6.2) additionally consumes
    admitted hole-contract signatures from the same environment.
  }];
  let options =
      [Option<"endpointKind", "endpoint-kind", "std::string",
              /*default=*/[{"verifier"}], "Endpoint kind to project">,
       Option<"protocolVocabulary", "protocol-vocabulary", "std::string",
              /*default=*/[{""}],
              "Protocol-vocabulary registry used to admit every raw sealed "
              "input before projection">,
       Option<"constructionProfileRegistry", "construction-profile-registry",
              "std::string", /*default=*/[{""}],
              "Construction-profile registry used in the same admission "
              "environment">,
       Option<"protocolName", "protocol", "std::string", /*default=*/[{""}],
              "Project only the sealed protocol with this name; empty projects "
              "every sealed protocol in the module. Composition leaves the "
              "operands alongside their composite, and an operand that only "
              "exports a claim has no verifier face of its own, so projecting "
              "a composite requires naming it">,
  ];
  let dependentDialects = ["zkc::oir::OirDialect"];
}

#endif // ZKC_DIALECT_PIR_TRANSFORMS_PASSES_TD
