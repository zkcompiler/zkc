# Proposed canonical-framed FS-family view bodies

This file is candidate owner text for F0-V3B. It is executable migration input, not an edit to the owner page.

## Exact insertion points

- Semantic fragment: `docs-next/pir/fiat-shamir.md`, Section 13, immediately before <!-- zkc-profile-source:canonical-framed-fs-semantics:end -->.
- Body compiler: `docs-next/pir/fiat-shamir.md`, Appendix A, immediately before <!-- zkc-profile-source:canonical-framed-fs-body-grammar:end -->.
- Manifest overlay: `canonical-framed-manifest-overlay.json` applies to `docs-next/pir/profiles/canonical-framed-fiat-shamir.json`; append the listed generated schema definitions and append their references to the selected source-view law. `pir.static-view-schema` is a generated definition kind, not a supported runtime subject kind, so the supported-subject catalog does not change.

## Assumptions and unresolved owner decisions

- The finite description source below is an owner candidate, not a reading of currently published body syntax.
- Canonical order is the displayed field order, represented by strictly increasing numeric record ordinals.
- The owner-local result_ref and prose result_schema are not body fields; the checked-result owner supplies the remaining closed record.
- Typed identifiers and opaque canonical values use the named canonical-body compilers; law fields use exact profile-law atoms.

The current owner text is silent about these exact finite bodies. Therefore every associated original obligation remains `CannotAnswer` until an owner selects or rejects this candidate:

- `F0V3-O-PUBLISHED-SCHEMAS`: `CannotAnswer` - publish four family-local schema subjects and their exact body compiler.
- `F0V3-O-CANONICAL-FRAME-SCHEDULE`: `CannotAnswer` - select initialization and frame-schedule coordinate bodies at current lines 1261 and 1268.
- `F0V3-O-CANONICAL-INFLUENCE`: `CannotAnswer` - select scope, influence, addition, and prefix-law bodies at current lines 1275-1278.
- `F0V3-O-CANONICAL-TRANSITION-ABI`: `CannotAnswer` - select namespace, ABIs, draw, transition, retry, failure, and decoding-coordinate bodies at current lines 1284-1292.
- `F0V3-O-CANONICAL-RESULT-BODY`: `CannotAnswer` - select a checked-result description, maps, conclusion, and omission of owner-local result_ref at current lines 1296-1305.

## Proposed semantic source

<!-- f0v3b-semantic-source:start -->
### Candidate finite FS-family static-view schemas

The following source is a proposed migration fragment. It is not active in this edition.

```text
F0V3BStaticViewSchemaV0(canonical-transcript-declaration-view-v0) = Owner(pir.transcript-construction);Tag(TranscriptDeclarationView);Body(canonical-framed-static-view-body-v0)
  Description = FamilyViewDescriptionV0(canonical-framed,CanonicalTranscriptDeclarationView)

F0V3BStaticViewSchemaV0(canonical-required-influence-view-v0) = Owner(pir.transcript-construction);Tag(RequiredInfluenceView);Body(canonical-framed-static-view-body-v0)
  Description = FamilyViewDescriptionV0(canonical-framed,CanonicalRequiredInfluenceView)

F0V3BStaticViewSchemaV0(canonical-challenge-transition-view-v0) = Owner(pir.transcript-construction);Tag(ChallengeTransitionView);Body(canonical-framed-static-view-body-v0)
  Description = FamilyViewDescriptionV0(canonical-framed,CanonicalChallengeTransitionView)

F0V3BStaticViewSchemaV0(canonical-fs-construction-view-v0) = Owner(pir.checked-fs-construction);Tag(FSConstructionView);Body(canonical-framed-static-view-body-v0)
  Description = FamilyViewDescriptionV0(canonical-framed,CanonicalFSConstructionView)
```

The exact finite descriptions named above are the following closed source.

<!-- f0v3b-schema-json:start -->
```json
{
  "body_compilers": [
    "algorithm-ref-body-v0",
    "canonical-value-body-v0",
    "challenge-ref-body-v0",
    "core-id-body-v0",
    "evaluation-contract-id-body-v0",
    "occurrence-kind-body-v0",
    "occurrence-ref-body-v0",
    "protocol-id-body-v0",
    "scope-ref-body-v0",
    "semantic-failure-type-body-v0",
    "transcript-construction-id-body-v0",
    "value-ref-body-v0",
    "value-type-body-v0"
  ],
  "definitions": {
    "AdditionEntry": {
      "record": [
        [
          0,
          {
            "ref": "ChallengeRef"
          }
        ],
        [
          1,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "ValueRef"
              },
              "max": 512,
              "min": 0
            }
          }
        ]
      ]
    },
    "AlgorithmRef": {
      "atom": {
        "compiler": "algorithm-ref-body-v0",
        "kind": "canonical-body"
      }
    },
    "AlgorithmUse": {
      "record": [
        [
          0,
          {
            "ref": "AlgorithmRef"
          }
        ],
        [
          1,
          {
            "ref": "EvaluationContractId"
          }
        ]
      ]
    },
    "CanonicalChallengeTransitionViewBody": {
      "record": [
        [
          0,
          {
            "ref": "TranscriptConstructionId"
          }
        ],
        [
          1,
          {
            "ref": "CoreId"
          }
        ],
        [
          2,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "canonical-framed:canonical-framed-prefix-and-domain-v0",
              "profile": "canonical-framed"
            }
          }
        ],
        [
          3,
          {
            "ref": "ChallengeABI"
          }
        ],
        [
          4,
          {
            "ref": "ChallengeABI"
          }
        ],
        [
          5,
          {
            "record": [
              [
                0,
                {
                  "atom": {
                    "kind": "natural",
                    "max": 4294967295
                  }
                }
              ],
              [
                1,
                {
                  "atom": {
                    "kind": "natural",
                    "max": 4294967295
                  }
                }
              ]
            ]
          }
        ],
        [
          6,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "canonical-framed:canonical-framed-body-grammar-v0",
              "profile": "canonical-framed"
            }
          }
        ],
        [
          7,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "canonical-framed:canonical-framed-admission-and-execution-v0",
              "profile": "canonical-framed"
            }
          }
        ],
        [
          8,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "canonical-framed:canonical-framed-admission-and-execution-v0",
              "profile": "canonical-framed"
            }
          }
        ],
        [
          9,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "canonical-framed:canonical-framed-admission-and-execution-v0",
              "profile": "canonical-framed"
            }
          }
        ],
        [
          10,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "ChallengeCoordinate"
              },
              "max": 512,
              "min": 0
            }
          }
        ]
      ]
    },
    "CanonicalFSConstructionViewBody": {
      "record": [
        [
          0,
          {
            "ref": "ProtocolId"
          }
        ],
        [
          1,
          {
            "ref": "ProtocolId"
          }
        ],
        [
          2,
          {
            "ref": "CoreId"
          }
        ],
        [
          3,
          {
            "ref": "TranscriptConstructionId"
          }
        ],
        [
          4,
          {
            "ref": "OccurrenceMap"
          }
        ],
        [
          5,
          {
            "ref": "ValueMap"
          }
        ],
        [
          6,
          {
            "ref": "ChallengeMap"
          }
        ],
        [
          7,
          {
            "ref": "CanonicalResultConclusion"
          }
        ]
      ]
    },
    "CanonicalFrameCoordinate": {
      "record": [
        [
          0,
          {
            "atom": {
              "kind": "natural",
              "max": 4294967295
            }
          }
        ],
        [
          1,
          {
            "ref": "OccurrenceRef"
          }
        ],
        [
          2,
          {
            "ref": "OccurrenceKind"
          }
        ]
      ]
    },
    "CanonicalRequiredInfluenceViewBody": {
      "record": [
        [
          0,
          {
            "ref": "TranscriptConstructionId"
          }
        ],
        [
          1,
          {
            "ref": "CoreId"
          }
        ],
        [
          2,
          {
            "sequence": {
              "discipline": "sorted-unique",
              "element": {
                "ref": "OccurrenceKind"
              },
              "max": 32,
              "min": 1
            }
          }
        ],
        [
          3,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "ScopeBinding"
              },
              "max": 64,
              "min": 0
            }
          }
        ],
        [
          4,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "InfluenceEntry"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          5,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "AdditionEntry"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          6,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "canonical-framed:canonical-framed-prefix-and-domain-v0",
              "profile": "canonical-framed"
            }
          }
        ]
      ]
    },
    "CanonicalResultConclusion": {
      "record": [
        [
          0,
          {
            "variant": [
              [
                0,
                {
                  "atom": {
                    "kind": "unit"
                  }
                }
              ]
            ]
          }
        ],
        [
          1,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "canonical-framed:canonical-framed-same-core-construction-v0",
              "profile": "canonical-framed"
            }
          }
        ]
      ]
    },
    "CanonicalTranscriptDeclarationViewBody": {
      "record": [
        [
          0,
          {
            "ref": "TranscriptConstructionId"
          }
        ],
        [
          1,
          {
            "ref": "CoreId"
          }
        ],
        [
          2,
          {
            "ref": "ValueType"
          }
        ],
        [
          3,
          {
            "ref": "ValueType"
          }
        ],
        [
          4,
          {
            "ref": "CanonicalValue"
          }
        ],
        [
          5,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "canonical-framed:canonical-framed-body-grammar-v0",
              "profile": "canonical-framed"
            }
          }
        ],
        [
          6,
          {
            "ref": "AlgorithmUse"
          }
        ],
        [
          7,
          {
            "ref": "AlgorithmUse"
          }
        ],
        [
          8,
          {
            "ref": "AlgorithmUse"
          }
        ],
        [
          9,
          {
            "ref": "CanonicalValue"
          }
        ],
        [
          10,
          {
            "ref": "SemanticFailureType"
          }
        ],
        [
          11,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "canonical-framed:canonical-framed-source-views-v0",
              "profile": "canonical-framed"
            }
          }
        ],
        [
          12,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "CanonicalFrameCoordinate"
              },
              "max": 512,
              "min": 0
            }
          }
        ]
      ]
    },
    "CanonicalValue": {
      "atom": {
        "compiler": "canonical-value-body-v0",
        "kind": "canonical-body"
      }
    },
    "ChallengeABI": {
      "record": [
        [
          0,
          {
            "ref": "AlgorithmUse"
          }
        ],
        [
          1,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "ValueType"
              },
              "max": 16,
              "min": 0
            }
          }
        ],
        [
          2,
          {
            "ref": "ValueType"
          }
        ]
      ]
    },
    "ChallengeCoordinate": {
      "record": [
        [
          0,
          {
            "ref": "ChallengeRef"
          }
        ],
        [
          1,
          {
            "atom": {
              "kind": "natural",
              "max": 4294967295
            }
          }
        ]
      ]
    },
    "ChallengeMap": {
      "sequence": {
        "discipline": "ordered",
        "element": {
          "record": [
            [
              0,
              {
                "ref": "ChallengeRef"
              }
            ],
            [
              1,
              {
                "ref": "ChallengeRef"
              }
            ]
          ]
        },
        "max": 512,
        "min": 0
      }
    },
    "ChallengeRef": {
      "atom": {
        "compiler": "challenge-ref-body-v0",
        "kind": "canonical-body"
      }
    },
    "CoreId": {
      "atom": {
        "compiler": "core-id-body-v0",
        "kind": "canonical-body"
      }
    },
    "EvaluationContractId": {
      "atom": {
        "compiler": "evaluation-contract-id-body-v0",
        "kind": "canonical-body"
      }
    },
    "InfluenceAtom": {
      "record": [
        [
          0,
          {
            "ref": "OccurrenceRef"
          }
        ],
        [
          1,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "OccurrenceKind"
              },
              "max": 16,
              "min": 1
            }
          }
        ],
        [
          2,
          {
            "atom": {
              "kind": "meta-boolean"
            }
          }
        ]
      ]
    },
    "InfluenceEntry": {
      "record": [
        [
          0,
          {
            "ref": "ChallengeRef"
          }
        ],
        [
          1,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "InfluenceAtom"
              },
              "max": 512,
              "min": 0
            }
          }
        ]
      ]
    },
    "OccurrenceKind": {
      "atom": {
        "compiler": "occurrence-kind-body-v0",
        "kind": "canonical-body"
      }
    },
    "OccurrenceMap": {
      "sequence": {
        "discipline": "ordered",
        "element": {
          "record": [
            [
              0,
              {
                "ref": "OccurrenceRef"
              }
            ],
            [
              1,
              {
                "ref": "OccurrenceRef"
              }
            ]
          ]
        },
        "max": 512,
        "min": 0
      }
    },
    "OccurrenceRef": {
      "atom": {
        "compiler": "occurrence-ref-body-v0",
        "kind": "canonical-body"
      }
    },
    "ProtocolId": {
      "atom": {
        "compiler": "protocol-id-body-v0",
        "kind": "canonical-body"
      }
    },
    "ScopeBinding": {
      "record": [
        [
          0,
          {
            "ref": "ScopeRef"
          }
        ],
        [
          1,
          {
            "variant": [
              [
                0,
                {
                  "atom": {
                    "kind": "unit"
                  }
                }
              ],
              [
                1,
                {
                  "ref": "ScopeRef"
                }
              ]
            ]
          }
        ],
        [
          2,
          {
            "variant": [
              [
                0,
                {
                  "atom": {
                    "kind": "unit"
                  }
                }
              ],
              [
                1,
                {
                  "ref": "OccurrenceRef"
                }
              ]
            ]
          }
        ]
      ]
    },
    "ScopeRef": {
      "atom": {
        "compiler": "scope-ref-body-v0",
        "kind": "canonical-body"
      }
    },
    "SemanticFailureType": {
      "atom": {
        "compiler": "semantic-failure-type-body-v0",
        "kind": "canonical-body"
      }
    },
    "TranscriptConstructionId": {
      "atom": {
        "compiler": "transcript-construction-id-body-v0",
        "kind": "canonical-body"
      }
    },
    "ValueMap": {
      "sequence": {
        "discipline": "ordered",
        "element": {
          "record": [
            [
              0,
              {
                "ref": "ValueRef"
              }
            ],
            [
              1,
              {
                "ref": "ValueRef"
              }
            ]
          ]
        },
        "max": 512,
        "min": 0
      }
    },
    "ValueRef": {
      "atom": {
        "compiler": "value-ref-body-v0",
        "kind": "canonical-body"
      }
    },
    "ValueType": {
      "atom": {
        "compiler": "value-type-body-v0",
        "kind": "canonical-body"
      }
    }
  },
  "family": "canonical-framed",
  "format": "zkc.f0v3b.proposed-family-view-schema.v0",
  "laws": [
    "canonical-framed:canonical-framed-admission-and-execution-v0",
    "canonical-framed:canonical-framed-body-grammar-v0",
    "canonical-framed:canonical-framed-prefix-and-domain-v0",
    "canonical-framed:canonical-framed-same-core-construction-v0",
    "canonical-framed:canonical-framed-source-views-v0"
  ],
  "maximum_sequence_length": 512,
  "views": {
    "CanonicalChallengeTransitionView": {
      "owner_subject_kind": "pir.transcript-construction",
      "schema": {
        "ref": "CanonicalChallengeTransitionViewBody"
      }
    },
    "CanonicalFSConstructionView": {
      "owner_subject_kind": "pir.checked-fs-construction",
      "schema": {
        "ref": "CanonicalFSConstructionViewBody"
      }
    },
    "CanonicalRequiredInfluenceView": {
      "owner_subject_kind": "pir.transcript-construction",
      "schema": {
        "ref": "CanonicalRequiredInfluenceViewBody"
      }
    },
    "CanonicalTranscriptDeclarationView": {
      "owner_subject_kind": "pir.transcript-construction",
      "schema": {
        "ref": "CanonicalTranscriptDeclarationViewBody"
      }
    }
  }
}
```
<!-- f0v3b-schema-json:end -->

<!-- f0v3b-semantic-source:end -->

## Proposed body-compiler source

<!-- f0v3b-body-source:start -->
### Candidate finite FS-family static-view body compiler

```text
CanonicalFramedStaticViewBodyV0(schema,value) =
  require schema is the exact profile-local finite description selected by the view kind;
  require value is accepted by that closed Atom/Record/Variant/bounded-Sequence description;
  return StaticViewBodyV0(schema,value) from the Interaction finite-description compiler;
  refuse a value carrying an extra owner-local coordinate, including result_ref bytes.
```

<!-- f0v3b-body-source:end -->

## Frozen owner-page diff

The block below must equal the unified diff produced by inserting the two source blocks at the exact markers above.

<!-- f0v3b-page-diff:start -->
--- docs-next/pir/fiat-shamir.md
+++ proposed/docs-next/pir/fiat-shamir.md
@@ -1410,6 +1410,823 @@
 and the sibling itself activates no theorem without a separate Analysis
 correspondence, source-validation result, and applicability judgment.
 
+### Candidate finite FS-family static-view schemas
+
+The following source is a proposed migration fragment. It is not active in this edition.
+
+```text
+F0V3BStaticViewSchemaV0(canonical-transcript-declaration-view-v0) = Owner(pir.transcript-construction);Tag(TranscriptDeclarationView);Body(canonical-framed-static-view-body-v0)
+  Description = FamilyViewDescriptionV0(canonical-framed,CanonicalTranscriptDeclarationView)
+
+F0V3BStaticViewSchemaV0(canonical-required-influence-view-v0) = Owner(pir.transcript-construction);Tag(RequiredInfluenceView);Body(canonical-framed-static-view-body-v0)
+  Description = FamilyViewDescriptionV0(canonical-framed,CanonicalRequiredInfluenceView)
+
+F0V3BStaticViewSchemaV0(canonical-challenge-transition-view-v0) = Owner(pir.transcript-construction);Tag(ChallengeTransitionView);Body(canonical-framed-static-view-body-v0)
+  Description = FamilyViewDescriptionV0(canonical-framed,CanonicalChallengeTransitionView)
+
+F0V3BStaticViewSchemaV0(canonical-fs-construction-view-v0) = Owner(pir.checked-fs-construction);Tag(FSConstructionView);Body(canonical-framed-static-view-body-v0)
+  Description = FamilyViewDescriptionV0(canonical-framed,CanonicalFSConstructionView)
+```
+
+The exact finite descriptions named above are the following closed source.
+
+<!-- f0v3b-schema-json:start -->
+```json
+{
+  "body_compilers": [
+    "algorithm-ref-body-v0",
+    "canonical-value-body-v0",
+    "challenge-ref-body-v0",
+    "core-id-body-v0",
+    "evaluation-contract-id-body-v0",
+    "occurrence-kind-body-v0",
+    "occurrence-ref-body-v0",
+    "protocol-id-body-v0",
+    "scope-ref-body-v0",
+    "semantic-failure-type-body-v0",
+    "transcript-construction-id-body-v0",
+    "value-ref-body-v0",
+    "value-type-body-v0"
+  ],
+  "definitions": {
+    "AdditionEntry": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "ChallengeRef"
+          }
+        ],
+        [
+          1,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "ValueRef"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ]
+      ]
+    },
+    "AlgorithmRef": {
+      "atom": {
+        "compiler": "algorithm-ref-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "AlgorithmUse": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "AlgorithmRef"
+          }
+        ],
+        [
+          1,
+          {
+            "ref": "EvaluationContractId"
+          }
+        ]
+      ]
+    },
+    "CanonicalChallengeTransitionViewBody": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "TranscriptConstructionId"
+          }
+        ],
+        [
+          1,
+          {
+            "ref": "CoreId"
+          }
+        ],
+        [
+          2,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "canonical-framed:canonical-framed-prefix-and-domain-v0",
+              "profile": "canonical-framed"
+            }
+          }
+        ],
+        [
+          3,
+          {
+            "ref": "ChallengeABI"
+          }
+        ],
+        [
+          4,
+          {
+            "ref": "ChallengeABI"
+          }
+        ],
+        [
+          5,
+          {
+            "record": [
+              [
+                0,
+                {
+                  "atom": {
+                    "kind": "natural",
+                    "max": 4294967295
+                  }
+                }
+              ],
+              [
+                1,
+                {
+                  "atom": {
+                    "kind": "natural",
+                    "max": 4294967295
+                  }
+                }
+              ]
+            ]
+          }
+        ],
+        [
+          6,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "canonical-framed:canonical-framed-body-grammar-v0",
+              "profile": "canonical-framed"
+            }
+          }
+        ],
+        [
+          7,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "canonical-framed:canonical-framed-admission-and-execution-v0",
+              "profile": "canonical-framed"
+            }
+          }
+        ],
+        [
+          8,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "canonical-framed:canonical-framed-admission-and-execution-v0",
+              "profile": "canonical-framed"
+            }
+          }
+        ],
+        [
+          9,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "canonical-framed:canonical-framed-admission-and-execution-v0",
+              "profile": "canonical-framed"
+            }
+          }
+        ],
+        [
+          10,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "ChallengeCoordinate"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ]
+      ]
+    },
+    "CanonicalFSConstructionViewBody": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "ProtocolId"
+          }
+        ],
+        [
+          1,
+          {
+            "ref": "ProtocolId"
+          }
+        ],
+        [
+          2,
+          {
+            "ref": "CoreId"
+          }
+        ],
+        [
+          3,
+          {
+            "ref": "TranscriptConstructionId"
+          }
+        ],
+        [
+          4,
+          {
+            "ref": "OccurrenceMap"
+          }
+        ],
+        [
+          5,
+          {
+            "ref": "ValueMap"
+          }
+        ],
+        [
+          6,
+          {
+            "ref": "ChallengeMap"
+          }
+        ],
+        [
+          7,
+          {
+            "ref": "CanonicalResultConclusion"
+          }
+        ]
+      ]
+    },
+    "CanonicalFrameCoordinate": {
+      "record": [
+        [
+          0,
+          {
+            "atom": {
+              "kind": "natural",
+              "max": 4294967295
+            }
+          }
+        ],
+        [
+          1,
+          {
+            "ref": "OccurrenceRef"
+          }
+        ],
+        [
+          2,
+          {
+            "ref": "OccurrenceKind"
+          }
+        ]
+      ]
+    },
+    "CanonicalRequiredInfluenceViewBody": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "TranscriptConstructionId"
+          }
+        ],
+        [
+          1,
+          {
+            "ref": "CoreId"
+          }
+        ],
+        [
+          2,
+          {
+            "sequence": {
+              "discipline": "sorted-unique",
+              "element": {
+                "ref": "OccurrenceKind"
+              },
+              "max": 32,
+              "min": 1
+            }
+          }
+        ],
+        [
+          3,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "ScopeBinding"
+              },
+              "max": 64,
+              "min": 0
+            }
+          }
+        ],
+        [
+          4,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "InfluenceEntry"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          5,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "AdditionEntry"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          6,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "canonical-framed:canonical-framed-prefix-and-domain-v0",
+              "profile": "canonical-framed"
+            }
+          }
+        ]
+      ]
+    },
+    "CanonicalResultConclusion": {
+      "record": [
+        [
+          0,
+          {
+            "variant": [
+              [
+                0,
+                {
+                  "atom": {
+                    "kind": "unit"
+                  }
+                }
+              ]
+            ]
+          }
+        ],
+        [
+          1,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "canonical-framed:canonical-framed-same-core-construction-v0",
+              "profile": "canonical-framed"
+            }
+          }
+        ]
+      ]
+    },
+    "CanonicalTranscriptDeclarationViewBody": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "TranscriptConstructionId"
+          }
+        ],
+        [
+          1,
+          {
+            "ref": "CoreId"
+          }
+        ],
+        [
+          2,
+          {
+            "ref": "ValueType"
+          }
+        ],
+        [
+          3,
+          {
+            "ref": "ValueType"
+          }
+        ],
+        [
+          4,
+          {
+            "ref": "CanonicalValue"
+          }
+        ],
+        [
+          5,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "canonical-framed:canonical-framed-body-grammar-v0",
+              "profile": "canonical-framed"
+            }
+          }
+        ],
+        [
+          6,
+          {
+            "ref": "AlgorithmUse"
+          }
+        ],
+        [
+          7,
+          {
+            "ref": "AlgorithmUse"
+          }
+        ],
+        [
+          8,
+          {
+            "ref": "AlgorithmUse"
+          }
+        ],
+        [
+          9,
+          {
+            "ref": "CanonicalValue"
+          }
+        ],
+        [
+          10,
+          {
+            "ref": "SemanticFailureType"
+          }
+        ],
+        [
+          11,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "canonical-framed:canonical-framed-source-views-v0",
+              "profile": "canonical-framed"
+            }
+          }
+        ],
+        [
+          12,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "CanonicalFrameCoordinate"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ]
+      ]
+    },
+    "CanonicalValue": {
+      "atom": {
+        "compiler": "canonical-value-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "ChallengeABI": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "AlgorithmUse"
+          }
+        ],
+        [
+          1,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "ValueType"
+              },
+              "max": 16,
+              "min": 0
+            }
+          }
+        ],
+        [
+          2,
+          {
+            "ref": "ValueType"
+          }
+        ]
+      ]
+    },
+    "ChallengeCoordinate": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "ChallengeRef"
+          }
+        ],
+        [
+          1,
+          {
+            "atom": {
+              "kind": "natural",
+              "max": 4294967295
+            }
+          }
+        ]
+      ]
+    },
+    "ChallengeMap": {
+      "sequence": {
+        "discipline": "ordered",
+        "element": {
+          "record": [
+            [
+              0,
+              {
+                "ref": "ChallengeRef"
+              }
+            ],
+            [
+              1,
+              {
+                "ref": "ChallengeRef"
+              }
+            ]
+          ]
+        },
+        "max": 512,
+        "min": 0
+      }
+    },
+    "ChallengeRef": {
+      "atom": {
+        "compiler": "challenge-ref-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "CoreId": {
+      "atom": {
+        "compiler": "core-id-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "EvaluationContractId": {
+      "atom": {
+        "compiler": "evaluation-contract-id-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "InfluenceAtom": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "OccurrenceRef"
+          }
+        ],
+        [
+          1,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "OccurrenceKind"
+              },
+              "max": 16,
+              "min": 1
+            }
+          }
+        ],
+        [
+          2,
+          {
+            "atom": {
+              "kind": "meta-boolean"
+            }
+          }
+        ]
+      ]
+    },
+    "InfluenceEntry": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "ChallengeRef"
+          }
+        ],
+        [
+          1,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "InfluenceAtom"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ]
+      ]
+    },
+    "OccurrenceKind": {
+      "atom": {
+        "compiler": "occurrence-kind-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "OccurrenceMap": {
+      "sequence": {
+        "discipline": "ordered",
+        "element": {
+          "record": [
+            [
+              0,
+              {
+                "ref": "OccurrenceRef"
+              }
+            ],
+            [
+              1,
+              {
+                "ref": "OccurrenceRef"
+              }
+            ]
+          ]
+        },
+        "max": 512,
+        "min": 0
+      }
+    },
+    "OccurrenceRef": {
+      "atom": {
+        "compiler": "occurrence-ref-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "ProtocolId": {
+      "atom": {
+        "compiler": "protocol-id-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "ScopeBinding": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "ScopeRef"
+          }
+        ],
+        [
+          1,
+          {
+            "variant": [
+              [
+                0,
+                {
+                  "atom": {
+                    "kind": "unit"
+                  }
+                }
+              ],
+              [
+                1,
+                {
+                  "ref": "ScopeRef"
+                }
+              ]
+            ]
+          }
+        ],
+        [
+          2,
+          {
+            "variant": [
+              [
+                0,
+                {
+                  "atom": {
+                    "kind": "unit"
+                  }
+                }
+              ],
+              [
+                1,
+                {
+                  "ref": "OccurrenceRef"
+                }
+              ]
+            ]
+          }
+        ]
+      ]
+    },
+    "ScopeRef": {
+      "atom": {
+        "compiler": "scope-ref-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "SemanticFailureType": {
+      "atom": {
+        "compiler": "semantic-failure-type-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "TranscriptConstructionId": {
+      "atom": {
+        "compiler": "transcript-construction-id-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "ValueMap": {
+      "sequence": {
+        "discipline": "ordered",
+        "element": {
+          "record": [
+            [
+              0,
+              {
+                "ref": "ValueRef"
+              }
+            ],
+            [
+              1,
+              {
+                "ref": "ValueRef"
+              }
+            ]
+          ]
+        },
+        "max": 512,
+        "min": 0
+      }
+    },
+    "ValueRef": {
+      "atom": {
+        "compiler": "value-ref-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "ValueType": {
+      "atom": {
+        "compiler": "value-type-body-v0",
+        "kind": "canonical-body"
+      }
+    }
+  },
+  "family": "canonical-framed",
+  "format": "zkc.f0v3b.proposed-family-view-schema.v0",
+  "laws": [
+    "canonical-framed:canonical-framed-admission-and-execution-v0",
+    "canonical-framed:canonical-framed-body-grammar-v0",
+    "canonical-framed:canonical-framed-prefix-and-domain-v0",
+    "canonical-framed:canonical-framed-same-core-construction-v0",
+    "canonical-framed:canonical-framed-source-views-v0"
+  ],
+  "maximum_sequence_length": 512,
+  "views": {
+    "CanonicalChallengeTransitionView": {
+      "owner_subject_kind": "pir.transcript-construction",
+      "schema": {
+        "ref": "CanonicalChallengeTransitionViewBody"
+      }
+    },
+    "CanonicalFSConstructionView": {
+      "owner_subject_kind": "pir.checked-fs-construction",
+      "schema": {
+        "ref": "CanonicalFSConstructionViewBody"
+      }
+    },
+    "CanonicalRequiredInfluenceView": {
+      "owner_subject_kind": "pir.transcript-construction",
+      "schema": {
+        "ref": "CanonicalRequiredInfluenceViewBody"
+      }
+    },
+    "CanonicalTranscriptDeclarationView": {
+      "owner_subject_kind": "pir.transcript-construction",
+      "schema": {
+        "ref": "CanonicalTranscriptDeclarationViewBody"
+      }
+    }
+  }
+}
+```
+<!-- f0v3b-schema-json:end -->
+
 <!-- zkc-profile-source:canonical-framed-fs-semantics:end -->
 
 ## 15. Bounded executable evidence
@@ -1654,4 +2471,14 @@
 only when a Foundation-owned mechanism or its interpretation changes. Old
 bytes are never reinterpreted.
 
+### Candidate finite FS-family static-view body compiler
+
+```text
+CanonicalFramedStaticViewBodyV0(schema,value) =
+  require schema is the exact profile-local finite description selected by the view kind;
+  require value is accepted by that closed Atom/Record/Variant/bounded-Sequence description;
+  return StaticViewBodyV0(schema,value) from the Interaction finite-description compiler;
+  refuse a value carrying an extra owner-local coordinate, including result_ref bytes.
+```
+
 <!-- zkc-profile-source:canonical-framed-fs-body-grammar:end -->
<!-- f0v3b-page-diff:end -->
