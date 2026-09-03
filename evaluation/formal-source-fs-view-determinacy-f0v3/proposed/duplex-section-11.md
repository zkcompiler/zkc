# Proposed duplex-sponge FS-family view bodies

This file is candidate owner text for F0-V3B. It is executable migration input, not an edit to the owner page.

## Exact insertion points

- Semantic fragment: `docs-next/pir/duplex-sponge-fiat-shamir.md`, Section 11, immediately before <!-- zkc-profile-source:duplex-sponge-fs-semantics:end -->.
- Body compiler: `docs-next/pir/duplex-sponge-fiat-shamir.md`, Appendix A, immediately before <!-- zkc-profile-source:duplex-sponge-fs-body-grammar:end -->.
- Manifest overlay: `duplex-sponge-manifest-overlay.json` applies to `docs-next/pir/profiles/duplex-sponge-fiat-shamir.json`; append the listed generated schema definitions and append their references to the selected source-view law. `pir.static-view-schema` is a generated definition kind, not a supported runtime subject kind, so the supported-subject catalog does not change.

## Assumptions and unresolved owner decisions

- The finite description source below is an owner candidate, not a reading of currently published body syntax.
- Canonical order is the displayed field order, represented by strictly increasing numeric record ordinals.
- AlwaysAccept, NoRetry, None, DuplexSponge, and StructurallyConstructed are closed unit variants rather than free text.
- The owner-local result_ref and prose result_schema are not body fields; the checked-result owner supplies the remaining closed record.
- The witness currently has no checked duplex-result issuer, so its result schema is compiled but not inhabited.

The current owner text is silent about these exact finite bodies. Therefore every associated original obligation remains `CannotAnswer` until an owner selects or rejects this candidate:

- `F0V3-O-PUBLISHED-SCHEMAS`: `CannotAnswer` - publish four family-local schema subjects and their exact body compiler.
- `F0V3-O-DUPLEX-STATE-INSTANCE`: `CannotAnswer` - select family, carrier, bit-convention, and binding-projection bodies at current lines 870 and 875-877.
- `F0V3-O-DUPLEX-MATERIAL-SALT`: `CannotAnswer` - select construction-material, salt-coordinate, and target-only material-map bodies at current lines 882, 898, and 948-949.
- `F0V3-O-DUPLEX-CODEC-ARGUMENTS`: `CannotAnswer` - select message-codec, semantic-shape, and encoded coverage bodies at current lines 883-884 and 899-901.
- `F0V3-O-DUPLEX-SCHEDULE-COVERAGE`: `CannotAnswer` - select schedule, binding-sequence, coverage-law, prohibited-addition, and resource bodies at current lines 885-887, 897, and 902-904.
- `F0V3-O-DUPLEX-TRANSITION-ABI`: `CannotAnswer` - select squeeze/decoder, totality, tags, execution-domain, and event bodies at current lines 921-929.
- `F0V3-O-DUPLEX-RESULT-BODY`: `CannotAnswer` - select the checked-result record, maps, projections, correspondences, conclusion, and omission of owner-local result_ref at current lines 937-952.

## Proposed semantic source

<!-- f0v3b-semantic-source:start -->
### Candidate finite FS-family static-view schemas

The following source is a proposed migration fragment. It is not active in this edition.

```text
F0V3BStaticViewSchemaV0(duplex-transcript-declaration-view-v0) = Owner(pir.transcript-construction);Tag(DuplexTranscriptDeclarationView);Body(duplex-sponge-static-view-body-v0)
  Description = FamilyViewDescriptionV0(duplex-sponge,DuplexTranscriptDeclarationView)

F0V3BStaticViewSchemaV0(duplex-encoded-input-coverage-view-v0) = Owner(pir.transcript-construction);Tag(DuplexEncodedInputCoverageView);Body(duplex-sponge-static-view-body-v0)
  Description = FamilyViewDescriptionV0(duplex-sponge,DuplexEncodedInputCoverageView)

F0V3BStaticViewSchemaV0(duplex-challenge-transition-view-v0) = Owner(pir.transcript-construction);Tag(DuplexChallengeTransitionView);Body(duplex-sponge-static-view-body-v0)
  Description = FamilyViewDescriptionV0(duplex-sponge,DuplexChallengeTransitionView)

F0V3BStaticViewSchemaV0(duplex-fs-construction-view-v0) = Owner(pir.checked-duplex-fs-construction);Tag(DuplexFSConstructionView);Body(duplex-sponge-static-view-body-v0)
  Description = FamilyViewDescriptionV0(duplex-sponge,DuplexFSConstructionView)
```

The exact finite descriptions named above are the following closed source.

<!-- f0v3b-schema-json:start -->
```json
{
  "body_compilers": [
    "algorithm-ref-body-v0",
    "binding-ref-body-v0",
    "canonical-value-body-v0",
    "challenge-ref-body-v0",
    "core-id-body-v0",
    "evaluation-contract-id-body-v0",
    "occurrence-kind-body-v0",
    "occurrence-ref-body-v0",
    "protocol-id-body-v0",
    "transcript-construction-id-body-v0",
    "value-ref-body-v0",
    "value-type-body-v0"
  ],
  "definitions": {
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
    "BindingProjection": {
      "record": [
        [
          0,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "BindingRef"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          1,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-source-views-v0",
              "profile": "duplex-sponge"
            }
          }
        ]
      ]
    },
    "BindingRef": {
      "atom": {
        "compiler": "binding-ref-body-v0",
        "kind": "canonical-body"
      }
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
    "CanonicalValue": {
      "atom": {
        "compiler": "canonical-value-body-v0",
        "kind": "canonical-body"
      }
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
    "ConstructionMaterialMap": {
      "record": [
        [
          0,
          {
            "ref": "MaterialCoordinate"
          }
        ],
        [
          1,
          {
            "ref": "MaterialSchema"
          }
        ]
      ]
    },
    "CoreId": {
      "atom": {
        "compiler": "core-id-body-v0",
        "kind": "canonical-body"
      }
    },
    "CoverageAtom": {
      "variant": [
        [
          0,
          {
            "ref": "BindingRef"
          }
        ],
        [
          1,
          {
            "ref": "MaterialCoordinate"
          }
        ],
        [
          2,
          {
            "ref": "OccurrenceRef"
          }
        ],
        [
          3,
          {
            "ref": "ChallengeRef"
          }
        ]
      ]
    },
    "CoverageEntry": {
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
                "ref": "CoverageAtom"
              },
              "max": 512,
              "min": 0
            }
          }
        ]
      ]
    },
    "DecoderMapEntry": {
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
        ],
        [
          2,
          {
            "ref": "AlgorithmUse"
          }
        ]
      ]
    },
    "DuplexChallengeTransitionViewBody": {
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
              "discipline": "ordered",
              "element": {
                "ref": "DecoderMapEntry"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          3,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-admission-and-execution-v0",
              "profile": "duplex-sponge"
            }
          }
        ],
        [
          4,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-state-transition-v0",
              "profile": "duplex-sponge"
            }
          }
        ],
        [
          5,
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
          6,
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
          7,
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
          8,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "ChallengeRef"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          9,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "ChallengeRef"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          10,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "SqueezeProjection"
              },
              "max": 512,
              "min": 0
            }
          }
        ]
      ]
    },
    "DuplexEncodedInputCoverageViewBody": {
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
              "discipline": "ordered",
              "element": {
                "ref": "BindingRef"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          3,
          {
            "ref": "MaterialCoordinate"
          }
        ],
        [
          4,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "CoverageEntry"
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
                "ref": "OccurrenceRef"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          6,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "ChallengeRef"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          7,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-source-views-v0",
              "profile": "duplex-sponge"
            }
          }
        ],
        [
          8,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-source-views-v0",
              "profile": "duplex-sponge"
            }
          }
        ],
        [
          9,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "CoverageAtom"
              },
              "max": 16,
              "min": 0
            }
          }
        ]
      ]
    },
    "DuplexFSConstructionViewBody": {
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
          5,
          {
            "ref": "OccurrenceMap"
          }
        ],
        [
          6,
          {
            "ref": "ValueMap"
          }
        ],
        [
          7,
          {
            "ref": "ChallengeMap"
          }
        ],
        [
          8,
          {
            "ref": "InstanceProjection"
          }
        ],
        [
          9,
          {
            "ref": "ConstructionMaterialMap"
          }
        ],
        [
          10,
          {
            "ref": "ScheduleCorrespondence"
          }
        ],
        [
          11,
          {
            "ref": "ScheduleCorrespondence"
          }
        ],
        [
          12,
          {
            "ref": "DuplexResultConclusion"
          }
        ]
      ]
    },
    "DuplexResultConclusion": {
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
              "law": "duplex-sponge:duplex-sponge-admission-and-execution-v0",
              "profile": "duplex-sponge"
            }
          }
        ]
      ]
    },
    "DuplexTranscriptDeclarationViewBody": {
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
              "kind": "natural",
              "max": 4294967295
            }
          }
        ],
        [
          6,
          {
            "atom": {
              "kind": "natural",
              "max": 4294967295
            }
          }
        ],
        [
          7,
          {
            "ref": "StateCarrier"
          }
        ],
        [
          8,
          {
            "ref": "InstanceCarrier"
          }
        ],
        [
          9,
          {
            "ref": "BindingProjection"
          }
        ],
        [
          10,
          {
            "ref": "AlgorithmUse"
          }
        ],
        [
          11,
          {
            "ref": "AlgorithmUse"
          }
        ],
        [
          12,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-state-transition-v0",
              "profile": "duplex-sponge"
            }
          }
        ],
        [
          13,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-state-transition-v0",
              "profile": "duplex-sponge"
            }
          }
        ],
        [
          14,
          {
            "ref": "MaterialSchema"
          }
        ],
        [
          15,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "MessageCodecEntry"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          16,
          {
            "record": [
              [
                0,
                {
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
                            "ref": "ValueType"
                          }
                        ]
                      ]
                    },
                    "max": 512,
                    "min": 0
                  }
                }
              ],
              [
                1,
                {
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
                            "ref": "ValueType"
                          }
                        ]
                      ]
                    },
                    "max": 512,
                    "min": 0
                  }
                }
              ]
            ]
          }
        ],
        [
          17,
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
        ],
        [
          18,
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
        ],
        [
          19,
          {
            "ref": "ResourceProjection"
          }
        ]
      ]
    },
    "EvaluationContractId": {
      "atom": {
        "compiler": "evaluation-contract-id-body-v0",
        "kind": "canonical-body"
      }
    },
    "InstanceCarrier": {
      "record": [
        [
          0,
          {
            "ref": "ValueType"
          }
        ],
        [
          1,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-body-grammar-v0",
              "profile": "duplex-sponge"
            }
          }
        ]
      ]
    },
    "InstanceProjection": {
      "record": [
        [
          0,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "BindingRef"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          1,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-source-views-v0",
              "profile": "duplex-sponge"
            }
          }
        ]
      ]
    },
    "MaterialCoordinate": {
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
                  "ref": "ChallengeRef"
                }
              ]
            ]
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
    "MaterialSchema": {
      "record": [
        [
          0,
          {
            "ref": "MaterialCoordinate"
          }
        ],
        [
          1,
          {
            "ref": "ValueType"
          }
        ],
        [
          2,
          {
            "atom": {
              "kind": "natural",
              "max": 4294967295
            }
          }
        ]
      ]
    },
    "MessageCodecEntry": {
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
            "ref": "AlgorithmUse"
          }
        ],
        [
          2,
          {
            "atom": {
              "kind": "natural",
              "max": 4294967295
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
    "ResourceProjection": {
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
        ],
        [
          2,
          {
            "atom": {
              "kind": "natural",
              "max": 4294967295
            }
          }
        ]
      ]
    },
    "ScheduleCorrespondence": {
      "record": [
        [
          0,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "ChallengeRef"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          1,
          {
            "sequence": {
              "discipline": "ordered",
              "element": {
                "ref": "ChallengeRef"
              },
              "max": 512,
              "min": 0
            }
          }
        ],
        [
          2,
          {
            "ref": "ChallengeMap"
          }
        ],
        [
          3,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-downstream-boundary-v0",
              "profile": "duplex-sponge"
            }
          }
        ]
      ]
    },
    "SqueezeProjection": {
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
            "ref": "OccurrenceRef"
          }
        ],
        [
          2,
          {
            "atom": {
              "kind": "natural",
              "max": 4294967295
            }
          }
        ]
      ]
    },
    "StateCarrier": {
      "record": [
        [
          0,
          {
            "ref": "ValueType"
          }
        ],
        [
          1,
          {
            "atom": {
              "kind": "exact-profile-law",
              "law": "duplex-sponge:duplex-sponge-state-transition-v0",
              "profile": "duplex-sponge"
            }
          }
        ]
      ]
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
  "family": "duplex-sponge",
  "format": "zkc.f0v3b.proposed-family-view-schema.v0",
  "laws": [
    "duplex-sponge:duplex-sponge-admission-and-execution-v0",
    "duplex-sponge:duplex-sponge-body-grammar-v0",
    "duplex-sponge:duplex-sponge-downstream-boundary-v0",
    "duplex-sponge:duplex-sponge-source-views-v0",
    "duplex-sponge:duplex-sponge-state-transition-v0"
  ],
  "maximum_sequence_length": 512,
  "views": {
    "DuplexChallengeTransitionView": {
      "owner_subject_kind": "pir.transcript-construction",
      "schema": {
        "ref": "DuplexChallengeTransitionViewBody"
      }
    },
    "DuplexEncodedInputCoverageView": {
      "owner_subject_kind": "pir.transcript-construction",
      "schema": {
        "ref": "DuplexEncodedInputCoverageViewBody"
      }
    },
    "DuplexFSConstructionView": {
      "owner_subject_kind": "pir.checked-duplex-fs-construction",
      "schema": {
        "ref": "DuplexFSConstructionViewBody"
      }
    },
    "DuplexTranscriptDeclarationView": {
      "owner_subject_kind": "pir.transcript-construction",
      "schema": {
        "ref": "DuplexTranscriptDeclarationViewBody"
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
DuplexSpongeStaticViewBodyV0(schema,value) =
  require schema is the exact profile-local finite description selected by the view kind;
  require value is accepted by that closed Atom/Record/Variant/bounded-Sequence description;
  return StaticViewBodyV0(schema,value) from the Interaction finite-description compiler;
  refuse a value carrying an extra owner-local coordinate, including result_ref bytes.
```

<!-- f0v3b-body-source:end -->

## Frozen owner-page diff

The block below must equal the unified diff produced by inserting the two source blocks at the exact markers above.

<!-- f0v3b-page-diff:start -->
--- docs-next/pir/duplex-sponge-fiat-shamir.md
+++ proposed/docs-next/pir/duplex-sponge-fiat-shamir.md
@@ -958,6 +958,1226 @@
 It likewise prevents a canonical consumer from treating absent duplex fields
 as empty values.
 
+### Candidate finite FS-family static-view schemas
+
+The following source is a proposed migration fragment. It is not active in this edition.
+
+```text
+F0V3BStaticViewSchemaV0(duplex-transcript-declaration-view-v0) = Owner(pir.transcript-construction);Tag(DuplexTranscriptDeclarationView);Body(duplex-sponge-static-view-body-v0)
+  Description = FamilyViewDescriptionV0(duplex-sponge,DuplexTranscriptDeclarationView)
+
+F0V3BStaticViewSchemaV0(duplex-encoded-input-coverage-view-v0) = Owner(pir.transcript-construction);Tag(DuplexEncodedInputCoverageView);Body(duplex-sponge-static-view-body-v0)
+  Description = FamilyViewDescriptionV0(duplex-sponge,DuplexEncodedInputCoverageView)
+
+F0V3BStaticViewSchemaV0(duplex-challenge-transition-view-v0) = Owner(pir.transcript-construction);Tag(DuplexChallengeTransitionView);Body(duplex-sponge-static-view-body-v0)
+  Description = FamilyViewDescriptionV0(duplex-sponge,DuplexChallengeTransitionView)
+
+F0V3BStaticViewSchemaV0(duplex-fs-construction-view-v0) = Owner(pir.checked-duplex-fs-construction);Tag(DuplexFSConstructionView);Body(duplex-sponge-static-view-body-v0)
+  Description = FamilyViewDescriptionV0(duplex-sponge,DuplexFSConstructionView)
+```
+
+The exact finite descriptions named above are the following closed source.
+
+<!-- f0v3b-schema-json:start -->
+```json
+{
+  "body_compilers": [
+    "algorithm-ref-body-v0",
+    "binding-ref-body-v0",
+    "canonical-value-body-v0",
+    "challenge-ref-body-v0",
+    "core-id-body-v0",
+    "evaluation-contract-id-body-v0",
+    "occurrence-kind-body-v0",
+    "occurrence-ref-body-v0",
+    "protocol-id-body-v0",
+    "transcript-construction-id-body-v0",
+    "value-ref-body-v0",
+    "value-type-body-v0"
+  ],
+  "definitions": {
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
+    "BindingProjection": {
+      "record": [
+        [
+          0,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "BindingRef"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          1,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-source-views-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ]
+      ]
+    },
+    "BindingRef": {
+      "atom": {
+        "compiler": "binding-ref-body-v0",
+        "kind": "canonical-body"
+      }
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
+    "CanonicalValue": {
+      "atom": {
+        "compiler": "canonical-value-body-v0",
+        "kind": "canonical-body"
+      }
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
+    "ConstructionMaterialMap": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "MaterialCoordinate"
+          }
+        ],
+        [
+          1,
+          {
+            "ref": "MaterialSchema"
+          }
+        ]
+      ]
+    },
+    "CoreId": {
+      "atom": {
+        "compiler": "core-id-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "CoverageAtom": {
+      "variant": [
+        [
+          0,
+          {
+            "ref": "BindingRef"
+          }
+        ],
+        [
+          1,
+          {
+            "ref": "MaterialCoordinate"
+          }
+        ],
+        [
+          2,
+          {
+            "ref": "OccurrenceRef"
+          }
+        ],
+        [
+          3,
+          {
+            "ref": "ChallengeRef"
+          }
+        ]
+      ]
+    },
+    "CoverageEntry": {
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
+                "ref": "CoverageAtom"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ]
+      ]
+    },
+    "DecoderMapEntry": {
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
+        ],
+        [
+          2,
+          {
+            "ref": "AlgorithmUse"
+          }
+        ]
+      ]
+    },
+    "DuplexChallengeTransitionViewBody": {
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
+              "discipline": "ordered",
+              "element": {
+                "ref": "DecoderMapEntry"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          3,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-admission-and-execution-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ],
+        [
+          4,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-state-transition-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ],
+        [
+          5,
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
+          6,
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
+          7,
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
+          8,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "ChallengeRef"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          9,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "ChallengeRef"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          10,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "SqueezeProjection"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ]
+      ]
+    },
+    "DuplexEncodedInputCoverageViewBody": {
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
+              "discipline": "ordered",
+              "element": {
+                "ref": "BindingRef"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          3,
+          {
+            "ref": "MaterialCoordinate"
+          }
+        ],
+        [
+          4,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "CoverageEntry"
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
+                "ref": "OccurrenceRef"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          6,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "ChallengeRef"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          7,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-source-views-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ],
+        [
+          8,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-source-views-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ],
+        [
+          9,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "CoverageAtom"
+              },
+              "max": 16,
+              "min": 0
+            }
+          }
+        ]
+      ]
+    },
+    "DuplexFSConstructionViewBody": {
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
+          5,
+          {
+            "ref": "OccurrenceMap"
+          }
+        ],
+        [
+          6,
+          {
+            "ref": "ValueMap"
+          }
+        ],
+        [
+          7,
+          {
+            "ref": "ChallengeMap"
+          }
+        ],
+        [
+          8,
+          {
+            "ref": "InstanceProjection"
+          }
+        ],
+        [
+          9,
+          {
+            "ref": "ConstructionMaterialMap"
+          }
+        ],
+        [
+          10,
+          {
+            "ref": "ScheduleCorrespondence"
+          }
+        ],
+        [
+          11,
+          {
+            "ref": "ScheduleCorrespondence"
+          }
+        ],
+        [
+          12,
+          {
+            "ref": "DuplexResultConclusion"
+          }
+        ]
+      ]
+    },
+    "DuplexResultConclusion": {
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
+              "law": "duplex-sponge:duplex-sponge-admission-and-execution-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ]
+      ]
+    },
+    "DuplexTranscriptDeclarationViewBody": {
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
+              "kind": "natural",
+              "max": 4294967295
+            }
+          }
+        ],
+        [
+          6,
+          {
+            "atom": {
+              "kind": "natural",
+              "max": 4294967295
+            }
+          }
+        ],
+        [
+          7,
+          {
+            "ref": "StateCarrier"
+          }
+        ],
+        [
+          8,
+          {
+            "ref": "InstanceCarrier"
+          }
+        ],
+        [
+          9,
+          {
+            "ref": "BindingProjection"
+          }
+        ],
+        [
+          10,
+          {
+            "ref": "AlgorithmUse"
+          }
+        ],
+        [
+          11,
+          {
+            "ref": "AlgorithmUse"
+          }
+        ],
+        [
+          12,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-state-transition-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ],
+        [
+          13,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-state-transition-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ],
+        [
+          14,
+          {
+            "ref": "MaterialSchema"
+          }
+        ],
+        [
+          15,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "MessageCodecEntry"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          16,
+          {
+            "record": [
+              [
+                0,
+                {
+                  "sequence": {
+                    "discipline": "ordered",
+                    "element": {
+                      "record": [
+                        [
+                          0,
+                          {
+                            "ref": "OccurrenceRef"
+                          }
+                        ],
+                        [
+                          1,
+                          {
+                            "ref": "ValueType"
+                          }
+                        ]
+                      ]
+                    },
+                    "max": 512,
+                    "min": 0
+                  }
+                }
+              ],
+              [
+                1,
+                {
+                  "sequence": {
+                    "discipline": "ordered",
+                    "element": {
+                      "record": [
+                        [
+                          0,
+                          {
+                            "ref": "ChallengeRef"
+                          }
+                        ],
+                        [
+                          1,
+                          {
+                            "ref": "ValueType"
+                          }
+                        ]
+                      ]
+                    },
+                    "max": 512,
+                    "min": 0
+                  }
+                }
+              ]
+            ]
+          }
+        ],
+        [
+          17,
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
+        ],
+        [
+          18,
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
+        ],
+        [
+          19,
+          {
+            "ref": "ResourceProjection"
+          }
+        ]
+      ]
+    },
+    "EvaluationContractId": {
+      "atom": {
+        "compiler": "evaluation-contract-id-body-v0",
+        "kind": "canonical-body"
+      }
+    },
+    "InstanceCarrier": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "ValueType"
+          }
+        ],
+        [
+          1,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-body-grammar-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ]
+      ]
+    },
+    "InstanceProjection": {
+      "record": [
+        [
+          0,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "BindingRef"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          1,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-source-views-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ]
+      ]
+    },
+    "MaterialCoordinate": {
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
+              ],
+              [
+                1,
+                {
+                  "ref": "OccurrenceRef"
+                }
+              ],
+              [
+                2,
+                {
+                  "ref": "ChallengeRef"
+                }
+              ]
+            ]
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
+    "MaterialSchema": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "MaterialCoordinate"
+          }
+        ],
+        [
+          1,
+          {
+            "ref": "ValueType"
+          }
+        ],
+        [
+          2,
+          {
+            "atom": {
+              "kind": "natural",
+              "max": 4294967295
+            }
+          }
+        ]
+      ]
+    },
+    "MessageCodecEntry": {
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
+            "ref": "AlgorithmUse"
+          }
+        ],
+        [
+          2,
+          {
+            "atom": {
+              "kind": "natural",
+              "max": 4294967295
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
+    "ResourceProjection": {
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
+            "atom": {
+              "kind": "natural",
+              "max": 4294967295
+            }
+          }
+        ],
+        [
+          2,
+          {
+            "atom": {
+              "kind": "natural",
+              "max": 4294967295
+            }
+          }
+        ]
+      ]
+    },
+    "ScheduleCorrespondence": {
+      "record": [
+        [
+          0,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "ChallengeRef"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          1,
+          {
+            "sequence": {
+              "discipline": "ordered",
+              "element": {
+                "ref": "ChallengeRef"
+              },
+              "max": 512,
+              "min": 0
+            }
+          }
+        ],
+        [
+          2,
+          {
+            "ref": "ChallengeMap"
+          }
+        ],
+        [
+          3,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-downstream-boundary-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ]
+      ]
+    },
+    "SqueezeProjection": {
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
+            "ref": "OccurrenceRef"
+          }
+        ],
+        [
+          2,
+          {
+            "atom": {
+              "kind": "natural",
+              "max": 4294967295
+            }
+          }
+        ]
+      ]
+    },
+    "StateCarrier": {
+      "record": [
+        [
+          0,
+          {
+            "ref": "ValueType"
+          }
+        ],
+        [
+          1,
+          {
+            "atom": {
+              "kind": "exact-profile-law",
+              "law": "duplex-sponge:duplex-sponge-state-transition-v0",
+              "profile": "duplex-sponge"
+            }
+          }
+        ]
+      ]
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
+  "family": "duplex-sponge",
+  "format": "zkc.f0v3b.proposed-family-view-schema.v0",
+  "laws": [
+    "duplex-sponge:duplex-sponge-admission-and-execution-v0",
+    "duplex-sponge:duplex-sponge-body-grammar-v0",
+    "duplex-sponge:duplex-sponge-downstream-boundary-v0",
+    "duplex-sponge:duplex-sponge-source-views-v0",
+    "duplex-sponge:duplex-sponge-state-transition-v0"
+  ],
+  "maximum_sequence_length": 512,
+  "views": {
+    "DuplexChallengeTransitionView": {
+      "owner_subject_kind": "pir.transcript-construction",
+      "schema": {
+        "ref": "DuplexChallengeTransitionViewBody"
+      }
+    },
+    "DuplexEncodedInputCoverageView": {
+      "owner_subject_kind": "pir.transcript-construction",
+      "schema": {
+        "ref": "DuplexEncodedInputCoverageViewBody"
+      }
+    },
+    "DuplexFSConstructionView": {
+      "owner_subject_kind": "pir.checked-duplex-fs-construction",
+      "schema": {
+        "ref": "DuplexFSConstructionViewBody"
+      }
+    },
+    "DuplexTranscriptDeclarationView": {
+      "owner_subject_kind": "pir.transcript-construction",
+      "schema": {
+        "ref": "DuplexTranscriptDeclarationViewBody"
+      }
+    }
+  }
+}
+```
+<!-- f0v3b-schema-json:end -->
+
 <!-- zkc-profile-source:duplex-sponge-fs-semantics:end -->
 
 ## 12. Analysis and theorem boundary
@@ -1146,4 +2366,14 @@
 `PIRDuplexSpongeFSProfile` and every dependent duplex subject. It does not
 reinterpret or rotate an unreferenced canonical-framed subject.
 
+### Candidate finite FS-family static-view body compiler
+
+```text
+DuplexSpongeStaticViewBodyV0(schema,value) =
+  require schema is the exact profile-local finite description selected by the view kind;
+  require value is accepted by that closed Atom/Record/Variant/bounded-Sequence description;
+  return StaticViewBodyV0(schema,value) from the Interaction finite-description compiler;
+  refuse a value carrying an extra owner-local coordinate, including result_ref bytes.
+```
+
 <!-- zkc-profile-source:duplex-sponge-fs-body-grammar:end -->
<!-- f0v3b-page-diff:end -->
