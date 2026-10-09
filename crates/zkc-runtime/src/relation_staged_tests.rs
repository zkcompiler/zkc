//! Staged assignments and the staged predicate over the shared bundle fixture.
use super::*;

const KB: &str = "koala-bear";
const EXT: &str = "koala-bear.ext8-binomial3";
/// Replaced by the identity of the staged program the assignment is read with.
const PROGRAM: &str = "staged-program-identity";

/// Two phases over the shared fixture. Phase 1 draws `alpha` and commits
/// `z = x + alpha` on cpu and `w(r) = values(r + 1)` on the cyclic rom; the
/// claim `total` is the cpu sum below. Phase 2 draws an extension challenge
/// `beta` and commits `acc(r + 1) = acc(r) + z(r) * alpha` with `acc(0) = 0`;
/// its claim `gamma` must equal `beta^2`. Both premises on phase-1 outputs are
/// false for the honest assignment: they are recorded, never checked.
fn program() -> String {
    let empty = || json!([[], ["zkc.ring/0", [], [], []], [], []]);
    let one = json!([
        [["alpha", KB]],
        [["total", KB]],
        [
            [
                [["z", KB, 1]],
                [
                    "zkc.ring/0",
                    [KB, KB, KB],
                    [
                        ["input", 0],
                        ["input", 1],
                        ["input", 2],
                        ["add", 1, 2],
                        ["neg", 3],
                        ["add", 0, 4]
                    ],
                    [5]
                ],
                [
                    ["read", 1, 0, "0", 0],
                    ["read", 0, 0, "0", 0],
                    ["challenge", 1, 0]
                ],
                [[0, ["all"]]]
            ],
            [
                [["w", KB, 1]],
                [
                    "zkc.ring/0",
                    [KB, KB],
                    [["input", 0], ["input", 1], ["neg", 1], ["add", 0, 2]],
                    [3, 0]
                ],
                [["read", 1, 0, "0", 0], ["read", 0, 0, "1", 0]],
                [[0, ["all"]]]
            ],
            empty()
        ]
    ]);
    let two = json!([
        [["beta", EXT]],
        [["gamma", EXT]],
        [
            [
                [["acc", KB, 1]],
                [
                    "zkc.ring/0",
                    [KB, KB, KB, KB],
                    [
                        ["input", 0],
                        ["input", 1],
                        ["input", 2],
                        ["input", 3],
                        ["mul", 2, 3],
                        ["add", 1, 4],
                        ["neg", 5],
                        ["add", 0, 6]
                    ],
                    [7, 1]
                ],
                [
                    ["read", 2, 0, "1", 0],
                    ["read", 2, 0, "0", 0],
                    ["read", 1, 0, "0", 0],
                    ["challenge", 1, 0]
                ],
                [[0, ["interior", 0, 1]], [1, ["first"]]]
            ],
            empty(),
            empty()
        ]
    ]);
    let global = json!([
        [
            "zkc.ring/0",
            [KB, EXT, EXT],
            [
                ["input", 0],
                ["constant", KB, "95"],
                ["neg", 1],
                ["add", 0, 2],
                ["input", 1],
                ["mul", 4, 4],
                ["neg", 5],
                ["input", 2],
                ["add", 7, 6]
            ],
            [3, 8]
        ],
        [["claim", 1, 0], ["challenge", 2, 0], ["claim", 2, 0]],
        [0, 1]
    ]);
    json!([
        "zkc.relation-staged/0",
        IDENTITY,
        [one, two],
        global,
        [
            ["characteristic-exceeds", KB, 64],
            ["nonzero", 1, 0, 0, ["all"]],
            ["boolean", 1, 1, 1, ["all"]]
        ]
    ])
    .to_string()
}
// alpha = 5, x = [0, 1, 3, 6], rom values 0..7, beta = X^4, beta^2 = 3.
const PHASE_ONE: &str =
    r#"[["5"],["95"],[[["5","6","8","11"]],[["1","2","3","4","5","6","7","0"]],[]]]"#;
const PHASE_TWO: &str = r#"[[["0","0","0","0","1","0","0","0"]],[["3","0","0","0","0","0","0","0"]],[[["0","25","55","95"]],[],[]]]"#;
fn assignment() -> String {
    format!(r#"["zkc.relation-staged-assignment/0","{PROGRAM}",[{PHASE_ONE},{PHASE_TWO}]]"#)
}

fn data(text: &str) -> Result<Value> {
    parse_json(
        text,
        DATA_BYTE_LIMIT,
        "bundle-data-schema",
        "bundle-data-limit",
    )
}
struct Fixture {
    bundle: Bundle,
    config: Configuration,
    instance: Instance,
    witness: Witness,
    staged: Staged,
    assignment: StagedAssignment,
}
/// Carriers: bundle, configuration, instance, witness, staged program and
/// assignment. Carriers name the parsed bundle and program identities.
fn fixture(texts: &[String; 6]) -> Result<Fixture> {
    let bundle = Bundle::parse(&texts[0])?;
    let named: Vec<String> = texts[1..]
        .iter()
        .map(|t| t.replace(IDENTITY, bundle.identity()))
        .collect();
    let config = bundle.decode_configuration(&data(&named[0])?)?;
    let instance = bundle.decode_instance(&data(&named[1])?)?;
    let witness = bundle.decode_witness(&data(&named[2])?)?;
    let staged = Staged::parse(&bundle, &named[3])?;
    let assignment =
        staged.decode_assignment(&data(&named[4].replace(PROGRAM, staged.identity()))?)?;
    Ok(Fixture {
        bundle,
        config,
        instance,
        witness,
        staged,
        assignment,
    })
}
fn texts() -> [String; 6] {
    [
        BUNDLE.into(),
        CONFIG.into(),
        INSTANCE.into(),
        WITNESS.into(),
        program(),
        assignment(),
    ]
}
fn honest() -> Fixture {
    fixture(&texts()).unwrap()
}
impl Fixture {
    fn evaluate(&self) -> Result<StagedEvaluation> {
        self.staged.evaluate(
            &self.bundle,
            &self.config,
            &self.instance,
            &self.witness,
            &self.assignment,
            &Reference,
        )
    }
}

/// One textual edit per entry: carrier index into [`texts`], the original
/// text and its replacement. The outcome is a refusal identifier,
/// "satisfied" or "unsatisfied".
const MUTATIONS: &[(&str, &[Edit], &str)] = &[
    ("honest", &[], "satisfied"),
    (
        "staged group value",
        &[(5, r#""5","6","8","11""#, r#""5","6","9","11""#)],
        "unsatisfied",
    ),
    (
        "received claim",
        &[(5, r#"["95"]"#, r#"["94"]"#)],
        "unsatisfied",
    ),
    (
        "extension claim",
        &[(
            5,
            r#"[["3","0","0","0","0","0","0","0"]]"#,
            r#"[["3","1","0","0","0","0","0","0"]]"#,
        )],
        "unsatisfied",
    ),
    (
        "cyclic wraparound",
        &[(5, r#""7","0"]]"#, r#""7","8"]]"#)],
        "unsatisfied",
    ),
    (
        "another challenge with the same columns",
        &[(5, r#"[["5"],"#, r#"[["6"],"#)],
        "unsatisfied",
    ),
    (
        "unsatisfied bundle, unread table",
        &[(3, r#""6","9""#, r#""6","8""#)],
        "satisfied",
    ),
    (
        "base admission precedes the staged program",
        &[
            (2, r#"["present",4,[["1","2","3","9"]]]"#, r#"["absent"]"#),
            (
                5,
                PROGRAM,
                "0000000000000000000000000000000000000000000000000000000000000000",
            ),
        ],
        "bundle-table-missing",
    ),
    (
        "assignment for another program",
        &[(
            5,
            PROGRAM,
            "0000000000000000000000000000000000000000000000000000000000000000",
        )],
        "staged-program",
    ),
    (
        "assignment tag",
        &[(
            5,
            "zkc.relation-staged-assignment/0",
            "zkc.relation-staged-assignment/1",
        )],
        "staged-data-schema",
    ),
    (
        "assignment phase count",
        &[(
            5,
            r#",[[["0","0","0","0","1","0","0","0"]],[["3","0","0","0","0","0","0","0"]],[[["0","25","55","95"]],[],[]]]"#,
            "",
        )],
        "staged-data-schema",
    ),
    (
        "assignment table count",
        &[(
            5,
            r#"[[["0","25","55","95"]],[],[]]"#,
            r#"[[["0","25","55","95"]],[]]"#,
        )],
        "staged-data-schema",
    ),
    (
        "challenge count",
        &[(5, r#"[["5"],["95"]"#, r#"[["5","5"],["95"]"#)],
        "staged-slot-shape",
    ),
    (
        "extension challenge as one coordinate",
        &[(5, r#"[["0","0","0","0","1","0","0","0"]]"#, r#"["0"]"#)],
        "bundle-value",
    ),
    (
        "noncanonical challenge",
        &[(5, r#"[["5"],"#, r#"[["05"],"#)],
        "bundle-value",
    ),
    (
        "staged value at the characteristic",
        &[(5, r#""5","6","8","11""#, r#""5","6","8","2130706433""#)],
        "bundle-value",
    ),
    (
        "no staged data for a present table",
        &[(5, r#"[[["5","6","8","11"]],"#, "[null,")],
        "staged-presence",
    ),
    (
        "staged data for an absent table",
        &[
            (2, r#"["present",4,[]]]"#, r#"["absent"]]"#),
            (3, r#",[["3","3","0","1","6","9","1","2"]]]"#, ",null]"),
        ],
        "staged-presence",
    ),
    (
        "absent table in every phase",
        &[
            (2, r#"["present",4,[]]]"#, r#"["absent"]]"#),
            (3, r#",[["3","3","0","1","6","9","1","2"]]]"#, ",null]"),
            (5, r#""7","0"]],[]]]"#, r#""7","0"]],null]]"#),
            (5, r#""95"]],[],[]]]"#, r#""95"]],[],null]]"#),
        ],
        "satisfied",
    ),
    (
        "staged group count",
        &[(5, r#"[["5","6","8","11"]]"#, r#"[["5","6","8","11"],[]]"#)],
        "bundle-group-count",
    ),
    (
        "staged group not a list",
        &[(5, r#"[["5","6","8","11"]]"#, r#"["5"]"#)],
        "bundle-data-shape",
    ),
    (
        "staged group length",
        &[(5, r#""5","6","8","11""#, r#""5","6","8""#)],
        "bundle-group-shape",
    ),
    (
        "finite window at the admitted height",
        &[(4, r#"["interior",0,1]"#, r#"["interval",0,4]"#)],
        "bundle-window",
    ),
    (
        "interval beyond the table",
        &[(4, r#"["interior",0,1]"#, r#"["interval",0,5]"#)],
        "bundle-scope-height",
    ),
    (
        "finite window undefined at every height",
        &[(4, r#"["interior",0,1]"#, r#"["all"]"#)],
        "bundle-window",
    ),
    (
        "phase one reads a phase-two group",
        &[(4, r#"["read",1,0,"0",0]"#, r#"["read",2,0,"0",0]"#)],
        "staged-phase-order",
    ),
    (
        "phase one uses a phase-two challenge",
        &[(4, r#"["challenge",1,0]"#, r#"["challenge",2,0]"#)],
        "staged-phase-order",
    ),
    (
        "global claim of a later phase",
        &[(4, r#"["claim",2,0]"#, r#"["claim",3,0]"#)],
        "staged-phase-order",
    ),
    (
        "global read",
        &[(
            4,
            r#"[["claim",1,0],["challenge",2,0]"#,
            r#"[["read",0,0,"0",0],["challenge",2,0]"#,
        )],
        "staged-global-read",
    ),
    (
        "premise on a missing output",
        &[(
            4,
            r#"["nonzero",1,0,0,["all"]]"#,
            r#"["nonzero",1,0,5,["all"]]"#,
        )],
        "staged-premise",
    ),
    (
        "program for another bundle",
        &[(
            4,
            IDENTITY,
            "0000000000000000000000000000000000000000000000000000000000000000",
        )],
        "bundle-relation",
    ),
    (
        "program tag",
        &[(4, "zkc.relation-staged/0", "zkc.relation-staged/1")],
        "staged-schema",
    ),
    (
        "staged group reuses a base group name",
        &[(4, r#"[["z","koala-bear",1]]"#, r#"[["x","koala-bear",1]]"#)],
        "bundle-duplicate-name",
    ),
];

fn outcome(texts: &[String; 6]) -> String {
    match fixture(texts).and_then(|f| f.evaluate()) {
        Ok(e) if e.satisfied => "satisfied".into(),
        Ok(_) => "unsatisfied".into(),
        Err(e) => e.0.into(),
    }
}

#[test]
fn staged_assignment_mutations() {
    let mut refusals = BTreeSet::new();
    for (name, edits, expected) in MUTATIONS {
        let mut texts = texts();
        for (carrier, from, to) in *edits {
            assert!(
                texts[*carrier].contains(from),
                "{name}: fixture lacks {from}"
            );
            texts[*carrier] = texts[*carrier].replacen(from, to, 1);
        }
        assert_eq!(outcome(&texts), *expected, "{name}");
        if !["satisfied", "unsatisfied"].contains(expected) {
            refusals.insert(*expected);
        }
    }
    assert_eq!(
        refusals.into_iter().collect::<Vec<_>>(),
        [
            "bundle-data-shape",
            "bundle-duplicate-name",
            "bundle-group-count",
            "bundle-group-shape",
            "bundle-relation",
            "bundle-scope-height",
            "bundle-table-missing",
            "bundle-value",
            "bundle-window",
            "staged-data-schema",
            "staged-global-read",
            "staged-phase-order",
            "staged-premise",
            "staged-presence",
            "staged-program",
            "staged-schema",
            "staged-slot-shape",
        ],
        "refusal identifiers asserted by the mutation table"
    );
}

#[test]
fn honest_staged_evaluation_details() {
    let f = honest();
    assert_eq!(
        f.staged.encode().to_string(),
        program(),
        "canonical program"
    );
    let text = assignment().replace(PROGRAM, f.staged.identity());
    assert_eq!(
        f.staged.encode_assignment(&f.assignment).to_string(),
        text,
        "canonical assignment"
    );
    let e = f.evaluate().unwrap();
    assert!(e.satisfied);
    // Phase 1: cpu over 4 rows and the cyclic rom over 8. Phase 2: the cpu
    // transition over 3 rows, then its first row. Ordered by phase, table,
    // assertion and row.
    let order: Vec<_> = e
        .residuals
        .iter()
        .map(|r| (r.phase, r.table, r.assertion, r.row))
        .collect();
    let mut expected: Vec<_> = (0..4).map(|r| (1, 0, 0, r)).collect();
    expected.extend((0..8).map(|r| (1, 1, 0, r)));
    expected.extend((0..3).map(|r| (2, 0, 0, r)));
    expected.push((2, 0, 1, 0));
    assert_eq!(order, expected);
    assert!(e.residuals.iter().all(|r| r.value == ["0"]));
    assert_eq!(e.global, [vec!["0".to_string()], vec!["0".to_string(); 8]]);
    // Staged tables only: 4 * (6 + 3 + 1 + 1) + 8 * (4 + 2 + 1 + 1)
    // + 4 * (8 + 4 + 2 + 1).
    assert_eq!(e.work, 168);
    // The bundle relation is a separate subject over the same data.
    assert!(
        f.bundle
            .evaluate(&f.config, &f.instance, &f.witness, &Reference)
            .unwrap()
            .satisfied
    );

    // Received values are checked as sent: total - 95 and gamma - beta^2.
    let mut claim = f.assignment.clone();
    claim.phases[0].claims[0] = vec!["94".into()];
    claim.phases[1].claims[0][1] = "1".into();
    let e = Fixture {
        assignment: claim,
        ..honest()
    }
    .evaluate()
    .unwrap();
    assert!(!e.satisfied);
    let mut gamma = vec!["0".to_string(); 8];
    gamma[1] = "1".into();
    assert_eq!(e.global, [vec!["2130706432".to_string()], gamma]);

    // A changed z row is a nonzero phase-1 residual and changes the phase-2
    // transition that reads it.
    let mut row = f.assignment.clone();
    row.phases[0].tables[0].as_mut().unwrap()[0][2] = "9".into();
    let e = Fixture {
        assignment: row,
        ..honest()
    }
    .evaluate()
    .unwrap();
    let failing: Vec<_> = e
        .residuals
        .iter()
        .filter(|r| r.value != ["0"])
        .map(|r| (r.phase, r.table, r.assertion, r.row, r.value[0].as_str()))
        .collect();
    assert_eq!(failing, [(1, 0, 0, 2, "1"), (2, 0, 0, 2, "2130706428")]);
}

#[test]
fn staged_assignment_shape_refusals() {
    let f = honest();
    let refuse = |assignment: StagedAssignment| {
        Fixture {
            assignment,
            ..honest()
        }
        .evaluate()
        .unwrap_err()
    };
    let mut slots = f.assignment.clone();
    slots.phases[1].challenges.push(vec!["1".into()]);
    assert_eq!(refuse(slots), Error("staged-slot-shape"));
    let mut claims = f.assignment.clone();
    claims.phases[0].claims.clear();
    assert_eq!(refuse(claims), Error("staged-slot-shape"));
    let mut phases = f.assignment.clone();
    phases.phases.pop();
    assert_eq!(refuse(phases), Error("staged-data-shape"));
    let mut tables = f.assignment.clone();
    tables.phases[1].tables.pop();
    assert_eq!(refuse(tables), Error("staged-data-shape"));
    // Group shape is compared with the admitted height before values.
    let mut short = f.assignment.clone();
    short.phases[1].tables[0].as_mut().unwrap()[0].pop();
    short.phases[0].challenges[0] = vec!["x".into()];
    assert_eq!(refuse(short), Error("bundle-group-shape"));
    let mut coordinates = f.assignment.clone();
    coordinates.phases[1].challenges[0].pop();
    assert_eq!(refuse(coordinates), Error("bundle-value"));
    // A staged program is read against the bundle it names.
    let other = Bundle::parse(&BUNDLE.replacen(r#"["start","#, r#"["begin","#, 1)).unwrap();
    assert_eq!(
        f.staged
            .evaluate(
                &other,
                &f.config,
                &f.instance,
                &f.witness,
                &f.assignment,
                &Reference
            )
            .unwrap_err(),
        Error("bundle-relation")
    );
}

fn power(mut base: u64, mut exponent: u64) -> u64 {
    let mut result = 1u64;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = ((u128::from(result) * u128::from(base)) % u128::from(P)) as u64;
        }
        base = ((u128::from(base) * u128::from(base)) % u128::from(P)) as u64;
        exponent >>= 1;
    }
    result
}
/// A logarithmic-derivative lookup argument for the fixture's range lookup:
/// phase 1 draws `alpha`, commits per-row inverses and running sums on cpu and
/// rom, and receives both table sums as claims, which must cancel. The
/// denominators carry recorded nonzero premises.
fn lookup_program() -> String {
    let table = |rom: bool| {
        let mut inputs = vec![
            json!(["challenge", 1, 0]),
            json!(["read", 0, 0, "0", 0]),
            json!(["read", 1, 0, "0", 0]),
            json!(["read", 1, 1, "0", 0]),
            json!(["read", 1, 1, "1", 0]),
            json!(["read", 1, 0, "1", 0]),
            json!(["claim", 1, u32::from(rom)]),
        ];
        let mut nodes: Vec<Value> = (0..7).map(|i| json!(["input", i])).collect();
        // 7: -entry, 8: alpha - entry, 9: inverse * (alpha - entry).
        nodes.extend([
            json!(["neg", 1]),
            json!(["add", 0, 7]),
            json!(["mul", 2, 8]),
        ]);
        if rom {
            // inverse * (alpha - value) + multiplicity = 0.
            inputs.push(json!(["read", 0, 1, "0", 0]));
            nodes.push(json!(["input", 7]));
        } else {
            // inverse * (alpha - x) - 1 = 0.
            nodes.extend([json!(["constant", KB, "1"]), json!(["neg", 10])]);
        }
        let numerator = nodes.len() - 1;
        let term = nodes.len();
        nodes.push(json!(["add", 9, numerator]));
        // acc - inverse, acc' - (acc + inverse'), acc - claim.
        nodes.extend([json!(["neg", 2]), json!(["add", 3, term + 1])]);
        nodes.extend([
            json!(["add", 3, 5]),
            json!(["neg", term + 3]),
            json!(["add", 4, term + 4]),
        ]);
        nodes.extend([json!(["neg", 6]), json!(["add", 3, term + 6])]);
        json!([
            [["inverse", KB, 1], ["sum", KB, 1]],
            [
                "zkc.ring/0",
                vec![KB; inputs.len()],
                nodes,
                [term, term + 2, term + 5, term + 7, 8]
            ],
            inputs,
            [
                [0, ["all"]],
                [1, ["first"]],
                [2, ["interior", 0, 1]],
                [3, ["last"]]
            ]
        ])
    };
    json!([
        "zkc.relation-staged/0",
        IDENTITY,
        [[
            [["alpha", KB]],
            [["cpu_sum", KB], ["rom_sum", KB]],
            [
                table(false),
                table(true),
                [[], ["zkc.ring/0", [], [], []], [], []]
            ]
        ]],
        [
            [
                "zkc.ring/0",
                [KB, KB],
                [["input", 0], ["input", 1], ["add", 0, 1]],
                [2]
            ],
            [["claim", 1, 0], ["claim", 1, 1]],
            [0]
        ],
        [
            ["nonzero", 1, 0, 4, ["all"]],
            ["nonzero", 1, 1, 4, ["all"]],
            ["characteristic-exceeds", KB, 64]
        ]
    ])
    .to_string()
}
/// Inverses and running sums for `alpha` over cpu `x` and rom `values` with
/// `multiplicity`. A zero denominator gets inverse 0.
fn lookup_assignment(
    staged: &Staged,
    alpha: u64,
    x: &[u64],
    multiplicity: &[u64],
) -> StagedAssignment {
    let rows = |entries: &[u64], weights: Option<&[u64]>| {
        let (mut inverse, mut sum, mut total) = (vec![], vec![], 0u64);
        for (i, v) in entries.iter().enumerate() {
            let numerator = weights.map_or(1, |w| (P - w[i]) % P);
            let term = (u128::from(numerator) * u128::from(power((alpha + P - v) % P, P - 2))
                % u128::from(P)) as u64;
            total = (total + term) % P;
            inverse.push(term.to_string());
            sum.push(total.to_string());
        }
        (vec![inverse, sum], total)
    };
    let (cpu, cpu_total) = rows(x, None);
    let (rom, rom_total) = rows(&(0..8).collect::<Vec<_>>(), Some(multiplicity));
    StagedAssignment {
        program: staged.identity().into(),
        phases: vec![StagedPhaseAssignment {
            challenges: vec![vec![alpha.to_string()]],
            claims: vec![vec![cpu_total.to_string()], vec![rom_total.to_string()]],
            tables: vec![Some(cpu), Some(rom), Some(vec![])],
        }],
    }
}

#[test]
fn lookup_predicate_is_indexed_by_actual_challenges() {
    let f = honest();
    let staged = Staged::parse(&f.bundle, &lookup_program()).unwrap();
    let x = [0, 1, 3, 6];
    let multiplicity = [1, 1, 0, 1, 0, 0, 1, 0];
    let evaluate = |witness: &Witness, assignment: &StagedAssignment| {
        staged
            .evaluate(
                &f.bundle,
                &f.config,
                &f.instance,
                witness,
                assignment,
                &Reference,
            )
            .unwrap()
    };
    let balanced = lookup_assignment(&staged, 1000, &x, &multiplicity);
    let e = evaluate(&f.witness, &balanced);
    assert!(e.satisfied && e.global == [vec!["0".to_string()]]);
    assert_eq!(
        staged
            .decode_assignment(&staged.encode_assignment(&balanced))
            .unwrap(),
        balanced,
        "assignment codec round trip"
    );
    // The same committed columns do not satisfy the predicate for another
    // challenge; columns recomputed for that challenge do.
    let mut other = balanced.clone();
    other.phases[0].challenges[0] = vec!["1001".into()];
    assert!(!evaluate(&f.witness, &other).satisfied);
    assert!(
        evaluate(
            &f.witness,
            &lookup_assignment(&staged, 1001, &x, &multiplicity)
        )
        .satisfied
    );
    // A challenge that zeroes a denominator falsifies a recorded premise.
    // The predicate is still evaluated as stated, and no inverse exists.
    let zero = evaluate(
        &f.witness,
        &lookup_assignment(&staged, 3, &x, &multiplicity),
    );
    assert!(!zero.satisfied);
    assert!(
        zero.residuals
            .iter()
            .any(|r| (r.table, r.assertion, r.row) == (0, 0, 2) && r.value != ["0"])
    );
    // An unbalanced lookup is unsatisfied as a bundle, and its honestly
    // computed claims do not cancel.
    let unbalanced = [1, 1, 0, 1, 0, 0, 0, 1];
    let mut witness = f.witness.clone();
    witness.tables[1] = Some(vec![unbalanced.iter().map(u64::to_string).collect()]);
    assert!(
        !f.bundle
            .evaluate(&f.config, &f.instance, &witness, &Reference)
            .unwrap()
            .satisfied
    );
    let e = evaluate(&witness, &lookup_assignment(&staged, 1000, &x, &unbalanced));
    assert!(!e.satisfied && e.residuals.iter().all(|r| r.value == ["0"]));
}

/// One required finite table with an instance height up to 2^20 and no base
/// groups or checks, and a one-phase program whose table assertions read the
/// challenge only. Global assertions check the claim `claims` times.
fn resource_case(
    challenge: &str,
    assertions: usize,
    extra_nodes: usize,
    group_width: Option<u32>,
    claims: usize,
) -> (Bundle, Staged) {
    let bundle = Bundle::parse(
        &json!([
            "zkc.relation-bundle/0",
            [],
            [],
            [[
                "t",
                "required",
                ["instance", 1, 1 << 20, false],
                "finite",
                [],
                ["zkc.ring/0", [], [], []],
                [],
                [],
                []
            ]]
        ])
        .to_string(),
    )
    .unwrap();
    let (mut fields, mut inputs) = (vec![challenge], vec![json!(["challenge", 1, 0])]);
    let mut nodes = vec![json!(["input", 0])];
    let groups = match group_width {
        Some(width) => {
            fields.push(KB);
            inputs.push(json!(["read", 1, 0, "0", 0]));
            nodes.extend([json!(["input", 1]), json!(["add", 0, 1])]);
            json!([["g", KB, width]])
        }
        None => json!([]),
    };
    for _ in 0..extra_nodes {
        let last = nodes.len() - 1;
        nodes.push(json!(["add", last, last]));
    }
    let outputs = [nodes.len() - 1];
    let checks: Vec<_> = (0..assertions).map(|_| json!([0, ["all"]])).collect();
    let global = if claims == 0 {
        json!([["zkc.ring/0", [], [], []], [], []])
    } else {
        json!([
            ["zkc.ring/0", [KB], [["input", 0]], [0]],
            [["claim", 1, 0]],
            vec![0; claims]
        ])
    };
    let claim_slots = if claims == 0 {
        json!([])
    } else {
        json!([["c", KB]])
    };
    let staged = Staged::parse(
        &bundle,
        &json!([
            "zkc.relation-staged/0",
            bundle.identity(),
            [[
                [["alpha", challenge]],
                claim_slots,
                [[
                    groups,
                    ["zkc.ring/0", fields, nodes, outputs],
                    inputs,
                    checks
                ]]
            ]],
            global,
            []
        ])
        .to_string(),
    )
    .unwrap();
    (bundle, staged)
}
/// Evaluate at `height` without any staged group values and with noncanonical
/// challenges, so every accepted preflight ends at `bundle-value`.
fn resource_refusal(case: &(Bundle, Staged), height: u32) -> Error {
    let (bundle, staged) = case;
    let id = bundle.identity().to_string();
    let config = Configuration {
        relation: id.clone(),
        tables: vec![(None, vec![])],
    };
    let instance = Instance {
        relation: id.clone(),
        publics: vec![],
        tables: vec![Some((Some(height), vec![]))],
    };
    let witness = Witness {
        relation: id,
        tables: vec![Some(vec![])],
    };
    let assignment = StagedAssignment {
        program: staged.identity().into(),
        phases: staged
            .phases()
            .iter()
            .map(|phase| StagedPhaseAssignment {
                challenges: phase
                    .challenges
                    .iter()
                    .map(|s| vec!["07".into(); degree(s.field).unwrap()])
                    .collect(),
                claims: phase.claims.iter().map(|_| vec!["0".into()]).collect(),
                tables: vec![Some(
                    phase.tables[0].groups.iter().map(|_| vec![]).collect(),
                )],
            })
            .collect(),
    };
    staged
        .evaluate(
            bundle,
            &config,
            &instance,
            &witness,
            &assignment,
            &Reference,
        )
        .unwrap_err()
}

#[test]
fn staged_resources_are_bounded_before_values() {
    let full = 1 << 20;
    // Records: 2^20 active rows per assertion, one per global assertion.
    assert_eq!(
        resource_refusal(&resource_case(KB, 1, 0, None, 0), full),
        Error("bundle-value"),
        "2^20 records are within the limit"
    );
    assert_eq!(
        resource_refusal(&resource_case(KB, 2, 0, None, 0), full),
        Error("bundle-result-limit")
    );
    assert_eq!(
        resource_refusal(&resource_case(KB, 1, 0, None, 1), full - 1),
        Error("bundle-value"),
        "2^20 - 1 rows and one global assertion"
    );
    assert_eq!(
        resource_refusal(&resource_case(KB, 1, 0, None, 2), full - 1),
        Error("bundle-result-limit"),
        "every global assertion is a record"
    );
    // Coordinates: the output field's degree per record.
    assert_eq!(
        resource_refusal(&resource_case(EXT, 1, 0, None, 0), full / 2),
        Error("bundle-value"),
        "2^19 extension records are 2^22 coordinates"
    );
    assert_eq!(
        resource_refusal(&resource_case(EXT, 1, 0, None, 1), full / 2),
        Error("bundle-result-limit")
    );
    assert_eq!(
        resource_refusal(&resource_case(EXT, 1, 0, None, 0), full),
        Error("bundle-result-limit")
    );
    // Work keeps precedence over the result bound.
    assert_eq!(
        resource_refusal(&resource_case(KB, 2, 70, None, 0), full),
        Error("bundle-work-limit")
    );
    // A width-8 staged group at height 2^20 declares 2^23 coordinates; the
    // declared shape refuses before the supplied lengths are compared.
    assert_eq!(
        resource_refusal(&resource_case(KB, 1, 0, Some(8), 0), full),
        Error("bundle-data-limit")
    );
    assert_eq!(
        resource_refusal(&resource_case(KB, 1, 0, Some(4), 0), full),
        Error("bundle-data-limit"),
        "the declared challenge also consumes the coordinate budget"
    );
    assert_eq!(
        resource_refusal(&resource_case(KB, 1, 0, Some(4), 0), full - 1),
        Error("bundle-group-shape")
    );
}

#[test]
fn result_bound_is_checked_in_table_order() {
    // Phase 1 materializes 2^21 records at height 2^20; phase 2 declares a
    // width-8 group, 2^23 coordinates. The result bound is checked after
    // each table, so the earlier table's refusal is reported.
    let (bundle, one) = resource_case(KB, 2, 0, None, 0);
    let mut program = one.encode();
    let (_, two) = resource_case(KB, 1, 0, Some(8), 0);
    let mut later = two.encode()[2][0].clone();
    later[0] = json!([]);
    let text = later.to_string().replace(
        r#"["challenge",1,0],["read",1,0,"0",0]"#,
        r#"["challenge",1,0],["read",2,0,"0",0]"#,
    );
    program[2]
        .as_array_mut()
        .unwrap()
        .push(serde_json::from_str(&text).unwrap());
    let staged = Staged::decode(&bundle, &program).unwrap();
    assert_eq!(
        resource_refusal(&(bundle.clone(), staged), 1 << 20),
        Error("bundle-result-limit")
    );
    // Without the earlier excess, the later table's declared shape refuses.
    let (_, single) = resource_case(KB, 1, 0, None, 0);
    let mut program = single.encode();
    program[2]
        .as_array_mut()
        .unwrap()
        .push(serde_json::from_str(&text).unwrap());
    let staged = Staged::decode(&bundle, &program).unwrap();
    assert_eq!(
        resource_refusal(&(bundle, staged), 1 << 20),
        Error("bundle-data-limit")
    );
}
