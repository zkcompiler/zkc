use super::*;

/// Independent test arithmetic: prime fields below 2^63 by u128 products and
/// the binomial extension X^8 = 3 over KoalaBear.
struct Reference;
const P: u64 = 2_130_706_433;
impl Algebra for Reference {
    type Value = Vec<u64>;
    fn value(&self, field: Identity, c: &[String]) -> Result<Vec<u64>> {
        if field != Identity::KoalaBear && field != Identity::KoalaBearExt8 {
            return Err(Error("test-field"));
        }
        c.iter()
            .map(|x| x.parse().map_err(|_| Error("test-value")))
            .collect()
    }
    fn constant(&self, field: Identity, literal: &str) -> Result<Vec<u64>> {
        let mut v = vec![0; degree(field).ok_or(Error("test-field"))?];
        v[0] = literal.parse().map_err(|_| Error("test-value"))?;
        Ok(v)
    }
    fn add(&self, _: Identity, a: &Vec<u64>, b: &Vec<u64>) -> Vec<u64> {
        a.iter().zip(b).map(|(x, y)| (x + y) % P).collect()
    }
    fn mul(&self, _: Identity, a: &Vec<u64>, b: &Vec<u64>) -> Vec<u64> {
        let d = a.len();
        let mut r = vec![0u64; d];
        for i in 0..d {
            for j in 0..d {
                let mut t = (u128::from(a[i]) * u128::from(b[j]) % u128::from(P)) as u64;
                if i + j >= d {
                    t = t * 3 % P;
                }
                r[(i + j) % d] = (r[(i + j) % d] + t) % P;
            }
        }
        r
    }
    fn neg(&self, _: Identity, a: &Vec<u64>) -> Vec<u64> {
        a.iter().map(|x| (P - x) % P).collect()
    }
    fn embed(&self, _: Identity, to: Identity, a: &Vec<u64>) -> Result<Vec<u64>> {
        let mut v = vec![0; degree(to).ok_or(Error("test-field"))?];
        v[0] = a[0];
        Ok(v)
    }
    fn coordinates(&self, _: Identity, a: &Vec<u64>) -> Vec<String> {
        a.iter().map(u64::to_string).collect()
    }
}

// Hand-authored fixture shared verbatim with compiler/test/relation_bundle.cpp.
// The identity was computed independently with Python hashlib over this text.
const BUNDLE: &str = r#"["zkc.relation-bundle/0",[["start","koala-bear"],["final","koala-bear"]],[["range","field-balance",["koala-bear"],"koala-bear"],["trace","multiset",["koala-bear","koala-bear"],"koala-bear"]],[["cpu","required",["instance",1,16,true],"finite",[["x","witness","koala-bear",1],["step","public","koala-bear",1]],["zkc.ring/0",["koala-bear","koala-bear","koala-bear","koala-bear","koala-bear"],[["input",0],["input",3],["neg",1],["add",0,2],["input",1],["input",2],["add",0,5],["neg",6],["add",4,7],["input",4],["neg",9],["add",0,10],["constant","koala-bear","1"]],[3,8,11,0,5,12]],[["read",0,"0",0],["read",0,"1",0],["read",1,"0",0],["public",0],["public",1]],[[0,["first"]],[1,["interior",0,1]],[2,["last"]]],[["field-balance",0,["global"],["all"],[3],5,null],["multiset",1,["global"],["all"],"push",[3,4],5,1]]],["rom","required",["fixed",8],"cyclic",[["values","config","koala-bear",1],["multiplicity","witness","koala-bear",1]],["zkc.ring/0",["koala-bear","koala-bear","koala-bear"],[["input",0],["input",1],["neg",1],["input",2],["neg",0],["constant","koala-bear","1"],["neg",5],["add",3,4],["add",7,6],["mul",8,3]],[0,2,9]],[["read",0,"0",0],["read",1,"0",0],["read",0,"1",0]],[[2,["all"]]],[["field-balance",0,["global"],["all"],[0],1,null]]],["log","optional",["instance",1,16,false],"finite",[["pairs","witness","koala-bear",2]],["zkc.ring/0",["koala-bear","koala-bear"],[["input",0],["input",1],["constant","koala-bear","1"]],[0,1,2]],[["read",0,"0",0],["read",0,"0",1]],[],[["multiset",1,["global"],["all"],"pull",[0,1],2,1]]]]]"#;
const IDENTITY: &str = "7f75e6710866e343e7024511e815e371f5d8bff2be4448f4e104bea92e54e0dc";
const CONFIG: &str = r#"["zkc.relation-configuration/0","7f75e6710866e343e7024511e815e371f5d8bff2be4448f4e104bea92e54e0dc",[[null,[]],[null,[["0","1","2","3","4","5","6","7"]]],[null,[]]]]"#;
const INSTANCE: &str = r#"["zkc.relation-instance/0","7f75e6710866e343e7024511e815e371f5d8bff2be4448f4e104bea92e54e0dc",["0","6"],[["present",4,[["1","2","3","9"]]],["present",null,[]],["present",4,[]]]]"#;
const WITNESS: &str = r#"["zkc.relation-witness/0","7f75e6710866e343e7024511e815e371f5d8bff2be4448f4e104bea92e54e0dc",[[["0","1","3","6"]],[["1","1","0","1","0","0","1","0"]],[["3","3","0","1","6","9","1","2"]]]]"#;

/// Shared mutation table: (carrier, from, to) edits and the expected outcome:
/// a refusal identifier, "satisfied" or "unsatisfied".
/// One textual edit: carrier index (bundle, configuration, instance,
/// witness), the original text and its replacement.
type Edit = (usize, &'static str, &'static str);
const MUTATIONS: &[(&str, &[Edit], &str)] = &[
    ("honest", &[], "satisfied"),
    (
        "configuration rom value",
        &[(1, r#""2","3","4""#, r#""2","9","4""#)],
        "unsatisfied",
    ),
    (
        "required table absent",
        &[(2, r#"["present",4,[["1","2","3","9"]]]"#, r#"["absent"]"#)],
        "bundle-table-missing",
    ),
    (
        "optional table absent",
        &[
            (2, r#"["present",4,[]]]"#, r#"["absent"]]"#),
            (3, r#",[["3","3","0","1","6","9","1","2"]]]"#, ",null]"),
        ],
        "unsatisfied",
    ),
    (
        "absent table with witness",
        &[(2, r#"["present",4,[]]]"#, r#"["absent"]]"#)],
        "bundle-witness-presence",
    ),
    (
        "height policy",
        &[
            (
                2,
                r#"["present",4,[["1","2","3","9"]]]"#,
                r#"["present",3,[["1","2","3"]]]"#,
            ),
            (3, r#"[["0","1","3","6"]]"#, r#"[["0","1","3"]]"#),
        ],
        "bundle-height",
    ),
    (
        "height mismatch",
        &[(3, r#"[["0","1","3","6"]]"#, r#"[["0","1","3"]]"#)],
        "bundle-group-shape",
    ),
    (
        "fixed height override",
        &[(2, r#"["present",null,[]]"#, r#"["present",8,[]]"#)],
        "bundle-height-authority",
    ),
    (
        "witness supplies configuration",
        &[(
            3,
            r#"[["1","1","0","1","0","0","1","0"]]"#,
            r#"[["0","1","2","3","4","5","6","7"],["1","1","0","1","0","0","1","0"]]"#,
        )],
        "bundle-group-count",
    ),
    (
        "transition read on every row",
        &[(0, r#"[1,["interior",0,1]]"#, r#"[1,["all"]]"#)],
        "bundle-window",
    ),
    (
        "finite rom wraparound",
        &[(0, r#""cyclic""#, r#""finite""#)],
        "bundle-window",
    ),
    (
        "multiset bound at characteristic",
        &[(0, r#""push",[3,4],5,1]"#, r#""push",[3,4],5,2130706433]"#)],
        "bundle-multiset-bound",
    ),
    (
        "challenge in deterministic relation",
        &[(0, r#"["public",0]"#, r#"["challenge",1,0]"#)],
        "bundle-input-kind",
    ),
    (
        "witness for another relation",
        &[(
            3,
            IDENTITY,
            "0000000000000000000000000000000000000000000000000000000000000000",
        )],
        "bundle-relation",
    ),
    (
        "pulled tuple",
        &[(3, r#""6","9""#, r#""6","8""#)],
        "unsatisfied",
    ),
    (
        "multiplicity above bound",
        &[(
            0,
            r#"["input",1],["constant","koala-bear","1"]],[0,1,2]]"#,
            r#"["input",1],["constant","koala-bear","2"]],[0,1,2]]"#,
        )],
        "unsatisfied",
    ),
    (
        "noncanonical value",
        &[(3, r#""1","1","0","1""#, r#""1","01","0","1""#)],
        "bundle-value",
    ),
    (
        "local request scope",
        &[(
            0,
            r#"["field-balance",0,["global"],["all"],[3],5,null]"#,
            r#"["field-balance",0,["local",0],["all"],[3],5,null]"#,
        )],
        "unsatisfied",
    ),
    (
        "cpu request weight",
        &[(
            0,
            r#"["constant","koala-bear","1"]],[3,8,11"#,
            r#"["constant","koala-bear","2"]],[3,8,11"#,
        )],
        "unsatisfied",
    ),
];

fn outcome(texts: &[String; 4]) -> String {
    let run = || -> Result<bool> {
        let bundle = Bundle::parse(&texts[0])?;
        // A mutated relation has a new identity; its carriers name it.
        let carriers: Vec<String> = texts[1..]
            .iter()
            .map(|t| t.replace(IDENTITY, bundle.identity()))
            .collect();
        let parse = |t: &str| {
            parse_json(
                t,
                DATA_BYTE_LIMIT,
                "bundle-data-schema",
                "bundle-data-limit",
            )
        };
        let c = bundle.decode_configuration(&parse(&carriers[0])?)?;
        let i = bundle.decode_instance(&parse(&carriers[1])?)?;
        let w = bundle.decode_witness(&parse(&carriers[2])?)?;
        Ok(bundle.evaluate(&c, &i, &w, &Reference)?.satisfied)
    };
    match run() {
        Ok(true) => "satisfied".into(),
        Ok(false) => "unsatisfied".into(),
        Err(e) => e.0.into(),
    }
}

#[test]
fn shared_fixture_identity_and_mutations() {
    let bundle = Bundle::parse(BUNDLE).unwrap();
    assert_eq!(bundle.encode().to_string(), BUNDLE, "canonical encoding");
    assert_eq!(
        bundle.identity(),
        IDENTITY,
        "independently computed identity"
    );
    let f = &bundle.facts()[0];
    assert_eq!(
        (f[1].degree, f[1].reads.clone()),
        (1, vec![(0, 0, 0), (0, 1, 0), (1, 0, 0)])
    );
    assert_eq!(f[0].publics, vec![0]);
    for (name, edits, expected) in MUTATIONS {
        let mut texts = [
            BUNDLE.to_string(),
            CONFIG.to_string(),
            INSTANCE.to_string(),
            WITNESS.to_string(),
        ];
        for (carrier, from, to) in *edits {
            assert!(
                texts[*carrier].contains(from),
                "{name}: fixture lacks {from}"
            );
            texts[*carrier] = texts[*carrier].replacen(from, to, 1);
        }
        assert_eq!(outcome(&texts), *expected, "{name}");
    }
}

#[test]
fn honest_evaluation_details() {
    let bundle = Bundle::parse(BUNDLE).unwrap();
    let parse = |t: &str| parse_json(t, DATA_BYTE_LIMIT, "x", "y").unwrap();
    let (c, i, w) = (
        bundle.decode_configuration(&parse(CONFIG)).unwrap(),
        bundle.decode_instance(&parse(INSTANCE)).unwrap(),
        bundle.decode_witness(&parse(WITNESS)).unwrap(),
    );
    assert_eq!(bundle.encode_configuration(&c).to_string(), CONFIG);
    assert_eq!(bundle.encode_instance(&i).to_string(), INSTANCE);
    assert_eq!(bundle.encode_witness(&w).to_string(), WITNESS);
    let e = bundle.evaluate(&c, &i, &w, &Reference).unwrap();
    assert!(e.satisfied && e.range_failures.is_empty());
    // Three cpu assertions over 1 + 3 + 1 rows, and one cyclic rom assertion
    // over 8 rows: row 7 reads row 0.
    assert_eq!(e.residuals.len(), 13);
    assert!(e.residuals.iter().all(|r| r.value == ["0"]));
    let multiset: Vec<_> = e
        .balances
        .iter()
        .filter(|b| b.kind == ChannelKind::Multiset)
        .collect();
    assert_eq!(multiset.len(), 4);
    assert!(
        multiset
            .iter()
            .all(|b| b.push == 1 && b.pull == 1 && b.balanced)
    );
    let field: Vec<_> = e
        .balances
        .iter()
        .filter(|b| b.kind == ChannelKind::FieldBalance)
        .collect();
    assert_eq!(
        field.len(),
        8,
        "every rom value is a key, including zero counts"
    );
    assert!(field.iter().all(|b| b.sum == ["0"]));
    let admitted = bundle.admit(&c, &i, &w).unwrap();
    assert_eq!(
        (admitted.present, admitted.heights),
        (vec![true, true, true], vec![4, 8, 4])
    );
}

/// A one-table bundle; `arena` is `(nodes, outputs)` over koala-bear inputs.
fn one_table(
    model: &str,
    height: Value,
    groups: Value,
    inputs: Value,
    arena: (Value, Value),
    assertions: Value,
    interactions: Value,
) -> String {
    let (nodes, outputs) = arena;
    let fields: Vec<_> = inputs
        .as_array()
        .unwrap()
        .iter()
        .map(|_| "koala-bear")
        .collect();
    json!([
        "zkc.relation-bundle/0",
        [],
        [],
        [[
            "t",
            "required",
            height,
            model,
            groups,
            ["zkc.ring/0", fields, nodes, outputs],
            inputs,
            assertions,
            interactions
        ]]
    ])
    .to_string()
}
fn window(model: &str, scope: Value, offset: &str) -> Result<Bundle> {
    Bundle::parse(&one_table(
        model,
        json!(["instance", 1, 8, false]),
        json!([
            ["x", "witness", "koala-bear", 1],
            ["y", "witness", "koala-bear", 1]
        ]),
        json!([["read", 0, offset, 0], ["read", 1, "0", 0]]),
        (
            json!([["input", 0], ["input", 1], ["neg", 1], ["add", 0, 2]]),
            json!([3]),
        ),
        json!([[0, scope]]),
        json!([]),
    ))
}
fn run_window(bundle: &Bundle, x: &[u64], y: &[u64]) -> std::result::Result<bool, &'static str> {
    let id = bundle.identity().to_string();
    let col = |v: &[u64]| v.iter().map(u64::to_string).collect::<Vec<_>>();
    let c = Configuration {
        relation: id.clone(),
        tables: vec![(None, vec![])],
    };
    let i = Instance {
        relation: id.clone(),
        publics: vec![],
        tables: vec![Some((Some(x.len() as u32), vec![]))],
    };
    let w = Witness {
        relation: id,
        tables: vec![Some(vec![col(x), col(y)])],
    };
    bundle
        .evaluate(&c, &i, &w, &Reference)
        .map(|e| e.satisfied)
        .map_err(|e| e.0)
}

#[test]
fn signed_finite_and_cyclic_windows() {
    for (scope, offset) in [
        (json!(["all"]), "1"),
        (json!(["all"]), "-1"),
        (json!(["first"]), "-1"),
        (json!(["last"]), "1"),
        (json!(["interior", 0, 0]), "-1"),
        (json!(["interior", 0, 1]), "2"),
    ] {
        assert_eq!(
            window("finite", scope.clone(), offset).unwrap_err(),
            Error("bundle-window"),
            "{scope} {offset}"
        );
    }
    let previous = window("finite", json!(["interior", 1, 0]), "-1").unwrap();
    assert_eq!(run_window(&previous, &[4, 5, 6], &[9, 4, 5]), Ok(true));
    assert_eq!(run_window(&previous, &[4, 5, 6], &[9, 4, 4]), Ok(false));
    let first = window("finite", json!(["first"]), "2").unwrap();
    assert_eq!(run_window(&first, &[1, 2], &[3, 0]), Err("bundle-window"));
    assert_eq!(run_window(&first, &[1, 2, 3], &[3, 0, 0]), Ok(true));
    let interval = window("finite", json!(["interval", 0, 3]), "1").unwrap();
    assert_eq!(
        run_window(&interval, &[1, 2, 3], &[2, 3, 0]),
        Err("bundle-window")
    );
    assert_eq!(
        run_window(&interval, &[1, 2, 3, 4], &[2, 3, 4, 0]),
        Ok(true)
    );
    let far = window("finite", json!(["interval", 2, 6]), "0").unwrap();
    assert_eq!(
        run_window(&far, &[1, 2, 3, 4], &[1, 2, 3, 4]),
        Err("bundle-scope-height")
    );
    let rotate = window("cyclic", json!(["all"]), "1").unwrap();
    assert_eq!(run_window(&rotate, &[1, 2, 3, 4], &[2, 3, 4, 1]), Ok(true));
    assert_eq!(run_window(&rotate, &[1, 2, 3, 4], &[2, 3, 4, 0]), Ok(false));
    let back = window("cyclic", json!(["all"]), "-1").unwrap();
    assert_eq!(run_window(&back, &[1, 2, 3, 4], &[4, 1, 2, 3]), Ok(true));
    assert_eq!(run_window(&back, &[7], &[7]), Ok(true));
    let far5 = window("cyclic", json!(["all"]), "5").unwrap();
    assert_eq!(run_window(&far5, &[1, 2, 3], &[3, 1, 2]), Ok(true));
    // A zero product does not hide an undefined read.
    let hidden = one_table(
        "finite",
        json!(["instance", 1, 8, false]),
        json!([["x", "witness", "koala-bear", 1]]),
        json!([["read", 0, "1", 0]]),
        (
            json!([["input", 0], ["constant", "koala-bear", "0"], ["mul", 0, 1]]),
            json!([2]),
        ),
        json!([[0, ["all"]]]),
        json!([]),
    );
    assert_eq!(Bundle::parse(&hidden).unwrap_err(), Error("bundle-window"));
    for offset in ["+0", "-0", "01", "65537", ""] {
        let text = window("cyclic", json!(["all"]), "0")
            .map(|b| b.encode().to_string())
            .unwrap()
            .replacen(
                r#"["read",0,"0",0]"#,
                &format!(r#"["read",0,"{offset}",0]"#),
                1,
            );
        assert_eq!(
            Bundle::parse(&text).unwrap_err(),
            Error("bundle-input"),
            "{offset}"
        );
    }
}

fn counts(kind: &str, bound: Value) -> Bundle {
    let interaction = |side: &str| {
        if kind == "multiset" {
            json!(["multiset", 0, ["global"], ["all"], side, [0], 1, bound])
        } else {
            json!(["field-balance", 0, ["global"], ["all"], [0], 1, null])
        }
    };
    let table = |name: &str, side: &str| {
        json!([
            name,
            "required",
            ["instance", 1, 8, false],
            "finite",
            [["rows", "witness", "koala-bear", 2]],
            [
                "zkc.ring/0",
                ["koala-bear", "koala-bear"],
                [["input", 0], ["input", 1]],
                [0, 1]
            ],
            [["read", 0, "0", 0], ["read", 0, "0", 1]],
            [],
            [interaction(side)]
        ])
    };
    Bundle::parse(
        &json!([
            "zkc.relation-bundle/0",
            [],
            [["bus", kind, ["koala-bear"], "koala-bear"]],
            [table("push", "push"), table("pull", "pull")]
        ])
        .to_string(),
    )
    .unwrap()
}
fn count_rows(bundle: &Bundle, push: &[&str], pull: &[&str]) -> Evaluation {
    let id = bundle.identity().to_string();
    let col = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    let c = Configuration {
        relation: id.clone(),
        tables: vec![(None, vec![]), (None, vec![])],
    };
    let i = Instance {
        relation: id.clone(),
        publics: vec![],
        tables: vec![
            Some((Some(push.len() as u32 / 2), vec![])),
            Some((Some(pull.len() as u32 / 2), vec![])),
        ],
    };
    let w = Witness {
        relation: id,
        tables: vec![Some(vec![col(push)]), Some(vec![col(pull)])],
    };
    bundle.evaluate(&c, &i, &w, &Reference).unwrap()
}

#[test]
fn field_weights_and_natural_multiplicities() {
    let field = counts("field-balance", Value::Null);
    let natural = counts("multiset", json!(3));
    assert!(
        count_rows(&field, &["5", "2130706432"], &["5", "1"]).satisfied,
        "p-1 and 1 cancel as field weights"
    );
    let wrapped = count_rows(&natural, &["5", "2130706432"], &["5", "1"]);
    assert!(
        !wrapped.satisfied && wrapped.range_failures == [(0, 0, 0)],
        "p-1 is not a natural count"
    );
    assert!(count_rows(&natural, &["5", "2"], &["5", "1", "5", "1"]).satisfied);
    assert!(!count_rows(&natural, &["5", "2"], &["5", "1"]).satisfied);
    assert!(count_rows(&natural, &["5", "3"], &["5", "3"]).satisfied);
    assert_eq!(
        count_rows(&natural, &["5", "4"], &["5", "4"])
            .range_failures
            .len(),
        2
    );
    assert!(
        !count_rows(&field, &["5", "2"], &["5", "1", "5", "1"]).satisfied,
        "field balance has no sides"
    );
    for bound in [json!(0), json!(2_130_706_433u64), json!(1u64 << 33)] {
        let text = counts("multiset", json!(3))
            .encode()
            .to_string()
            .replace(r#","push",[0],1,3]"#, &format!(r#","push",[0],1,{bound}]"#));
        assert_eq!(
            Bundle::parse(&text).unwrap_err(),
            Error("bundle-multiset-bound"),
            "{bound}"
        );
    }
    let ext = counts("multiset", json!(3)).encode().to_string().replace(
        r#""multiset",["koala-bear"],"koala-bear""#,
        r#""multiset",["koala-bear"],"koala-bear.ext8-binomial3""#,
    );
    assert_eq!(
        Bundle::parse(&ext).unwrap_err(),
        Error("bundle-multiset-field")
    );
    let kind = field.encode().to_string().replacen(
        r#"["field-balance",0,["global"],["all"],[0],1,null]"#,
        r#"["multiset",0,["global"],["all"],"push",[0],1,1]"#,
        1,
    );
    assert_eq!(
        Bundle::parse(&kind).unwrap_err(),
        Error("bundle-interaction-kind")
    );
}

#[test]
fn formation_and_schema_refusals() {
    let base = |groups: Value,
                height: Value,
                nodes: Value,
                inputs: Value,
                outputs: Value,
                assertions: Value| {
        Bundle::parse(&one_table(
            "finite",
            height,
            groups,
            inputs,
            (nodes, outputs),
            assertions,
            json!([]),
        ))
    };
    let x = json!([["x", "witness", "koala-bear", 1]]);
    let h = json!(["instance", 1, 8, false]);
    let read = json!([["read", 0, "0", 0]]);
    assert!(
        base(
            x.clone(),
            h.clone(),
            json!([["input", 0]]),
            read.clone(),
            json!([0]),
            json!([[0, ["all"]]])
        )
        .is_ok()
    );
    assert_eq!(
        base(
            x.clone(),
            h.clone(),
            json!([["input", 0]]),
            read.clone(),
            json!([0]),
            json!([])
        )
        .unwrap_err(),
        Error("bundle-unused-output")
    );
    assert_eq!(
        base(
            x.clone(),
            h.clone(),
            json!([["input", 0]]),
            json!([["read", 0, "0", 0], ["read", 0, "1", 0]]),
            json!([0]),
            json!([[0, ["all"]]])
        )
        .unwrap_err(),
        Error("bundle-unused-input"),
        "a declared binding no output uses"
    );
    assert_eq!(
        base(
            x.clone(),
            h.clone(),
            json!([["input", 0], ["input", 1], ["add", 0, 1]]),
            json!([["read", 0, "0", 0], ["read", 0, "0", 0]]),
            json!([2]),
            json!([[0, ["all"]]])
        )
        .unwrap_err(),
        Error("bundle-duplicate-input")
    );
    assert_eq!(
        base(
            json!([["x", "config", "koala-bear", 1]]),
            h.clone(),
            json!([["input", 0]]),
            read.clone(),
            json!([0]),
            json!([[0, ["all"]]])
        )
        .unwrap_err(),
        Error("bundle-config-height")
    );
    assert!(
        base(
            json!([["x", "config", "koala-bear", 1]]),
            json!(["fixed", 4]),
            json!([["input", 0]]),
            read.clone(),
            json!([0]),
            json!([[0, ["all"]]])
        )
        .is_ok()
    );
    assert_eq!(
        base(
            json!([["x", "witness", "koala-bear", 0]]),
            h.clone(),
            json!([["input", 0]]),
            read.clone(),
            json!([0]),
            json!([[0, ["all"]]])
        )
        .unwrap_err(),
        Error("bundle-width")
    );
    for (height, code) in [
        (json!(["instance", 0, 4, false]), "bundle-height"),
        (json!(["instance", 5, 7, true]), "bundle-height"),
        (
            json!(["instance", 1, (1u32 << 20) + 1, false]),
            "bundle-height",
        ),
        (json!(["fixed", 2, 3]), "bundle-height"),
    ] {
        assert_eq!(
            base(
                x.clone(),
                height,
                json!([["input", 0]]),
                read.clone(),
                json!([0]),
                json!([[0, ["all"]]])
            )
            .unwrap_err(),
            Error(code)
        );
    }
    assert_eq!(
        base(
            x.clone(),
            h.clone(),
            json!([["input", 0]]),
            read.clone(),
            json!([0]),
            json!([[0, ["interval", 3, 2]]])
        )
        .unwrap_err(),
        Error("bundle-scope")
    );
    assert_eq!(
        base(
            json!([
                ["x", "witness", "koala-bear", 1],
                ["x", "witness", "koala-bear", 1]
            ]),
            h.clone(),
            json!([["input", 0]]),
            read.clone(),
            json!([0]),
            json!([[0, ["all"]]])
        )
        .unwrap_err(),
        Error("bundle-duplicate-name")
    );
    for kind in ["challenge", "claim", "selector"] {
        let text = BUNDLE.replacen(r#"["public",0]"#, &format!(r#"["{kind}",1,0]"#), 1);
        assert_eq!(
            Bundle::parse(&text).unwrap_err(),
            Error("bundle-input-kind"),
            "{kind}"
        );
    }
    assert_eq!(
        Bundle::parse(&BUNDLE.replacen("zkc.relation-bundle/0", "zkc.relation-bundle/1", 1))
            .unwrap_err(),
        Error("bundle-schema")
    );
    assert_eq!(
        Bundle::parse(&BUNDLE.replacen(r#""finite","#, r#""finite",0,"#, 1)).unwrap_err(),
        Error("bundle-schema")
    );
    assert_eq!(
        Bundle::parse(&BUNDLE.replacen(
            r#"["instance",1,16,true]"#,
            r#"["instance",01,16,true]"#,
            1
        ))
        .unwrap_err(),
        Error("bundle-schema")
    );
    assert_eq!(
        Bundle::parse(&BUNDLE.replacen(r#""witness""#, r#""prover""#, 1)).unwrap_err(),
        Error("bundle-schema")
    );
    assert_eq!(
        Bundle::parse(&BUNDLE.replacen(r#"["all"]"#, r#"["every"]"#, 1)).unwrap_err(),
        Error("bundle-scope")
    );
    assert_eq!(
        Bundle::parse(&BUNDLE.replacen("[", "{", 1)).unwrap_err(),
        Error("bundle-schema")
    );
}

#[test]
fn preflight_precedes_values_and_arithmetic() {
    // A window refusal is reported before a noncanonical value is parsed.
    let first = window("finite", json!(["first"]), "2").unwrap();
    let id = first.identity().to_string();
    let c = Configuration {
        relation: id.clone(),
        tables: vec![(None, vec![])],
    };
    let i = Instance {
        relation: id.clone(),
        publics: vec![],
        tables: vec![Some((Some(2), vec![]))],
    };
    let w = Witness {
        relation: id,
        tables: vec![Some(vec![
            vec!["01".into(), "1".into()],
            vec!["0".into(), "0".into()],
        ])],
    };
    assert_eq!(first.admit(&c, &i, &w).unwrap_err(), Error("bundle-window"));
    // Work is bounded from heights and arena size before any value is read.
    let mut nodes = vec![json!(["input", 0])];
    for k in 0..70 {
        nodes.push(json!(["add", k, k]));
    }
    let heavy = Bundle::parse(&one_table(
        "finite",
        json!(["instance", 1, 1 << 20, false]),
        json!([["x", "witness", "koala-bear", 1]]),
        json!([["read", 0, "0", 0]]),
        (json!(nodes), json!([70])),
        json!([[0, ["all"]]]),
        json!([]),
    ))
    .unwrap();
    let id = heavy.identity().to_string();
    let c = Configuration {
        relation: id.clone(),
        tables: vec![(None, vec![])],
    };
    let i = Instance {
        relation: id.clone(),
        publics: vec![],
        tables: vec![Some((Some(1 << 20), vec![]))],
    };
    let w = Witness {
        relation: id,
        tables: vec![Some(vec![vec!["x".into(); 1 << 20]])],
    };
    assert_eq!(
        heavy.admit(&c, &i, &w).unwrap_err(),
        Error("bundle-work-limit")
    );
}

#[test]
fn staged_program_is_a_separate_subject() {
    let bundle = Bundle::parse(BUNDLE).unwrap();
    let empty = || json!([[], ["zkc.ring/0", [], [], []], [], []]);
    // Phase 1: challenge alpha, a cpu group z with z - (x + alpha) = 0, and a
    // claim checked globally against zero.
    let cpu = json!([
        [["z", "koala-bear", 1]],
        [
            "zkc.ring/0",
            ["koala-bear", "koala-bear", "koala-bear"],
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
    ]);
    let global = json!([
        ["zkc.ring/0", ["koala-bear"], [["input", 0]], [0]],
        [["claim", 1, 0]],
        [0]
    ]);
    let program = |cpu: &Value, premises: Value| {
        json!([
            "zkc.relation-staged/0",
            IDENTITY,
            [[
                [["alpha", "koala-bear"]],
                [["total", "koala-bear"]],
                [cpu, empty(), empty()]
            ]],
            global,
            premises
        ])
        .to_string()
    };
    let staged = Staged::parse(
        &bundle,
        &program(
            &cpu,
            json!([
                ["characteristic-exceeds", "koala-bear", 64],
                ["nonzero", 1, 0, 0, ["all"]],
                ["boolean", 0, 2, 0, ["all"]]
            ]),
        ),
    )
    .unwrap();
    assert_eq!(staged.premises().len(), 3);
    assert_eq!(
        Staged::parse(&bundle, &staged.encode().to_string())
            .unwrap()
            .identity(),
        staged.identity()
    );
    assert_eq!(
        bundle.identity(),
        IDENTITY,
        "the staged program does not change the relation"
    );
    let later = program(
        &cpu.to_string()
            .replace(r#"["challenge",1,0]"#, r#"["challenge",2,0]"#)
            .parse()
            .unwrap(),
        json!([]),
    );
    assert_eq!(
        Staged::parse(&bundle, &later).unwrap_err(),
        Error("staged-phase-order")
    );
    let phase_zero = program(
        &cpu.to_string()
            .replace(r#"["challenge",1,0]"#, r#"["challenge",0,0]"#)
            .parse()
            .unwrap(),
        json!([]),
    );
    assert_eq!(
        Staged::parse(&bundle, &phase_zero).unwrap_err(),
        Error("staged-input")
    );
    let global_read =
        program(&cpu, json!([])).replace(r#"[["claim",1,0]],[0]]"#, r#"[["read",0,0,"0",0]],[0]]"#);
    assert_eq!(
        Staged::parse(&bundle, &global_read).unwrap_err(),
        Error("staged-global-read")
    );
    let premise = program(&cpu, json!([["nonzero", 1, 0, 7, ["all"]]]));
    assert_eq!(
        Staged::parse(&bundle, &premise).unwrap_err(),
        Error("staged-premise")
    );
    let other = program(&cpu, json!([])).replacen(IDENTITY, &"0".repeat(64), 1);
    assert_eq!(
        Staged::parse(&bundle, &other).unwrap_err(),
        Error("bundle-relation")
    );
}
