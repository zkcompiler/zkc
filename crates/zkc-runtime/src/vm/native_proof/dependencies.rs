//! Dependency admission for private participant inputs and service replies.
//! Shared construction inputs and event-loop counts cannot depend on those
//! values. The caller selects participants needing this check. It establishes
//! value dependence, not termination or a cryptographic independence theorem.
use super::*;
use std::sync::Arc;

type Environment = BTreeMap<String, bool>;
// General carrier admission bounds identifiers to 128 bytes. Normalization
// preserves those names or introduces bounded generated names, so work counts
// value slots rather than unbounded strings. Local cache keys also copy names.
fn flag(env: &Environment, name: &str) -> Result<bool> {
    env.get(name)
        .copied()
        .ok_or_else(|| refuse("native-proof-dependency-scope"))
}
fn flags(env: &Environment, names: &[String]) -> Result<Vec<bool>> {
    names.iter().map(|name| flag(env, name)).collect()
}
fn bind(env: &mut Environment, names: &[String], flags: &[bool]) -> Result<()> {
    if names.len() != flags.len() {
        return Err(refuse("native-proof-dependency-shape"));
    }
    env.extend(names.iter().cloned().zip(flags.iter().copied()));
    Ok(())
}
fn merge(target: &mut [bool], source: &[bool]) -> Result<bool> {
    if target.len() != source.len() {
        return Err(refuse("native-proof-dependency-shape"));
    }
    let mut changed = false;
    for (a, b) in target.iter_mut().zip(source) {
        changed |= !*a && *b;
        *a |= *b;
    }
    Ok(changed)
}
struct Dependencies<'a> {
    functions: &'a BTreeMap<String, Arc<Function>>,
    adapters: &'a BTreeSet<String>,
    returns: &'a [PhysicalType],
    cache: BTreeMap<(String, Vec<bool>), Vec<bool>>,
    work: usize,
    producer: bool,
}
impl Dependencies<'_> {
    fn charge(&mut self, cost: usize) -> Result<()> {
        self.work = self
            .work
            .checked_sub(cost)
            .ok_or_else(|| refuse("native-proof-dependency-limit"))?;
        Ok(())
    }
    fn capture(&mut self, env: &Environment, names: &[String]) -> Result<Environment> {
        self.charge(names.len())?;
        names
            .iter()
            .map(|n| Ok((n.clone(), flag(env, n)?)))
            .collect()
    }
    fn local(&mut self, function: &str, inputs: Vec<bool>) -> Result<Vec<bool>> {
        self.charge(function.len() + inputs.len())?;
        let key = (function.to_owned(), inputs);
        if let Some(size) = self.cache.get(&key).map(Vec::len) {
            self.charge(size)?;
            return Ok(self.cache[&key].clone());
        }
        let function = self
            .functions
            .get(function)
            .ok_or_else(|| refuse("native-proof-dependency-scope"))?;
        if function.inputs.len() != key.1.len() {
            return Err(refuse("native-proof-dependency-shape"));
        }
        let env = function
            .inputs
            .iter()
            .map(|(n, _)| n.clone())
            .zip(key.1.iter().copied())
            .collect();
        let outputs = self
            .local_block(&function.body, env, 0)?
            .unwrap_or_else(|| vec![false; function.outputs.len()]);
        self.cache.insert(key, outputs.clone());
        Ok(outputs)
    }
    fn local_block(
        &mut self,
        body: &[LocalInstruction],
        mut env: Environment,
        depth: usize,
    ) -> Result<Option<Vec<bool>>> {
        if depth > 64 {
            return Err(refuse("native-proof-dependency-limit"));
        }
        for op in body {
            self.charge(1)?;
            match op {
                LocalInstruction::BoolConstant { output, .. } => {
                    env.insert(output.clone(), false);
                }
                LocalInstruction::Op {
                    inputs, outputs, ..
                } => {
                    self.charge(inputs.len() + outputs.len())?;
                    let private = flags(&env, inputs)?.contains(&true);
                    bind(&mut env, outputs, &vec![private; outputs.len()])?;
                }
                LocalInstruction::Variant {
                    payload, output, ..
                } => {
                    self.charge(payload.len())?;
                    let private = flags(&env, payload)?.contains(&true);
                    env.insert(output.clone(), private);
                }
                LocalInstruction::Conditional {
                    condition,
                    captures,
                    then_body,
                    else_body,
                    outputs,
                    ..
                } => {
                    self.charge(outputs.len())?;
                    let mut joined = vec![false; outputs.len()];
                    let mut returning = 0;
                    for branch in [then_body, else_body] {
                        let nested = self.capture(&env, captures)?;
                        if let Some(values) = self.local_block(branch, nested, depth + 1)? {
                            returning += 1;
                            self.charge(values.len())?;
                            merge(&mut joined, &values)?;
                        }
                    }
                    if returning > 1 && flag(&env, condition)? {
                        joined.fill(true);
                    }
                    bind(&mut env, outputs, &joined)?;
                }
                LocalInstruction::Match {
                    input,
                    captures,
                    arms,
                    outputs,
                    ..
                } => {
                    self.charge(outputs.len())?;
                    let private = flag(&env, input)?;
                    let mut joined = vec![false; outputs.len()];
                    let mut returning = 0;
                    for arm in arms {
                        let mut nested = self.capture(&env, captures)?;
                        self.charge(arm.payload.len())?;
                        bind(&mut nested, &arm.payload, &vec![private; arm.payload.len()])?;
                        if let Some(values) = self.local_block(&arm.body, nested, depth + 1)? {
                            returning += 1;
                            self.charge(values.len())?;
                            merge(&mut joined, &values)?;
                        }
                    }
                    if returning > 1 && private {
                        joined.fill(true);
                    }
                    bind(&mut env, outputs, &joined)?;
                }
                LocalInstruction::For {
                    conditional,
                    induction,
                    lower,
                    upper,
                    carried,
                    captures,
                    body,
                    outputs,
                    ..
                } => {
                    self.charge(carried.len() + outputs.len())?;
                    let control = flag(&env, lower)? || flag(&env, upper)?;
                    let mut carried_flags: Vec<_> = carried
                        .iter()
                        .map(|(_, value)| Ok(control || flag(&env, value)?))
                        .collect::<Result<_>>()?;
                    loop {
                        self.charge(carried.len())?;
                        let mut nested = self.capture(&env, captures)?;
                        nested.insert(induction.clone(), control);
                        nested.extend(
                            carried
                                .iter()
                                .map(|(n, _)| n.clone())
                                .zip(carried_flags.iter().copied()),
                        );
                        let Some(values) = self.local_block(body, nested, depth + 1)? else {
                            break;
                        };
                        let (condition, values) = if *conditional {
                            let (condition, rest) = values
                                .split_first()
                                .ok_or_else(|| refuse("native-proof-dependency-shape"))?;
                            (*condition, rest)
                        } else {
                            (false, values.as_slice())
                        };
                        self.charge(values.len())?;
                        let next: Vec<_> = values.iter().map(|v| *v || condition).collect();
                        if !merge(&mut carried_flags, &next)? {
                            break;
                        }
                    }
                    bind(&mut env, outputs, &carried_flags)?;
                }
                LocalInstruction::Stop { .. } => return Ok(None),
                LocalInstruction::Return(values) | LocalInstruction::Yield(values) => {
                    self.charge(values.len())?;
                    return Ok(Some(flags(&env, values)?));
                }
                LocalInstruction::Release(_) => (),
            }
        }
        Err(refuse("native-proof-dependency-shape"))
    }
    fn shared(&mut self, body: &[Instruction], depth: usize) -> Result<bool> {
        if depth > 64 {
            return Err(refuse("native-proof-dependency-limit"));
        }
        for op in body {
            self.charge(1)?;
            match op {
                Instruction::Send { .. } | Instruction::Receive { .. } => return Ok(true),
                Instruction::Local { function, .. } if self.adapters.contains(function) => {
                    return Ok(true);
                }
                Instruction::Loop { body, .. } if self.shared(body, depth + 1)? => return Ok(true),
                _ => (),
            }
        }
        Ok(false)
    }
    fn participant(
        &mut self,
        body: &[Instruction],
        mut env: Environment,
        depth: usize,
    ) -> Result<Vec<bool>> {
        if depth > 64 {
            return Err(refuse("native-proof-dependency-limit"));
        }
        for op in body {
            self.charge(1)?;
            match op {
                Instruction::Query { outputs, .. } => {
                    self.charge(outputs.len())?;
                    bind(&mut env, outputs, &vec![true; outputs.len()])?;
                }
                Instruction::Local {
                    function,
                    inputs,
                    outputs,
                    ..
                } => {
                    self.charge(inputs.len() + outputs.len())?;
                    let selected = flags(&env, inputs)?;
                    if self.adapters.contains(function) && selected.contains(&true) {
                        return Err(refuse("native-proof-private-dependency"));
                    }
                    let result = self.local(function, selected)?;
                    bind(&mut env, outputs, &result)?;
                }
                Instruction::Receive { output, .. } => {
                    env.insert(output.clone(), false);
                }
                Instruction::Send { input, .. } => {
                    if self.producer {
                        // Only the exact transmitted value becomes shared.
                        // Revealing f(secret) does not reveal secret itself.
                        flag(&env, input)?;
                        env.insert(input.clone(), false);
                    } else if flag(&env, input)? {
                        return Err(refuse("native-proof-private-dependency"));
                    }
                }
                Instruction::Loop {
                    count,
                    carried,
                    captures,
                    body,
                    outputs,
                    ..
                } => {
                    self.charge(carried.len() + outputs.len())?;
                    let control = flag(&env, &count.value)?;
                    if control && self.shared(body, depth + 1)? {
                        return Err(refuse("native-proof-private-dependency"));
                    }
                    let mut carried_flags: Vec<_> = carried
                        .iter()
                        .map(|(_, v)| Ok(control || flag(&env, v)?))
                        .collect::<Result<_>>()?;
                    loop {
                        self.charge(carried.len())?;
                        let mut nested = self.capture(&env, captures)?;
                        nested.insert(count.induction.clone(), control);
                        nested.extend(
                            carried
                                .iter()
                                .map(|(n, _)| n.clone())
                                .zip(carried_flags.iter().copied()),
                        );
                        let result = self.participant(body, nested, depth + 1)?;
                        self.charge(result.len())?;
                        if !merge(&mut carried_flags, &result)? {
                            break;
                        }
                    }
                    bind(&mut env, outputs, &carried_flags)?;
                }
                Instruction::ReturnIf {
                    values,
                    continuations,
                    ..
                } => {
                    // Completion may depend on private verifier data. The false
                    // edge only renames the existing affine inputs.
                    self.charge(values.len())?;
                    if values.len() != self.returns.len() {
                        return Err(refuse("native-proof-dependency-shape"));
                    }
                    let flags: Vec<_> = values
                        .iter()
                        .zip(self.returns)
                        .filter(|(_, ty)| ty.is_affine())
                        .map(|(n, _)| flag(&env, n))
                        .collect::<Result<_>>()?;
                    bind(&mut env, continuations, &flags)?;
                }
                Instruction::Return(values) | Instruction::Yield(values) => {
                    self.charge(values.len())?;
                    return flags(&env, values);
                }
            }
        }
        Err(refuse("native-proof-dependency-shape"))
    }
}

pub(super) fn check_participant(
    admitted: &Program,
    body: &[Instruction],
    returns: &[PhysicalType],
    helpers: &BTreeMap<String, Helper<'_>>,
    env: Environment,
    producer: bool,
) -> Result<()> {
    let adapters = helpers.keys().cloned().collect();
    let mut checker = Dependencies {
        functions: &admitted.program.functions,
        adapters: &adapters,
        returns,
        cache: BTreeMap::new(),
        work: 1_000_000,
        producer,
    };
    checker.participant(body, env, 0)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn names(values: &[&str]) -> Vec<String> {
        values.iter().map(|v| (*v).into()).collect()
    }
    fn function(
        name: &str,
        inputs: &[&str],
        outputs: usize,
        body: Vec<LocalInstruction>,
    ) -> Arc<Function> {
        let ty =
            PhysicalType::default_for(super::super::super::LogicalType::parse("bool").unwrap())
                .unwrap();
        Arc::new(Function {
            name: name.into(),
            inputs: inputs.iter().map(|n| ((*n).into(), ty.clone())).collect(),
            outputs: vec![ty; outputs],
            origin: LogicalOrigin {
                definition: name.into(),
                arguments: vec![],
            },
            body: body.into(),
        })
    }
    fn call(name: &str, inputs: &[&str], outputs: &[&str]) -> Instruction {
        Instruction::Local {
            site: name.into(),
            function: name.into(),
            inputs: names(inputs),
            outputs: names(outputs),
        }
    }
    fn query(output: &str) -> Instruction {
        Instruction::Query {
            site: "private".into(),
            port: "private".into(),
            method: "draw".into(),
            inputs: vec![],
            outputs: names(&[output]),
        }
    }
    fn loop_body(
        count: &str,
        carried: &[(&str, &str)],
        captures: &[&str],
        body: Vec<Instruction>,
        outputs: &[&str],
    ) -> Instruction {
        Instruction::Loop {
            site: "loop".into(),
            count: LoopCount {
                value: count.into(),
                maximum: 4,
                induction: "i".into(),
            },
            carried: carried
                .iter()
                .map(|(a, b)| ((*a).into(), (*b).into()))
                .collect(),
            captures: names(captures),
            body: body.into(),
            outputs: names(outputs),
        }
    }
    fn check(
        functions: Vec<Arc<Function>>,
        body: Vec<Instruction>,
        budget: usize,
    ) -> Result<Vec<bool>> {
        check_as(functions, body, budget, false)
    }
    fn check_as(
        functions: Vec<Arc<Function>>,
        body: Vec<Instruction>,
        budget: usize,
        producer: bool,
    ) -> Result<Vec<bool>> {
        let functions: BTreeMap<_, _> =
            functions.into_iter().map(|f| (f.name.clone(), f)).collect();
        let adapters = BTreeSet::from(["observe".into()]);
        let mut checker = Dependencies {
            functions: &functions,
            adapters: &adapters,
            returns: &[],
            cache: BTreeMap::new(),
            work: budget,
            producer,
        };
        checker.participant(&body, BTreeMap::from([("public".into(), false)]), 0)
    }
    fn identity() -> Arc<Function> {
        function(
            "observe",
            &["value"],
            1,
            vec![LocalInstruction::Return(names(&["value"]))],
        )
    }
    #[test]
    fn return_if_preserves_private_affine_continuations() {
        let functions = BTreeMap::new();
        let adapters = BTreeSet::new();
        let returns = [PhysicalType::parse("rng:bls12-381.fr@host.resource/0").unwrap()];
        let mut checker = Dependencies {
            functions: &functions,
            adapters: &adapters,
            returns: &returns,
            cache: BTreeMap::new(),
            work: 1000,
            producer: false,
        };
        let body = vec![
            Instruction::ReturnIf {
                site: "exit".into(),
                condition: "condition".into(),
                values: names(&["resource"]),
                continuations: names(&["continued"]),
            },
            Instruction::Return(names(&["continued"])),
        ];
        for private in [false, true] {
            let env = BTreeMap::from([("condition".into(), true), ("resource".into(), private)]);
            assert_eq!(checker.participant(&body, env, 0).unwrap(), vec![private]);
        }
    }
    #[test]
    fn malformed_normalized_bodies_refuse() {
        assert_eq!(
            check(vec![], vec![], 1000).unwrap_err().0,
            "native-proof-dependency-shape"
        );
        assert_eq!(
            check(vec![], vec![call("absent", &[], &[])], 1000)
                .unwrap_err()
                .0,
            "native-proof-dependency-scope"
        );
        let missing_return = function("broken", &[], 0, vec![]);
        assert_eq!(
            check(vec![missing_return], vec![call("broken", &[], &[])], 1000)
                .unwrap_err()
                .0,
            "native-proof-dependency-shape"
        );
        let body = vec![
            loop_body(
                "public",
                &[("carry", "public")],
                &[],
                vec![Instruction::Yield(vec![])],
                &["out"],
            ),
            Instruction::Return(names(&["out"])),
        ];
        assert_eq!(
            check(vec![], body, 1000).unwrap_err().0,
            "native-proof-dependency-shape"
        );
    }
    #[test]
    fn producer_start_requires_shared_arguments() {
        let body = vec![
            query("private"),
            call("observe", &["private"], &["state"]),
            Instruction::Return(names(&["state"])),
        ];
        assert_eq!(
            check_as(vec![identity()], body, 1000, true).unwrap_err().0,
            "native-proof-private-dependency"
        );
    }
    #[test]
    fn producer_can_observe_and_reuse_a_published_value() {
        let body = vec![
            query("private"),
            Instruction::Send {
                site: "publish".into(),
                schema: "publish".into(),
                peer: "V".into(),
                input: "private".into(),
            },
            call("observe", &["private"], &["state"]),
            Instruction::Return(names(&["state"])),
        ];
        assert_eq!(
            check_as(vec![identity()], body, 1000, true).unwrap(),
            vec![false]
        );
    }
    #[test]
    fn publication_does_not_reveal_the_values_used_to_compute_it() {
        let derived = function(
            "derived",
            &["input"],
            1,
            vec![LocalInstruction::Return(names(&["input"]))],
        );
        let body = vec![
            query("private"),
            call("derived", &["private"], &["published"]),
            Instruction::Send {
                site: "publish".into(),
                schema: "publish".into(),
                peer: "V".into(),
                input: "published".into(),
            },
            call("observe", &["private"], &["state"]),
            Instruction::Return(names(&["state"])),
        ];
        assert_eq!(
            check_as(vec![identity(), derived], body, 1000, true)
                .unwrap_err()
                .0,
            "native-proof-private-dependency"
        );
    }
    #[test]
    fn published_value_can_feed_replay_without_revealing_its_input() {
        let derived = function(
            "derived",
            &["input"],
            1,
            vec![LocalInstruction::Return(names(&["input"]))],
        );
        let body = vec![
            query("private"),
            call("derived", &["private"], &["published"]),
            Instruction::Send {
                site: "publish".into(),
                schema: "publish".into(),
                peer: "V".into(),
                input: "published".into(),
            },
            call("derived", &["published"], &["replay"]),
            call("observe", &["replay"], &["state"]),
            Instruction::Return(names(&["state", "private"])),
        ];
        assert_eq!(
            check_as(vec![identity(), derived], body, 1000, true).unwrap(),
            [false, true]
        );
    }
    #[test]
    fn later_publication_cannot_authorize_an_earlier_observation() {
        let body = vec![
            query("private"),
            call("observe", &["private"], &["state"]),
            Instruction::Send {
                site: "publish".into(),
                schema: "publish".into(),
                peer: "V".into(),
                input: "private".into(),
            },
            Instruction::Return(names(&["state"])),
        ];
        assert_eq!(
            check_as(vec![identity()], body, 1000, true).unwrap_err().0,
            "native-proof-private-dependency"
        );
    }
    #[test]
    fn publishing_a_related_value_does_not_authorize_a_private_loop_count() {
        let derived = function(
            "derived",
            &["input"],
            1,
            vec![LocalInstruction::Return(names(&["input"]))],
        );
        let body = vec![
            query("private_count"),
            call("derived", &["private_count"], &["published"]),
            Instruction::Send {
                site: "publish".into(),
                schema: "publish".into(),
                peer: "V".into(),
                input: "published".into(),
            },
            loop_body(
                "private_count",
                &[],
                &["public"],
                vec![
                    call("observe", &["public"], &["state"]),
                    Instruction::Yield(vec![]),
                ],
                &[],
            ),
            Instruction::Return(vec![]),
        ];
        assert_eq!(
            check_as(vec![identity(), derived], body, 1000, true)
                .unwrap_err()
                .0,
            "native-proof-private-dependency"
        );
    }
    #[test]
    fn ordinary_returns_retain_per_output_dependencies() {
        let split = function(
            "split",
            &["a", "b"],
            2,
            vec![LocalInstruction::Return(names(&["a", "b"]))],
        );
        let result = check(
            vec![split, identity()],
            vec![
                query("secret"),
                call("split", &["public", "secret"], &["shared", "private"]),
                call("observe", &["shared"], &["state"]),
                Instruction::Return(names(&["state", "private"])),
            ],
            1000,
        )
        .unwrap();
        assert_eq!(result, [false, true]);
    }
    #[test]
    fn private_adapter_arguments_refuse() {
        assert_eq!(
            check(
                vec![identity()],
                vec![
                    query("secret"),
                    call("observe", &["secret"], &["state"]),
                    Instruction::Return(names(&["state"]))
                ],
                1000
            )
            .unwrap_err()
            .0,
            "native-proof-private-dependency"
        );
    }
    #[test]
    fn a_private_branch_taints_even_public_branch_results() {
        let choose = function(
            "choose",
            &["condition", "a"],
            1,
            vec![
                LocalInstruction::Conditional {
                    site: "choose".into(),
                    condition: "condition".into(),
                    captures: names(&["a"]),
                    then_body: vec![LocalInstruction::Yield(names(&["a"]))].into(),
                    else_body: vec![LocalInstruction::Yield(names(&["a"]))].into(),
                    outputs: names(&["result"]),
                },
                LocalInstruction::Return(names(&["result"])),
            ],
        );
        assert_eq!(
            check(
                vec![choose, identity()],
                vec![
                    query("secret"),
                    call("choose", &["secret", "public"], &["chosen"]),
                    call("observe", &["chosen"], &["state"]),
                    Instruction::Return(names(&["state"]))
                ],
                1000
            )
            .unwrap_err()
            .0,
            "native-proof-private-dependency"
        );
    }
    #[test]
    fn loop_fixed_point_catches_a_later_private_count() {
        let inner = loop_body(
            "carried",
            &[],
            &["public"],
            vec![
                call("observe", &["public"], &["state"]),
                Instruction::Yield(vec![]),
            ],
            &[],
        );
        let outer = loop_body(
            "public",
            &[("carried", "public")],
            &["public"],
            vec![
                inner,
                query("secret"),
                Instruction::Yield(names(&["secret"])),
            ],
            &["out"],
        );
        assert_eq!(
            check(
                vec![identity()],
                vec![outer, Instruction::Return(vec![])],
                1000
            )
            .unwrap_err()
            .0,
            "native-proof-private-dependency"
        );
    }
    #[test]
    fn private_local_loop_may_feed_a_verdict_but_not_a_shared_action() {
        let body = vec![
            query("secret"),
            loop_body(
                "secret",
                &[("a", "public")],
                &[],
                vec![Instruction::Yield(names(&["a"]))],
                &["verdict"],
            ),
            Instruction::Return(names(&["verdict"])),
        ];
        assert_eq!(check(vec![], body, 1000).unwrap(), [true]);
        let body = vec![
            query("secret"),
            Instruction::Send {
                site: "send".into(),
                schema: "send".into(),
                peer: "P".into(),
                input: "secret".into(),
            },
            Instruction::Return(vec![]),
        ];
        assert_eq!(
            check(vec![], body, 1000).unwrap_err().0,
            "native-proof-private-dependency"
        );
    }
    #[test]
    fn local_loop_propagates_carried_dependencies() {
        let local = function(
            "fold",
            &["limit", "private"],
            1,
            vec![
                LocalInstruction::For {
                    conditional: false,
                    site: "fold".into(),
                    induction: "i".into(),
                    lower: "limit".into(),
                    upper: "limit".into(),
                    carried: vec![("a".into(), "limit".into())],
                    captures: names(&["private"]),
                    body: vec![LocalInstruction::Yield(names(&["private"]))].into(),
                    outputs: names(&["r"]),
                },
                LocalInstruction::Return(names(&["r"])),
            ],
        );
        let body = vec![
            query("secret"),
            call("fold", &["public", "secret"], &["out"]),
            Instruction::Return(names(&["out"])),
        ];
        assert_eq!(check(vec![local], body, 1000).unwrap(), [true]);
    }
    #[test]
    fn bounded_dependency_work_refuses() {
        assert_eq!(
            check(
                vec![],
                vec![query("private"), Instruction::Return(names(&["private"]))],
                1
            )
            .unwrap_err()
            .0,
            "native-proof-dependency-limit"
        );
    }
    #[test]
    fn missing_normalized_definition_refuses_without_panicking() {
        assert_eq!(
            check(
                vec![identity()],
                vec![
                    call("observe", &["missing"], &["state"]),
                    Instruction::Return(names(&["state"]))
                ],
                1000
            )
            .unwrap_err()
            .0,
            "native-proof-dependency-scope"
        );
    }
    #[test]
    fn a_private_guard_does_not_taint_the_surviving_value() {
        let guard = function(
            "guard",
            &["condition", "value"],
            1,
            vec![
                LocalInstruction::Conditional {
                    site: "guard".into(),
                    condition: "condition".into(),
                    captures: names(&["value"]),
                    then_body: vec![LocalInstruction::Stop {
                        site: "stop".into(),
                        reason: "reject".into(),
                    }]
                    .into(),
                    else_body: vec![LocalInstruction::Yield(names(&["value"]))].into(),
                    outputs: names(&["out"]),
                },
                LocalInstruction::Return(names(&["out"])),
            ],
        );
        let result = check(
            vec![guard, identity()],
            vec![
                query("private"),
                call("guard", &["private", "public"], &["surviving"]),
                call("observe", &["surviving"], &["state"]),
                Instruction::Return(names(&["state"])),
            ],
            1000,
        )
        .unwrap();
        assert_eq!(result, [false]);
    }
    #[test]
    fn conditional_local_loop_retains_the_private_exit_dependency() {
        let fold = function(
            "fold",
            &["limit", "condition"],
            1,
            vec![
                LocalInstruction::For {
                    conditional: true,
                    site: "fold".into(),
                    induction: "i".into(),
                    lower: "limit".into(),
                    upper: "limit".into(),
                    carried: vec![("a".into(), "limit".into())],
                    captures: names(&["condition"]),
                    body: vec![LocalInstruction::Yield(names(&["condition", "a"]))].into(),
                    outputs: names(&["out"]),
                },
                LocalInstruction::Return(names(&["out"])),
            ],
        );
        assert_eq!(
            check(
                vec![fold],
                vec![
                    query("private"),
                    call("fold", &["public", "private"], &["out"]),
                    Instruction::Return(names(&["out"]))
                ],
                1000
            )
            .unwrap(),
            [true]
        );
    }
    #[test]
    fn shared_scan_has_its_own_depth_bound() {
        let mut nested = vec![
            call("observe", &["public"], &["state"]),
            Instruction::Yield(vec![]),
        ];
        for _ in 0..65 {
            nested = vec![
                loop_body("public", &[], &["public"], nested, &[]),
                Instruction::Yield(vec![]),
            ];
        }
        assert_eq!(
            check(
                vec![identity()],
                vec![
                    query("private"),
                    loop_body("private", &[], &["public"], nested, &[]),
                    Instruction::Return(vec![])
                ],
                10000
            )
            .unwrap_err()
            .0,
            "native-proof-dependency-limit"
        );
    }
    #[test]
    fn cached_output_copy_is_charged() {
        let wide = function(
            "wide",
            &[],
            32,
            vec![
                LocalInstruction::BoolConstant {
                    site: "constant".into(),
                    output: "value".into(),
                    value: false,
                },
                LocalInstruction::Return(vec!["value".into(); 32]),
            ],
        );
        let functions = BTreeMap::from([("wide".into(), wide)]);
        let adapters = BTreeSet::new();
        let mut checker = Dependencies {
            functions: &functions,
            adapters: &adapters,
            returns: &[],
            cache: BTreeMap::new(),
            work: 1000,
            producer: false,
        };
        checker.local("wide", vec![]).unwrap();
        checker.work = 5;
        assert_eq!(
            checker.local("wide", vec![]).unwrap_err().0,
            "native-proof-dependency-limit"
        );
    }
}
