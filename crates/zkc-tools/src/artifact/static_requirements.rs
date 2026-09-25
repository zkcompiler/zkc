use serde_json::Value as Json;

/// Independent replay of the static requirement owner's versioned certificate.
/// `true` means the exact goal was proved under the supplied assumptions and
/// installed implications; `false` means unresolved. This does not authenticate
/// those declarations, perform sorted frontend formation, or admit an artifact.
/// The caller bounds JSON parsing; this function bounds all carrier collections.
pub fn replay_static_requirements(request: &Json, certificate: &Json) -> Result<Vec<bool>, String> {
    check(request, certificate)
}

use std::collections::HashSet;
type ReplayResult<T> = std::result::Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Term {
    Root(String),
    Project(usize, String),
    Apply(String, Vec<usize>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Predicate {
    name: String,
    arguments: Vec<usize>,
}
fn ensure(ok: bool, code: &str) -> ReplayResult<()> {
    if ok { Ok(()) } else { Err(code.into()) }
}
fn array(value: &Json, limit: usize) -> ReplayResult<&[Json]> {
    let result = value.as_array().ok_or("requirements-array")?;
    ensure(result.len() <= limit, "requirements-limit")?;
    Ok(result)
}
fn name(value: &Json) -> ReplayResult<String> {
    let s = value.as_str().ok_or("requirements-name")?;
    ensure(!s.is_empty() && s.len() <= 256, "requirements-name")?;
    Ok(s.into())
}
fn index(value: &Json) -> ReplayResult<usize> {
    let n = value.as_u64().ok_or("requirements-index")?;
    ensure(n <= 65536, "requirements-index")?;
    Ok(n as usize)
}
fn indices(value: &Json, limit: usize, bound: usize) -> ReplayResult<Vec<usize>> {
    array(value, limit)?
        .iter()
        .map(|v| {
            let n = index(v)?;
            ensure(n < bound, "requirements-index")?;
            Ok(n)
        })
        .collect()
}
fn predicate(value: &Json, count: usize) -> ReplayResult<Predicate> {
    let [head, args] = array(value, 2)? else {
        return Err("requirements-predicate".into());
    };
    let name = name(head)?;
    let arguments = indices(args, 16, count)?;
    ensure(name != "=" || arguments.len() == 2, "requirements-equality")?;
    Ok(Predicate { name, arguments })
}
fn equal(p: &Predicate, a: usize, b: usize) -> bool {
    p.name == "=" && p.arguments == [a, b]
}
pub(super) fn check(request: &Json, certificate: &Json) -> ReplayResult<Vec<bool>> {
    let [version, ts, ps, rs, gs] = array(request, 5)? else {
        return Err("requirements-format".into());
    };
    let [certificate_version, ss, answers] = array(certificate, 3)? else {
        return Err("requirements-format".into());
    };
    ensure(
        version == "zkc.requirements/1" && certificate_version == "zkc.requirements-certificate/1",
        "requirements-version",
    )?;
    let mut terms = Vec::new();
    let mut weights: Vec<usize> = Vec::new();
    let mut term_work = 0;
    let mut identities = HashSet::new();
    for t in array(ts, 128)? {
        let next = match array(t, 3)? {
            [Json::Null, key] => Term::Root(name(key)?),
            [parent, key] => {
                let parent = index(parent)?;
                ensure(parent < terms.len(), "requirements-term-index")?;
                Term::Project(parent, name(key)?)
            }
            [tag, head, args] if tag == "apply" => {
                Term::Apply(name(head)?, indices(args, 16, terms.len())?)
            }
            _ => return Err("requirements-term".into()),
        };
        let weight = 1 + match &next {
            Term::Root(_) => 0,
            Term::Project(parent, _) => weights[*parent],
            Term::Apply(_, children) => children.iter().map(|&i| weights[i]).sum(),
        };
        term_work += weight;
        ensure(term_work <= 16384, "requirements-work-limit")?;
        weights.push(weight);
        ensure(
            identities.insert(next.clone()),
            "requirements-duplicate-term",
        )?;
        terms.push(next);
    }
    let predicates = |value| {
        array(value, 1024)?
            .iter()
            .map(|v| predicate(v, terms.len()))
            .collect::<ReplayResult<Vec<_>>>()
    };
    let assumptions = predicates(ps)?;
    let goals = predicates(gs)?;
    let predicate_work = |p: &Predicate| 1 + p.arguments.iter().map(|&i| weights[i]).sum::<usize>();
    ensure(
        assumptions
            .iter()
            .chain(&goals)
            .map(&predicate_work)
            .sum::<usize>()
            <= 262144,
        "requirements-work-limit",
    )?;
    let mut rules = Vec::new();
    for rule in array(rs, 128)? {
        let [a, b] = array(rule, 2)? else {
            return Err("requirements-implication".into());
        };
        let (a, b) = (name(a)?, name(b)?);
        ensure(a != "=" && b != "=", "requirements-implication")?;
        rules.push((a, b));
    }
    let mut facts: Vec<Predicate> = Vec::new();
    let mut proof_work = 0;
    for step in array(ss, 65536)? {
        let [conclusion, tag, premises, declaration] = array(step, 4)? else {
            return Err("requirements-step".into());
        };
        let p = predicate(conclusion, terms.len())?;
        proof_work += predicate_work(&p);
        ensure(proof_work <= 262144, "requirements-work-limit")?;
        let premises = indices(premises, 17, facts.len())?;
        let declaration = index(declaration)?;
        let tag = tag.as_str().ok_or("requirements-rule")?;
        ensure(
            matches!(tag, "assumption" | "implication") || declaration == 0,
            "requirements-declaration",
        )?;
        let pairwise = |left: &[usize], right: &[usize], proofs: &[usize]| {
            left.len() == right.len()
                && left.len() == proofs.len()
                && left
                    .iter()
                    .zip(right)
                    .zip(proofs)
                    .all(|((&a, &b), &i)| equal(&facts[i], a, b))
        };
        let valid = match (tag, premises.as_slice()) {
            ("assumption", []) => assumptions.get(declaration) == Some(&p),
            ("reflexivity", []) => p.name == "=" && p.arguments[0] == p.arguments[1],
            ("symmetry", [a]) => p.name == "=" && equal(&facts[*a], p.arguments[1], p.arguments[0]),
            ("transitivity", [a, b]) => {
                p.name == "="
                    && facts[*a].name == "="
                    && facts[*a].arguments[0] == p.arguments[0]
                    && equal(&facts[*b], facts[*a].arguments[1], p.arguments[1])
            }
            ("projection", [i]) if p.name == "=" => {
                match (&terms[p.arguments[0]], &terms[p.arguments[1]]) {
                    (Term::Project(a, m), Term::Project(b, n)) => {
                        m == n && equal(&facts[*i], *a, *b)
                    }
                    _ => false,
                }
            }
            ("application", proofs) if p.name == "=" => {
                match (&terms[p.arguments[0]], &terms[p.arguments[1]]) {
                    (Term::Apply(f, a), Term::Apply(g, b)) => f == g && pairwise(a, b, proofs),
                    _ => false,
                }
            }
            ("transport", [source, proofs @ ..]) => {
                p.name != "="
                    && facts[*source].name == p.name
                    && pairwise(&facts[*source].arguments, &p.arguments, proofs)
            }
            ("implication", [source]) if p.name != "=" && p.arguments.len() == 1 => {
                rules.get(declaration).is_some_and(|(a, b)| {
                    facts[*source].name == *a
                        && p.name == *b
                        && facts[*source].arguments == p.arguments
                })
            }
            _ => false,
        };
        ensure(valid, "requirements-invalid-derivation")?;
        facts.push(p);
    }
    let answers = array(answers, 1024)?;
    ensure(answers.len() == goals.len(), "requirements-goal-count")?;
    answers
        .iter()
        .zip(&goals)
        .map(|(answer, goal)| {
            if answer.is_null() {
                return Ok(false);
            }
            ensure(
                facts.get(index(answer)?) == Some(goal),
                "requirements-wrong-conclusion",
            )?;
            Ok(true)
        })
        .collect()
}

#[cfg(test)]
mod tests;
