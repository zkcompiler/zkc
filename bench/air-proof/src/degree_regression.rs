//! Independent hostile producer retained from the argument review. It changes
//! one committed trace by X^N - 1, preserving every original trace-row value,
//! and bypasses the honest prover's degree and terminal checks. The production
//! verifier must reject its authenticated, correctly framed proof.
use super::*;
#[test]
fn rejects_degree_slack_with_authentic_openings() {
    for height in [2, 4, 8, 16, 32] {
        let p = Parameters {
            height,
            blowup: 4,
            queries: 128,
        };
        let (s, w) = example(height);
        let proof = degree_slack_prove(p, s, &w).unwrap();
        assert_eq!(verify(p, s, &proof), Err(Error::Terminal));
    }
}
fn degree_slack_prove(p: Parameters, s: Statement, witness: &Witness) -> Result<Proof> {
    let n = p.check()?;
    if [&witness.left, &witness.right, &witness.sum]
        .iter()
        .any(|v| v.len() != p.height)
    {
        return Err(Error::Shape);
    }
    let k = Kernels::default();
    let d = domain(n, shift())?;
    let de = domain(n, E::from(shift()))?;
    if domain(p.height, F::ONE)?.contains(shift()) || de.contains(E::ONE) {
        return Err(Error::Parameters);
    }
    let mut coeff = coefficients(
        &k,
        &[
            witness.left.clone(),
            witness.right.clone(),
            witness.sum.clone(),
        ],
    )?;
    coeff[0][0] -= F::ONE;
    coeff[0].resize(p.height + 1, F::ZERO);
    coeff[0][p.height] = F::ONE;
    assert_eq!(coeff[0].len(), p.height + 1);
    let main_values = evaluations(&k, &coeff, d)?;
    let (main_a, state_a) = commit(&[main_values[0].clone()])?;
    let (main_b, state_b) = commit(&main_values[1..])?;
    let mut t = Transcript::new(p, s);
    t.root(&main_a);
    t.root(&main_b);
    let beta = t.challenge()?;
    let aux = [
        prefixes(&witness.left, beta),
        prefixes(&witness.right, beta),
    ];
    let terminals = [*aux[0].last().unwrap(), *aux[1].last().unwrap()];
    let aux_coeff = coefficients(&k, &aux)?;
    let aux_values = evaluations(&k, &aux_coeff, de)?;
    let (aux_a, state_aux_a) = commit(&[aux_values[0].clone()])?;
    let (aux_b, state_aux_b) = commit(&[aux_values[1].clone()])?;
    t.root(&aux_a);
    t.root(&aux_b);
    for v in terminals {
        t.value(v);
    }
    let alpha = t.challenge()?;
    let at = |i| {
        [
            E::from(main_values[0][i]),
            E::from(main_values[1][i]),
            E::from(main_values[2][i]),
            aux_values[0][i],
            aux_values[1][i],
        ]
    };
    let mut q = [Vec::with_capacity(n), Vec::with_capacity(n)];
    for i in 0..n {
        let values = quotient_value(
            p,
            s,
            de.point(i).unwrap(),
            beta,
            alpha,
            terminals,
            [at(i), at((i + p.blowup) % n)],
        )?;
        for j in 0..2 {
            q[j].push(values[j]);
        }
    }
    let q_coeff: Vec<_> = q.iter().map(|v| k.interpolate(v, de).unwrap()).collect();
    assert_eq!(q_coeff[0].len(), p.height + 1);
    if q_coeff.iter().any(|c| c.len() > p.height + 1) {
        return Err(Error::Constraint);
    }
    let (q_root, state_q) = commit(&q)?;
    t.root(&q_root);
    let z = t.challenge()?;
    if z == E::ZERO || de.contains(z) || domain(p.height, E::ONE)?.contains(z) {
        return Err(Error::Challenge);
    }
    let gz = z * domain(p.height, E::ONE)?.generator();
    let base_e: Vec<Vec<E>> = coeff
        .iter()
        .map(|c| c.iter().copied().map(E::from).collect())
        .collect();
    let all: Vec<_> = base_e.iter().chain(aux_coeff.iter()).collect();
    let ood = Ood {
        current: core::array::from_fn(|i| polynomial::evaluate_at(all[i], z)),
        next: core::array::from_fn(|i| polynomial::evaluate_at(all[i], gz)),
        quotient: core::array::from_fn(|i| polynomial::evaluate_at(&q_coeff[i], z)),
    };
    ood.observe(&mut t);
    let opening_challenges = OpeningChallenges {
        point: z,
        next_point: gz,
        batch: t.challenge()?,
        degree_mix: t.challenge()?,
    };
    let mut current: Vec<E> = (0..n)
        .map(|i| {
            combined(
                at(i),
                [q[0][i], q[1][i]],
                &ood,
                de.point(i).unwrap(),
                &opening_challenges,
            )
        })
        .collect::<Result<_>>()?;
    let deep_coeff = k.interpolate(&current, de).unwrap();
    assert_eq!(deep_coeff.len(), p.height + 1);
    println!(
        "degree-slack: height={} a_degree={} q_a_degree={} deep_degree={}",
        p.height,
        coeff[0].len() - 1,
        q_coeff[0].len() - 1,
        deep_coeff.len() - 1
    );
    let mut current_domain = de;
    let mut layers = Vec::new();
    let mut states = Vec::new();
    for _ in 0..p.height.trailing_zeros() {
        let (root, state) = commit(&[current.clone()])?;
        t.root(&root);
        layers.push(root);
        states.push(state);
        let challenge = t.challenge()?;
        current = polynomial::fold(&current, current_domain, challenge).map_err(|_| Error::Fold)?;
        current_domain = current_domain.folded().unwrap();
    }
    let terminal = current[0];
    // Malicious prover ignores the honest terminal-constancy requirement.
    assert!(current.iter().any(|v| *v != terminal));
    t.value(terminal);
    // Freeze the entire query randomness before producing any query response.
    let indices = t.indices(p.queries, n / 2);
    let mut queries = Vec::new();
    for index in indices {
        let source_row = |i| {
            Ok(SourceRows {
                main: [open(&state_a, i)?, open(&state_b, i)?],
                aux: [open(&state_aux_a, i)?, open(&state_aux_b, i)?],
                quotient: open(&state_q, i)?,
            })
        };
        let source = [source_row(index)?, source_row(index + n / 2)?];
        let mut position = index;
        let mut size = n;
        let mut opened = Vec::new();
        for state in &states {
            let base = position % (size / 2);
            opened.push([open(state, base)?, open(state, base + size / 2)?]);
            position = base;
            size /= 2;
        }
        queries.push(Query {
            source,
            layers: opened,
        });
    }
    Ok(Proof {
        main: [main_a, main_b],
        aux: [aux_a, aux_b],
        quotient: q_root,
        terminals,
        ood,
        layers,
        terminal,
        queries,
    })
}
