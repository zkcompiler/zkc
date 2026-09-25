//! Direct baseline for the authored argument under integration, not a backend
//! operation. Two original AIRs are connected by challenged auxiliary products.
//! AIR -> scope quotients -> DEEP opening batching -> classical binary FRI.
//! Nonhiding, experimental parameters; no claimed security-bit estimate.

use crate::{
    oracle::{self, Digest, Octic as E, Shape, State},
    polynomial::{self, Domain, Kernels},
};
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::KoalaBear as F;

#[derive(Clone, Copy, Debug)]
pub struct Parameters {
    pub height: usize,
    pub blowup: usize,
    pub queries: usize,
}
#[derive(Clone, Copy, Debug)]
pub struct Statement {
    pub initial: F,
    pub final_value: F,
    pub sum: F,
}
#[derive(Clone, Debug)]
pub struct Witness {
    pub left: Vec<F>,
    pub right: Vec<F>,
    pub sum: Vec<F>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Parameters,
    Shape,
    Polynomial,
    Authentication,
    Challenge,
    Constraint,
    Connection,
    Opening,
    Fold,
    Terminal,
}
type Result<T> = std::result::Result<T, Error>;
const LIMIT: usize = 1 << 22;
const BYTE_LIMIT: usize = 1 << 30;

struct Transcript(merlin::Transcript);
impl Transcript {
    fn new(p: Parameters, s: Statement) -> Self {
        let mut t = merlin::Transcript::new(b"zkc.air-permutation.argument/2");
        t.append_message(
            b"profile",
            b"koala-bear/ext8-binomial3;canonical-natural-order;keccak-framed-merkle/1",
        );
        for n in [p.height, p.blowup, p.queries] {
            t.append_message(b"parameter", &(n as u64).to_le_bytes());
        }
        for f in [s.initial, s.final_value, s.sum] {
            t.append_message(b"statement", &f.as_canonical_u32().to_le_bytes());
        }
        Self(t)
    }
    fn root(&mut self, root: &Digest) {
        self.0.append_message(b"oracle-root", root);
    }
    fn value(&mut self, value: E) {
        let bytes: Vec<u8> = value
            .as_basis_coefficients_slice()
            .iter()
            .flat_map(|c: &F| c.as_canonical_u32().to_le_bytes())
            .collect();
        self.0.append_message(b"extension-value", &bytes);
    }
    fn challenge(&mut self) -> Result<E> {
        let mut coordinates = [F::ZERO; 8];
        let mut count = 0;
        for _ in 0..16 {
            let mut b = [0u8; 64];
            self.0.challenge_bytes(b"challenge", &mut b);
            for word in b.as_chunks::<4>().0 {
                let n = u32::from_le_bytes(*word) & 0x7fff_ffff;
                if n < F::ORDER_U32 {
                    coordinates[count] = F::from_u32(n);
                    count += 1;
                    if count == 8 {
                        return Ok(E::from_basis_coefficients_slice(&coordinates).unwrap());
                    }
                }
            }
        }
        Err(Error::Challenge)
    }
    fn indices(&mut self, count: usize, bound: usize) -> Vec<usize> {
        debug_assert!(bound.is_power_of_two() && bound <= LIMIT);
        (0..count)
            .map(|_| {
                let mut b = [0; 64];
                self.0
                    .append_message(b"query-bound", &(bound as u64).to_le_bytes());
                self.0.challenge_bytes(b"query-index", &mut b);
                u64::from_le_bytes(b[..8].try_into().unwrap()) as usize & (bound - 1)
            })
            .collect()
    }
}
fn shape(width: usize, height: usize) -> Result<Shape> {
    Shape::new(width, height, LIMIT * 4).map_err(|_| Error::Shape)
}
fn domain<T: p3_field::ExtensionField<F>>(n: usize, shift: T) -> Result<Domain<T>> {
    Domain::new(n, shift, LIMIT).map_err(|_| Error::Parameters)
}
impl Parameters {
    fn check(self) -> Result<usize> {
        if self.height < 2
            || !self.height.is_power_of_two()
            || self.blowup < 4
            || !self.blowup.is_power_of_two()
            || self.queries == 0
            || self.queries > 128
        {
            return Err(Error::Parameters);
        }
        self.height
            .checked_mul(self.blowup)
            .filter(|n| *n <= LIMIT)
            .ok_or(Error::Parameters)
    }
}
fn shift() -> F {
    F::GENERATOR
}
fn flatten<T: Copy>(columns: &[Vec<T>]) -> Vec<T> {
    (0..columns[0].len())
        .flat_map(|i| columns.iter().map(move |c| c[i]))
        .collect()
}
fn coefficients<T: p3_field::ExtensionField<F>>(
    k: &Kernels,
    columns: &[Vec<T>],
) -> Result<Vec<Vec<T>>> {
    columns
        .iter()
        .map(|c| {
            k.interpolate(c, domain(c.len(), T::ONE)?)
                .map_err(|_| Error::Polynomial)
        })
        .collect()
}
fn evaluations<T: p3_field::ExtensionField<F>>(
    k: &Kernels,
    columns: &[Vec<T>],
    d: Domain<T>,
) -> Result<Vec<Vec<T>>> {
    columns
        .iter()
        .map(|c| k.evaluate(c, d).map_err(|_| Error::Polynomial))
        .collect()
}
fn commit<T: oracle::Element>(columns: &[Vec<T>]) -> Result<(Digest, State<T>)> {
    oracle::commit(
        flatten(columns),
        shape(columns.len(), columns[0].len())?,
        BYTE_LIMIT,
    )
    .map_err(|_| Error::Shape)
}
fn prefixes(values: &[F], challenge: E) -> Vec<E> {
    let mut product = E::ONE;
    values
        .iter()
        .map(|v| {
            product *= challenge - E::from(*v);
            product
        })
        .collect()
}

/// Values at z and g*z, in order a,b,sum,product(a),product(b), followed by
/// the two batched quotient evaluations at z. This fixed ordering is a
/// protocol-library choice; the oracle adapter has no knowledge of it.
#[derive(Clone, Debug)]
pub struct Ood {
    pub current: [E; 5],
    pub next: [E; 5],
    pub quotient: [E; 2],
}
impl Ood {
    fn observe(&self, t: &mut Transcript) {
        for v in self
            .current
            .into_iter()
            .chain(self.next)
            .chain(self.quotient)
        {
            t.value(v);
        }
    }
}
fn quotient_value(
    p: Parameters,
    s: Statement,
    x: E,
    beta: E,
    alpha: E,
    terminals: [E; 2],
    rows: [[E; 5]; 2],
) -> Result<[E; 2]> {
    let h = domain(p.height, E::ONE)?;
    let last = h.point(p.height - 1).unwrap();
    let z_first = x - E::ONE;
    let z_last = x - last;
    let z_all = x.exp_u64(p.height as u64) - E::ONE;
    if z_first == E::ZERO || z_last == E::ZERO || z_all == E::ZERO {
        return Err(Error::Challenge);
    }
    let divisors = [z_first.inverse(), z_last / z_all, z_last.inverse()];
    Ok(quotient_with_divisors(
        s, beta, alpha, terminals, rows, divisors,
    ))
}
fn quotient_with_divisors(
    s: Statement,
    beta: E,
    alpha: E,
    terminals: [E; 2],
    rows: [[E; 5]; 2],
    divisors: [E; 3],
) -> [E; 2] {
    let [v, next] = rows;
    let constraint = [
        [
            v[0] - E::from(s.initial),
            next[0] - v[0] - E::ONE,
            v[0] - E::from(s.final_value),
            v[3] - (beta - v[0]),
            next[3] - v[3] * (beta - next[0]),
            v[3] - terminals[0],
        ],
        [
            v[2] - v[1],
            next[2] - v[2] - next[1],
            v[2] - E::from(s.sum),
            v[4] - (beta - v[1]),
            next[4] - v[4] * (beta - next[1]),
            v[4] - terminals[1],
        ],
    ];
    constraint.map(|c| {
        c.iter()
            .enumerate()
            .rev()
            .fold(E::ZERO, |acc, (i, v)| acc * alpha + *v * divisors[i % 3])
    })
}
struct OpeningChallenges {
    point: E,
    next_point: E,
    batch: E,
    degree_mix: E,
}
fn combined(
    v: [E; 5],
    quotient: [E; 2],
    ood: &Ood,
    x: E,
    challenges: &OpeningChallenges,
) -> Result<E> {
    let (z, gz) = (challenges.point, challenges.next_point);
    if x == z || x == gz {
        return Err(Error::Challenge);
    }
    let iz = (x - z).inverse();
    let igz = (x - gz).inverse();
    Ok(combined_with_inverses(
        v,
        quotient,
        ood,
        x,
        challenges,
        [iz, igz],
    ))
}
fn combined_with_inverses(
    v: [E; 5],
    quotient: [E; 2],
    ood: &Ood,
    x: E,
    challenges: &OpeningChallenges,
    inverses: [E; 2],
) -> E {
    let [iz, igz] = inverses;
    let eta = challenges.batch;
    let mut power = E::ONE;
    let mut result = E::ZERO;
    for ((value, at_z), at_gz) in v.into_iter().zip(ood.current).zip(ood.next) {
        result += power * (value - at_z) * iz;
        power *= eta;
        result += power * (value - at_gz) * igz;
        power *= eta;
    }
    for (value, at_z) in quotient.into_iter().zip(ood.quotient) {
        result += power * (value - at_z) * iz;
        power *= eta;
    }
    // Random degree correction tests both D and X*D. A fixed multiplier X
    // alone admits reciprocal words on the nonzero sampling domain.
    (E::ONE + challenges.degree_mix * x) * result
}

#[derive(Clone, Debug)]
pub struct Row<T> {
    pub values: Vec<T>,
    pub path: Vec<Digest>,
}
fn open<T: oracle::Element>(state: &State<T>, index: usize) -> Result<Row<T>> {
    let (values, path) = state.open(index).map_err(|_| Error::Opening)?;
    Ok(Row { values, path })
}
fn check_row<T: oracle::Element>(
    root: Digest,
    width: usize,
    n: usize,
    index: usize,
    row: &Row<T>,
) -> Result<()> {
    oracle::verify(root, shape(width, n)?, index, &row.values, &row.path)
        .map_err(|_| Error::Authentication)
}
#[derive(Clone, Debug)]
pub struct SourceRows {
    pub main: [Row<F>; 2],
    pub aux: [Row<E>; 2],
    pub quotient: Row<E>,
}
#[derive(Clone, Debug)]
pub struct Query {
    pub source: [SourceRows; 2],
    pub layers: Vec<[Row<E>; 2]>,
}
#[derive(Clone, Debug)]
pub struct Proof {
    pub main: [Digest; 2],
    pub aux: [Digest; 2],
    pub quotient: Digest,
    pub terminals: [E; 2],
    pub ood: Ood,
    pub layers: Vec<Digest>,
    pub terminal: E,
    pub queries: Vec<Query>,
}

pub fn prove(p: Parameters, s: Statement, witness: &Witness) -> Result<Proof> {
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
    let coeff = coefficients(
        &k,
        &[
            witness.left.clone(),
            witness.right.clone(),
            witness.sum.clone(),
        ],
    )?;
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
    let points: Vec<_> = (0..n).map(|i| de.point(i).unwrap()).collect();
    let last = domain(p.height, E::ONE)?.point(p.height - 1).unwrap();
    let denominators: Vec<_> = points
        .iter()
        .flat_map(|x| [*x - E::ONE, x.exp_u64(p.height as u64) - E::ONE, *x - last])
        .collect();
    if denominators.contains(&E::ZERO) {
        return Err(Error::Challenge);
    }
    let inverse = p3_field::batch_multiplicative_inverse(&denominators);
    let mut q = [Vec::with_capacity(n), Vec::with_capacity(n)];
    for i in 0..n {
        let values = quotient_with_divisors(
            s,
            beta,
            alpha,
            terminals,
            [at(i), at((i + p.blowup) % n)],
            [
                inverse[3 * i],
                (points[i] - last) * inverse[3 * i + 1],
                inverse[3 * i + 2],
            ],
        );
        for j in 0..2 {
            q[j].push(values[j]);
        }
    }
    let q_coeff: Vec<_> = q.iter().map(|v| k.interpolate(v, de).unwrap()).collect();
    if q_coeff.iter().any(|c| c.len() > p.height) {
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
    let denominators: Vec<_> = points.iter().flat_map(|x| [*x - z, *x - gz]).collect();
    if denominators.contains(&E::ZERO) {
        return Err(Error::Challenge);
    }
    let inverse = p3_field::batch_multiplicative_inverse(&denominators);
    let mut current: Vec<E> = (0..n)
        .map(|i| {
            combined_with_inverses(
                at(i),
                [q[0][i], q[1][i]],
                &ood,
                points[i],
                &opening_challenges,
                [inverse[2 * i], inverse[2 * i + 1]],
            )
        })
        .collect();
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
    if current.iter().any(|v| *v != terminal) {
        return Err(Error::Terminal);
    }
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

pub fn verify(p: Parameters, s: Statement, proof: &Proof) -> Result<()> {
    let n = p.check()?;
    let rounds = p.height.trailing_zeros() as usize;
    if proof.layers.len() != rounds
        || proof.queries.len() != p.queries
        || proof.queries.iter().any(|q| q.layers.len() != rounds)
    {
        return Err(Error::Shape);
    }
    let de = domain(n, E::from(shift()))?;
    let h = domain(p.height, E::ONE)?;
    if h.contains(E::from(shift())) || de.contains(E::ONE) {
        return Err(Error::Parameters);
    }
    let mut t = Transcript::new(p, s);
    for r in &proof.main {
        t.root(r);
    }
    let beta = t.challenge()?;
    for r in &proof.aux {
        t.root(r);
    }
    for v in proof.terminals {
        t.value(v);
    }
    if proof.terminals[0] != proof.terminals[1] {
        return Err(Error::Connection);
    }
    let alpha = t.challenge()?;
    t.root(&proof.quotient);
    let z = t.challenge()?;
    if z == E::ZERO || de.contains(z) || h.contains(z) {
        return Err(Error::Challenge);
    }
    if quotient_value(
        p,
        s,
        z,
        beta,
        alpha,
        proof.terminals,
        [proof.ood.current, proof.ood.next],
    )? != proof.ood.quotient
    {
        return Err(Error::Constraint);
    }
    proof.ood.observe(&mut t);
    let gz = z * domain(p.height, E::ONE)?.generator();
    let opening_challenges = OpeningChallenges {
        point: z,
        next_point: gz,
        batch: t.challenge()?,
        degree_mix: t.challenge()?,
    };
    let mut challenges = Vec::new();
    for root in &proof.layers {
        t.root(root);
        challenges.push(t.challenge()?);
    }
    t.value(proof.terminal);
    let indices = t.indices(p.queries, n / 2);
    for (index, query) in indices.into_iter().zip(&proof.queries) {
        let mut deep = [E::ZERO; 2];
        for (side, rows) in query.source.iter().enumerate() {
            let i = index + side * (n / 2);
            check_row(proof.main[0], 1, n, i, &rows.main[0])?;
            check_row(proof.main[1], 2, n, i, &rows.main[1])?;
            for j in 0..2 {
                check_row(proof.aux[j], 1, n, i, &rows.aux[j])?;
            }
            check_row(proof.quotient, 2, n, i, &rows.quotient)?;
            let v = [
                E::from(rows.main[0].values[0]),
                E::from(rows.main[1].values[0]),
                E::from(rows.main[1].values[1]),
                rows.aux[0].values[0],
                rows.aux[1].values[0],
            ];
            deep[side] = combined(
                v,
                [rows.quotient.values[0], rows.quotient.values[1]],
                &proof.ood,
                de.point(i).unwrap(),
                &opening_challenges,
            )?;
        }
        let mut d = de;
        let mut position = index;
        let mut expected = E::ZERO;
        for (r, pair) in query.layers.iter().enumerate() {
            let half = d.size() / 2;
            let base = position % half;
            for (side, row) in pair.iter().enumerate() {
                check_row(proof.layers[r], 1, d.size(), base + side * half, row)?;
            }
            let a = pair[0].values[0];
            let b = pair[1].values[0];
            if r == 0 {
                if [a, b] != deep {
                    return Err(Error::Opening);
                }
            } else if pair[position / half].values[0] != expected {
                return Err(Error::Fold);
            }
            let x = d.point(base).unwrap();
            expected = (a + b) / E::TWO + challenges[r] * (a - b) / (E::TWO * x);
            d = d.folded().unwrap();
            position = base;
        }
        if expected != proof.terminal {
            return Err(Error::Terminal);
        }
    }
    Ok(())
}

pub fn example(height: usize) -> (Statement, Witness) {
    let left: Vec<F> = (0..height).map(|i| F::from_usize(i + 3)).collect();
    let right: Vec<F> = (0..height).map(|i| left[(i * 5 + 1) % height]).collect();
    let mut acc = F::ZERO;
    let sum: Vec<F> = right
        .iter()
        .map(|x| {
            acc += *x;
            acc
        })
        .collect();
    (
        Statement {
            initial: left[0],
            final_value: left[height - 1],
            sum: acc,
        },
        Witness { left, right, sum },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn composed_argument_and_tampering() {
        for height in [2, 4, 8, 16, 32] {
            let p = Parameters {
                height,
                blowup: 4,
                queries: 6,
            };
            let (s, w) = example(height);
            let proof = prove(p, s, &w).unwrap();
            assert_eq!(verify(p, s, &proof), Ok(()));
            let mut bad = proof.clone();
            bad.ood.current[0] += E::ONE;
            assert!(verify(p, s, &bad).is_err());
            let mut bad = proof.clone();
            bad.terminals[1] += E::ONE;
            assert_eq!(verify(p, s, &bad), Err(Error::Connection));
            let mut bad = proof.clone();
            bad.queries[0].source[0].aux[0].values[0] += E::ONE;
            assert_eq!(verify(p, s, &bad), Err(Error::Authentication));
            let mut bad = proof.clone();
            bad.queries[0].layers[0][0].path[0][0] ^= 1;
            assert_eq!(verify(p, s, &bad), Err(Error::Authentication));
            let mut bad = proof.clone();
            bad.terminal += E::ONE;
            assert!(verify(p, s, &bad).is_err());
            let mut bad = proof.clone();
            bad.queries.pop();
            assert_eq!(verify(p, s, &bad), Err(Error::Shape));
            let mut wrong = s;
            wrong.sum += F::ONE;
            assert!(verify(p, wrong, &proof).is_err());
            let mut wrong = w.clone();
            wrong.left[0] += F::ONE;
            assert!(prove(p, s, &wrong).is_err());
            let mut wrong = w.clone();
            wrong.right[0] += F::ONE;
            let mut acc = F::ZERO;
            wrong.sum = wrong
                .right
                .iter()
                .map(|x| {
                    acc += *x;
                    acc
                })
                .collect();
            let mut statement = s;
            statement.sum = acc;
            // Each original AIR can be satisfied while the cross-AIR
            // permutation is false. The challenged connection must reject.
            let disconnected = prove(p, statement, &wrong).unwrap();
            assert_eq!(verify(p, statement, &disconnected), Err(Error::Connection));
        }
    }
}

#[cfg(test)]
#[path = "degree_regression.rs"]
mod degree_regression;

#[cfg(test)]
#[path = "laurent_regression.rs"]
mod laurent_regression;
