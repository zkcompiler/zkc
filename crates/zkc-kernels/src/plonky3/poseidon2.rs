//! The width-16 Poseidon2 permutation over KoalaBear with Plonky3 0.8.0's
//! default parameters: `p3_koala_bear::default_koalabear_poseidon2_16`, with
//! eight full rounds, twenty partial rounds, the cube S-box, the Grain-LFSR round
//! constants and the internal diagonal pinned by that release. The kernel
//! permutes each consecutive 16-element state of one vector. See
//! docs/spec/domains/permutations.md.
use super::KoalaBear;
use crate::interop::Work;
use p3_koala_bear::{Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_symmetric::Permutation;
use std::sync::OnceLock;

/// Invalid state width at the typed permutation boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Width,
}

/// Field elements in one permutation state.
pub const WIDTH: usize = 16;

/// The installed instance, constructed once from the pinned constants.
pub fn permutation() -> &'static Poseidon2KoalaBear<WIDTH> {
    static PERMUTATION: OnceLock<Poseidon2KoalaBear<WIDTH>> = OnceLock::new();
    PERMUTATION.get_or_init(default_koalabear_poseidon2_16)
}

/// Logical work of permuting `elements` values: one unit per state.
pub fn work(elements: usize) -> Result<Work, Error> {
    if !elements.is_multiple_of(WIDTH) {
        return Err(Error::Width);
    }
    Ok(Work {
        permutations: (elements / WIDTH) as u64,
        ..Work::default()
    })
}

/// Append every permuted consecutive state of `states` to `out`, in order.
/// Invalid widths leave `out` untouched. Callers may reserve destination space
/// before evaluation; this primitive imposes no allocation or work policy.
pub fn permute_states(states: &[KoalaBear], out: &mut Vec<KoalaBear>) -> Result<(), Error> {
    if !states.len().is_multiple_of(WIDTH) {
        return Err(Error::Width);
    }
    for state in states.as_chunks::<WIDTH>().0 {
        let mut state = *state;
        permutation().permute_mut(&mut state);
        out.extend_from_slice(&state);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordered_states_append_the_pinned_permutation() {
        let states: Vec<_> = (0..48).map(KoalaBear::new).collect();
        let mut out = vec![KoalaBear::new(99)];
        permute_states(&states, &mut out).unwrap();
        assert_eq!(out[0], KoalaBear::new(99));
        for (state, block) in states
            .as_chunks::<WIDTH>()
            .0
            .iter()
            .zip(out[1..].chunks(WIDTH))
        {
            let mut expected = *state;
            default_koalabear_poseidon2_16().permute_mut(&mut expected);
            assert_eq!(block, expected);
        }
        assert_eq!(out.len(), states.len() + 1);
        assert_eq!(work(states.len()).unwrap().permutations, 3);
        let saved = out.clone();
        permute_states(&[], &mut out).unwrap();
        assert_eq!(out, saved);
        assert_eq!(work(0), Ok(Work::default()));
    }

    #[test]
    fn invalid_widths_leave_the_destination_unchanged() {
        for width in [1, 15, 17, 31] {
            let mut out = vec![KoalaBear::new(99)];
            assert_eq!(work(width), Err(Error::Width));
            assert_eq!(
                permute_states(&vec![KoalaBear::new(1); width], &mut out),
                Err(Error::Width)
            );
            assert_eq!(out, [KoalaBear::new(99)]);
        }
    }
}
