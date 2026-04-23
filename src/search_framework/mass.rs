use std::fmt;
use std::time::Duration;

/// A mass value measured as a **fraction** of the total search
/// space, in `[0, 1]` (clamped on aggregation). `total_mass` is
/// always `1.0` by contract — it represents the whole space to be
/// searched. `covered_mass` is the fraction of that space that a
/// handler has provably ruled out (either directly, or as the
/// product of accepted filters).
///
/// Fractions are additive over **disjoint** sub-cubes, which makes
/// this the right unit for the universal TTC formula
/// `remaining / (covered / elapsed)`. A previous iteration of this
/// type used `log2(|sub-cube|)` bits; that was mathematically
/// unsound because logs of disjoint cube sizes do not sum to the
/// log of the union. Handlers that want to report in bits can
/// compute `log2(1 / (1 - covered))` at display time without
/// changing the stored unit.
///
/// Handlers that can't cheaply compute a fraction (e.g. the sync
/// walker and the stochastic sampler) should credit `ZERO` and
/// set [`TtcQuality::Projected`] so the summary clearly signals
/// "no universal coverage; see mode-specific telemetry."
#[derive(Clone, Copy, Debug, Default, PartialEq, PartialOrd)]
pub struct MassValue(pub f64);

impl MassValue {
    pub const ZERO: Self = Self(0.0);
    /// Convenience: `total_mass = ONE` for every run.
    pub const ONE: Self = Self(1.0);

    pub fn saturating_sub(self, rhs: Self) -> Self {
        Self((self.0 - rhs.0).max(0.0))
    }
}

impl fmt::Display for MassValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.6}", self.0)
    }
}

/// Quality label for a published TTC estimate.
///
/// * [`TtcQuality::Direct`] — `covered_mass` is a real additive
///   fraction of the full search space; TTC is trustworthy as a
///   leading indicator.
/// * [`TtcQuality::Projected`] — `covered_mass` is estimate-only
///   (e.g. sync walker, stochastic sampler). The number is
///   present for dashboard continuity; mode-specific telemetry is
///   authoritative.
/// * [`TtcQuality::Hybrid`] — blend; used by adapters that report
///   a real partial fraction but rely on a tail projection for
///   the remainder.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TtcQuality {
    Direct,
    Projected,
    Hybrid,
}

pub type CoverageQuality = TtcQuality;

impl TtcQuality {
    /// Backward-compat alias: the original enum spelled this
    /// variant `Exact`. The three `Direct | Projected | Hybrid`
    /// labels from TELEMETRY.md replace it directly.
    #[allow(non_upper_case_globals)]
    pub const Exact: Self = TtcQuality::Direct;
}

#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct MassDelta {
    pub covered_exact: MassValue,
    pub covered_partial: MassValue,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MassSnapshot {
    pub total: MassValue,
    pub covered_exact: MassValue,
    pub covered_partial: MassValue,
}

impl MassSnapshot {
    pub fn new(total: MassValue) -> Self {
        Self {
            total,
            covered_exact: MassValue::ZERO,
            covered_partial: MassValue::ZERO,
        }
    }

    pub fn apply_delta(&mut self, delta: MassDelta) {
        self.covered_exact = MassValue((self.covered_exact.0 + delta.covered_exact.0).max(0.0));
        self.covered_partial =
            MassValue((self.covered_partial.0 + delta.covered_partial.0).max(0.0));

        if self.covered_exact.0 > self.total.0 {
            self.covered_exact = self.total;
        }

        let partial_cap = (self.total.0 - self.covered_exact.0).max(0.0);
        if self.covered_partial.0 > partial_cap {
            self.covered_partial = MassValue(partial_cap);
        }
    }

    pub fn covered(&self) -> MassValue {
        MassValue(self.covered_exact.0 + self.covered_partial.0)
    }

    pub fn remaining(&self) -> MassValue {
        self.total.saturating_sub(self.covered())
    }

    pub fn throughput_per_sec(&self, elapsed: Duration) -> MassValue {
        let secs = elapsed.as_secs_f64();
        if secs <= f64::EPSILON {
            MassValue::ZERO
        } else {
            MassValue(self.covered().0 / secs)
        }
    }

    pub fn ttc(&self, elapsed: Duration) -> Option<Duration> {
        let rate = self.throughput_per_sec(elapsed).0;
        if rate <= f64::EPSILON {
            None
        } else {
            Some(Duration::from_secs_f64(self.remaining().0 / rate))
        }
    }
}

pub trait SearchMassModel: Send + Sync {
    /// Always `MassValue::ONE` under the current fraction-based
    /// contract. Kept as a method so modes can override for
    /// diagnostic displays (e.g. report a scaled bit count).
    fn total_mass(&self) -> MassValue {
        MassValue::ONE
    }
    fn covered_mass(&self) -> MassValue;
    fn quality(&self) -> CoverageQuality;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn remaining_mass_never_negative() {
        let mut snap = MassSnapshot::new(MassValue::ONE);
        snap.apply_delta(MassDelta {
            covered_exact: MassValue(1.2),
            covered_partial: MassValue(0.1),
        });
        assert_eq!(snap.covered().0, 1.0);
        assert_eq!(snap.remaining().0, 0.0);
    }

    #[test]
    fn covered_mass_is_monotone_for_positive_deltas() {
        let mut snap = MassSnapshot::new(MassValue::ONE);
        let mut prev = snap.covered().0;
        for _ in 0..4 {
            snap.apply_delta(MassDelta {
                covered_exact: MassValue(0.1),
                covered_partial: MassValue(0.05),
            });
            assert!(snap.covered().0 >= prev);
            prev = snap.covered().0;
        }
    }

    #[test]
    fn ttc_is_none_when_rate_is_zero() {
        let snap = MassSnapshot::new(MassValue::ONE);
        assert!(snap.ttc(Duration::from_secs(5)).is_none());
    }

    #[test]
    fn disjoint_fractions_sum_to_one() {
        // The core reason we use fractions, not log2(sub-cube size):
        // disjoint sub-cubes are additive, so N chunks of size 1/N
        // sum to exactly 1. With log2(size) they would sum to
        // -N·log2(N), which is nonsense for "total space covered".
        let mut snap = MassSnapshot::new(MassValue::ONE);
        let n = 10;
        let chunk = 1.0 / n as f64;
        for _ in 0..n {
            snap.apply_delta(MassDelta {
                covered_exact: MassValue(chunk),
                covered_partial: MassValue::ZERO,
            });
        }
        assert!((snap.covered().0 - 1.0).abs() < 1e-9);
    }
}
